import json
import os
import select
import threading
from typing import Union, Callable, get_args, Optional

import cattrs
import lsprotocol.types
from lsprotocol import converters

from k_pycoq.jsonrpc_converter import to_json, from_json

JSONRPC_REQ_FORMAT = 'Content-Length: {content_length}\r\n\r\n{content}'


class JSONRPCWriter:
    def __init__(self, stdin, converter: cattrs.Converter):
        """Creates a new endpoint for communicating through jsonrpc
        """
        self.stdin = stdin
        self.converter = converter if converter is not None else converters.get_converter()

    def close(self):
        self.stdin.close()

    def __del__(self):
        self.close()

    @staticmethod
    def _add_header(content: str):
        return JSONRPC_REQ_FORMAT.format(content_length=len(content), content=content)

    def send_message(self, notification: Union[lsprotocol.types.NOTIFICATIONS, lsprotocol.types.REQUESTS]):
        """sends a message through jsonrpc"""
        content = json.dumps(self.converter.unstructure(notification))
        # content = '{"id": 0, "params": {"capabilities": {}}, "method": "initialize", "jsonrpc": "2.0"}'
        self.stdin.write(self._add_header(content))
        self.stdin.flush()


class JSONRPCReader:
    def __init__(self, stdout, message_handler: Callable):
        """Creates a new endpoint for communicating through jsonrpc

        :param stdout: the stream to read jsonrpc messages from
        :param message_handler: a function is called everytime a message is received. Should take a single parameter
        which is the message received (in string form).
        """
        self.stdout = stdout

        # create pipe for closing the reader
        # the selector will block until something is written to the pipe or stdout
        # Thus we can use the pipe to close the reader while stdout is blocking
        self.close_pipe_read, self.close_pipe_write = os.pipe()
        # self.reader = selectors.DefaultSelector()
        # self.reader.register(self.stdout, selectors.EVENT_READ)
        # self.reader.register(self.close_pipe_read, selectors.EVENT_READ)

        self.closed = False

        # only one thread can read from stdout at a time
        self.stdout_lock = threading.Lock()
        # used to signal to other threads when JSONRPCReader is done reading a message,
        # and it is safe to interact with data structures that were modified by the message handler
        self.can_read = threading.Condition()

        self.connection = threading.Thread(target=self.begin_reading, args=(message_handler,))
        self.connection.start()

    def is_closed(self):
        """Returns true if the reader is closed, false otherwise."""
        return self.closed

    def close_thread(self):
        """Closes the reader thread."""
        # write to the pipe to unblock the reader thread
        os.write(self.close_pipe_write, b'CloseEvent')
        self.connection.join()
        # close auxiliary pipe
        # self.reader.close()
        os.close(self.close_pipe_read)
        os.close(self.close_pipe_write)

    def flush(self) -> str:
        """
        Flushes the stdout stream.
        :return: the flushed data
        """
        # make sure the reader thread is closed before flushing to prevent deadlock
        if not self.closed:
            self.close_thread()
        with self.stdout_lock:
            if self.stdout.closed:
                raise EOFError('Stream closed.')
            return self.stdout.flush()

    def close(self):
        if self.closed:
            return

        self.flush()  # TODO: log this?
        with self.stdout_lock:
            self.stdout.close()

        self.closed = True

    def __del__(self):
        self.close()

    def reader_is_closed(self):
        """
        Returns true if the ReaderClose event has been sent, false otherwise.
        Used to prevent a thread from blocking while reading when trying to close thread.
        """
        (readable, _, _) = select.select([self.stdout, self.close_pipe_read], [], [])
        return self.close_pipe_read in readable

    def begin_reading(self, message_handler):
        """Starts reading from the reader. Continues reading until the reader is closed."""
        while True:
            response = self.read_response()
            if response is None:
                break
            with self.can_read:
                message_handler(response)
                self.can_read.notify_all()

        with self.can_read:
            self.can_read.notify_all()

    def read_response(self):
        """parses response from jsonrpc"""
        headers = {}
        while True:
            with self.stdout_lock:
                if self.reader_is_closed():
                    return
                line = self.stdout.readline().strip()

            if line == '':
                break

            header = line.split(':')

            if len(header) != 2:
                raise Exception(f'Received invalid header {line}')

            key, value = header[0].strip(), header[1].strip()
            if value.isdigit():
                value = int(value)
            headers[key] = value

        if len(headers) == 0:
            raise EOFError('Unexpected EOF while reading from stream.')  # TODO: just ignore this and try to continue?

        if 'Content-Length' not in headers:
            raise Exception(f'Received invalid response header. Expected Content-Length, got {headers}')

        if not isinstance(headers['Content-Length'], int):
            raise Exception(f'Received invalid content length {headers["Content-Length"]} of '
                            f'type {type(headers["Content-Length"])}')

        with self.stdout_lock:
            if self.reader_is_closed():
                return
            content = self.stdout.read(headers['Content-Length'])

        return content


# async def read_response(reader):
#     """parses response from jsonrpc format"""
#     headers = {}
#     while True:
#         line = await reader.readline().strip()
#
#         if line == '':
#             break
#
#         header = line.split(':')
#
#         if len(header) != 2:
#             raise Exception(f'Received invalid header {line}')
#
#         key, value = header[0].strip(), header[1].strip()
#         if value.isdigit():
#             value = int(value)
#         headers[key] = value
#
#     if len(headers) == 0:
#         raise EOFError()
#
#     if 'Content-Length' not in headers:
#         raise Exception(f'Received invalid response header. Expected Content-Length, got {headers}')
#
#     if not isinstance(headers['Content-Length'], int):
#         raise Exception(f'Received invalid content length {headers["Content-Length"]} of '
#                         f'type {type(headers["Content-Length"])}')
#
#     content = reader.read(headers['Content-Length'])
#
#     return content
#
#
# async def read_responses(reader):
#     """Iterable that yields responses from jsonrpc format as they are received"""
#     while True:
#         try:
#             response = await read_response(reader)
#         except EOFError:
#             raise StopAsyncIteration()
#
#         yield response

Id = Union[int, str]


class BaseClient:
    """Base class for jsonrpc clients"""
    jsonrpc_version = '2.0'

    def __init__(self, stdin, stdout, converter: Optional[cattrs.Converter] = None):
        """Creates a new jsonrpc client"""
        self.converter = converter if converter is not None else converters.get_converter()

        self.reader = JSONRPCReader(stdin, self.handle_response)
        self.writer = JSONRPCWriter(stdout, converter)
        self.closed = False

        self.id = 0
        self.request_history: dict[Id, lsprotocol.types.REQUESTS] = {}
        self.notification_history: list[lsprotocol.types.NOTIFICATIONS] = []

        self.unfinished_requests: set[Id] = set()

        self.request_responses: dict[Id, lsprotocol.types.RESPONSES] = {}
        self.other_responses: list[lsprotocol.types.RESPONSES] = []

    def close(self):
        """Closes the client"""
        self.closed = True
        self.reader.close()
        self.writer.close()

    def send_request(self, method: str, params, return_result: bool = False):
        """Sends request through jsonrpc.

        If return_result is true, the result of the request is returned. Note: will block until the result is received.
        """
        if self.closed:
            raise Exception('Cannot send request on closed client')

        request_type = lsprotocol.types.METHOD_TO_TYPES[method][0]
        request = request_type(id=self.id, method=method, jsonrpc=self.jsonrpc_version, params=params)
        self.request_history[request.id] = request
        self.unfinished_requests.add(request.id)
        self.id += 1
        self.writer.send_message(request)

        if return_result:
            return self.get_response(request.id)

    def send_notification(self, method: str, params):
        """sends notification through jsonrpc"""
        if self.closed:
            raise Exception('Cannot send request on closed client')

        notification_type = lsprotocol.types.METHOD_TO_TYPES[method][0]
        notification = notification_type(method=method, jsonrpc=self.jsonrpc_version, params=params)
        self.notification_history.append(notification)
        self.writer.send_message(notification)

    def get_message_type(self, message):
        """
        Gets the type and group of the message.
        :param message: the message as a dict
        :return: the message type and message group (notification, request, response, error)
        """
        if 'method' in message:  # this is a notification/request
            message_group = 'request' if 'id' in message else 'notification'
            return lsprotocol.types.METHOD_TO_TYPES[message['method']][0], message_group
        elif 'id' in message:  # this is a response
            response_name = self.request_history[message['id']].method
            return lsprotocol.types.METHOD_TO_TYPES[response_name][1], 'response'
        elif 'error' in message:  # this is an error response
            return lsprotocol.types.ResponseErrorMessage, 'error'
        else:
            raise Exception(f'Received invalid response {message}')

    def handle_response(self, response: str):
        """handles response from jsonrpc"""
        response = json.loads(response)
        response_type, message_group = self.get_message_type(response)

        response = self.converter.structure(response, response_type)
        print(response)

        if message_group == 'response':
            if response.id in self.request_history:
                self.request_responses[response.id] = response
                self.unfinished_requests.remove(response.id)
            else:
                raise Exception(f'Received response with id {response.id} that was not requested')
        elif message_group == 'notification':
            self.other_responses.append(response)
        elif message_group == 'error':
            # TODO: custom internal error class to allow catching
            raise Exception(f'Received error response {response}')
        elif message_group == 'request':
            raise Exception(f'Should not be receiving requests from server, but received {response}')

    def get_response(self, id: Id = None, timeout=None):
        """
        Waits until response for given request is received and returns it. If no id is specified, waits until all
        requests are finished and returns the last response
        """
        if id is not None and id not in self.request_history:
            raise Exception(f'No request with id {id} was sent.')

        # acquire reader lock to prevent race conditions
        # and wait until response corresponding to id is received
        with self.reader.can_read:
            # use last id if none is specified
            if id is None:
                id = self.id - 1
                self.reader.can_read.wait_for(
                    lambda: len(self.unfinished_requests) == 0 or self.reader.is_closed(),
                    timeout=timeout
                )
            else:
                self.reader.can_read.wait_for(
                    lambda: id not in self.unfinished_requests or self.reader.is_closed(),
                    timeout=timeout
                )

            if self.reader.is_closed():
                raise Exception('Reader closed before response was received. See log for details.')  # TODO: logging

            return self.request_responses[id]


def test_client():
    from pathlib import Path
    import subprocess
    from k_pycoq.opam import create_opam_subprocess
    """Tests the client by sending a request and receiving a response"""
    lsp = create_opam_subprocess('coq-lsp --bt', 'coqlsp',
                                 Path('/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug'
                                      '/debug_simple_arith'),
                                 stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
    client = BaseClient(lsp.stdout, lsp.stdin)
    print(client.send_request('initialize', lsprotocol.types.InitializeParams(
        capabilities=lsprotocol.types.ClientCapabilities(),
        process_id=1234,
        root_path='/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith',
        root_uri='/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith',
        workspace_folders=[lsprotocol.types.WorkspaceFolder(
            name='debug_simple_arith',
            uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
        )]
    ), return_result=True))
    client.close()

if __name__ == '__main__':
    test_client()