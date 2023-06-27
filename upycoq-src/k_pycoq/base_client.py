import asyncio
import json
import os
import re
import select
import selectors
import threading
from concurrent.futures import ThreadPoolExecutor
from enum import Enum
from typing import Union, Callable, Optional, Type

import cattrs
import lsprotocol.types
from lsprotocol import converters

from k_pycoq.jsonrpc_converter import to_json, from_json

JSONRPC_REQ_FORMAT = 'Content-Length: {content_length}\r\n\r\n{content}'

import time


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

    def send_message(self, message: Union[lsprotocol.types.NOTIFICATIONS, lsprotocol.types.REQUESTS]):
        """sends a message through jsonrpc"""
        content = json.dumps(self.converter.unstructure(message))
        self.stdin.write(self._add_header(content))
        self.stdin.flush()


class JSONRPCReader:
    def __init__(self, stdout, message_handler: Callable):
        """Creates a new endpoint for communicating through jsonrpc

        :param stdout: the stream to read jsonrpc messages from
        :param message_handler: a function is called everytime a message is received. Should take a single parameter
        which is the message received (in string form).
        """
        # pipe_read, self.pipe_write = os.pipe()
        self.stdout = stdout

        # create pipe for closing the reader
        # the selector will block until something is written to the pipe or stdout
        # Thus we can use the pipe to close the reader while stdout is blocking
        # self.close_pipe_read, self.close_pipe_write = os.pipe()
        # self.reader = selectors.DefaultSelector()
        # self.reader.register(self.stdout, selectors.EVENT_READ)
        # self.reader.register(self.close_pipe_read, selectors.EVENT_READ)

        self.closed = False

        # only one thread can read from stdout at a time
        self.stdout_lock = threading.Lock()
        # condition to signal to threads that the reader is closed
        # self.closed_event = asyncio.Event()
        # used to signal to other threads when JSONRPCReader is done reading a message,
        # and it is safe to interact with data structures that were modified by the message handler
        self.can_read = threading.Condition()

        # self.sel = selectors.DefaultSelector()
        # self.sel.register(self.stdout, selectors.EVENT_READ)
        # self.sel.register(self.close_pipe_read, selectors.EVENT_READ)

        # loop = asyncio.new_event_loop()
        # self.reading_task = loop.run_in_executor(None, self.begin_reading, message_handler)
        # close_task = loop.run_in_executor(None, self.closed_event.wait)

        # self._thread = asyncio.wait([reading_task, self.closed_event.wait()], return_when=asyncio.FIRST_COMPLETED)

        self.connection = threading.Thread(target=self.begin_reading, args=(message_handler,))
        self.connection.start()
        # self._thread = ThreadPoolExecutor(max_workers=1)
        # self._reader = self._thread.submit(self.begin_reading, message_handler)
        # self.loop = asyncio.get_event_loop()
        # print(self.loop)

        # async def create_connection():
        #     connection = asyncio.create_task(self.begin_reading(message_handler))
        #     print('connection created')
        #     print(connection)
        #     return connection
        #
        # print('creating connection')
        # self.connection = asyncio.run(create_connection())
        # print('connection created')
        # print(self.connection)

    def is_closed(self):
        """Returns true if the reader is closed, false otherwise."""
        return self.closed

    def close_thread(self):
        """Closes the reader thread."""
        # write to the pipe to unblock the reader thread
        # os.write(self.close_pipe_write, b'CloseEvent')
        # self.closed_event.set()
        # done, pending = await self._thread
        # self.reading_task.cancel()
        # close remaining tasks
        # for task in pending:
        #     task.cancel()
        self.connection.join()
        # self.connection.cancel()
        # try:
        #     await self.connection
        # except asyncio.CancelledError:
        #     pass
        # wait for connection
        # asyncio.SubprocessProtocol()
        # asyncio.wait_for(self.connection, None)
        # close auxiliary pipe
        # self.reader.close()
        # self.sel.close()
        # os.close(self.close_pipe_read)
        # os.close(self.close_pipe_write)

    def flush(self) -> str:
        """
        Flushes the stdout stream.
        :return: the flushed data
        """
        # make sure the reader thread is closed before flushing to prevent deadlock
        if not self.closed:
            self.close_thread()
        # print(self.stdout_lock.locked())
        print('Flushing Lock')
        if self.stdout.closed:
            raise EOFError('Stream closed.')
        return self.stdout.flush()

    def close(self):
        if self.closed:
            return

        self.flush()  # TODO: log this?
        print('Closing Lock')
        with self.stdout_lock:
            self.stdout.close()

        self.closed = True

    def __del__(self):
        self.close()

    # def reader_is_closed(self):
    #     """
    #     Returns true if the ReaderClose event has been sent, false otherwise.
    #     Used to prevent a thread from blocking while reading when trying to close thread.
    #     """
    #     print('Checking if reader is closed')
    #     # events = self.reader.select()
    #     (readable, _, _) = select.select([self.stdout], [], [])
    #     # print(events)
    #     print(readable)
    #     # return self.close_pipe_read in [key.fileobj for (key, _) in events]
    #     return self.close_pipe_read in readable

    def begin_reading(self, message_handler):
        """Starts reading from the reader. Continues reading until the reader is closed."""
        # reading_task = asyncio.create_task(self.read_loop(message_handler))
        # stoping_task = asyncio.create_task(asynself.closed_event.wait())

        self.read_loop(message_handler)

        with self.can_read:
            self.can_read.notify_all()

    def read_loop(self, message_handler):
        while True:
            response = self.read_response()
            with self.can_read:
                message_handler(response)
                self.can_read.notify_all()

    def read_response(self):
        """parses response from jsonrpc"""
        headers = {}
        while True:
            print('----- BEGIN READING HEADER -----')
            # events = self.sel.select()
            # for key, mask in events:
            #     if key.fileobj is self.close_pipe_read:
            #         return
            print('----- END READING HEADER -----')
            with self.stdout_lock:
                line = self.stdout.readline().strip()
            if line == 'Content-Length: 102':
                print('found it')
            print('----- END READING LINE -----')

            if line == '':
                break
            print(line, end='')
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

        print('----- BEGIN READING CONTENT -----')
        # events = self.sel.select()
        # for key, mask in events:
        #     if key.fileobj is self.close_pipe_read:
        #         return
        with self.stdout_lock:
            content = self.stdout.read(headers['Content-Length'])

        return content


# Convert JSONRPC to asyncio.Protocol
def get_header_regex():
    """matches any number of subsequent lines of the form "Header-Name: Value\r\n"""
    headers = ['Content-Length', 'Content-Type']
    # Union of all headers (Header-Name: (?P<HeaderName>[^\r\n]+)\r\n)
    header_lines = '|'.join([f'({header}: (?P<{header.replace("-", "")}>[^\r\n]+)\r\n)' for header in headers])

    return re.compile(rf'\s*({header_lines})+\r\n')


HEADER_PATTERN = get_header_regex()


# enum for the different types of messages
class MessageType(Enum):
    REQUEST = 0
    RESPONSE = 1
    NOTIFICATION = 2
    ERROR = 3


class JsonRPCProtocol(threading.Thread):

    def __init__(self, message_types: dict[str, Type],
                 response_types: dict[str, Type],
                 error_type: Type,
                 converter: cattrs.Converter = converters.get_converter()):
        """
        Implements the JSONRPC protocol. This protocol is used to communicate with the language server. It is
        implemented as an asyncio.Protocol and can be used with asyncio.
        :param message_types: A mapping from message method to message type
        e.g. {'textDocument/definition': TextDocumentDefinitionRequest}
        :param response_types: A mapping from message method to response type
        e.g. {'textDocument/definition': TextDocumentDefinitionResponse}
        :param error_type: The error type to use for error responses
        e.g. ResponseErrorMessage
        :param converter: The converter to use for converting attrs objects to and from JSON
        """
        self.message_types = message_types
        self.response_types = response_types
        self.error_type = error_type
        self.converter = converter

        self.request_history: dict = {}
        self._request_futures: dict = {}
        self.received_responses: dict = {}
        self.received_notifications = []

        self.wait_for_event = None
        self.wait_for_predicate = None

        self.transport = None
        self._message_buffer = []
        self.body_length = None

    async def wait_for(self, predicate: Callable, timeout=None):
        """
        Waits for a response that satisfies the given predicate. Warning, does not check response history, may
        want to call before sending a request.
        :param predicate: The predicate to use for the response. The predicate should take a response object as
        its only argument and return a boolean.
        :return: The response that satisfies the predicate.
        """
        if self.wait_for_event is not None:
            raise Exception('Already waiting for a response.')

        self.wait_for_predicate = predicate
        self.wait_for_event = asyncio.Event()
        response = await asyncio.wait_for(self.wait_for_event.wait(), timeout)

        self.wait_for_event = None
        self.wait_for_predicate = None

        return response

    async def wait_for_response(self, id: int, timeout=None):
        """
        Waits for a response to the given request.
        :param id: The id of the request to wait for.
        :return: The response to the given request.
        """
        if not self._request_futures[id].is_set():
            await asyncio.wait_for(self._request_futures[id].wait(), timeout)

        return self.received_responses[id]

    def connection_made(self, transport):
        self.transport = transport

    def get_message_kind(self, message):
        """
        Gets the type and group of the message.
        :param message: the message as a dict
        :return: the message type and message group (notification, request, response, error)
        """
        if 'method' in message:
            message_group = MessageType.REQUEST if 'id' in message else MessageType.NOTIFICATION
            message_type = self.message_types[message['method']]
            return message_type, message_group
        elif 'id' in message:
            response_for = self.request_history[message['id']].method
            return self.response_types[response_for], MessageType.RESPONSE
        elif 'error' in message:
            return self.error_type, MessageType.ERROR
        else:
            raise Exception(f'Received invalid response {message}')

    def handle_response(self, response, message_group: MessageType):
        """
        Handles the message by calling the appropriate handler.
        :param response: the response to handle
        :param message_group: the message group of the response
        """
        if message_group == MessageType.RESPONSE:
            if response.id in self.request_history:
                self.received_responses[response.id] = response
                self._request_futures[response.id].set()
            else:
                raise Exception(f'Received response with id {response.id} that was not requested')
        elif message_group == MessageType.NOTIFICATION:
            self.received_notifications.append(response)
        elif message_group == MessageType.ERROR:
            # TODO: custom internal error class to allow catching
            raise Exception(f'Received error response {response}')
        elif message_group == MessageType.REQUEST:
            raise Exception(f'Should not be receiving requests from server, but received {response}')

    def data_received(self, message):
        """
        Parses the incoming message and calls the message handler with the parsed message.
        Unlike typical asyncio protocols, this protocol expects to receive the entire message
        :param message: the jsonrpc message
        """

        # time_start = time.time()
        response = json.loads(message)

        if 'method' in response:
            if response['method'] == '$/coq/fileProgress':
                print(response)
                return

        response_type, message_group = self.get_message_kind(response)

        response = self.converter.structure(response, response_type)
        print(response)

        if self.wait_for_event is not None:
            if self.wait_for_predicate(response):
                self.wait_for_event.set()

        self.handle_response(response, message_group)

        # time_end = time.time()
        # self.time_read += time_end - time_start

        # matches any number of subsequent lines of the form "Header-Name: Value\r\n"
        # while len(message):
        #     # Append incoming data to buffer
        #     self._message_buffer += message
        #
        #     if self.body_length is None:
        #         # Look for the header of the message
        #         match = HEADER_PATTERN.match(self._message_buffer)
        #         if not match:
        #             # Message header is incomplete, wait for more data
        #             return
        #
        #         body_start = match.end()
        #         self._message_buffer = self._message_buffer[body_start:]
        #
        #         # Extract the body length
        #         self.body_length = int(match.group('ContentLength'))
        #
        #     if len(self._message_buffer) < self.body_length:
        #         # Message body is incomplete, wait for more data
        #         return
        #
        #     # We have received entire message body
        #     body, data = self._message_buffer[:self.body_length], self._message_buffer[self.body_length:]
        #     # reset buffer
        #     self._message_buffer = []
        #     self.body_length = None
        #     print(body)
        # self.message_handler(body)

    def read(self, stdout):
        while True:
            try:
                message = self.read_message(stdout)
                self.data_received(message)
            except EOFError:
                break

    @staticmethod
    def read_message(stdout):
        headers = {}
        while True:
            line = stdout.readline().strip()

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

        content = stdout.read(headers['Content-Length'])

        return content

    def connection_lost(self, exc):
        print('Connection lost')

    @staticmethod
    def _add_header(content: str):
        return JSONRPC_REQ_FORMAT.format(content_length=len(content), content=content)

    def send_message(self, message):
        """
        Sends a message to the server. Converts message to jsonrpc format and adds header.
        :param message: the message to send
        """
        if not message:
            return

        if self.transport is None:
            raise Exception('Transport is not set.')

        formatted_message = json.dumps(self.converter.unstructure(message))
        self.transport.write(self._add_header(formatted_message))

    def send_request(self, request):
        """
        Sends a request to the server and stores the request in the request history.
        :param request: the request message to send
        """
        self.request_history[request.id] = request
        self._request_futures[request.id] = threading.Event()
        self.send_message(request)

    def send_notification(self, notification):
        """
        Sends a notification to the server.
        :param notification: the notification message to send
        """
        self.send_message(notification)


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

    def __init__(self, message_types: dict[str, Type],
                 response_types: dict[str, Type],
                 error_type: Type,
                 stdin, stdout,
                 converter: cattrs.Converter = converters.get_converter()):
        """Creates a new jsonrpc client"""
        self.converter = converter
        self.message_types = message_types
        self.response_types = response_types
        self.error_type = error_type

        self.stdin = stdin
        self.stdout = stdout

        self.protocol = JsonRPCProtocol(message_types, response_types, error_type, converter)
        self.connection: Union[asyncio.Task, None] = None

        asyncio.run(self.start())

        # self.reader = JSONRPCReader(stdin, self.handle_response)
        # self.writer = JSONRPCWriter(stdout, converter)
        self.closed = False
        self.id = 0
        #
        # self.id = 0
        # self.request_history: dict[Id, lsprotocol.types.REQUESTS] = {}
        # self.notification_history: list[lsprotocol.types.NOTIFICATIONS] = []
        #
        # self.unfinished_requests: set[Id] = set()
        #
        # self.request_responses: dict[Id, lsprotocol.types.RESPONSES] = {}
        # self.other_responses: list[lsprotocol.types.RESPONSES] = []
        #
        # self.time_read = 0

    async def start(self):
        """Starts the client"""
        self.protocol.connection_made(self.stdout)
        self.connection = asyncio.create_task(
            self.protocol.read(self.stdin)
        )

    async def close_connection(self):
        """Closes connection to protocol. Note that stdin and stdout should be closed by now."""
        # TODO: test if this check works
        if not self.stdin.at_eof() or not self.stdout.at_eof():
            raise Exception('stdin and stdout must be closed before closing connection.')
        self.connection.cancel()
        await self.connection

    def close(self):
        """Closes the client"""
        self.closed = True
        asyncio.run(self.close_connection())

    def send_request(self, method: str, params, return_result: bool = False):
        """Sends request through jsonrpc.

        If return_result is true, the result of the request is returned. Note: will block until the result is received.
        :param method: the method to send
        :param params: the parameters to send
        :param return_result: whether to block and return the result of the request
        :return: the result of the request if return_result is true, otherwise None
        """
        if self.closed:
            raise Exception('Cannot send request on closed client')

        request_type = lsprotocol.types.METHOD_TO_TYPES[method][0]
        request = request_type(id=self.id, method=method, jsonrpc=self.jsonrpc_version, params=params)
        self.id += 1
        print(request)
        self.protocol.send_request(request)

        if return_result:
            return asyncio.run(self.protocol.wait_for_response(request.id))
        else:
            return None

    def send_notification(self, method: str, params):
        """sends notification through jsonrpc"""
        if self.closed:
            raise Exception('Cannot send request on closed client')

        notification_type = lsprotocol.types.METHOD_TO_TYPES[method][0]
        notification = notification_type(method=method, jsonrpc=self.jsonrpc_version, params=params)
        print(notification)
        self.protocol.send_notification(notification)

    def get_response(self, id: Id = None, timeout=None):
        """Gets a response from the server.

        If id is specified, the response with that id is returned. Otherwise, the next response is returned.
        :param id: the id of the response to get
        :param timeout: the timeout to wait for the response
        :return: the response
        """
        if id is None:
            return asyncio.run(self.protocol.wait_for_response(self.id - 1, timeout=timeout))
        else:
            return asyncio.run(self.protocol.wait_for_response(id, timeout=timeout))

    # def get_message_type(self, message):
    #     """
    #     Gets the type and group of the message.
    #     :param message: the message as a dict
    #     :return: the message type and message group (notification, request, response, error)
    #     """
    #     if 'method' in message:  # this is a notification/request
    #         message_group = 'request' if 'id' in message else 'notification'
    #         return lsprotocol.types.METHOD_TO_TYPES[message['method']][0], message_group
    #     elif 'id' in message:  # this is a response
    #         response_name = self.request_history[message['id']].method
    #         return lsprotocol.types.METHOD_TO_TYPES[response_name][1], 'response'
    #     elif 'error' in message:  # this is an error response
    #         return lsprotocol.types.ResponseErrorMessage, 'error'
    #     else:
    #         raise Exception(f'Received invalid response {message}')
    #
    # def handle_response(self, response: str):
    #     """handles response from jsonrpc"""
    #     time_start = time.time()
    #     response = json.loads(response)
    #     if 'method' in response:
    #         if response['method'] == '$/coq/fileProgress':
    #             print(response)
    #             return
    #     response_type, message_group = self.get_message_type(response)
    #
    #     response = self.converter.structure(response, response_type)
    #     print(response)
    #
    #     if message_group == 'response':
    #         if response.id in self.request_history:
    #             print(f'Received response {response.id}')
    #             self.request_responses[response.id] = response
    #             self.unfinished_requests.remove(response.id)
    #         else:
    #             raise Exception(f'Received response with id {response.id} that was not requested')
    #     elif message_group == 'notification':
    #         self.other_responses.append(response)
    #     elif message_group == 'error':
    #         # TODO: custom internal error class to allow catching
    #         raise Exception(f'Received error response {response}')
    #     elif message_group == 'request':
    #         raise Exception(f'Should not be receiving requests from server, but received {response}')
    #
    #     time_end = time.time()
    #     self.time_read += time_end - time_start
    #
    # def get_response(self, id: Id = None, timeout=None):
    #     """
    #     Waits until response for given request is received and returns it. If no id is specified, waits until all
    #     requests are finished and returns the last response
    #     """
    #     if id is not None and id not in self.request_history:
    #         raise Exception(f'No request with id {id} was sent.')
    #
    #     # acquire reader lock to prevent race conditions
    #     # and wait until response corresponding to id is received
    #     with self.reader.can_read:
    #         print(f'==== waiting for response {id} ====')
    #         print(self.unfinished_requests)
    #
    #         def wait_for():
    #             print(f'==== wait_for {id} ====')
    #             print(self.request_responses.keys())
    #             return id not in self.unfinished_requests or self.reader.is_closed()
    #
    #         # use last id if none is specified
    #         if id is None:
    #             id = self.id - 1
    #             self.reader.can_read.wait_for(
    #                 lambda: len(self.unfinished_requests) == 0 or self.reader.is_closed(),
    #                 timeout=timeout
    #             )
    #         else:
    #             self.reader.can_read.wait_for(
    #                 wait_for,
    #                 timeout=timeout
    #             )
    #
    #         if self.reader.is_closed():
    #             raise Exception('Reader closed before response was received. See log for details.')  # TODO: logging
    #
    #         return self.request_responses[id]


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
    message_types = {k: v[0] for k, v in lsprotocol.types.METHOD_TO_TYPES.items()}
    response_types = {k: v[1] for k, v in lsprotocol.types.METHOD_TO_TYPES.items()}
    error_type = lsprotocol.types.ResponseErrorMessage
    client = BaseClient(message_types, response_types, error_type, lsp.stdout, lsp.stdin)
    client.send_request('initialize', lsprotocol.types.InitializeParams(
        capabilities=lsprotocol.types.ClientCapabilities(),
        process_id=1234,
        root_path='/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith',
        root_uri='/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith',
        workspace_folders=[lsprotocol.types.WorkspaceFolder(
            name='debug_simple_arith',
            uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
        )]
    ))
    client.send_notification('initialized', lsprotocol.types.InitializedParams())
    client.send_notification('textDocument/didOpen', lsprotocol.types.DidOpenTextDocumentParams(
        text_document=lsprotocol.types.TextDocumentItem(
            uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                '/DebugSimpleArith.v',
            language_id='coq',
            version=1,
            text='Require Import Arith.\n'
                 'Theorem plus_0_n : forall n : nat, 0 + n = n.\n'
                 'Proof.\n'
                 '  intros n.\n'
                 '  simpl.\n'
                 '  reflexivity.\n'
                 'Qed.'
        )
    ))
    client.send_request('textDocument/definition', lsprotocol.types.DefinitionParams(
        text_document=lsprotocol.types.TextDocumentIdentifier(
            uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                '/DebugSimpleArith.v'
        ),
        position=lsprotocol.types.Position(line=4, character=5)
    ))
    client.get_response()
    import time
    time.sleep(3)
    print('-----------------')
    print(f'time: {client.time_read}')
    lsp.terminate()
    client.close()


if __name__ == '__main__':
    test_client()
