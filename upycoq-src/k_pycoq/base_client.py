import threading
from typing import Union, Callable

import lsprotocol.types

from k_pycoq.json_converter import to_json, from_json

JSONRPC_REQ_FORMAT = 'Content-Length: {content_length}\r\n\r\n{content}'


class JSONRPCWriter:
    def __init__(self, stdin):
        """Creates a new endpoint for communicating through jsonrpc
        """
        self.stdin = stdin

    def close(self):
        self.stdin.close()

    def __del__(self):
        self.close()

    @staticmethod
    def _add_header(content: str):
        return JSONRPC_REQ_FORMAT.format(content_length=len(content), content=content)

    def send_message(self, notification: Union[lsprotocol.types.NOTIFICATIONS, lsprotocol.types.REQUESTS]):
        """sends a message through jsonrpc"""
        content = to_json(notification)
        self.stdin.write(self._add_header(content))
        self.stdin.flush()


class JSONRPCReader:
    def __init__(self, stdout, message_handler: Callable):
        """Creates a new endpoint for communicating through jsonrpc

        :param stdout: the stream to read jsonrpc messages from
        :param message_handler: a function is called everytime a message is received. Should take a single parameter
        which is the message received.
        """
        self.stdout = stdout

        self.can_read = threading.Condition()

        self.stop_event = threading.Event()
        self.connection = threading.Thread(target=self.begin_reading, args=(message_handler,))

    def close(self):
        self.stop_event.set()
        self.stdout.close()
        self.connection.join()

    def __del__(self):
        self.close()

    def begin_reading(self, message_handler):
        """Starts reading from the reader. Continues reading until the reader is closed."""
        while not self.stop_event.is_set():
            try:
                response = self.read_response()
                with self.can_read:
                    message_handler(response)
                    self.can_read.notify_all()
            except EOFError:
                break

    def read_response(self):
        """parses response from jsonrpc"""
        headers = {}
        while not self.stop_event.is_set():
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

        if 'Content-Length' not in headers:
            raise Exception(f'Received invalid response header. Expected Content-Length, got {headers}')

        if not isinstance(headers['Content-Length'], int):
            raise Exception(f'Received invalid content length {headers["Content-Length"]} of '
                            f'type {type(headers["Content-Length"])}')

        content = self.stdout.read(headers['Content-Length'])
        return from_json(content)


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

    def __init__(self, stdin, stdout):
        """Creates a new jsonrpc client"""
        self.reader = JSONRPCReader(stdin, self.handle_response)
        self.writer = JSONRPCWriter(stdout)
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

        request_type = lsprotocol.types.METHOD_TO_TYPES[method]
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

        notification_type = lsprotocol.types.METHOD_TO_TYPES[method]
        notification = notification_type(method=method, jsonrpc=self.jsonrpc_version, params=params)
        self.notification_history.append(notification)
        self.writer.send_message(notification)

    def handle_response(self, response: lsprotocol.types.MESSAGE_TYPES):
        """handles response from jsonrpc"""
        if isinstance(response, lsprotocol.types.RESPONSES):
            if response.id in self.request_history:
                self.request_responses[response.id] = response
                self.unfinished_requests.remove(response.id)
            else:
                raise Exception(f'Received response with id {response.id} that was not requested')
        elif isinstance(response, lsprotocol.types.NOTIFICATIONS):
            self.other_responses.append(response)
        elif isinstance(response, lsprotocol.types.ResponseErrorMessage):
            raise Exception(f'Received error response {response}')
        elif isinstance(response, lsprotocol.types.REQUESTS):
            raise Exception(f'Should not be receiving requests from server, but received {response}')
        else:
            raise Exception(f'Received invalid response {response}')

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
                self.reader.can_read.wait_for(lambda: len(self.unfinished_requests) == 0, timeout=timeout)
            else:
                self.reader.can_read.wait_for(lambda: id not in self.unfinished_requests, timeout=timeout)

            return self.request_responses[id]
