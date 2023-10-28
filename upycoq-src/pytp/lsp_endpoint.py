import threading
from collections import defaultdict
from typing import Optional

from lsprotocol import converters
from lsprotocol.types import LSPErrorCodes, ErrorCodes

from pytp.json_streams import JsonRpcStreamReader, JsonRpcStreamWriter
from pytp.lsp_config import LSPConfig

JSONRPC_VERSION = '2.0'


class LSPEndpoint(threading.Thread):
    """
    A class that represents an endpoint for a language server. It is used to send and receive messages to and from the
    server. It is also used to wait for responses to requests. It is a subclass of threading.Thread, so reading from
    stdout is done in a separate thread. This is necessary because the server might send notifications at any time,
    and we need to be able to handle them.

    Example:
        # create subprocess
        process = subprocess.Popen('coqlsp', stdin=subprocess.PIPE, stdout=subprocess.PIPE)

        message_types = {k: v[0] for k, v in lsprotocol.types.METHOD_TO_TYPES.items()}
        response_types = {k: v[1] for k, v in lsprotocol.types.METHOD_TO_TYPES.items()}
        error_type = lsprotocol.types.ResponseErrorMessage

        endpoint = LspEndpoint(process.stdin, process.stdout, message_types, response_types, error_type)
        endpoint.start()

        # send a request
        endpoint.send_request(1, 'initialize', {'capabilities': {}})

        # wait for response
        response = endpoint.wait_for_response(id=1)

        # to close, make sure to terminate the process first and then join the thread, otherwise the thread will block
        process.terminate()
        process.wait()
        endpoint.join()
    """

    def __init__(self, stdin, stdout, config: LSPConfig):
        threading.Thread.__init__(self)
        self.reader = JsonRpcStreamReader(stdout)
        self.writer = JsonRpcStreamWriter(stdin)

        # a list of messages that have been sent by the endpoint
        self.sent_messages = []
        # a list of messages that have been received by the endpoint
        self._received_messages = []
        # a dictionary mapping request ids to received responses
        self._received_responses = {}
        # a lock that is used to make sure that all received data is accessed in a threadsafe way
        self.received_data_lock = threading.Lock()
        # message received event
        self.message_received_event = threading.Event()
        # a dictionary of events that are used to wait for responses to requests
        self.response_events: dict[int, threading.Event] = {}
        # a dictionary mapping request ids to method names
        self.requested_methods: dict[int, str] = {}
        # a dictionary mapping method names to callbacks
        self.notification_callbacks: defaultdict[str, list[callable]] = defaultdict(list)
        # self.notification_callbacks: dict[str, dict[str, callable]] = {}

        self._converter = config.converter
        self.message_types = config.message_types
        self.response_types = config.response_types
        self.error_type = config.error_type

        self.server_did_error = False

    def join(self, timeout: Optional[float] = None):
        """
        Wait until the endpoint terminates.

        Override the default join method to make sure that the stdout is closed before joining the thread,
        otherwise the endpoint will hang.

        :param timeout: The timeout to wait for the thread to join.
        """
        if not self.reader.stdout.closed:
            raise Exception('stdout must be closed before closing the endpoint, otherwise the thread will hang.')

        if not not self.writer.stdin.closed:
            self.writer.close()

        super().join(timeout)

    def received_messages(self, start: int = 0, wait_for_more: bool = False):
        """
        Threadsafe iterable over the messages that have been received by the endpoint.
        :param start: The index to start at.
        :param wait_for_more: If True, the iterable will wait for more messages to be received if the index is out of
        bounds.
        """
        idx = start
        # loop through all messages that have already been received
        while True:
            with self.received_data_lock:
                if idx < len(self._received_messages):
                    message = self._received_messages[idx]
                    idx += 1
                elif wait_for_more:
                    # wait for more messages to be received
                    self.message_received_event.clear()
                    self.received_data_lock.release()
                    self.message_received_event.wait()
                    if self.server_did_error:
                        raise Exception('Error received from server. Check the logs for more information.')
                    self.received_data_lock.acquire()
                    continue
                else:
                    break
            yield message

    def wait_for_response(self, id: int, timeout=None):
        """
        Waits for a response to a request with the given id. Returns the response.
        """
        if not self.response_events.get(id):
            raise ValueError(f'No request with id {id} has been sent.')
        self.response_events[id].wait(timeout=timeout)
        if id not in self._received_responses.keys():
            return None
        response = self._received_responses[id]
        if isinstance(response, self.error_type):
            raise Exception(f'Error received from server: {response.error}')
        return response

    def register_notification_callback(self, method: str, callback: callable):
        """
        Registers a callback that will be called when a notification with the given method is received.
        :param method: The method of the notification.
        :param callback: The callback to call.
        :return: The index of the callback in the list of callbacks for the given method.
        """
        self.notification_callbacks[method].append(callback)
        return len(self.notification_callbacks[method]) - 1

    def unregister_notification_callback(self, method: str, idx: int):
        """
        Unregisters the callback that will be called when a notification with the given method is received.
        :param method: The method of the notification.
        :param idx: The index of the callback in the list of callbacks for the given method.
        """
        self.notification_callbacks[method].pop(idx)

    def run(self):
        while True:
            message = self.reader.read_message()
            if message is None:
                # stream was closed, time to stop the thread
                break

            method = message.get("method")
            id = message.get("id")
            result = message.get("result")
            error = message.get("error")

            # handle the 4 different kinds of messages
            if method:
                if id:
                    self.server_did_error = True
                    self.message_received_event.set()
                    raise ValueError(f'Should not receive requests from server, but received {message}')
                else:
                    # convert json to python object of type self.message_types[method]
                    notification = self._converter.structure(message, self.message_types[method])
                    with self.received_data_lock:
                        self._received_messages.append(notification)
                        self.message_received_event.set()

                    # handle notification callbacks
                    callback = self.notification_callbacks.get(method)
                    if callback:
                        for c in callback:
                            c(notification)
            else:
                if result is not None:
                    method = self.requested_methods[id]
                    # print(message)
                    # print(f'Received response to {self.response_types[method]}')
                    response = self._converter.structure(message, self.response_types[method])
                    with self.received_data_lock:
                        self._received_messages.append(response)
                        self._received_responses[id] = response
                        self.message_received_event.set()

                    # notify threads that are waiting for this response
                    self.response_events[id].set()
                elif error:
                    self.server_did_error = True
                    response = self._converter.structure(message, self.error_type)
                    with self.received_data_lock:
                        self._received_messages.append(response)
                        self._received_responses[id] = response
                        self.message_received_event.set()

                    self.response_events[id].set()

                    error = response.error
                    if error.code in list(LSPErrorCodes):
                        error_code = LSPErrorCodes(error.code).name
                    elif error.code in list(ErrorCodes):
                        error_code = ErrorCodes(error.code).name
                    else:
                        error_code = error.code
                    if error_code == 'RequestCancelled':
                        self.server_did_error = False
                        print('Request cancelled by client.')
                        continue
                    raise Exception(
                        f'Error received from server with error code: {error_code}, message: {error.message}')
                else:
                    self.server_did_error = True
                    raise ValueError(f'Failed to parse received message: {message}')

    def send_message(self, message):
        """
        Sends a message to the server.
        """
        if self.server_did_error:
            raise Exception('Server raised an error, cannot send message. Check the logs for more information.')
        message = self._converter.unstructure(message)
        self.writer.write_message(message)

    def send_notification(self, method: str, params):
        """
        Sends a notification to the server.
        :param method: The method to call
        :param params:  The parameters to pass to the method
        """
        if method not in self.message_types:
            raise ValueError(f'Unknown notification {method}')

        notification_type = self.message_types[method]
        notification = notification_type(method=method, jsonrpc=JSONRPC_VERSION, params=params)
        self.send_message(notification)

    def send_request(self, id, method: str, params, return_result: bool = False):
        """
        Sends a request to the server. If return_result is True, the method will block until a response is received.
        :param id: The id of the request
        :param method: The method to call
        :param params: The parameters to pass to the method
        :param return_result: Whether to wait for a response from the server
        :return: The response from the server if return_result is True else None
        """
        if id in self.response_events:
            raise ValueError(f'Request with id {id} has already been sent.')
        if method not in self.message_types:
            raise ValueError(f'Unknown request {method}')

        request_type = self.message_types[method]
        request = request_type(id=id, method=method, jsonrpc=JSONRPC_VERSION, params=params)

        self.response_events[id] = threading.Event()
        self.requested_methods[id] = method

        self.send_message(request)

        if return_result:
            self.response_events[id].wait()
            with self.received_data_lock:
                response = self._received_responses[id]
            # TODO: do we want to allow errors?
            if isinstance(response, self.error_type):
                raise Exception(f'Error received from server: {response.error}')
            return response.result


def example_endpoint():
    # test endpoint
    import os

    converter = converters.get_converter()

    # create to server pipe
    to_server_r, to_server_w = os.pipe()
    # create from server pipe
    from_server_r, from_server_w = os.pipe()

    to_server_r = os.fdopen(to_server_r, 'rb')
    to_server_w = os.fdopen(to_server_w, 'wb')
    from_server_r = os.fdopen(from_server_r, 'rb')
    from_server_w = os.fdopen(from_server_w, 'wb')

    # create 'server' aka stream readers
    server_reader = JsonRpcStreamReader(to_server_r)
    server_writer = JsonRpcStreamWriter(from_server_w)

    # create dummy types
    from typing import Any, Union
    import attrs

    @attrs.define
    class Notification:
        """A class that represents a generic json rpc notification message.
        Used as a fallback for unknown types.
        """

        method: str
        params: Any
        jsonrpc: str = attrs.field(default="2.0")

    @attrs.define
    class RequestMessage:
        """A class that represents a generic json rpc request message.
        Used as a fallback for unknown types.
        """

        id: Union[int, str]
        method: str
        params: Any
        jsonrpc: str = attrs.field(default="2.0")

    @attrs.define
    class ResponseMessage:
        """A class that represents a generic json rpc response message.
        Used as a fallback for unknown types.
        """

        id: Union[int, str]
        result: Any
        jsonrpc: str = attrs.field(default="2.0")

    @attrs.define
    class ResponseErrorMessage:
        id: Union[int, str]
        error: str
        jsonrpc: str = attrs.field(default="2.0")

    message_types = {'notification': Notification, 'request': RequestMessage}
    response_types = {'request': ResponseMessage}
    error_type = ResponseErrorMessage

    # create endpoint
    config = LSPConfig(
        message_types, response_types, error_type, converter=converter
    )
    endpoint = LSPEndpoint(to_server_w, from_server_r, config)
    endpoint.start()

    # ======== test basic send request ========
    # send a request
    endpoint.send_request(1, 'request', {'test': 'test'})

    # read the request from the pipe
    request = server_reader.read_message()
    assert request == converter.unstructure(
        RequestMessage(id=1, method='request', jsonrpc='2.0', params={'test': 'test'}))

    # send a response
    original_response = ResponseMessage(id=1, result={'test': 'test'})
    server_writer.write_message(converter.unstructure(original_response))

    # read the response from the pipe
    response = endpoint.wait_for_response(1)
    assert response == original_response.result

    # ======== test send a notification to endpoint with callback ========
    event = threading.Event()
    received_notification = []

    def callback(notification):
        received_notification.append(notification)
        event.set()

    endpoint.register_notification_callback('notification', callback)

    server_writer.write_message(
        converter.unstructure(Notification(method='notification', jsonrpc='2.0', params={'test': 'test'})))
    event.wait()
    assert received_notification[0] == Notification(method='notification', jsonrpc='2.0', params={'test': 'test'})

    # ======== test send a request to endpoint with return_result=True ========
    # send a response to endpoint before request is sent, so we don't block from return_result=True
    server_writer.write_message(converter.unstructure(ResponseMessage(id=2, result={'test': 'test'})))

    # send request from endpoint
    response = endpoint.send_request(2, 'request', {'test': 'test'}, return_result=True)
    assert response == ResponseMessage(id=2, result={'test': 'test'}).result

    # ======== test looping through received messages ========
    assert len([message for message in endpoint.received_messages()]) == 3

    # ======== test receive new message while looping ========
    event.clear()

    i = 0
    for _ in endpoint.received_messages():
        if i == 1:
            server_writer.write_message(converter.unstructure(
                Notification(method='notification', jsonrpc='2.0', params={'test': 'test'})
            ))
        if i == 2:
            # wait until endpoint has received the notification
            event.wait()
        i += 1
    assert i == 4

    # ======== test blocking loop with new message received ========
    i = 0
    for message in endpoint.received_messages(start=3, wait_for_more=True):
        if i == 0:
            server_writer.write_message(converter.unstructure(
                Notification(method='notification', jsonrpc='2.0', params={'test2': 'test'})
            ))
        if i == 1:
            # can only reach here if loop was successfully blocked until new message was received
            assert message == Notification(method='notification', jsonrpc='2.0', params={'test2': 'test'})
            break
        i += 1

    # ======== test error handling ========
    # uncomment to test (hard to catch these errors because they are from another thread)

    # ValueError: Error received from server: {'id': 3, 'error': 'test error', 'jsonrpc': '2.0'}
    # server_writer.write_message(converter.unstructure(ResponseErrorMessage(id=3, error='test error')))

    # ValueError: Failed to parse received message: {'badly formed': 'message'}
    # server_writer.write_message({'badly formed': 'message'})

    # ValueError: Should not receive requests from server, but received
    # {'id': 4, 'method': 'request', 'params': {'a': 'b'}}
    # server_writer.write_message(converter.unstructure(RequestMessage(id=4, method='request', params={'a': 'b'})))

    # test badly formed message
    # cattrs.errors.ClassValidationError: While structuring Notification (1 sub-exception)
    # TODO: perhaps we should catch cattrs errors to make them more readable
    # server_writer.write_message({'method': 'notification', 'badly formed': 'message'})

    try:
        endpoint.send_request(1, 'request', {'test': 'test'})
        raise Exception('Should have raised ValueError')
    except ValueError as e:
        assert str(e) == 'Request with id 1 has already been sent.'

    try:
        endpoint.send_request(5, 'bad name', {'test': 'test'})
        raise Exception('Should have raised ValueError')
    except ValueError as e:
        assert str(e) == 'Unknown request bad name'

    # close 'server'
    server_reader.close()
    server_writer.close()

    # close endpoint
    endpoint.join()

    # close remaining pipes
    to_server_w.close()
    from_server_r.close()

    print('Test passed!')


if __name__ == '__main__':
    example_endpoint()
