from pytp.lsp_config import LSPConfig
from pytp.lsp_endpoint import LSPEndpoint


class BaseClient:
    def __init__(self, stdin, stdout, config: LSPConfig):
        self.endpoint = LSPEndpoint(stdin, stdout, config)
        self.config = config
        self.id = 0

        # start the endpoint thread
        self.endpoint.start()

    def close(self):
        """
        Close the client. Make sure stdout is closed first, otherwise the thread will block on writing to stdout.
        """
        self.endpoint.join()

    def get_new_id(self) -> int:
        id = self.id
        self.id += 1
        return id

    def send_notification(self, method: str, params) -> None:
        """Make a `{method_name}` notification.
        :param method: The name of the method to call
        :param params: The parameters to send with the notification
        """
        self.endpoint.send_notification(method, params)

    def send_request(self, method: str, params, return_result: bool = False):
        """Make a `{method_name}` request.
        :param method: The name of the method to call
        :param params: The parameters to send with the request
        :param return_result: Whether to return the result of the request
        :return: The id of the request if return_result is False, otherwise the result of the request
        """
        id = self.get_new_id()
        result = self.endpoint.send_request(id, method, params, return_result=return_result)
        if return_result:
            return result
        else:
            return id

    def register_notification_callback(self, method: str, callback: callable) -> None:
        """
        Registers a callback that will be called when a notification with the given method is received.
        :param method: The method to register the callback for.
        :param callback: The callback to register. The callback should take a single parameter,
        the notification.
        """
        self.endpoint.register_notification_callback(method, callback)

    def unregister_notification_callback(self, method: str) -> None:
        """
        Unregisters a callback that was previously registered with `register_notification_callback`.
        :param method: The method to unregister the callback for.
        """
        self.endpoint.unregister_notification_callback(method)

    def wait_for_response(self, id: int, timeout=None):
        """
        Waits for and returns the response to a request with the given id.
        :param id: The id of the request to wait for
        :return: The response to the request with id `id`
        """
        return self.endpoint.wait_for_response(id, timeout=timeout)

    def received_messages(self, start: int = 0, wait_for_more: bool = False):
        """
        Generator for received messages. Iterates over all messages received from the server so far.
        :param start: The index of the first message to yield
        :param wait_for_more: Whether to wait for more messages to be received if there are no more messages to yield.
        """
        for message in self.endpoint.received_messages(start, wait_for_more):
            yield message
