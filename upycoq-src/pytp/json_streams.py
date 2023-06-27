import threading
import json

CONTENT_LENGTH_HEADER = b'Content-Length: '

JSONRPC_MESSAGE_STRUCTURE = 'Content-Length: {content_length}\r\n' \
                            'Content-Type: application/pytp-jsonrpc; charset=utf8\r\n\r\n' \
                            '{content}'


class JsonRpcStreamReader:

    def __init__(self, stdout):
        self.stdout = stdout

    def close(self):
        self.stdout.close()

    def read_message(self):
        """Reads the contents of a message.
        :returns: the message contents or None if no message is available
        """
        content_length = self.get_content_length()

        if not content_length:
            return None

        # Consume remainder of header
        while True:
            line = self.stdout.readline()
            if not line:
                return None
            if line == b'\r\n':
                break

        body = self.stdout.read(content_length).decode('utf-8')
        return json.loads(body)

    def get_content_length(self):
        """Reads the content length header.
        :returns: the content length or None if no content length is available
        """
        while True:
            line = self.stdout.readline()
            if not line:
                return None

            if line.startswith(CONTENT_LENGTH_HEADER):
                content_length = line[len(CONTENT_LENGTH_HEADER):].strip()
                return int(content_length)


class JsonRpcStreamWriter:

    def __init__(self, stdin):
        self.stdin = stdin

    def close(self):
        self.stdin.close()

    def write_message(self, message):
        if self.stdin.closed:
            return

        body = json.dumps(message)

        # get length in bytes
        content_length = len(body.encode('utf-8'))

        response = JSONRPC_MESSAGE_STRUCTURE.format(
            content_length=content_length,
            content=body
        )

        self.stdin.write(response.encode('utf-8'))
        self.stdin.flush()


def example_stream():
    # test streams
    import os
    import time

    # create pipe
    pipe_in, pipe_out = os.pipe()
    pipe_in = os.fdopen(pipe_in, 'rb', 0)
    pipe_out = os.fdopen(pipe_out, 'wb', 0)

    stream_reader = JsonRpcStreamReader(pipe_in)
    stream_writer = JsonRpcStreamWriter(pipe_out)

    received_messages = []


    # send messages
    stream_writer.write({'jsonrpc': '2.0', 'method': 'test', 'params': {'a': 1, 'b': 2}, 'id': 1})
    stream_writer.write({'jsonrpc': '2.0', 'method': 'test', 'params': {'a': 3, 'b': 4}, 'id': 2})
    # send with multibyte characters
    stream_writer.write({'jsonrpc': '2.0', 'method': 'test', 'params': {'a': '€', 'b': '日本語'}, 'id': 3})

    # receive messages
    for i in range(3):
        message = stream_reader.read_message()
        received_messages.append(json.loads(message))

    assert len(received_messages) == 3
    assert received_messages[0] == {'jsonrpc': '2.0', 'method': 'test', 'params': {'a': 1, 'b': 2}, 'id': 1}
    assert received_messages[1] == {'jsonrpc': '2.0', 'method': 'test', 'params': {'a': 3, 'b': 4}, 'id': 2}
    assert received_messages[2] == {'jsonrpc': '2.0', 'method': 'test', 'params': {'a': '€', 'b': '日本語'}, 'id': 3}

    # close streams
    stream_reader.close()
    stream_writer.close()

    print('Test passed!')


if __name__ == '__main__':
    example_stream()

