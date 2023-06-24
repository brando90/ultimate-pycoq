import json
from typing import Union

from lsprotocol import converters, types


def to_json(obj: types.MESSAGE_TYPES, converter=None) -> str:
    """Converts a given attrs object to json string"""
    if converter is None:
        converter = converters.get_converter()

    return json.dumps(converter.unstructure(obj))


def from_json(obj: Union[str, dict], method: str = None, converter=None) -> types.MESSAGE_TYPES:
    """Parses json string into attrs object.

    :param obj: json string or dict
    :param method: method name to convert to. If None, method is taken from `obj` if available. Note that result types
        must have a method name supplied.
    :param converter: converter to use
    """
    if converter is None:
        converter = converters.get_converter()

    if isinstance(obj, str):
        obj = json.loads(obj)

    if method is None:
        method = obj.get('method', None)

    if 'result' in obj:
        if method is None:
            raise ValueError('`method` must not be None for response type objects.')
        obj_type = types.METHOD_TO_TYPES[method][1]
    elif 'error' in obj:
        obj_type = types.ResponseErrorMessage
    else:
        obj_type = types.METHOD_TO_TYPES[method][0]
    return converter.structure(obj, obj_type)


def run_tests():
    """Test json conversion"""
    obj = types.ResponseErrorMessage(error=types.ResponseError(code=1, message='test'))
    import cattrs
    converter = cattrs.Converter()
    print(converter.unstructure(obj))
    json_str = to_json(obj)
    assert json_str == '{"error": {"code": 1, "message": "test"}, "jsonrpc": "2.0"}'
    assert from_json(json_str) == obj

    obj = types.InitializeResponse(result=types.InitializeResult(capabilities=types.ServerCapabilities()), id=1)
    json_str = to_json(obj)
    assert from_json(json_str, method='initialize') == obj

    import timeit
    print(timeit.timeit(lambda: to_json(obj), number=1000))
    print(timeit.timeit(lambda: from_json(json_str, method='textDocument/didOpen'), number=1000))

    # test request
    obj = types.TextDocumentDidOpenNotification(
        types.DidOpenTextDocumentParams(
            text_document=types.TextDocumentItem(
                uri='file:///path/to/file',
                language_id='python',
                version=1,
                text='test',
            )
        ),
    )
    json_str = to_json(obj)
    assert json_str == json.dumps({"params": {"textDocument": {"uri": "file:///path/to/file", "languageId": "python",
                                                               "version": 1, "text": "test"}},
                                   "method": "textDocument/didOpen",
                                   "jsonrpc": "2.0"})
    assert from_json(json_str, method='textDocument/didOpen') == obj

    # timing test
    import timeit
    print(timeit.timeit(lambda: to_json(obj), number=1000))
    print(timeit.timeit(lambda: from_json(json_str, method='textDocument/didOpen'), number=1000))


if __name__ == '__main__':
    run_tests()
