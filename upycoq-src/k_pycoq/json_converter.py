# Copyright (c) Microsoft Corporation. All rights reserved.
# Licensed under the MIT License.
# from https://github.com/microsoft/lsprotocol/blob/main/tests/python/common/jsonrpc.py

import json

from lsprotocol import converters, types


def to_json(obj: types.MESSAGE_TYPES, method: str = None, converter=None) -> str:
    """Converts a given attrs object to json string"""
    if converter is None:
        converter = converters.get_converter()

    if method is None:
        method = obj.method if hasattr(obj, 'method') else None

    if hasattr(obj, 'result'):
        if method is None:
            raise ValueError('`method` must not be None for response type objects.')
        obj_type = types.METHOD_TO_TYPES[method][1]
    elif hasattr(obj, 'error'):
        obj_type = types.ResponseErrorMessage
    elif hasattr(obj, 'params'):
        obj_type = types.METHOD_TO_TYPES[method][0]
    else:
        raise ValueError(f'Unknown object type {obj}.')

    return json.dumps(converter.unstructure(obj, unstructure_as=obj_type))


def from_json(json_str: str, method: str = None, converter=None) -> types.MESSAGE_TYPES:
    """Parses json string into attrs object."""
    if converter is None:
        converter = converters.get_converter()

    obj = json.loads(json_str)

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
    json_str = to_json(obj)
    assert json_str == '{"error": {"code": 1, "message": "test"}, "jsonrpc": "2.0"}'
    assert from_json(json_str) == obj

    obj = types.InitializeResponse(result=types.InitializeResult(capabilities=types.ServerCapabilities()), id=1)
    json_str = to_json(obj, method='initialize')
    assert from_json(json_str, method='initialize') == obj

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
    json_str = to_json(obj, method='textDocument/didOpen')
    assert json_str == json.dumps({"params": {"textDocument": {"uri": "file:///path/to/file", "languageId": "python",
                                                               "version": 1, "text": "test"}},
                                   "method": "textDocument/didOpen",
                                   "jsonrpc": "2.0"})
    assert from_json(json_str, method='textDocument/didOpen') == obj


if __name__ == '__main__':
    run_tests()
