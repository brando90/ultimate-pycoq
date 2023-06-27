import argparse
import re
import sys
import textwrap
from collections import defaultdict
from pathlib import Path
from typing import Type, List, ForwardRef, Optional, Union

import attrs
import typing_inspect
from lsprotocol._hooks import _resolve_forward_references
from lsprotocol.types import METHOD_TO_TYPES
from lsprotocol.types import message_direction


INDENT = ' '*4


FILE_FORMAT = """\"\"\"
****** THIS IS A GENERATED FILE, DO NOT EDIT. ******
To regenerate file, run {build_command}
\"\"\"

{imports}

from pytp.base_client import BaseClient
from pytp.lsp_config import LSPConfig, default_lsp_config

Id = int


class LSPClient(BaseClient):
    def __init__(
        self,
        name: str,
        version: str,
        stdin,
        stdout,
        config: LSPConfig = default_lsp_config,
    ):
        self.name = name
        self.version = version
        super().__init__(stdin, stdout, config)
{methods}
"""

REQUEST = """
def {python_method_name}(self, params: {params}, return_result=False) -> {result_type}:
    \"\"\"
    Make a `{method_name}` request.
    {doc_string}
    :param params: The parameters to send with the request. An instance of `{params}`.
    :param return_result: Whether to return the result of the request. If `True`, the method will block until the
    result is received. If `False`, the method will return the request's id.
    :return: The result of the request if `return_result` is `True`, otherwise the request's id.
    \"\"\"
    return self.send_request('{method_name}', params, return_result=return_result)
"""

NOTIFICATION = """
def {python_method_name}(self, params: {params}) -> None:
    \"\"\"
    Make a `{method_name}` notification.
    {doc_string}
    :param params: The parameters to send with the notification. An instance of `{params}`.
    :return: None
    \"\"\"
    self.send_notification('{method_name}', params)
"""


def resolve_type(abstract_type: Type, type_dict: defaultdict[str, set[str]]):
    """
    Resolves the dependencies a possibly composite type.

    :param abstract_type: The type to resolve the dependencies of
    :param type_dict: The dictionary to store the dependencies in. Dependencies are stored as
    type_dict[module] = {type1, type2, ...}
    """

    if abstract_type is None:
        return 'None'

    # recurse on subtypes
    args = set()
    for t in typing_inspect.get_args(abstract_type):
        args.add(resolve_type(t, type_dict))

    module_name = abstract_type.__module__

    # get type name
    type_name = 'NoneType'
    if typing_inspect.is_forward_ref(abstract_type):
        type_name = f"'{abstract_type.__forward_arg__}'"
        module_name = 'forward_ref'
    elif hasattr(abstract_type, '__name__'):
        type_name = abstract_type.__name__
    elif hasattr(abstract_type, '_name'):
        type_name = abstract_type._name
        if type_name is None:  # last ditch effort
            type_name = str(abstract_type.__origin__).split('.')[-1]

    if type_name == 'NoneType':
        return 'None'

    # attach type to module
    if module_name != 'builtins' and module_name != 'forward_ref':
        type_dict[module_name].add(type_name)

    # format type
    if len(args) == 0:
        return type_name
    elif 'None' in args:
        args.remove('None')
        type_dict['typing'].add('Optional')
        if type_name == 'Union' and len(args) == 1:  # clean up singleton Union types
            return f'Optional[{args.pop()}]'
        else:
            return f'Optional[{type_name}[{", ".join(args)}]]'
    else:
        return f'{type_name}[{", ".join(args)}]'


def format_import(module_name, type_names):
    types = ',\n    '.join(sorted(type_names))
    return f'from {module_name} import (\n    {types}\n)'


def pythonic_method_name(method_name):
    """
    Converts a method name to a pythonic method name.
    :param method_name: The lsp method name to convert e.g. $/cancelRequest
    :return: The pythonic method name e.g. cancel_request
    """
    # convert camel case to snake case
    method_name = re.sub(r'(?<!^)(?=[A-Z])', '_', method_name).lower()
    # (?<!^) - negative lookbehind, don't match the start of the string
    # (?=[A-Z]) - positive lookahead, match any uppercase letter

    method_name = method_name.replace('$/', '').replace('/', '_')

    return method_name


def generate_client_code(build_command: str):
    """
    Generates the lsp client file from the lsprotocol description
    """

    import_list: defaultdict[str, set[str]] = defaultdict(set)
    methods: list[str] = []

    for method_name, types in sorted(METHOD_TO_TYPES.items()):
        # we only care about messages the client sends
        if message_direction(method_name) == "serverToClient":
            continue

        request, response, params, registration_options = types

        python_method_name = pythonic_method_name(method_name)

        doc_string = ''
        if request.__doc__ is not None:
            doc_string = request.__doc__.strip()
            doc_string = '\n' + INDENT + doc_string + '\n' + INDENT

        param_type_str = resolve_type(params, import_list)

        if response is None:
            method = NOTIFICATION.format(python_method_name=python_method_name, method_name=method_name,
                                         params=param_type_str, doc_string=doc_string)
        else:
            # TODO: temporary hack, currently uses Optional for all responses, ideally, we would use a sentile value
            #  to indicate a null value and reserve None for missing values
            root_type = attrs.fields(response).result.type
            response_type_str = resolve_type(root_type, import_list)

            # add Id to the end of the response type
            if response_type_str.startswith('Union'):
                response_type_str = response_type_str[:-1] + ', Id]'
            else:
                response_type_str = f'Union[{response_type_str}, Id]'
            method = REQUEST.format(python_method_name=python_method_name, method_name=method_name,
                                    params=param_type_str, doc_string=doc_string, result_type=response_type_str)

        methods.append(textwrap.indent(method, INDENT))

    imports = '\n'.join([format_import(module_name, type_names) for module_name, type_names in import_list.items()])
    return FILE_FORMAT.format(imports=imports, methods=''.join(methods), build_command=build_command)


def main():
    parser = argparse.ArgumentParser(
        description="generate language client from lsprotocol types."
    )
    parser.add_argument("-o", "--output", default=None)
    args = parser.parse_args()

    # Make sure all the type annotations in lsprotocol are resolved correctly.
    _resolve_forward_references()

    # get the build command
    script_path = Path(sys.argv[0])
    script_path = script_path.parent / script_path.name
    sys.argv[0] = script_path.parent.name + '/' + script_path.name
    build_command = ' '.join(sys.argv)

    client_code = generate_client_code(build_command)

    if args.output is None:
        print(client_code)
    else:
        with open(args.output, 'w') as f:
            f.write(client_code)


if __name__ == "__main__":
    main()
