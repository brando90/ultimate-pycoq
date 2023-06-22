import argparse
import re
import textwrap
from collections import defaultdict
from typing import Type, List, ForwardRef

import attrs
import typing_inspect
from lsprotocol._hooks import _resolve_forward_references
from lsprotocol.types import METHOD_TO_TYPES
from lsprotocol.types import message_direction


INDENT = ' '*4


FILE_FORMAT = """\"\"\"
****** THIS IS A GENERATED FILE, DO NOT EDIT. ******
To regenerate file, run scripts/genclient.py
\"\"\"

{imports}

from k_pycoq.base_client import BaseClient


class LSPClient(BaseClient):
    def __init__(
        self,
        name: str,
        version: str,
        stdin,
        stdout,
    ):
        self.name = name
        self.version = version
        super().__init__(stdin, stdout)
{methods}
"""

REQUEST = """
def {python_method_name}(self, params: {params}, return_result=False) -> {result_type}:
    \"\"\"
    Make a `{method_name}` request.
    {doc_string}\"\"\"
    return self.send_request('{method_name}', params, return_result=return_result)
"""

NOTIFICATION = """
def {python_method_name}(self, params: {params}) -> None:
    \"\"\"
    Make a `{method_name}` notification.
    {doc_string}\"\"\"
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


def generate_client_code():
    """
    Generates the lsp client file from the lsprotocol description
    """

    import_list: defaultdict[str, set[str]] = defaultdict(set)
    methods: list[str] = []

    for method_name, types in METHOD_TO_TYPES.items():
        # we only care about messages the client sends
        if message_direction(method_name) == "serverToClient":
            continue

        request, response, params, registration_options = types

        python_method_name = pythonic_method_name(method_name)

        doc_string = ''
        if request.__doc__ is not None:
            doc_string = request.__doc__.strip()
            doc_string = '\n' + INDENT + doc_string + '\n' + INDENT

        param_name = resolve_type(params, import_list)

        if response is None:
            method = NOTIFICATION.format(python_method_name=python_method_name, method_name=method_name,
                                         params=param_name, doc_string=doc_string)
        else:
            response_name = resolve_type(attrs.fields(response).result.type, import_list)
            method = REQUEST.format(python_method_name=python_method_name, method_name=method_name,
                                    params=param_name, doc_string=doc_string, result_type=response_name)

        methods.append(textwrap.indent(method, INDENT))

    imports = '\n'.join([format_import(module_name, type_names) for module_name, type_names in import_list.items()])

    return FILE_FORMAT.format(imports=imports, methods=''.join(methods))


def main():
    parser = argparse.ArgumentParser(
        description="generate language client from lsprotocol types."
    )
    parser.add_argument("-o", "--output", default=None)
    args = parser.parse_args()

    # Make sure all the type annotations in lsprotocol are resolved correctly.
    _resolve_forward_references()
    client_code = generate_client_code()

    if args.output is None:
        print(client_code)
    else:
        with open(args.output, 'w') as f:
            f.write(client_code)


if __name__ == "__main__":
    main()
