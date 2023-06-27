from cattrs.gen import make_dict_unstructure_fn, override, make_dict_structure_fn
from lsprotocol import converters

from pytp.coq.coq_types import GoalConfig


def get_coq_lsp_converter():
    converter = converters.get_converter()

    # given_up should not be converted to camel case which the default converter does
    unstructure_hook = make_dict_unstructure_fn(GoalConfig, converter, given_up=override(rename='given_up'))
    converter.register_unstructure_hook(GoalConfig, unstructure_hook)

    structure_hook = make_dict_structure_fn(GoalConfig, converter, given_up=override(rename='given_up'))
    converter.register_structure_hook(GoalConfig, structure_hook)

    return converter
