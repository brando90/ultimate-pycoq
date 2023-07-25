import attrs
import cattrs
from cattrs.gen import make_dict_unstructure_fn, override, make_dict_structure_fn
from lsprotocol import converters

from pytp.coq.coq_types import GoalConfig, CoqInitializationOptions


def get_coq_lsp_converter():
    converter = converters.get_converter()

    # given_up should not be converted to camel case which the default converter does
    unstructure_hook = make_dict_unstructure_fn(GoalConfig, converter, given_up=override(rename='given_up'))
    converter.register_unstructure_hook(GoalConfig, unstructure_hook)

    structure_hook = make_dict_structure_fn(GoalConfig, converter, given_up=override(rename='given_up'))
    converter.register_structure_hook(GoalConfig, structure_hook)

    # CoqInitializationOptions fields should not be omitted if they are default
    # (since we use different defaults that coq-lsp/coq-lsp defaults may change unexpectedly)
    attributes = {
        a.name: cattrs.gen.override(
            omit_if_default=False,
        )
        for a in attrs.fields(CoqInitializationOptions)
    }
    unstructure_hook = make_dict_unstructure_fn(CoqInitializationOptions, converter, **attributes)
    converter.register_unstructure_hook(CoqInitializationOptions, unstructure_hook)

    structure_hook = make_dict_structure_fn(CoqInitializationOptions, converter, **attributes)
    converter.register_structure_hook(CoqInitializationOptions, structure_hook)

    return converter
