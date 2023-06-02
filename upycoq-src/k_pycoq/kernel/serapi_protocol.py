from dataclasses import dataclass
from enum import Enum
from typing import Union, List, Any, Tuple

from sexpdata import parse, Symbol


class OCamlType:
    def __repr__(self):
        return f"{self.__class__.__name__}({self.__dict__})"

    def __str__(self):
        return f"{self.__class__.__name__}({self.__dict__})"


StateId = int
DocumentId = int
# TODO: these complex types
CoqObject = Any
Loc = Any  # https://coq.github.io/doc/v8.10/api/coq/Loc/index.html
Pp = Any  # https://coq.github.io/doc/v8.13/api/coq/Pp/index.html#type-t


@dataclass
class Ack(OCamlType):
    pass


@dataclass
class Completed(OCamlType):
    pass


NewAddTip = None
AddFocus = Union[NewAddTip, StateId]


@dataclass
class Added(OCamlType):
    state_id: StateId
    loc: Loc
    add_focus: AddFocus


@dataclass
class Canceled(OCamlType):
    state_ids: List[StateId]


@dataclass
class ObjList(OCamlType):
    coq_objects: List[CoqObject]


# TODO: complex type for coq exceptions
CoqExn = Any

AnswerKind = Union[Ack, Completed, Added, Canceled, ObjList, CoqExn]


@dataclass
class Answer(OCamlType):
    cmd_tag: str
    answer_kind: AnswerKind


Processed = None
Incomplete = None
Complete = None
ProcessingIn = str
InProgress = int
WorkerStatus = Tuple[str, str]
AddedAxiom = None
FileDependency = Tuple[str, str]
FileLoaded = Tuple[str, str]

FeedbackLevel = Enum('FeedbackLevel', 'Debug Info Notice Warning Error')


@dataclass
class Message(OCamlType):
    level: FeedbackLevel
    loc: Loc
    pp: Pp
    str: str

FeedbackContent = Union[Processed, Incomplete, Complete, ProcessingIn, InProgress,
                        WorkerStatus, AddedAxiom, FileDependency, FileLoaded, Message]

RouteId = int


@dataclass
class Feedback(OCamlType):
    doc_id: DocumentId
    span_id: StateId
    route: RouteId
    contents: FeedbackContent


def parse_exp(exp):
    def parse_expr(exp):
        if isinstance(exp, list):
            return parse_list(exp)
        else:
            return parse_value(exp)

    def parse_list(l):
        if len(l) == 0:
            return None
        elif len(l) == 1:
            return parse_expr(l[0])
        elif isinstance(l[0], list):
            return [parse_expr(l[i]) for i in range(0, len(l))]
        else:
            key = parse_expr(l[0])
            value = [parse_expr(l[i]) for i in range(1, len(l))]
            return {key: value if len(value) > 1 else value[0]}

    def parse_value(v):
        if isinstance(v, Symbol):
            return str(v)
        else:
            return v

    return parse_expr(exp)

# create a function that parses the reply and returns the appropriate type
def parse_reply(reply: str):
    """ parses serapi reply and returns the result as an instence of Feedbakc or Message """
    S_expr = parse(reply)

    def parse_expr(exp):
        if isinstance(exp, list):
            if len(exp) == 0:
                return None
            elif len(exp) == 1:
                return parse_expr(exp[0])
            elif isinstance(exp[0], list):
                return [parse_expr(e) for e in exp]
            else:
                try:
                    cls = globals()[str(exp[0])]
                except KeyError:
                    # if the class is not in globals then convert to dict
                    print(exp)
                    return parse_exp(exp)
                # get args from remaining elements in list
                print(exp[1:])
                args = [parse_expr(e) for e in exp[1:]]
                print(args)
                if len(args) == 1:
                    args = args[0]
                try:
                    return cls(*args)
                except TypeError:
                    return args
        if isinstance(exp, Symbol):
            return str(exp)
        else:
            return exp

    return parse_expr(S_expr)


if __name__ == '__main__':
    # test parse_reply

    reply = '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))' \
            '(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message(level Error)(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 8)(ep 14))))(pp(Pp_glue((Pp_string"String is not a module or module type."))))(str"String is not a module or module type.")))))' \
            '(Answer 1(CoqExn((loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 8)(ep 14))))(stm_ids((1 2)))(backtrace(Backtrace()))(exn("Modintern.ModuleInternalizationError(_)"))(pp(Pp_glue((Pp_glue())(Pp_string String)(Pp_string" is not a module or module type."))))(str"String is not a module or module type."))))'
    print(parse_reply(reply))
