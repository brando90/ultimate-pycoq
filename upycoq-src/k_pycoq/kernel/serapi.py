"""
Defines a kernel interface for serapi. This file outlines the main entry point for interacting with coq through serapi.
"""
import argparse
import asyncio
import re
import subprocess
from collections import namedtuple
from pathlib import Path
import shlex
from typing import List

import pexpect

from k_pycoq.kernel import AbstractKernel
from k_pycoq.opam import create_opam_subprocess

from pexpect import fdpexpect

from sexpdata import parse, Symbol

# from asyncio import StreamWriter

# StreamReader = fdpexpect.fdspawn

PIPE_BUFFER_LIMIT = 2048 * 1024 * 1024  # 2048 Mb

REPLY_PATTERN = re.compile(r'\(Answer \d+ Ack\)(.|\s)*\(Answer \d+ Completed\)')
# REPLY_PATTERN = re.compile(r'Completed')
# REPLY_PATTERN = re.compile(r'\(Answer\s\d+\sCompleted\)')


# def parse_reply(reply: str):
#     """ parses serapi reply """
#     S_expr = parse(reply)
#
#     # convert to list of dicts
#     # S_expr is a list of lists
#     # The first value in each list is the key if there are more than 1 values
#     # and the remaining sublist is the associated value
#     # if there is only one value then:
#     # if the value is a list, then treat the list as the current list (ie don't allow nested singleton lists)
#     # if the value is not a list, then treat the value as the current value
#     # use recursion
#     # for example
#     # [Symbol('Add'), [[Symbol('pp'), [[Symbol('PPser'), 'hi']]]], 'statement']
#     # becomes
#     # {'Add': [{'pp': ['PPser', 'hi']}, 'statement']}
#     def parse_expr(exp):
#         if isinstance(exp, List):
#             return parse_list(exp)
#         else:
#             return parse_value(exp)
#
#     def strip_singleton_list(lst):
#         if isinstance(lst, List) and len(lst) == 1:
#             return strip_singleton_list(lst[0])
#         else:
#             return lst
#
#     def get_value_names(lst):
#         names = []
#         values = []
#         for i, v in enumerate(lst):
#             if isinstance(v, List):
#                 if isinstance(v[0], Symbol):
#                     names.append(str(v[0]))
#                     values.append(parse_expr(v[1]))
#                 else:
#                     names.append(f'field_{i}')
#                     values.append(parse_expr(v))
#             else:
#                 names.append(f'field_{i}')
#                 values.append(parse_expr(v))
#
#         return names, values
#
#     def parse_list(l):
#         if len(l) == 0:
#             return None
#         elif len(l) == 1:
#             return parse_expr(l[0])
#         elif isinstance(l[0], Symbol):
#             key = str(l[0])
#             # values = [parse_expr(l[i]) for i in range(1, len(l))]
#             values = strip_singleton_list(l[1:])
#             print(key)
#             print(values)
#             value_names, values = get_value_names(values)
#             print(value_names, values)
#             Class = namedtuple(key, value_names)
#             return Class(*values)
#         else:
#             return [parse_expr(l[i]) for i in range(0, len(l))]
#
#
#     def parse_value(v):
#         if isinstance(v, Symbol):
#             return str(v)
#         else:
#             return v
#
#     return parse_expr(S_expr)

def parse_reply(S_expr):
    """ parses serapi reply """
    exp = parse(S_expr)

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


def _process_flags(flags: List[str]):
    """ -I, -Q, -R flags arguments must be combined into a single argument seperated by commas for sertop. """
    parser = argparse.ArgumentParser()
    parser.add_argument('-I', metavar=('dir'),
                        nargs=1,
                        action='append',
                        default=[],
                        help='append filesystem to ML load path')

    parser.add_argument('-Q', metavar=('dir', 'coqdir'),
                        nargs=2, action='append',
                        default=[],
                        help='append filesystem dir mapped to coqdir to coq load path')

    parser.add_argument('-R', metavar=('dir', 'coqdir'),
                        nargs=2, action='append',
                        default=[],
                        help='recursively append filesystem dir mapped '
                             'to coqdir to coq load path')
    flags, _ = parser.parse_known_args(flags)

    res = []
    for x in flags.I:
        res += ['-I', ','.join(x)]

    for x in flags.Q:
        res += ['-Q', ','.join(x)]

    for x in flags.R:
        res += ['-R', ','.join(x)]

    return res


class SerapiKernel(AbstractKernel):

    def __init__(self, opam_switch: str = None, opam_root=None, top_file: str = None, flags: List[str] = None):
        super().__init__()
        self.opam_switch: str = opam_switch
        self.opam_root = opam_root
        self.flags: List[str] = _process_flags(flags)
        self.top_file: str = top_file
        self._process = None

    def start(self):
        command = f'sertop {" ".join(self.flags)} --topfile {self.top_file}'

        self._process = create_opam_subprocess(command, self.opam_switch, self.opam_root)
        # import sys
        # self._process.logfile = sys.stdout

    def terminate(self):
        # TODO: check if this is the right way to terminate a process (see original implementation from brando)
        self._process.close(force=True)

    def _write(self, data):
        """ writes data to kernel input """
        self._process.send(data)
        self._process.send('\n')
        # self._writer.write(data)
        # self._writer.write('\n')

    def _read_response(self):
        """ reads serapi response from kernel stdout """
        self._process.expect(REPLY_PATTERN)
        answers = parse_reply(self._process.match.group())
        command_tag = answers[0]['Answer'][0]
        return command_tag, answers

    def add(self, statement: str):
        """adds statement to kernel"""
        self._write(f'(Add () "{statement.strip()}")')
        return self._read_response()

    def query(self, statement: str):
        """queries statement to kernel"""
        self._write(f'(Query "{statement}")')
        return self._read_response()

    def exec(self, statement_id: int):
        """executes statement"""
        self._write(f'(Exec {statement_id})')
        return self._read_response()


if __name__ == '__main__':
    from asyncio import run

    # test parse_reply
    # reply = '(Answer 1 Ack)(Add 1 1)(Answer 1 Completed)'
    # print(parse_reply(reply))

    # reply = '(Answer 2 Ack)' \
    #         '(Answer 2(Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)' \
    #         '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 18))NewAddTip))' \
    #         '(Answer 2(Added 4((fname ToplevelInput)(line_nb 1)(bol_pos 0)' \
    #         '(line_nb_last 1)(bol_pos_last 0)(bp 19)(ep 37))NewAddTip))' \
    #         '(Answer 2 Completed)'
    # # reply = '(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message(level Error)(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 8)(ep 14))))(pp(Pp_glue((Pp_string"String is not a module or module type."))))(str"String is not a module or module type.")))))'
    # print(parse_reply(reply))

    # test _process_flags
    flags = ['-I', 'src', '-R', 'src', 'Debug_Proj', '-Q', 'src', 'Debug_Proj', '-Q', 'src2', 'Debug_Proj2']
    assert _process_flags(flags) == ['-I', 'src', '-Q', 'src,Debug_Proj', '-Q', 'src2,Debug_Proj2', '-R', 'src,Debug_Proj']

    from k_pycoq.coqproject import CoqProject

    project = CoqProject('Debug_Proj', 'ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1',
                         Path('/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug'
                              '/debug_simple_arith'),
                         'make clean && make')

    kernel = SerapiKernel(opam_switch=project.switch, opam_root=project.project_directory,
                          top_file=project.build_order[0].name, flags=project.flags)

    async def main():
        try:
            kernel.start()
            for statement in project.build_order[0].coq_statements():
                print(statement)
                print(kernel.add(statement))

        except Exception as e:
            print(e)
            kernel.terminate()


    run(main())
