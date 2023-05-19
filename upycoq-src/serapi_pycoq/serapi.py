'''
functions to work with coq-serapi
'''
import logging
import re
import json

from typing import List, Union, Tuple, Optional

import serapi_pycoq.kernel
from serapi_pycoq.kernel import LocalKernel
from serapi_pycoq.common import LocalKernelConfig

from dataclasses import dataclass
from collections.abc import Iterable

COMPLETED_PATTERN = re.compile(r"\(Answer\s\d+\sCompleted\)")
ANSWER_PATTERN = re.compile(r"\(Answer\s(\d+)(.*)\)")
ANSWER_PATTERN_OBJLIST = re.compile(r"\(Answer\s(\d+)(\(ObjList.*\))\)")
ADDED_PATTERN = re.compile(r"\(Added\s(\d+)(.*)\)")
COQEXN_PATTERN = re.compile(r"\((CoqExn\(.*\))\)")


# from serapi_pycoq.query_goals import SerapiGoals


def ocaml_string_quote(s: str):
    """
    OCaml-quote string 
    """
    return s.replace('\\', '\\\\').replace('\"', '\\\"')


def sexp(x) -> str:
    """
    make s-expression of python object
    """
    if isinstance(x, int):
        return str(x)
    elif isinstance(x, str):
        return '"' + ocaml_string_quote(x) + '"'
    elif isinstance(x, Iterable):
        return '(' + " ".join(sexp(e) for e in x) + ')'
    else:
        return str(x)
        # raise TypeError(f'serapi_pycoq.serapi.sexp for type {type(x)} is not yet implemented')


def matches_answer_completed(line: str, ind: int):
    """
    checks if coq-serapi responses matches "Answer Completed"
    """
    return line.strip() == f'(Answer {ind} Completed)'


def matches_answer(line: str, sent_index):
    """ 
    if line matches Answer
    return (index, answer)
    """

    match = ANSWER_PATTERN.match(line)
    if match and int(match.group(1)) == sent_index:
        return match.group(2).strip()


def parse_added_sid(line: str):
    """
    find sentence id (sid) in coq-serapi response
    """

    match = ADDED_PATTERN.match(line)
    if match:
        return int(match.group(1))
    else:
        return None


@dataclass
class CoqExn():
    message: str


def parse_coqexn(line: str):
    """
    parse CoqExn in coq-serapi response
    """
    match = COQEXN_PATTERN.match(line)
    if match:
        return CoqExn(message=match.group(0))
    else:
        return None


class CoqSerapi():
    """ 
    object of CoqSerapi provides communication with coq through coq-serapi interface through the self._kernel object

    initialise by passing either a kernel object that has interface

        kernel.readline()
        kernel.readlines()
        kernel.writeline()
        
    of config defined by the protocol: serapi_pycoq.kernel.LocalKernel

    """

    def __init__(self, kernel: LocalKernel, logfname=None):
        """ 
        wraps coq-serapi interface on the running kernel object
        """
        self._logfname = logfname  # seems to log to responses from coq serapi to ._serapi_log logfile (not sure why)
        self._kernel: serapi_pycoq.kernel.LocalKernel = kernel  # object that can start the background coq-serapi process
        self._cfg: LocalKernelConfig = self._kernel.cfg  # config of the (coq serapi) kernel (which runs the serapi)

        # serapi command history for this CoqSerapi object/instance
        self._sent_history = []
        self._serapi_response_history = []
        self._added_sids = []
        self._executed_sids = []
        # import serlib.parser
        # self.parser = serlib.parser.SExpParser()
        self._queried_local_ctx_and_goals = []
        # note: self.__aenter__() calls self.start() which starts the kernel proc (serapi)

    async def __aenter__(self):
        await self._kernel.start()
        return self

    async def __aexit__(self, exception_type, exception_value, traceback):
        await self._kernel.__aexit__(exception_type, exception_value, traceback)
        async for line in self._kernel.readlines():
            self._serapi_response_history.append(line)

        if not self._logfname is None:
            await self.save_serapi_log()

    async def add(self, coq_stmt: str):
        """ sends serapi command
        (Add () "coq_stmt")
        """

        cmd_tag = len(self._sent_history)

        quoted = ocaml_string_quote(coq_stmt)
        cmd = f'(Add () "{quoted}")'
        await self._kernel.writeline(cmd)
        self._sent_history.append(cmd)

        return cmd_tag

    async def query_goals(self, opts: str = '') -> str:
        """ sends serapi command 
        (Query () Goals)
        """
        cmd_tag = len(self._sent_history)
        cmd = f'(Query ({opts}) Goals)'
        await self._kernel.writeline(cmd)
        self._sent_history.append(cmd)
        return cmd_tag

    async def query_definition(self, name) -> str:
        """ 
        sends serapi command
        (Query () Definition name)
        """
        cmd_tag = len(self._sent_history)
        cmd = f'(Query () (Definition {name}))'
        await self._kernel.writeline(cmd)
        self._sent_history.append(cmd)
        return cmd_tag

    async def exec(self, sid: int):
        """ sends serapi command to execute coq statement sid
        (Exec sid)
        """
        cmd_tag = len(self._sent_history)

        cmd = f'(Exec {sid})'
        await self._kernel.writeline(cmd)
        self._sent_history.append(cmd)

        return cmd_tag

    async def cancel(self, sids: List[int]) -> bool:
        """ cancels given list of sids
        """
        cmd_tag = len(self._sent_history)
        cmd = f'(Cancel {sexp(sids)})'

        await self._kernel.writeline(cmd)
        self._sent_history.append(cmd)
        return cmd_tag

    async def wait_for_answer_completed(self, cmd_tag: int):
        """ read and save responses from serapi to _serapi_response_history
        stop when (Answer cmd_tag Completed) is received
        """
        while True:
            line = await self._kernel.readline()
            if line == '':
                print("empty readline: ", end='')
                time.sleep(0.1)
                print("process terminated with proc code", self._kernel._proc.returncode)
                raise EOFError

            self._serapi_response_history.append(line)
            if matches_answer_completed(line, cmd_tag):
                return len(self._serapi_response_history)

    async def add_completed(self, coq_stmt: str) -> Tuple[int, int, Union[int, str]]:
        """ sends serapi command Add CoqSerapi.add()
        awaits completed response; returns list of sids / CoqExns
        """

        cmd_tag = await self.add(coq_stmt)
        resp_ind = await self.wait_for_answer_completed(cmd_tag)

        sids = await self.added_sids(cmd_tag)  # separate added sids vs CoqExns
        self._added_sids.append(sids)
        coqexns = await self.coqexns(cmd_tag)

        return (cmd_tag, resp_ind, sids, coqexns)

    async def exec_completed(self, sid: int) -> List[str]:  # returns list of coqexn
        """ sends serapi command Exec
        awaits completed response
        returns ind of completed message
        and CoqExns
        """
        cmd_tag = await self.exec(sid)
        resp_ind = await self.wait_for_answer_completed(cmd_tag)
        coqexns = await self.coqexns(cmd_tag)

        return (cmd_tag, resp_ind, coqexns)

    async def cancel_completed(self, sids: List[int]) -> List[str]:  # List[CoqExn]
        cmd_tag = await self.cancel(sids)
        resp_ind = await self.wait_for_answer_completed(cmd_tag)
        coqexns = await self.coqexns(cmd_tag)
        if coqexns != []:
            raise RuntimeError(f'Unexpected error during coq-serapi command Cancel'
                               f'with CoqExns {coqexns}')
        return (cmd_tag, resp_ind)

    async def _query_goals_completed(self, opts: str = '') -> List[str]:
        """ returns literal serapi response (Query () Goals)
        """
        cmd_tag = await self.query_goals(opts)
        resp_ind = await self.wait_for_answer_completed(cmd_tag)
        coqexns = await self.coqexns(cmd_tag)
        if coqexns != []:
            raise RuntimeError(f'Unexpected error during coq-serapi command Query () Goals '
                               f'with CoqExns {coqexns}')
        goals = await self._answer(cmd_tag)
        return goals

    async def _query_definition_completed(self, name) -> List[str]:
        """
        returns literal serapi response (Query () Definition name)
        """
        cmd_tag = await self.query_definition(name)
        resp_ind = await self.wait_for_answer_completed(cmd_tag)
        coqexns = await self.coqexns(cmd_tag)
        if coqexns != []:
            raise RuntimeError(f'Unexpected error during coq-serapi command Query () Definition {name}'
                               f'with CoqExns {coqexns}')
        definition = await self._answer(cmd_tag)
        return definition

    async def query_goals_completed(self, opts: str = '') -> str:
        """
        returns a single serapi response on (Query () Goals)
        """

        serapi_goals: List[str] = await self._query_goals_completed(opts)

        if len(serapi_goals) != 1:
            print("serapi_pycoq received list of goals", serapi_goals)
            raise RuntimeError("unexpected behaviour of serapi_pycoq - serapi - coq API: "
                               "query goals returned a list of len != 1 in serapi response")
        else:
            return serapi_goals[0]

    # async def serapi_goals(self) -> SerapiGoals:
    # async def serapi_goals(self):
    #     """
    #     returns parsed SerapiGoals object
    #     """
    #     from pycoq.query_goals import SerapiGoals
    #     _serapi_goals: str = await self.query_goals_completed()
    #     post_fix = self.parser.postfix_of_sexp(_serapi_goals)
    #     import serlib.parser
    #     ann = serlib.cparser.annotate(post_fix)
    #     ret_serapi_goals: SerapiGoals = pycoq.query_goals.parse_serapi_goals(self.parser, post_fix, ann, pycoq.query_goals.SExpr)
    #     return ret_serapi_goals
    # return serapi_pycoq.query_goals.parse_serapi_goals(self.parser, post_fix, ann, pycoq.query_goals.SExpr)

    async def query_local_ctx_and_goals(self) -> Union[str, list]:
        """
        Returns the proof state as the local context + goals as a single string.
        In particular, sends serapi command
            (Query ((pp ((pp_format PpStr)))) Goals)
        If it's not in proving mode (e.g. not in a thoerem) then it returns the empty string ''.

        Details:
            Want to get the entire context from SerAPI from some Py-SerAPI interface.
            (Add () "Lemma addn0 n : n + 0 = n.")
            (Add () "Proof.")
            (Exec 3)

            (Query ((pp ((pp_format PpStr)))) Goals)
            (Answer 2 Completed)
            (Query ((pp ((pp_format PpStr)))) Goals)
            (Answer 3 Ack)
            (Answer 3
             (ObjList
              ((CoqString  "\
                          \n  n : nat\
                          \n============================\
                          \nn + 0 = n"))))
            (Answer 3 Completed)
        """
        from sexpdata import loads

        print(f'{self._sent_history[-4:]=}')
        _local_ctx_and_goals: str = await self.query_goals_completed(opts='(pp ((pp_format PpStr)))')
        _local_ctx_and_goals: list = loads(_local_ctx_and_goals)
        print(f'{_local_ctx_and_goals=}')
        print(f'{str(_local_ctx_and_goals[0])=}')
        assert str(_local_ctx_and_goals[0]) == 'ObjList' or str(_local_ctx_and_goals[0]) == "Symbol('ObjList')"
        if _local_ctx_and_goals[1] == []:
            return []  # if not in proof mode there is no coq-str obj so return empty list
        else:
            # example smallest valid goals: (ObjList ((CoqString "")))
            obj_list: list = _local_ctx_and_goals[1]
            coq_str_sexp: list = obj_list[0]  # e.g. (CoqString "")
            assert len(coq_str_sexp) == 2
            assert str(coq_str_sexp[0]) == 'CoqString'
            # local_ctx_and_goals: str = _local_ctx_and_goals[1][0][1]
            local_ctx_and_goals: str = coq_str_sexp[1]
            return local_ctx_and_goals

    async def in_proof_mode(self) -> bool:
        """
        Detects if we are in proof mode.

        Only true if goals query cmd returns a CoqString even the empty string.

        Only not in proof mode if query cmd goals returns the empty CoqObjecy.

        e.g.
        in proof mode, query goals returns string:
        case 1: in the middle of some step.
            rlwrap sertop --printer=human

            (Add () "
            Theorem easy: nat -> nat. intros.
            ")

            (Exec 3)

            (Query ((pp ((pp_format PpStr)))) Goals)
            (Answer 2 Ack)
            (Answer 2
             (ObjList ((CoqString  "\
                                  \n  H : nat\
                                  \n============================\
                                  \nnat"))))
            (Answer 2 Completed)


        case 2: proof is done but still in proof mode (e.g. without a Qed.)
            rlwrap sertop --printer=human

            (Add () "
            Theorem easy: nat -> nat. intros. apply O.
            ")
            (Exec 4)

            (Query ((pp ((pp_format PpStr)))) Goals)
            (Answer 2 Ack)
            (Answer 2 (ObjList ((CoqString ""))))
            (Answer 2 Completed)


        case 3: if outside the proving mode then (e.g. "Qed.") then goala returns empty CoqObject
            rlwrap sertop --printer=human

            (Add () "
            Theorem easy: nat -> nat. intros. apply O. Qed.
            ")

            (Exec 5)

            (Query ((pp ((pp_format PpStr)))) Goals)
            (Answer 2 Ack)
            (Answer 2 (ObjList ()))
            (Answer 2 Completed)

        case 3: Definitions
            rlwrap sertop --printer=human

            (Add () "
            Definition par : Line -> Point -> Line.
            ")

            (Add () "
            Definition par : Line -> Point -> Line.
            ")

        todo: for some reason it's missing \nDefinition par : Line -> Point -> Line.\n
        """
        goals: Union[str, list] = await self.query_local_ctx_and_goals()
        # print(f'-> coq.in_proof_mode() says the goals are: {goals=}')
        # logging.info(f'-> coq.in_proof_mode() says the goals are: {goals=}')
        in_proof_mode: bool = isinstance(goals, str)
        return in_proof_mode

    async def focused_goals_closed(self) -> bool:
        """
        Only returns true if your focused goals has no more goals.
        There are no more goals if it returns the empty string.
        Note: if it's the empty string you don't know if you've closed the top proof.
        if true:
            -> focused goals are closed (so goals == "", the empty string)
        else if false:
            -> then goals != ""...could mean anything (likely your still on a proof if goals is a string or outside a proving env if
            it returns the empty list. But this function does not check the last too, so false is not super informative).

        Cases:
        case 1: right after a focused base case goal.
        rlwrap sertop --printer=human

        (Add ()
        "
        Theorem n_plus_zero_eqs_n_inductive:
            forall n : nat, n + O = n.
            Proof.
                intros.
                induction n.
                - simpl. reflexivity.
        "
        )
        (Exec 8)

        (Query ((pp ((pp_format PpStr)))) Goals)

        (Query ((pp ((pp_format PpStr)))) Goals)
        (Answer 2 Ack)
        (Answer 2 (ObjList ((CoqString ""))))
        (Answer 2 Completed)

        case 2: right after an inductive step proof.
        rlwrap sertop --printer=human

        (Add ()
        "
        Theorem n_plus_zero_eqs_n_inductive:
            forall n : nat, n + O = n.
            Proof.
                intros. induction n.
                - simpl. reflexivity.
                - auto.
        "
        )
        (Exec 10)

        (Query ((pp ((pp_format PpStr)))) Goals)
        (Answer 2 Ack)
        (Answer 2 (ObjList ((CoqString ""))))
        (Answer 2 Completed)

        case 3: when proof term has no holes.
        rlwrap sertop --printer=human

        (Add ()
        "
        Theorem n_plus_zero_eqs_n_inductive:
            forall n : nat, n + O = n.
            Proof.
                intros. induction n.
                - simpl. reflexivity.
                - auto.
                Show Proof.
        "
        )
        (Exec 11)

        (Query ((pp ((pp_format PpStr)))) Goals)
        (Query ((pp ((pp_format PpStr)))) Goals)
        (Answer 2 Ack)
        (Answer 2 (ObjList ((CoqString ""))))
        (Answer 2 Completed)
        """
        goals = await self.query_local_ctx_and_goals()
        # print(f'-> coq.focused_goals_closed() says the goals are: {goals=}')
        # logging.info(f'-> coq.focused_goals_closed() says the goals are: {goals=}')
        proof_closed_done: bool = goals == ""  # effectively says the current tactic closed the current focused goals (not top thm goals).
        return proof_closed_done

    async def outside_a_proving_env(self) -> bool:
        """
        You are outside a proving env if the return of the goals query cmd is the empty prove object (and thus not a
        string).

        Useful to detect Qed. has been done if previous step goals is the empty string.
        """
        goals: Union[str, list] = await self.query_local_ctx_and_goals()
        # print(f'-> coq.outside_a_proving_env() says the goals are: {goals=}')
        # logging.info(f'-> coq.outside_a_proving_env() says the goals are: {goals=}')
        outside_a_proof: bool = goals == []
        return outside_a_proof

    async def query_coq_proof(self):
        """
        (Query ((pp ((pp_format PpStr)))) CoqProof)
        """
        _local_ctx_and_goals: str = await self.query_goals_completed(opts='(pp ((pp_format PpStr)))')
        raise NotImplemented

    async def get_current_proof_term_via_add(self) -> Union[str, list[CoqExn]]:
        """
        Returns the proof term (proof object, lambda term etc.) representation of the proof.

        (Add () "Show Proof.")
        """
        coq_stmt: str = 'Show Proof.'
        cmd_tag, resp_ind, coq_exns, sids = await self.execute(coq_stmt)
        if coq_exns:
            logging.info(f'{await self.query_local_ctx_and_goals()=}')
            logging.info(f'{await self.in_proof_mode()=}')
            raise ValueError(f'Got an error, are you sure you can get the proof term right now? err: {coq_exns=}'
                             f', {self._sent_history=}')
            # return coq_exns
        # todo: another place where perhaps we should move to VP's serlib? unsure if worth it.
        # - extract_proof_term, following the Feedback constructor from type answer serapir response: http://ejgallego.github.io/coq-serapi/coq-serapi/Serapi/Serapi_protocol/#type-answer.Feedback
        from sexpdata import loads
        serapi_response: str = self._serapi_response_history[-3]
        res: str = serapi_response
        _res: list = loads(res)
        feedback: list = _res[-1]
        assert len(feedback) == 4
        contents: list = feedback[-1]
        assert len(contents) == 2
        message: list = contents[-1]
        assert len(message) == 5
        string: list = message[-1]
        assert str(string[0]) == 'str'
        # - edge case if the sexpdata sees an atom that is a string it didn't wrap it in a Symbol for some reason
        if isinstance(string[-1], str):
            ppt: str = string[-1]
        else:
            ppt: str = str(string[-1])
        return ppt

    async def query_definition_completed(self, name) -> str:
        """
        returns a single serapi response on (Query () Definition name))
        """
        definition = await self._query_definition_completed(name)

        if len(definition) != 1:
            # print("pycoq received definition", definition)
            logging.info("pycoq received definition", definition)
            raise RuntimeError("unexpected behaviour of pycoq - serapi - coq API: "
                               "definition returned a list of len != 1 in serapi response")
        else:
            return definition[0]

    async def show_name_of_theorem(self) -> str:
        """
        Returns name/identifier of theorem/conjecture currently being proved (as a string).
        see: https://coq.github.io/doc/v8.10/refman/proof-engine/proof-handling.html#coq:cmdv.show-conjectures

        e.g.
Theorem zero_plus_n_eq_n:
  forall n: nat, 0 + n = n.
Show Conjectures.

zero_plus_n_eq_n
---
(Add () "
Theorem add_easy_0'':
forall n:nat,
  0 + n = n.
Proof.
    intros.
    simpl.
")
(Exec 5)

(Add () "Show Conjectures.")
(Exec 6)

(Answer 3 Ack)
(Answer 3
 (Added 6
  ((fname ToplevelInput) (line_nb 1) (bol_pos 0) (line_nb_last 1)
   (bol_pos_last 0) (bp 0) (ep 17))
  NewTip))
(Answer 3 Completed)

(Exec 6)
(Answer 4 Ack)
(Feedback
 ((doc_id 0) (span_id 6) (route 0) (contents (ProcessingIn master))))
(Feedback ((doc_id 0) (span_id 5) (route 0) (contents Processed)))
(Feedback
 ((doc_id 0) (span_id 6) (route 0)
  (contents
   (Message (level Notice) (loc ()) (pp (Pp_string add_easy_0''))
    (str add_easy_0'')))))
(Feedback ((doc_id 0) (span_id 6) (route 0) (contents Processed)))
(Answer 4 Completed)
        """
        cmd_tag, resp_ind, coq_exns, sids = await self.execute(coq_stmt="Show Conjectures.")
        if coq_exns:
            raise ValueError(f'Error: {coq_exns=}')
        # parse response see self.get_current_proof_term_via_add as an example
        raise NotImplemented

    async def show_open_all_goals_and_existential_variables(self):
        """
        Displays all open goals / existential variables in the current proof along with the type and the context of each variable.
        Execute" "Show Existentials."

Displays all open goals / existential variables in the current proof along with the type and the context of each variable.

https://coq.github.io/doc/v8.10/refman/proof-engine/proof-handling.html#coq:cmdv.show-conjectures
3:14
Show Existentials. is interesting too.  It shows the proof state for each goal/e-variable, and also makes clear what the e-variables names are in the proof.
3:15
https://coq.github.io/doc/v8.10/refman/proof-engine/proof-handling.html#coq:cmdv.show-existentials
```

```
Theorem zero_plus_n_eq_n:
  forall n: nat, 0 + n = n.
  Show.
 Proof.
  intros.
  simpl.
  Show Existentials.

Existential 1 =
?Goal : [n : nat |- n = n]

Displays all open goals / existential variables in the current proof along with the type and the context of each variable.
        """
        cmd_tag, resp_ind, coq_exns, sids = await self.execute(coq_stmt="Show Existentials.")
        if coq_exns:
            raise ValueError(f'Error: {coq_exns=}')
        # parse response see self.get_current_proof_term_via_add as an example
        raise NotImplemented

    async def started_proving(self, stmt: str, undo_coq_state_change: bool = True) -> bool:
        """
        Checks if after executing the current statement would start a proving e.g. statements Theorem, Lemma, etc.
        It undos the change of that statement by default avoid side effects.

        Details:
            - after stmt exec, goals changes as follows: [] -> ""
        """
        goals_before_cmd: Union[str, list] = await self.query_local_ctx_and_goals()
        cmd_tag, resp_ind, coq_exns, sids = await self.execute(stmt)
        goals_after_cmd: Union[str, list] = await self.query_local_ctx_and_goals()
        if undo_coq_state_change:
            # cancel stmt you just sent, we only sent it to check make the check we want
            await self.cancel_completed(sids)
        # raise ValueError('Not Tested')
        # note, "" == '' are equal, so check with "" is fine
        # only need to make sure the cancel actually works as expected.
        # [] -> "" ==> thm
        if goals_before_cmd == [] and goals_after_cmd == "":
            return True
        # "" -> [] ==> qed/abort
        elif goals_before_cmd == "" and goals_after_cmd == []:
            return False
        # "" -> "" ==> in proof mode
        elif goals_before_cmd == "" and goals_after_cmd == "":
            return False
        # [] -> [] ==> not in proving
        else:
            return False

    async def _fully_finished_top_proof(self, stmt: str, undo_coq_state_change: bool = True) -> bool:
        """
        Approximately checks if top proof is done i.e. Qed-like coq command.
        It undos the change of that statement by default avoid side effects.

        Details:
        Previous cmd query goals is empty string "" and next is empty proof object [].
            - after stmt exec, goals changes as follows: "" -> []
        We also cancel the execution of the current tactic so that the coq state doesn't change randomly for the user.
        """
        raise NotImplemented
        goals_before_cmd: Union[str, list] = await self.query_local_ctx_and_goals()
        cmd_tag, resp_ind, coq_exns, sids = await self.execute(stmt)
        goals_after_cmd: Union[str, list] = await self.query_local_ctx_and_goals()
        if undo_coq_state_change:
            # cancel stmt you just sent, we only sent it to check make the check we want
            await self.cancel_completed(sids)
        # raise ValueError('Not Tested')
        # note, "" == '' are equal, so check with "" is fine
        # only need to make sure the cancel actually works as expected.
        # [] -> "" ==> thm
        if goals_before_cmd == [] and goals_after_cmd == "":
            return False
        # "" -> [] ==> qed/abort
        elif goals_before_cmd == "" and goals_after_cmd == []:
            return True
        # "" -> "" ==> in proof mode
        elif goals_before_cmd == "" and goals_after_cmd == "":
            return False
        # [] -> [] ==> not in proving
        else:
            return False

    async def would_cause_or_remain_in_proof_mode(self, stmt: str, undo_coq_state_change: bool = True) -> bool:
        """
        Returns True if executing the given stmt would cause coq to go or remain in proving mode.
        It undos the change of that statement by default avoid side effects.

        Details:
            - only case if executing current stmt would remain outputting goals as a string.
        """
        cmd_tag, resp_ind, coq_exns, sids = await self.execute(stmt)
        in_proof_mode: bool = await self.in_proof_mode()
        if undo_coq_state_change:
            # cancel stmt you just sent, we only sent it to check make the check we want
            await self.cancel_completed(sids)
        return in_proof_mode

    async def execute(self, coq_stmt: str) -> List[CoqExn]:
        """ tries to execute coq_stmt
        if CoqExn then cancel coq_stmt
        returns (cmd_tag, resp_ind, List[CoqExn], List[executed sids])
        """

        cmd_tag, resp_ind, sids, coqexns = await self.add_completed(coq_stmt)

        assert all(isinstance(sid, int) for sid in sids)
        if len(sids) == 0:
            print(f"notice: {len(sids)} sids in coq_stmt: {coq_stmt}")

        if coqexns:
            (cmd_tag, resp_ind) = await self.cancel_completed(sids)
            return (cmd_tag, resp_ind, coqexns, [])

        for sid in sids:
            cmd_tag, resp_ind, coqexns = await self.exec_completed(sid)
            if coqexns:
                (cmd_tag, resp_ind) = await self.cancel_completed(sids)
                return (cmd_tag, resp_ind, coqexns, None)
            self._executed_sids.append(sid)

        return (cmd_tag, resp_ind, [], sids)

    async def get_first_n_global_ctx_ids_and_terms(self):
        raise NotImplemented

    async def get_first_n_global_wrt_coqhammer_ctx_ids_and_terms(self):
        raise NotImplemented

    async def added_sids(self, cmd_tag) -> List[Union[int, str]]:
        """ 
        returns the list of sid (sentence id) from history of serapi responses

        """
        cur = len(self._serapi_response_history) - 1
        res = []
        while cur >= 0:
            line = self._serapi_response_history[cur].strip()
            line_answer = matches_answer(line, cmd_tag)
            if line_answer is None or line_answer == 'Completed':
                cur -= 1
                continue
            if line_answer == 'Ack':
                break
            sid = parse_added_sid(line_answer)
            if not sid is None:
                res.append(sid)
            cur -= 1

        return list(reversed(res))

    async def coqexns(self, cmd_tag):
        '''
        retrieves List of coqexns that serapi transmited on a given serapi command with cmd_tag
        '''
        cur = len(self._serapi_response_history) - 1
        res = []
        while cur >= 0:
            line = self._serapi_response_history[cur].strip()
            line_answer = matches_answer(line, cmd_tag)
            if line_answer is None or line_answer == 'Completed':
                cur -= 1
                continue
            if line_answer == 'Ack':
                break

            coqexn = parse_coqexn(line_answer)
            if not coqexn is None:
                res.append(coqexn)
            cur -= 1

        return res

    async def _answer(self, cmd_tag) -> List[str]:
        """ return the list of str matching answer cmd_tag
        """
        cur = len(self._serapi_response_history) - 1
        res = []
        while cur >= 0:
            line = self._serapi_response_history[cur].strip()
            line_answer = matches_answer(line, cmd_tag)
            if line_answer is None or line_answer == 'Completed':
                cur -= 1
                continue
            if line_answer == 'Ack':
                break
            res.append(line_answer)
            cur -= 1

        return res

    async def save_serapi_log(self):
        """
        dumps json log of sent and received serapi lines
        """
        with open(self._logfname, 'w') as f:
            stderr = []
            async for line in self._kernel.readlines_err(quiet=False):
                stderr.append(line)

            json.dump({'response': self._serapi_response_history,
                       'sent': self._sent_history,
                       'stderr': stderr}, fp=f)

    async def echo(self, quiet=False, timeout=None):
        async for line in self._kernel.readlines(timeout=timeout, quiet=quiet):
            print(line, end='')

    async def echo_err(self, quiet=False, timeout=None):
        async for line in self._kernel.readlines_err(timeout=timeout, quiet=quiet):
            print(line, end='')

    def finished(self):
        return not self._kernel._proc.returncode is None

    def top_thm_close(self, stmt: Optional[str] = None) -> bool:
        """
        Returns True if the top theorem is closed (see details for precise meaning) otherwise in any other case
        it will return False.

        Details: only returns the top thm is closed if the goals & local context transition as follows:
            "" -> []
        """
        if self._queried_local_ctx_and_goals == []:
            raise Exception(
                f'To use top_thm_close() proof you need to make sure you run the execute(ctmt, coq) function'
                f'to populate the coq._queried_local_ctx_and_goals fiedl. '
                f'Right now it looks empty: \n{self._queried_local_ctx_and_goals=}'
                f'\ncurrent coq object is: {self=}'
                f'\nwith fields: {vars(self)=}')
        # - is top thm closed?
        if len(self._queried_local_ctx_and_goals) <= 2:
            return False
        else:
            prev_goals: Union[str, list] = self._queried_local_ctx_and_goals[-2]
            current_goals: Union[str, list] = self._queried_local_ctx_and_goals[-1]
        return prev_goals == "" and current_goals == []


async def execute(stmt: str, coq: CoqSerapi) -> Union[str, list]:
    """
    Execute a Coq statement.
    """
    _, _, coq_exc, _ = await coq.execute(stmt)
    goals: Union[str, list] = await coq.query_local_ctx_and_goals()
    # - store the goals (and local context) so that you can later check what your previous coq stmt & do nice things like know if you've proved the top level thm.
    coq._queried_local_ctx_and_goals.append(goals)

    if coq_exc:
        logging.critical('\n-----Error: coq_exc')
        logging.critical(f'Error, tried executing this statement: {stmt=}')
        logging.critical(f'{coq_exc[0]=}')
        raise Exception(coq_exc[0])
        # raise coq_exc[0]
    return goals


# - test, examples, tutorials

def fixing_query_goals_lc_refined_coq_stmt_vs_stmt_should_be_same_test():
    """

    :return:
    """
    import os
    from pycoq.common import get_pycoq_context_as_dict
    from pycoq.opam import opam_executable
    # -- Args
    switch: str = 'coq-8.16.0'
    pwd = '~/iit-term-synthesis/coq_projects/debug_proj',  # only matters I think if we are building the coq proj
    executable: str = opam_executable('coqc', switch)
    target_coq_file: str = '~/pycoq/debug_coq_project/definition_test.v'
    # figure out later how to automate this, getting it from each project, might not be needed...
    args: list[str] = ["coqc", "-q", "-w", "all", "-Q", ".", "Debug_Proj", target_coq_file.split('/')[-1]]
    env = dict(os.environ)
    # - get pycoq context as dict
    coq_context_dict: dict = get_pycoq_context_as_dict(pwd, executable, target_coq_file, args, env, switch)
    # --
    # import data_pkg
    # #DataPoints = dict[ProofStepID, RawDataPoint]; DataThm = dict[Thm, DataPoints]; DataFile = dict[ThmID, DataThm]
    # data_f: DataFile = {thm_id, {'t'}}
    # # coq_ctxt: CoqContext = pycoq.common.load_context(path2filename)
    # coq_ctxt: CoqContext = CoqContext.from_dict(coq_context_dict)
    # stmts_in_file: iter[str] = pycoq.split.coq_stmts_of_context(coq_ctxt)
    # async with get_coq_serapi(coq_ctxt) as coq:
    #     mode: str = 'init_coq_proj_data_obj'
    #     await update_data_file_from_coq_file(data_f, stmts_in_file, coq, mode=mode, path2filename=path2filename)
    # async with get_coq_serapi(coq_ctxt) as coq:
    #     mode: str = 'hole_refine'
    #     await update_data_file_from_coq_file(data_f, stmts_in_file, coq, mode=mode, path2filename=path2filename)


def playground_sexpdata():
    import sexpdata
    from sexpdata import Symbol

    _local_ctx_and_goals = [Symbol('ObjList'), []]
    print(_local_ctx_and_goals)
    print(_local_ctx_and_goals[0])
    print(str(_local_ctx_and_goals[0]))
    print(type(_local_ctx_and_goals[0]))
    print(sexpdata.__version__)
    print()


# - run __main__

if __name__ == '__main__':
    import time

    start = time.time()
    playground_sexpdata()
    print(f'Done {start - time.time()}')
