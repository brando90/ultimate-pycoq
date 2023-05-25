import re
from typing import Iterator, List


COMMENT_START = r'\(\*'  # (*
COMMENT_END = r'\*\)'  # *)
QUOTE = r'"'  # "
STATEMENT_END = r'\.\s+'  # . followed by at least one whitespace

# regex to find the start and end of comments
COMMENT_SEPARATORS = (
    f'(?P<start>{COMMENT_START})|'
    f'(?P<end>{COMMENT_END})'
)
comment_separators = re.compile(COMMENT_SEPARATORS)

# regex to find the start and end of quotes
quote_separator = re.compile(QUOTE)

# regex to find the start and end of comments, quotes, and statement ends
SEPARATORS = (
    f'(?P<quote>{QUOTE})|'
    f'(?P<statement_end>{STATEMENT_END})|'
    f'(?P<comment_start>{COMMENT_START})|'
    f'(?P<comment_end>{COMMENT_END})')
separators = re.compile(SEPARATORS)


class StatementParser(Iterator[str]):

    def __init__(self, file):
        self.file = file
        self.contents: str = file.read()
        self.line_number: int = 0
        self.statement_start: int = 0  # start of the current statement in self.contents
        self.file_pointer: int = 0  # current position in self.contents while parsing
        self.separators = separators.finditer(self.contents)

    def __next__(self):
        return self.next_statement()

    def parse_comment(self):
        """
        Parses the next comment from the file. Assumes that the starting comment '(*' has already been read from self.separators.
        :return: None
        """
        comment_level = 1
        for m in self.separators:
            sep = m.lastgroup
            if sep == 'comment_start':
                comment_level += 1
            elif sep == 'comment_end':
                comment_level -= 1

            if comment_level == 0:
                self.file_pointer = m.end()
                return
        raise EOFError('EOF reached before end of comment')

    def parse_quote(self):
        """
        Parses the next quote from the file. Assumes that the starting quote has already been read from self.separators.
        :return: None
        """
        for m in self.separators:
            sep = m.lastgroup
            if sep == 'quote':
                self.file_pointer = m.end()
                return
        raise EOFError('EOF reached before end of quote')

    def next_statement(self) -> str:
        """
        Parses the next statement from the file.
        :return: the next statement
        """
        for m in self.separators:
            self.file_pointer = m.start()
            sep = m.lastgroup
            if sep == 'comment_start':
                self.parse_comment()
            elif sep == 'quote':
                self.parse_quote()
            elif sep == 'statement_end':
                self.file_pointer = m.end()
                statement = self.contents[self.statement_start:self.file_pointer]
                self.statement_start = self.file_pointer
                return statement
            else:
                raise Exception(f'Unknown separator: {sep}')

        self.file_pointer = len(self.contents)
        statement = self.contents[self.statement_start:]
        self.statement_start = self.file_pointer

        # return last part of file, even if we didn't find a statement end
        # (it could be we had a period followed by EOF)
        if statement != '':
            return statement
        raise StopIteration


def parse_comment(file, line: str, pos: int) -> (str, int):
    """
    Takes a file object, and moves the file pointer to the end of the next comment.
    :param file: coq file
    :param line: current line
    :param pos: position of the start of the comment in line
    :return: the comment, the new current line, and the position of the end of the comment
    """

    comment_level = 0
    line = line[pos:]
    comment = ''

    while line != '':
        for m in comment_separators.finditer(line):
            sep = m.lastgroup
            if sep == 'start':
                comment_level += 1
            elif sep == 'end':
                comment_level -= 1
            else:
                raise Exception(f'Unknown separator: {sep}')

            if comment_level == 0:
                comment += line[:m.end()]
                return comment, line, m.end()

        comment += line
        line = file.readline()

    raise EOFError('EOF reached before end of comment')


def parse_quote(file, line: str, pos: int) -> (str, int):
    """
    Takes a file object, and moves the file pointer to the end of the next quote.
    :param file: coq file
    :param line: current line
    :param pos: position of the start of the string in line
    :return: the quote, the new current line, and the position of the end of the quote
    """

    in_quote = False
    line = line[pos:]
    quote = ''

    while line != '':
        for m in quote_separator.finditer(line):
            in_quote = not in_quote
            if not in_quote:
                quote += line[:m.end()]
                return quote, line, m.end()

        quote += line
        line = file.readline()

    raise EOFError('EOF reached before end of quote')


def statement_iter(file):
    """
    Takes a coq file object, and iterates over the statements in the file.
    :param file: coq file
    :return: the next statement in the file
    """
    statement = ''
    line = file.readline()
    pos = 0

    while line != '':
        # remove the part of the line that has already been parsed
        line = line[pos:]
        m = separators.search(line)

        # if no separator is found, the statement continues on the next line
        if m is None:
            statement += line
            line = file.readline()
            pos = 0
        else:  # if a separator is found, parse it
            sep = m.lastgroup
            statement += line[:m.start()]
            if sep == 'statement_end':
                statement += line[m.start():m.end()]
                pos = m.end()  # move the position to the end of the statement
                yield statement
                statement = ''
            elif sep == 'quote':
                quote, line, pos = parse_quote(file, line, m.start())
                statement += quote
            elif sep == 'comment_start':
                comment, line, pos = parse_comment(file, line, m.start())
                statement += comment
            elif sep == 'comment_finish':
                raise Exception(f'Found unexpected comment end "*)" in line: {line}')
            else:
                raise Exception(f'Unknown separator: {sep}')
    # if the file didn't end with a statement, still yield it
    # TODO: is this how we should be handling it?
    if statement != '':
        yield statement


if __name__ == '__main__':
    from textwrap import dedent

    # begin time test
    import time

    total_parse_time = 0


    def test_parse_comment(coq_text, true_statements):
        import tempfile
        statements = []
        with tempfile.NamedTemporaryFile(mode='w+t') as temporary_file:
            temporary_file.write(coq_text)
            temporary_file.seek(0)

            start = time.time()

            parser = StatementParser(temporary_file)
            # for statement in statement_iter(temporary_file):
            for statement in parser:
                statements.append(statement)

            end = time.time()
            global total_parse_time
            total_parse_time += end - start
        assert statements == true_statements


    for i in range(1000):
        coq_test = """\
        (* This is a comment *).
        "This is a string.".   
        "This is a. string. with a (* comment *) in it".
        "This is a string with.a (* comment (* nested comment *) *) in it".
        (* This is a comment. with a "string" in it *).
        (* This is a comment with a "string (* nested. comment *) " in it *).
        (* This is a comment.with a "string (* nested comment (* nested. comment *) *) " in it *).
        Require Import Lia. (* comment after line *).
        """

        true_statements = ['(* This is a comment *).\n',
                           '"This is a string.".   \n',
                           '"This is a. string. with a (* comment *) in it".\n',
                           '"This is a string with.a (* comment (* nested comment *) *) in it".\n',
                           '(* This is a comment. with a "string" in it *).\n',
                           '(* This is a comment with a "string (* nested. comment *) " in it *).\n',
                           '(* This is a comment.with a "string (* nested comment (* nested. comment *) *) " in it *).\n',
                           'Require Import Lia. ', '(* comment after line *).\n']

        test_parse_comment(dedent(coq_test), true_statements)

        coq_test = """
        Theorem n_plus_1_greater_than_n: (* comment inside statement *) forall n: nat, n + 1> n.
        Proof.
        intro. (* comment after line *)
        (* comment before line *) lia.
        Qed.
        """

        true_statements = [
            '\nTheorem n_plus_1_greater_than_n: (* comment inside statement *) forall n: nat, n + 1> n.\n',
            'Proof.\n',
            'intro. ',
            '(* comment after line *)\n'
            '(* comment before line *) lia.\n',
            'Qed.\n']

        test_parse_comment(dedent(coq_test), true_statements)

        coq_test = """
        Require Import Strings.String.
        Local Open Scope string_scope.
    
        (* comment with single double quote
        (* *) "
        *)
    
        Definition test : string := "Hello "" .World!".
        Definition test2 : string := " . "". "". (* *) ".
        
        "String with single open comment (* "
        "String with single close comment *) "
    
        Print test.
        """

        true_statements = ['\nRequire Import Strings.String.\n',
                           'Local Open Scope string_scope.\n\n',
                           '(* comment with single double quote\n(* *) "\n*)\n\n'
                           'Definition test : string := "Hello "" .World!".\n',
                           'Definition test2 : string := " . "". "". (* *) ".\n\n',
                           '"String with single open comment (* "\n'
                           '"String with single close comment *) "\n\n'
                           'Print test.\n']

        test_parse_comment(dedent(coq_test), true_statements)

        coq_test = """
        "string""str. ing"   "str. ing""string" (* com. ment *).  "string""string" (* comment *)(* com. ment *).
        """

        true_statements = ['\n"string""str. ing"   "str. ing""string" (* com. ment *).  ',
                           '"string""string" (* comment *)(* com. ment *).\n']

        test_parse_comment(dedent(coq_test), true_statements)

        coq_test = """
        "string
        on
        multiple
        lines".
        (* comment
        on
        multiple
        lines
        *)
        """

        true_statements = ['\n"string\non\nmultiple\nlines".\n',
                           '(* comment\non\nmultiple\nlines\n*)\n']

        test_parse_comment(dedent(coq_test), true_statements)

    print(f'All tests passed in time {total_parse_time:.2f}s')
