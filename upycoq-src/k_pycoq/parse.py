import re
from typing import Iterator, List

COMMENT_START = r'\(\*'  # (*
COMMENT_FINISH = r'\*\)'  # *)
QUOTE = r'"' # "
STATEMENT_END = r'\.\s+'  # . followed by at least one whitespace

# regex to find the start and end of comments
COMMENT_SEPARATORS = (
    f'(?P<start>{COMMENT_START})|'
    f'(?P<end>{COMMENT_FINISH})'
)
comment_separators = re.compile(COMMENT_SEPARATORS)

# regex to find the start and end of quotes
quote_separator = re.compile(QUOTE)

# regex to find the start and end of comments, quotes, and statement ends
SEPARATORS = (
    f'(?P<quote>{QUOTE})|'
    f'(?P<statement_end>{STATEMENT_END})|'
    f'(?P<comment_start>{COMMENT_START})|'
    f'(?P<comment_finish>{COMMENT_FINISH})')
separators = re.compile(SEPARATORS)


class StatementParser(Iterator[str]):
    def __next__(self):
        return self.parse_statement()

    def __init__(self, file):
        self.file = file
        self.buffer = ''
        self.line_number = 0
        self.current_statement = []

    def _end_of_file(self):
        """
        Reads the next line from file to buffer if buffer is empty. If end of file is reached, buffer remains empty.
        :return: True if end of file is reached, False otherwise
        """
        if self.buffer == '':
            self.buffer = self.file.readline()
            self.line_number += 1
        return self.buffer == ''

    def _dump_buffer(self, idx: int = None) -> str:
        """
        returns the buffer content upto idx, and removes the text upto idx from the buffer.
        :param idx: index to dump upto
        :return: buffer contents upto idx
        """
        idx = idx if idx is not None else len(self.buffer)

        contents = self.buffer[:idx]
        self.buffer = self.buffer[idx:]

        return contents

    def next_match(self, regex, start: bool = True) -> (bool, List[str]):
        """
        Finds the next match of regex in the file, and moves the buffer to the start or end of the match
        depending on the value of start.
        :param regex: regex to match
        :param start: if True, move buffer to start of match, else move buffer to end of match
        :return: regex match if found and buffer contents upto the match, split by newlines. Note that the
        positions of the regex match are wrong since the buffer has been modified.
        """
        contents = []
        while not self._end_of_file():
            m = re.search(regex, self.buffer)
            if m is None:
                contents.append(self._dump_buffer())
            else:
                idx = m.start() if start else m.end()
                contents.append(self._dump_buffer(idx=idx))
                return m, contents

        return None, contents

    def parse_comment(self) -> List[str]:
        """
        Moves the buffer to the end of the next comment.
        :return: the parsed comment, split by newlines
        """
        comment_level = 0
        comment = []

        while True:
            m, content = self.next_match(comment_separators, start=False)
            if not m:
                raise EOFError('EOF reached before end of comment.')

            comment.extend(content)

            sep_type = m.lastgroup
            if sep_type == 'start':
                comment_level += 1
            elif sep_type == 'end':
                comment_level -= 1

            if comment_level == 0:
                return comment

    def parse_quote(self) -> List[str]:
        """
        Moves the buffer to the end of the next quote.
        :return: the parsed quote, split by newlines
        """
        in_quote = False
        quote = []

        while True:
            m, content = self.next_match(quote_separator, start=False)
            if not m:
                raise EOFError('EOF reached before end of quote.')

            quote.extend(content)

            in_quote = not in_quote
            if not in_quote:
                return quote

    def parse_statement(self) -> str:
        """
        Moves the buffer to the end of the next statement.
        :return: the parsed statement
        """
        statement = []

        while not self._end_of_file():
            # find the next comment, quote, or statement end
            m, content = self.next_match(separators, start=True)

            statement.extend(content)

            # if we have reached the end of the file, return the statement
            if m is None:
                return ''.join(statement)

            sep_type = m.lastgroup
            if sep_type == 'statement_end':
                statement.append(self._dump_buffer(idx=len(m.group())))
                return ''.join(statement)
            elif sep_type == 'quote':
                statement.extend(self.parse_quote())
            elif sep_type == 'comment_start':
                statement.extend(self.parse_comment())
            elif sep_type == 'comment_finish':
                raise Exception(f'Unexpected comment end found on line {self.line_number}.')
            else:
                raise Exception(f'Unknown separator: {sep_type}')

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
    start = time.time()

    def test_parse_comment(coq_text, true_statements):
        import tempfile
        statements = []
        with tempfile.NamedTemporaryFile(mode='w+t') as temporary_file:
            temporary_file.write(coq_text)
            temporary_file.seek(0)
            parser = StatementParser(temporary_file)
            for statement in parser:
                statements.append(statement)
        assert statements == true_statements

    for i in range(1000):
        coq_test = """\
        (* This is a comment *).
        "This is a string.".
        "This is a. string. with a (* comment *) in it".
        "This is a string with.a (* comment (* nested comment *) *) in it".
        (* This is a comment.with a "string" in it *).
        (* This is a comment with a "string (* nested. comment *) " in it *).
        (* This is a comment.with a "string (* nested comment (* nested.comment *) *) " in it *).
        Require Import Lia. (* comment after line *).
        """

        true_statements = ['(* This is a comment *).\n',
                           '"This is a string.".\n',
                           '"This is a. string. with a (* comment *) in it".\n',
                           '"This is a string with.a (* comment (* nested comment *) *) in it".\n',
                           '(* This is a comment.with a "string" in it *).\n',
                           '(* This is a comment with a "string (* nested. comment *) " in it *).\n',
                           '(* This is a comment.with a "string (* nested comment (* nested.comment *) *) " in it *).\n',
                           'Require Import Lia. ', '(* comment after line *).\n']

        test_parse_comment(dedent(coq_test), true_statements)

        coq_test = """
        Theorem n_plus_1_greater_than_n: (* comment inside statement *) forall n: nat, n + 1> n.
        Proof.
        intro. (* comment after line *)
        (* comment before line *) lia.
        Qed.
        """

        true_statements = ['\nTheorem n_plus_1_greater_than_n: (* comment inside statement *) forall n: nat, n + 1> n.\n',
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
                           'Local Open Scope string_scope.\n',
                           '\n(* comment with single double quote\n(* *) "\n*)\n\n'
                           'Definition test : string := "Hello "" .World!".\n',
                           'Definition test2 : string := " . "". "". (* *) ".\n',
                           '\n"String with single open comment (* "\n'
                           '"String with single close comment *) "\n'
                           '\nPrint test.\n']

        test_parse_comment(dedent(coq_test), true_statements)

        coq_test = """
        "string""str. ing"   "str. ing""string" (* com. ment *). "string""string" (* comment *)(* com. ment *).
        """

        true_statements = ['\n"string""str. ing"   "str. ing""string" (* com. ment *). ',
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

    end = time.time()

    print(f'All tests passed in time {end - start:.2f}s')
