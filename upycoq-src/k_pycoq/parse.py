import re

COMMENT_START = r'\(\*'
COMMENT_FINISH = r'\*\)'
QUOTE = r'"'
STATEMENT_END = r'\.\s+'

# regex to find the start and end of comments
COMMENT_SEPARATORS = (
    f'(?P<start>{COMMENT_START})|'
    f'(?P<end>{COMMENT_FINISH})'
)
comment_separators = re.compile(COMMENT_SEPARATORS)

# regex to find the start and end of quotes
quote_separators = re.compile(QUOTE)

# regex to find the start and end of comments, quotes, and dot whites
SEPARATORS = (
    f'(?P<quote>{QUOTE})|'
    f'(?P<statement_end>{STATEMENT_END})|'
    f'(?P<comment_start>{COMMENT_START})|'
    f'(?P<comment_finish>{COMMENT_FINISH})')
separators = re.compile(SEPARATORS)


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
        for m in quote_separators.finditer(line):
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


    def test_parse_comment(coq_text, true_statements):
        import tempfile
        statements = []
        with tempfile.NamedTemporaryFile(mode='w+t') as temporary_file:
            temporary_file.write(coq_text)
            temporary_file.seek(0)
            for statement in statement_iter(temporary_file):
                statements.append(statement)
        assert statements == true_statements


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

    print('All tests passed!')
