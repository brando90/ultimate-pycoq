"""
Use this to prototype an proof state extractor

Quote from Kai and Brando:

lsp_client = CoqLSPClient('coq-lsp', '0.1.0', config=config)
lsp_client.initialize(...)

proof_script = ProofScript('file://...', lsp_client)
# Edit the proof script (document is a string)
# Also perhaps implement functionality to edit array of statements as well
proof_script.document += "reflexivity.\nQed."
proof_script.update_document()  # handle lsp stuff (update statement list)

for statement in proof_script.statements:
    # where in proof_script.script is the statement located
    statement_range = statement.range

    # Retrieve proof status
    proof_status = statement.proof_status

    # Handle proof-related metadata
    partial_proof_term = statement.partial_proof_term
    goals = statement.goals
"""
import subprocess
from pathlib import Path
from typing import Union
import json

from packaging.version import parse as parse_version

from pytp.coq.coq_types import ResponseErrorMessage, GoalRequest, GoalAnswer, FlecheDocumentParams, \
    FlecheDocument, FlecheSaveParams, COQ_MESSAGE_TYPES, COQ_RESPONSE_TYPES
from pytp.coq.opam import create_opam_subprocess, opam_run
from pytp.lsp_client import LSPClient, Id
from pytp.lsp_config import LSPConfig
from pytp.coq.converter import get_coq_lsp_converter

from pytp.coq.coq_lsp_client import CoqLSPClient, get_default_coq_lsp_config, get_extract_coq_lsp_config

from itertools import tee, zip_longest
import re

"""
TODO: host a working client outside ./coq, do we have enough utility functions provided by coq_lsp_client ?
"""


"""
Some utility function to be moved elsewhere later
"""
def split_by_idx(S, list_of_indices, strip_whitespace=False):
    left, right = 0, list_of_indices[0] + 1
    if strip_whitespace:
        yield S[left:right].strip()
    else:
        yield S[left:right]

    left = right
    for right in list_of_indices[1:]:
        right += 1
        if strip_whitespace:
            yield S[left:right].strip()
        else:
            yield S[left:right]
        left = right
    if strip_whitespace:
        yield S[left:].strip()
    else:
        yield S[left:]


def find_all(s, c):
    """
    Given a charactor, find index of each each appearance.
    """
    idx = s.find(c)
    while idx != -1:
        yield idx
        idx = s.find(c, idx + 1)


"""
Extraction
"""
def old_parse_proof_file(file_path: Path) :
    """
    Given a proof file, parse information that are needed later in extraction:
    - text: the raw text of the proof file
    - augmented_text: text with appended 'show proof' queries.
    - num_lines: number of lines
    - checkpoints: positions of each '.' (i.e. end of each statement)
    - augmented_checkpoints = [(position of original statement, position of 'show proof' query), ...]

    {
        "uri": uri of this file
        "text": original text,
        "augmented_text": augmented text for extracting proof terms,
        "theorems": info about theorems in this file
        {
            "name": name of the theorem,
            "definition": how the theorem is defined,
            "start_position": [text_index, line, line_index],
            "end_position": [text_index, line, line_index],
            "statements": list of proof steps info
            [{
                "start_position": [text_index, line, line_index],
                "end_position": [text_index, line, line_index],
                "goal": goal at this step,
                "proof_term": partial proof term at this step
                "statements": sub list of proof steps
                [{more statement objs ...}]
            },...],
        }
    }
    """
    text = ""
    augmented_text = ""
    statements = []
    num_line = 0
    checkpoints = []
    augmented_checkpoints = []


    file_data = {
        "uri": file_path, 
        "text": text,
        "augmented_text": augmented_text,
        "theorems": []
    }

    with open(file_path, 'r') as file:

        curr_char_length = 0

        curr_thm_idx = 0
        wait_thm_init = True
        wait_thm_def = True
        wait_thm_stmt = True

        for idx, each in enumerate(file):
            text += each
            num_line += 1
            
            if wait_thm_init and wait_thm_def and wait_thm_stmt:
                # mark position of theorems let's assume there is only one theorem on each line for now TODO: multiple theorem in one line?
                thm_find = each.find('Theorem')
                theorem_start_position = [curr_char_length + thm_find, idx, thm_find]

                # get theorem name. same assumption as above
                colon_find = each.find(':')
                theorem_name = each[theorem_start_position[2] : colon_find].strip()

                # append new thm obj to dict
                thm_obj = {
                    "name": theorem_name,
                    "definition": None,
                    "start_position": theorem_start_position,
                    "end_position": None,
                    "statements": []
                }
                file_data['theorems'].append(thm_obj)

                wait_thm_init = False
            
            if not wait_thm_init and wait_thm_def:
                proof_find = text[theorem_start_position[0]:].find('Proof')
                if proof_find != -1:    # reached proof section, theorem definition must be complete in text
                    print(text[theorem_start_position[0]:proof_find])
                    file_data['theorems'][curr_thm_idx]['definition'] = text[theorem_start_position[0]:proof_find].split(":")[1]
                    wait_thm_def = False
            
            if not wait_thm_def and wait_thm_stmt:
                qed_find = each.find('Qed')


            # determine checkpoints in the original text
            checkpoint = list(find_all(each, '.'))
            checkpoints.append(zip([idx * len(checkpoint)], checkpoint))
            print(checkpoint)
            
            # split text by '.' to get individual statements
            if len(checkpoint):
                statements_in_line = list(split_by_idx(each, checkpoint, strip_whitespace=True))[:-1]
                statements.append(statements_in_line)
                print(statements_in_line)
            else:
                statements.append([])
                print('no statement')
            
            # create augmented text and checkpoints


            # increment char count
            curr_char_length += len(each)

    return text, num_line, checkpoints, statements


def get_text(file_path: Path):
    with open(file_path, 'r') as file:
        text = ''
        lines = []
        for each in file:
            text += each
            lines.append(each)
        return text, lines


def get_theorem_symbols(document_symbol):
    theorems = []
    for each_symbol in document_symbol.result:
        if each_symbol.detail == 'Theorem':
            theorems.append(each_symbol)
    return theorems


def get_theorem_name(theorem_symbol):
    return theorem_symbol.name


def get_theorem_text(theorem_symbol, text_lines, return_range = False):
    """Get the text of a theorem based on its symbol

    Note that the range given by the symbol only goes so far to its the end of definition, not the end of proof.

    Args:
        theorem_symbol (symbol): _description_
        text_lines (list of str): _description_

    Returns:
        str: the full text of the theorem
    """
    assert theorem_symbol.detail == 'Theorem'
    start_line = theorem_symbol.range.start.line
    end_line = theorem_symbol.range.end.line
    start_char = theorem_symbol.range.start.character
    end_char = theorem_symbol.range.end.character
    thm_text = ''
    
    # gather within given range
    for i in range(start_line, end_line + 1):
        if i == start_line:
            thm_text += text_lines[i][start_char:]
        elif i == end_line:
            thm_text += text_lines[i][:end_char+1]
        else:
            thm_text += text_lines[i]
   
    # find the proof
    proof_text = ''
    proof_start_line = end_line
    proof_start_char = end_char + 1
    if end_char + 1 == len(text_lines[end_line]) : # theorem def reaches end of line
        proof_start_line = end_line + 1
        proof_start_char = 0

    proof_end_line = proof_start_line
    proof_end_char = 0
    # first see if a proof exists, that is if theorems ends with 'Qed.'
    for i in range(proof_start_line, len(text_lines)):
        start_char = 0
        if i == proof_start_line:
            start_char = proof_start_char
        proof_text += text_lines[i][start_char:]
        if 'Qed.' in text_lines[i][start_char:]:
            proof_end_line = i
            proof_end_char = text_lines[i][start_char:].find('Qed.') + 4
            break
        if 'Abort.' in text_lines[i][start_char:]:
            proof_end_line = i
            proof_end_char = text_lines[i][start_char:].find('Abort.') + 6
            break
        
    if return_range:
        return thm_text + proof_text, [start_line, start_char, end_line, end_char], [proof_start_line, proof_start_char, proof_end_line, proof_end_char]
    else:
        return thm_text + proof_text


def get_theorem_definition(theorem_text):
    """Get the definition of a theorem from its text

    Returns:
        definition_text (str): the text of the theorem definition
    """
    definition_start = theorem_text.find(':')
    definition_end = theorem_text.find('Proof.')
    
    if definition_end == -1: # if the 'Proof.' keyword is not used
        definition_end = theorem_text.find('.') + 1
    
    definition_text = theorem_text[definition_start + 1: definition_end]
        
    return definition_text


def get_theorem_proof(theorem_text):
    """Get the proof of a theorem from its text

    Returns:
        proof_text (str): the text of the theorem proof
    """
    proof_start = theorem_text.find('Proof.')
    proof_end = theorem_text.find('Qed.')

    proof_text = ''

    if proof_start == -1: # if the 'Proof.' keyword is not used
        proof_start = theorem_text.find('.') + 1
    else:
        proof_start += 6
    
    proof_text = theorem_text[proof_start: proof_end]
        
    return proof_text


def format_proof_text(proof_text):
    """Format the proof text to remove bullet points, comments and indentation
    
    TODO: support bullet level

    Args:
        proof_text (_type_): _description_
    """

    proof_texts = [each.strip() for each in proof_text.split('\n')]

    for each_idx, each in enumerate(proof_texts):
        # remove bullet points
        re_front_bullet = re.compile(r'^[\*\-{\+]+')
        proof_texts[each_idx] = re_front_bullet.sub('', each).replace('}','').strip()

        # remove comments
        re_comment = re.compile(r'\(\*.*\*\)')
        proof_texts[each_idx] = re_comment.sub('', proof_texts[each_idx]).strip()
    
    idx = 0 
    while idx < len(proof_texts): 
        # break lines at each step
        line_split = proof_texts[idx].split('.')
        if len(line_split) > 2:
            proof_texts[idx] = line_split[0] + '.'
            for j, each in enumerate(line_split[1:-1]):
                if each.strip() != "Show Proof": # skip all exisiting Show Proof
                    proof_texts.insert(idx + j + 1, each.strip() + '.')
            idx += len(line_split) - 1
        else:
            idx += 1

    proof_texts.append('Qed.')
    
    proof_texts = filter(lambda x: x != '', proof_texts)
    
    
    return '\n'.join(proof_texts)


def get_augmented_proof_steps(formated_proof_text):
    proof_steps = formated_proof_text.split('\n')
    augmented_proof_steps = ['Show Proof.'] + [proof_steps + ' Show Proof.' for proof_steps in proof_steps]  # the first Show Proof will always be '?Goal', TODO: check this
    return augmented_proof_steps


def mark_checkpoints_in_range(text_lines, start_line, start_char, end_line, end_char):
    check_points = []
    for l, each in enumerate(text_lines[start_line:end_line+1]):
        l += start_line
        check_points += [*[[l, i] for i in find_all(each, '.') if i != len(each) - 1 and (l != 0 or i != 0) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char) and (l != end_line or i != end_char) and (l != start_line or i != start_char)]]
    return check_points


def substitute_augmented_proof_steps(text_lines, augmented_proof_steps, proof_start_line, proof_start_char, proof_end_line, proof_end_char):
    for i in range(len(augmented_proof_steps)):
        if i == 0:
            text_lines[proof_start_line] = text_lines[proof_start_line][:proof_start_char] + ' ' + augmented_proof_steps[0] + ' '
        elif i == len(augmented_proof_steps) - 1:
            text_lines[proof_start_line] += augmented_proof_steps[-1] + '\n' # TODO: for now assume the next thm must be on the next line
        else:
            text_lines[proof_start_line] += augmented_proof_steps[i] + ' '
    for i in range(proof_start_line+1, proof_end_line+1):
        if i == proof_end_line and proof_end_char != len(text_lines[i]) - 1:
            text_lines[i] = text_lines[i][proof_end_char+1:]
        else:
            text_lines[i] = '\n'
    return text_lines


def parse_proof_file(file_path: Path):
    text, lines = get_text(file_path)
    return text, len(lines), lines


def winston_coq_lsp():
    # test coq-lsp
    config = get_extract_coq_lsp_config()
    config.lsp_settings['switch'] = 'coqlsp'
    config.lsp_settings['flags'] = ['--bt']
    client = CoqLSPClient('coq-lsp', '0.1.0', config=config)

    import lsprotocol.types as lsp_types

    # # initialize client
    # id = client.initialize(params=lsp_types.InitializeParams(
    #     capabilities=lsp_types.ClientCapabilities(),
    #     root_path=str(Path.cwd()),
    #     root_uri=str(Path.cwd().as_uri()),
    #     workspace_folders=[lsp_types.WorkspaceFolder(uri=str(Path.cwd().as_uri()), name='name')]
    # ))

    # print(client.wait_for_response(id))
    # print('Initialized')

    new_workspace_path = Path('~/ultimate-pycoq/coq-projects/debug/debug_simple_arith').expanduser()
    new_workspace_path = Path('~/ultimate-pycoq/coq-projects/basic-lf/lf').expanduser()

    # change workspace folder
    client.workspace_did_change_workspace_folders(params=lsp_types.DidChangeWorkspaceFoldersParams(
        event=lsp_types.WorkspaceFoldersChangeEvent(
            added=[lsp_types.WorkspaceFolder(
                uri=new_workspace_path.as_uri(),
                name='name')],
            removed=[]
        )
    ))

    # open file
    proof_path = new_workspace_path / 'debug_0_plus_n_eq_n.v'
    proof_path = new_workspace_path / 'Basics.v'
    # proof_path = new_workspace_path / 'Lists.v'
    file_text, num_lines, text_lines = parse_proof_file(proof_path)
    print("===========")
    print(file_text)
    print("===========")
    client.text_document_did_open(params=lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri=(proof_path).as_uri(),
            language_id='coq',
            version=1,
            text = file_text 
        )
    ))

    id = client.text_document_document_symbol(params=lsp_types.DocumentSymbolParams(
        text_document=lsp_types.TextDocumentItem(
            uri=(proof_path).as_uri(),
            language_id='coq',
            version=1,
            text = file_text 
        )
    ))
    document_symbols = client.wait_for_response(id)
    print(f'Document Symbols: {document_symbols}')

    # get theorems
    thm_symbols = get_theorem_symbols(document_symbols)
    theorems = {}
    for each_thm_symbol in thm_symbols:
        thm_text, def_ranges, proof_ranges = get_theorem_text(each_thm_symbol, text_lines, return_range=True)
        thm_def = get_theorem_definition(thm_text)
        thm_proof = get_theorem_proof(thm_text)
        theorems[get_theorem_name(each_thm_symbol)] = {
            'text': thm_text,
            'definition': thm_def, 
            'proof': thm_proof,
            'def_ranges': def_ranges, # [start_line, start_char, end_line, end_char]
            'proof_ranges': proof_ranges,
            'proof_steps': []
        }
    
    curr_version = 1
    
    for k, v in theorems.items():
        print("=======================")
        print(f'Theorem: {k}') 
        print(f'Definition Range: {v["def_ranges"]}')
        print(f'Proof Range: {v["proof_ranges"]}')
        print("===========")
        print(f'Text: {v["text"]}')
        print("===========")
        print(f'Definition: {v["definition"]}')
        print("===========")
        print(f'Proof: {v["proof"]}')
        print("===========")
        print(f'Formated Proof: {format_proof_text(v["proof"])}')
        print("===========")
        text_lines = substitute_augmented_proof_steps(text_lines, get_augmented_proof_steps(format_proof_text(v["proof"])), *v['proof_ranges'])
        new_thm_text = "".join(text_lines[v["def_ranges"][0]:v["proof_ranges"][2]])
        print(f'Augmented Text: {new_thm_text}')
        print("===========")
        checkpoints = mark_checkpoints_in_range(text_lines, v['def_ranges'][0],v['def_ranges'][1],v['proof_ranges'][2],v['proof_ranges'][3])
        print(f'Checkpoints: {checkpoints}')
        print("===========")
        curr_version += 1
        id = client.text_document_did_change(params=lsp_types.DidChangeTextDocumentParams(
            text_document=lsp_types.VersionedTextDocumentIdentifier(
                uri=(proof_path).as_uri(),
                version=curr_version
            ),
            content_changes=[lsp_types.TextDocumentContentChangeEvent_Type2(text=''.join(text_lines))]
        ))

        is_statement = True
        proof_steps = {
            'text': None,
            'goal_before': None,
            'goal_after': None,
            'proof_term_before': None, 
            'proof_term_after': None, 
        }

        curr_idx = 0
        for i in range(2, len(checkpoints)):
            if is_statement:
                proof_steps['text'] = format_proof_text(v['proof']).split('\n')[curr_idx]

                id = client.proof_goals(params=GoalRequest(text_document=lsp_types.VersionedTextDocumentIdentifier(
                                        uri=(proof_path).as_uri(),
                                        version=curr_version
                                        ), position=lsp_types.Position(line=checkpoints[i][0], character=max(checkpoints[i][1] - 1, 0))))
                goal = client.wait_for_response(id)
                proof_steps['goal_before'] = [each_g.ty for each_g in goal.result.goals.goals] if goal.result.goals else []
                proof_steps['proof_term_before'] = theorems[k]['proof_steps'][-1]['proof_term_after'] if len(theorems[k]['proof_steps']) else []
            else:
                id = client.proof_goals(params=GoalRequest(text_document=lsp_types.VersionedTextDocumentIdentifier(
                                        uri=(proof_path).as_uri(),
                                        version=curr_version
                                        ), position=lsp_types.Position(line=checkpoints[i][0], character=max(checkpoints[i][1] - 1, 0))))
                proof_term = client.wait_for_response(id)
                proof_steps['goal_after'] = [each_g.ty for each_g in proof_term.result.goals.goals] if proof_term.result.goals else []
                proof_steps['proof_term_after'] = [each_m.text for each_m in proof_term.result.messages]
                theorems[k]['proof_steps'].append(proof_steps)
                proof_steps = {
                    'text': None,
                    'goal_before': None,
                    'goal_after': None,
                    'proof_term_before': None, 
                    'proof_term_after': None, 
                }
                curr_idx += 1
            is_statement = not is_statement
        print("===========")
        # proof_steps = theorems[k]['proof_steps']
        # for each in proof_steps: print(each)
        
        print("=======================")
        
    with open(f'extracted_theorems.json', 'w') as out_f:
        thm_json = json.dumps(theorems)
        out_f.write(thm_json)


    # close client
    client.close()

    print('Tests passed!')
    print(theorems)


if __name__ == '__main__':
    winston_coq_lsp()
