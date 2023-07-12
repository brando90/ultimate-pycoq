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


from packaging.version import parse as parse_version

from pytp.coq.coq_types import ResponseErrorMessage, GoalRequest, GoalAnswer, FlecheDocumentParams, \
    FlecheDocument, FlecheSaveParams, COQ_MESSAGE_TYPES, COQ_RESPONSE_TYPES
from pytp.coq.opam import create_opam_subprocess, opam_run
from pytp.lsp_client import LSPClient, Id
from pytp.lsp_config import LSPConfig
from pytp.coq.converter import get_coq_lsp_converter

from pytp.coq.coq_lsp_client import CoqLSPClient, get_default_coq_lsp_config

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
def parse_proof_file(file_path: Path):
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


def winston_coq_lsp():
    # test coq-lsp
    config = get_default_coq_lsp_config()
    config.lsp_settings['switch'] = 'coqlsp'
    config.lsp_settings['flags'] = ['--bt']
    client = CoqLSPClient('coq-lsp', '0.1.0', config=config)

    import lsprotocol.types as lsp_types

    # initialize client
    id = client.initialize(params=lsp_types.InitializeParams(
        capabilities=lsp_types.ClientCapabilities(),
        root_path=str(Path.cwd()),
        root_uri=str(Path.cwd().as_uri()),
        workspace_folders=[lsp_types.WorkspaceFolder(uri=str(Path.cwd().as_uri()), name='name')]
    ))

    print(client.wait_for_response(id))
    print('Initialized')

    new_workspace_path = Path('~/ultimate-pycoq/coq-projects/debug/debug_simple_arith').expanduser()

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
    proof_path = new_workspace_path / 'DebugSimpleArith.v'
    proof_text, proof_num_lines, proof_checkpoints, proof_statements = parse_proof_file(proof_path)
    print("===========")
    print(proof_text)
    print("===========")
    client.text_document_did_open(params=lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri=(proof_path).as_uri(),
            language_id='coq',
            version=1,
            text = proof_text 
        )
    ))

    id = client.text_document_document_symbol(params=lsp_types.DocumentSymbolParams(
        text_document=lsp_types.TextDocumentItem(
            uri=(proof_path).as_uri(),
            language_id='coq',
            version=1,
            text = proof_text 
        )
    ))
    response = client.wait_for_response(id)
    print(f'Document Symbols: {response}')

    # get goals for each line
    proof_goals = []
    proof_messages = []
    for i in range(proof_num_lines):
        # get proof goals for each statement
        # line_goals = []
        # for ckpt in proof_checkpoints[i]:
        #     id = client.proof_goals(params=GoalRequest(text_document=lsp_types.VersionedTextDocumentIdentifier(
        #         uri=(new_workspace_path / 'DebugSimpleArith.v').as_uri(),
        #         version=1
        #     ), position=lsp_types.Position(line=i, character=0)))

        # get proof terms for each statement

        response = client.wait_for_response(id)
        print(f'Goals at line {i}: {response}')

        proof_messages.append(response.messages)
        proof_goals.append(response.goals)

        # handle proof related meta-data
        pass
    
    print("===========")
    for idx, each in enumerate(proof_goals):
        print(idx, each)
    print("===========")
    print("===========")
    for idx, each in enumerate(proof_messages):
        print(idx, each)
    print("===========")

    # close client
    client.close()

    print('Tests passed!')


if __name__ == '__main__':
    winston_coq_lsp()
