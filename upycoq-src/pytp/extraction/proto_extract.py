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


def example_coq_lsp():
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

    # change workspace folder
    client.workspace_did_change_workspace_folders(params=lsp_types.DidChangeWorkspaceFoldersParams(
        event=lsp_types.WorkspaceFoldersChangeEvent(
            added=[lsp_types.WorkspaceFolder(
                uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith',
                name='name')],
            removed=[]
        )
    ))

    # open file
    client.text_document_did_open(params=lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                '/DebugSimpleArith.v',
            language_id='coq',
            version=1,
            text='Require Import Arith.\n'
                 'Theorem plus_0_n : forall n : nat, 0 + n = n.\n'
                 'Proof.\n'
                 '  intros n.\n'
                 '  simpl.\n'
                 '  reflexivity.\n'
                 'Qed.'
        )
    ))

    # get goals
    id = client.proof_goals(params=GoalRequest(text_document=lsp_types.VersionedTextDocumentIdentifier(
        uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
            '/DebugSimpleArith.v',
        version=1
    ), position=lsp_types.Position(line=4, character=4)))

    print(f'Goals: {client.wait_for_response(id)}')

    # close client
    client.close()
    print('Tests passed!')


if __name__ == '__main__':
    example_coq_lsp()
