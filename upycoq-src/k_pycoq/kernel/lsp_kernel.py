"""
This file defines the kernel interface for Coq through coq-lsp. This file outlines the main entry point for
interacting with Coq.
"""
import subprocess
import json
from pathlib import Path
from typing import Any

from k_pycoq.kernel import AbstractKernel
from k_pycoq.opam import create_opam_subprocess

import k_pycoq.kernel.lsp_protocol as lsp_protocol

_method_params = {
    'initialize': lsp_protocol.InitializeParams,
    'initialized': None,
    # 'client/registerCapability': lsp_protocol.RegistrationParams,  # not planned atm
    '$/setTrace': lsp_protocol.SetTraceParams,
    '$/logTrace': lsp_protocol.LogTraceParams,
    'textDocument/didOpen': lsp_protocol.DidOpenTextDocumentParams,
    'textDocument/didChange': lsp_protocol.DidChangeTextDocumentParams,
    'textDocument/didSave': lsp_protocol.DidSaveTextDocumentParams,
    'textDocument/didClose': lsp_protocol.DidCloseTextDocumentParams,
    # 'notebookDocument/didOpen': ...,  # planned
    # 'textDocument/declaration': ...,  # planned, blocked on upstream issues
    'textDocument/definition': lsp_protocol.TextDocumentPositionParams,  # partial
    # 'textDocument/references': ...,  # planned, blocked on upstream issues
    'textDocument/hover': lsp_protocol.HoverParams,
    # 'textDocument/codeLens': ...,
    # 'textDocument/foldingRange': ...,
    'textDocument/documentSymbol': lsp_protocol.DocumentSymbolParams,
    # 'textDocument/semanticTokens': ...,  # planned
    # 'textDocument/inlineValues': ...,  # planned
    # 'textDocument/inlayHints': ...,  # planned
    'textDocument/completion': lsp_protocol.CompletionParams, # partial
    'textDocument/publishDiagnostics': lsp_protocol.PublishDiagnosticsParams,
    # 'textDocument/diagnostics': ..., # planned
    # 'textDocument/codeAction': ..., # planned
    'workspace/workspaceFolders': lsp_protocol.WorkspaceFoldersParams,  # folders should contain _CoqProject in root
    'workspace/didChangeWorkspaceFolders': lsp_protocol.DidChangeWorkspaceFoldersParams,
}

JSONRPC_REQ_FORMAT = 'Content-Length: {content_length}\r\n\r\n{content}'


class LSPEndPoint:
    def __init__(self, lsp):
        """Creates a new endpoint for communicating with lsp
        lsp: the subprocess to communicate with
        """
        self.lsp = lsp
        self.id = 0

    @staticmethod
    def _add_header(content: str):
        return JSONRPC_REQ_FORMAT.format(content_length=len(content), content=content)

    def send_notification(self, method: str, params: dict[str: Any]):
        """sends notification to lsp"""
        content = json.dumps({'jsonrpc': '2.0', 'method': method, 'params': params}, indent=1)
        print(f'NOTIFICATION: {content}')
        self.lsp.stdin.write(self._add_header(content))
        self.lsp.stdin.flush()

    def _parse_response(self):
        """parses response from lsp"""
        headers = {}
        while True:
            line = self.lsp.stdout.readline().strip()
            if line == '':
                break

            header = line.split(':')

            if len(header) != 2:
                raise Exception(f'Received invalid header {line}')

            key, value = header[0].strip(), header[1].strip()
            if value.isdigit():
                value = int(value)
            headers[key] = value

        if 'Content-Length' not in headers:
            raise Exception(f'Received invalid response header. Expected Content-Length, got {headers}')

        if not isinstance(headers['Content-Length'], int):
            raise Exception(f'Received invalid content length {headers["Content-Length"]} of '
                            f'type {type(headers["Content-Length"])}')

        content = self.lsp.stdout.read(headers['Content-Length'])
        print(f'RECEIVED: {content}')
        content = json.loads(content)
        return content

    def send_request(self, method: str, params: dict[str: Any]):
        """sends request to lsp"""
        self.id += 1
        content = json.dumps({'jsonrpc': '2.0', 'method': method, 'params': params, 'id': self.id}, indent=1)
        print(f'REQUEST: {content}')
        self.lsp.stdin.write(self._add_header(content))
        self.lsp.stdin.flush()
        return self._parse_response()


class LSPKernel(AbstractKernel):

    def __init__(self, opam_switch: str, opam_root, top_file: str, flags: list[str]):
        super().__init__()
        self.opam_switch: str = opam_switch
        self.opam_root = opam_root
        self.flags: list[str] = flags
        self.top_file: str = top_file
        self._lsp = create_opam_subprocess('coq-lsp', self.opam_switch, self.opam_root,
                                           stdin=subprocess.PIPE,
                                           stdout=subprocess.PIPE,
                                           stderr=subprocess.STDOUT)
        self._lsp_endpoint = LSPEndPoint(self._lsp)


if __name__ == '__main__':
    # test lsp_endpoint
    lsp = create_opam_subprocess('coq-lsp --bt', 'coqlsp',
                                 Path('/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug'
                                      '/debug_simple_arith'),
                                 stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
    lsp_endpoint = LSPEndPoint(lsp)
    # lsp.stdin.write('Content-Length: 0\r\n\r\n')
    # lsp.stdin.flush()
    # print(lsp_endpoint._parse_response())
    import os
    pid = os.getpid()

    lsp_endpoint.send_request('initialize', {
        'processId': pid,
        'workspaceFolders': [{
            'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith',
            'name': 'coq-lsp'
        }],
        'clientInfo': {
            'name': 'pycoq',
            'version': '0.0.1'
        },
        'capabilities': {
            'textDocument': {
                'publishDiagnostics': {
                    'relatedInformation': True
                }
            },
            'workspace': {
                'workspaceFolders': True
            }
        }
    })

    lsp_endpoint._parse_response()
    lsp_endpoint._parse_response()

    # wait for 0.1 sec
    # import time
    # time.sleep(0.1)
    # print(response)

    lsp_endpoint.send_notification('initialized', {})
    # time.sleep(0.1)

    # send: "wrong_file.v",
    #     "coq",
    #     0,
    #     "Definition a := 3."

    lsp_endpoint.send_notification('textDocument/didOpen', {
        'textDocument': {
            'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                        '/SimpleArith.v',
            'languageId': 'coq',
            'version': 1,
            'text': 'Require Import Arith.\n\nGoal 1 + 1 = 2.\nProof.\n  reflexivity.\nQed.'
        }
    })

    # textDocument/publishDiagnostics
    # lsp_endpoint.send_notification('coq/getDocument', {
    #     'textDocument': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #                     '/SimpleArith.v'
    # })

    # interface GoalRequest {
    #     textDocument: VersionedTextDocumentIdentifier;
    #     position: Position;
    #     pp_format?: 'Pp' | 'Str';
    # }

    # lsp_endpoint.send_request('proof/goals', {
    #     'textDocument': {
    #         'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #                '/SimpleArith.v',
    #         'languageId': 'coq',
    #         'version': 1
    #     },
    #     'position': {
    #         'line': 4,
    #         'character': 0
    #     }
    # })

    lsp_endpoint.send_request('coq/getDocument', {
        'textDocument': {
            'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                   '/SimpleArith.v',
            'languageId': 'coq',
            'version': 1
        }
    })



    # lsp_endpoint.send_notification('initialized', {})

    # lsp_endpoint.send_notification('textDocument/didOpen', {
    #     'textDocument': {
    #         'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #                  '/SimpleArith.v',
    #         'languageId': 'coq',
    #         'version': 1,
    #         'text': 'Require Import Arith.\n\nGoal 1 + 1 = 2.\nProof.\n  reflexivity.\nQed.'
    #     }
    # })
    #
    # lsp_endpoint.send_notification('textDocument/didSave', {
    #     'textDocument': {
    #         'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #                     '/SimpleArith.v',
    #         'version': 2
    #     }
    # })

    while True:
        line = lsp.stdout.readline()
        if line != '':
            print(line, end='')


