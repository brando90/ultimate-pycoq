"""
This file defines the kernel interface for Coq through coq-lsp. This file outlines the main entry point for
interacting with Coq.
"""
import subprocess
import json
from enum import Enum
from pathlib import Path
from typing import Any

from k_pycoq.kernel import AbstractKernel
from k_pycoq.opam import create_opam_subprocess
"""
import k_pycoq.kernel.lsp_protocol as lsp_protocol


class MethodType(Enum):
    Request = 1
    Notification = 2


_methods = {
    'initialize': {
        'kind': MethodType.Request,
        'params': lsp_protocol.InitializeParams,
        'result': lsp_protocol.InitializeResult,
    },
    'initialized': {
        'kind': MethodType.Notification,
        'params': None,
    },
    # 'client/registerCapability': lsp_protocol.RegistrationParams,  # not planned atm
    '$/setTrace': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.SetTraceParams,
    },
    '$/logTrace': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.LogTraceParams,
    },
    'textDocument/didOpen': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.DidOpenTextDocumentParams,
    },
    'textDocument/didChange': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.DidChangeTextDocumentParams,
    },
    'textDocument/didSave': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.DidSaveTextDocumentParams,
    },
    'textDocument/didClose': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.DidCloseTextDocumentParams,
    },
    # 'notebookDocument/didOpen': ...,  # planned
    # 'textDocument/declaration': ...,  # planned, blocked on upstream issues
    'textDocument/definition': {  # partial
        'kind': MethodType.Request,
        'params': lsp_protocol.DefinitionParams,
        'result': lsp_protocol.LocationResult,
    },
    # 'textDocument/references': ...,  # planned, blocked on upstream issues
    'textDocument/hover': {
        'kind': MethodType.Request,
        'params': lsp_protocol.HoverParams,
        'result': lsp_protocol.HoverResult,
    },
    # 'textDocument/codeLens': ...,
    # 'textDocument/foldingRange': ...,
    'textDocument/documentSymbol': {
        'kind': MethodType.Request,
        'params': lsp_protocol.DocumentSymbolParams,
        'result': lsp_protocol.SymbolResult,
    },
    # 'textDocument/semanticTokens': ...,  # planned
    # 'textDocument/inlineValues': ...,  # planned
    # 'textDocument/inlayHints': ...,  # planned
    'textDocument/completion': {  # partial
        'kind': MethodType.Request,
        'params': lsp_protocol.CompletionParams,
        'result': lsp_protocol.CompletionResult,
    },
    'textDocument/publishDiagnostics': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.PublishDiagnosticsParams,
    },
    # 'textDocument/diagnostics': ..., # planned
    # 'textDocument/codeAction': ..., # planned
    'workspace/workspaceFolders': {  # folders should contain _CoqProject in root
        'kind': MethodType.Notification,
        'params': None,
    },
    'workspace/didChangeWorkspaceFolders': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.DidChangeWorkspaceFoldersParams,
    },
    # coq specific
    'proof/goals': {
        'kind': MethodType.Request,
        'params': lsp_protocol.GoalsParams,
        'result': lsp_protocol.GoalResult,
    },
    '$/coq/fileProgress': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.CoqFileProgressParams,
    },
    'coq/getDocument': {
        'kind': MethodType.Request,
        'params': lsp_protocol.FlecheDocumentParams,
        'result': lsp_protocol.FlecheDocumentResult,
    },
    'coq/saveVo': {
        'kind': MethodType.Request,
        'params': lsp_protocol.FlecheSaveParams,
        'result': None,
    },
    '$/coq/filePerfData': {
        'kind': MethodType.Notification,
        'params': lsp_protocol.DocumentPerfParams,
    },
}
# """

JSONRPC_REQ_FORMAT = 'Content-Length: {content_length}\r\n\r\n{content}'


class LSPEndPoint:
    def __init__(self, lsp: subprocess.Popen):
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

    def read_response(self):
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
        return content

    def send_request(self, method: str, params: dict[str: Any]):
        """sends request to lsp"""
        self.id += 1
        content = json.dumps({'jsonrpc': '2.0', 'method': method, 'params': params, 'id': self.id}, indent=1)
        print(f'REQUEST: {content}')
        self.lsp.stdin.write(self._add_header(content))
        self.lsp.stdin.flush()


class LSPKernel(AbstractKernel):

    def __init__(self, opam_switch: str, opam_root, top_file: str, flags: list[str]):
        super().__init__()
        self.opam_switch: str = opam_switch
        self.opam_root = opam_root
        self.flags: list[str] = flags
        self.top_file: str = top_file
        self._lsp = create_opam_subprocess('coq-lsp --bt', self.opam_switch, self.opam_root,
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
        'initializationOptions': {
            # 'trace': 'messages',
            'debug': True,
            # 'verbosity': 2,  # TODO: throws parsing error? think it must be an error with coqlsp
            'show_notices_as_diagnostics': True,
            'show_coq_info_messages': True,
        },
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

    lsp_endpoint.read_response()
    lsp_endpoint.read_response()

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
            # 'text': 'Require Import Arith.\n\nDefinition a := 2.\nGoal 1 + 1 = 2.\nProof.\nShow Proof.\nreflexivity.\nQed.'
            'text': """
Theorem add_easy_induct_1:
forall n:nat,
  n + 0 = n.
Proof.
Show Proof. 
  intros.
Show Proof.
  induction n as [| n' IH].
Show Proof.
  - simpl.
Show Proof.
    reflexivity.
Show Proof.
  - simpl.
Show Proof.
    rewrite -> IH.
Show Proof.
    reflexivity.
Show Proof.
Qed."""
        }
    })

    # textDocument/publishDiagnostics
    lsp_endpoint.send_notification('coq/getDocument', {
        'textDocument': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                        '/SimpleArith.v'
    })

    # interface GoalRequest {
    #     textDocument: VersionedTextDocumentIdentifier;
    #     position: Position;
    #     pp_format?: 'Pp' | 'Str';
    # }

    # lsp_endpoint.send_request('textDocument/definition', {
    #     'textDocument': {
    #         'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #                '/SimpleArith.v',
    #         'languageId': 'coq',
    #         'version': 1
    #     },
    #     'position': {
    #         'line': 2,
    #         'character': 11
    #     }
    # })
    # lsp_endpoint.send_request('proof/goals', {
    #     'textDocument': {
    #         'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #                '/SimpleArith.v',
    #         'languageId': 'coq',
    #         'version': 1
    #     },
    #     'position': {
    #         'line': 6,
    #         'character': 0
    #     }
    # })
    # #
    lsp_endpoint.send_request('coq/getDocument', {
        'textDocument': {
            'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                   '/SimpleArith.v',
            'languageId': 'coq',
            'version': 1
        }
    })

    # lsp_endpoint.send_request('coq/saveVo', {
    #     'textDocument': {
    #         'uri': 'file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #                  '/SimpleArith.v',
    #         'version': 1
    #     }
    # })

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
