import os
import subprocess
from pathlib import Path
from typing import Union

from lsprotocol.types import InitializeParams, ClientCapabilities, WorkspaceFolder, VersionedTextDocumentIdentifier, \
    DidOpenTextDocumentParams, DidChangeTextDocumentParams
from packaging.version import parse as parse_version

from pytp.coq.coq_types import ResponseErrorMessage, GoalRequest, GoalAnswer, FlecheDocumentParams, \
    FlecheDocument, FlecheSaveParams, COQ_MESSAGE_TYPES, COQ_RESPONSE_TYPES, CoqInitializationOptions, \
    CoqFileProgressParams, CoqFileProgressNotification
from pytp.coq.opam import create_opam_subprocess, opam_run
from pytp.lsp_client import LSPClient, Id
from pytp.lsp_config import LSPConfig
from pytp.coq.converter import get_coq_lsp_converter


def get_default_coq_lsp_config() -> LSPConfig:
    """
    Get the default LSPConfig for Coq.
    :return: The default LSPConfig for Coq.
    """
    converter = get_coq_lsp_converter()

    # Use METHOD_TO_TYPES from pytp.coq.coq_types instead of lsprotocol.types.METHOD_TO_TYPES
    # because the former has been modified to include the coq-specific methods.
    return LSPConfig(
        message_types=COQ_MESSAGE_TYPES,
        response_types=COQ_RESPONSE_TYPES,
        error_type=ResponseErrorMessage,
        converter=converter,
        lsp_settings={
            'switch': 'default',
            'cwd': Path.cwd(),
            'initializationOptions': CoqInitializationOptions(debug=True),
            'flags': ['--bt'],
            # options for coq-lsp include (Note, not all of these might be implemented yet):
            # obtained from https://github.com/ejgallego/coq-lsp/blob/main/controller/coq_lsp.ml on 26 June 2023
            # --bt: Enable backtraces
            # --coqcorelib=COQCORELIB:
            #       Path to Coq plugin directories.
            # --coqlib=COQLIB:
            #       Load Coq.Init.Prelude from COQLIB; theories and user-contrib should live there.
            # --ocamlpath:
            #       Path to Coq plugin directories.
            # -I, -R, -Q
            # -D, --idle-delay:
            #       Delay value in seconds when server is idle.
        }
    )
    

def get_extraction_coq_lsp_config() -> LSPConfig:
    """
    Get the default LSPConfig for Coq.
    :return: The default LSPConfig for Coq.
    """
    converter = get_coq_lsp_converter()

    # Use METHOD_TO_TYPES from pytp.coq.coq_types instead of lsprotocol.types.METHOD_TO_TYPES
    # because the former has been modified to include the coq-specific methods.
    return LSPConfig(
        message_types=COQ_MESSAGE_TYPES,
        response_types=COQ_RESPONSE_TYPES,
        error_type=ResponseErrorMessage,
        converter=converter,
        lsp_settings={
            'switch': 'default',
            'cwd': Path.cwd(),
            'initializationOptions': CoqInitializationOptions(eager_diagnostics=False, show_coq_info_messages=True),
            'flags': ['--bt'],
            # options for coq-lsp include (Note, not all of these might be implemented yet):
            # obtained from https://github.com/ejgallego/coq-lsp/blob/main/controller/coq_lsp.ml on 26 June 2023
            # --bt: Enable backtraces
            # --coqcorelib=COQCORELIB:
            #       Path to Coq plugin directories.
            # --coqlib=COQLIB:
            #       Load Coq.Init.Prelude from COQLIB; theories and user-contrib should live there.
            # --ocamlpath:
            #       Path to Coq plugin directories.
            # -I, -R, -Q
            # -D, --idle-delay:
            #       Delay value in seconds when server is idle.
        }
    )


class CoqLSPClient(LSPClient):
    def __init__(self, name: str, version: str, config: LSPConfig = get_default_coq_lsp_config()):
        self.config = config

        self.coq_lsp_version = self.coq_lsp_version()
        if parse_version(self.coq_lsp_version) < parse_version('0.1.6'):
            raise Exception('Coq LSP version must be at least 0.1.6. '
                            f'Current version is {self.coq_lsp_version}.')
        # TODO: remove this warning once Coq LSP 0.1.7 is released
        if parse_version(self.coq_lsp_version) > parse_version('0.1.6'):
            print(f'WARNING: Coq LSP version is {self.coq_lsp_version}. '
                  'This version of CoqLSPClient has only been tested with version 0.1.6. '
                  'Use at your own risk.')

        coq_lsp_cmd = ' '.join(['coq-lsp'] + config.lsp_settings['flags'])
        self._process = create_opam_subprocess(coq_lsp_cmd, config.lsp_settings['switch'],
                                               cwd=config.lsp_settings['cwd'],
                                               stdin=subprocess.PIPE,
                                               stdout=subprocess.PIPE,
                                               stderr=subprocess.STDOUT)
        super().__init__(name, version, self._process.stdin, self._process.stdout, config)

        self.document = ''

        self.endpoint.register_notification_callback('$/logTrace', lambda notification: print(notification.params.message))
        self.endpoint.register_notification_callback('window/logMessage', lambda notification: print(notification.params.message))

        def on_file_progress(notification: CoqFileProgressNotification):
            start = notification.params.processing[0].range.start
            end = notification.params.processing[0].range.end
            print(f'Processed {start.line}:{end.line}:')  # {self.document[start.offset:end.offset]}')

        self.endpoint.register_notification_callback('$/coq/fileProgress', on_file_progress)
        self.endpoint.register_notification_callback('textDocument/publishDiagnostics', lambda notification: print(notification.params))

        init_params = InitializeParams(
            capabilities=ClientCapabilities(),
            process_id=os.getpid(),
            root_path=str(Path.cwd()),  # TODO: once version 0.1.7 is released, we don't have to initialize any uris
            root_uri=str(Path.cwd().as_uri()),
            workspace_folders=[WorkspaceFolder(uri=str(Path.cwd().as_uri()), name='name')],
            initialization_options=self.config.lsp_settings['initializationOptions']
        )

        self.initialize(init_params, return_result=True)

    def text_document_did_open(self, params: DidOpenTextDocumentParams) -> None:
        """
        Notify the server that a text document has been opened.
        """
        self.document = params.text_document.text
        super().text_document_did_open(params)

    def text_document_did_change(self, params: DidChangeTextDocumentParams) -> None:
        """
        Notify the server that a text document has been changed.
        """
        self.document = params.content_changes[0].text
        super().text_document_did_change(params)

    def coq_lsp_version(self) -> str:
        """
        Get the version of the coq-lsp server.
        """
        return opam_run('coq-lsp --version',
                        switch=self.config.lsp_settings['switch'],
                        cwd=self.config.lsp_settings['cwd']).stdout.decode('utf-8').strip()

    def close(self):
        """
        Close the client.
        """
        self._process.terminate()
        self._process.wait()
        if self._process.stdout:
            self._process.stdout.close()
        if self._process.stderr:
            self._process.stderr.close()
        try:  # Flushing a BufferedWriter may raise an error
            if self._process.stdin:
                self._process.stdin.close()
        finally:
            super().close()

    def __del__(self):
        self.close()

    def proof_goals(self, params: GoalRequest, return_result=False) -> Union[GoalAnswer, Id]:
        """The `proof/goals` request is sent from the client to the server to get the goals at a given position.

        @since 0.1.0

        :param params: The parameters to send with the request. An instance of `GoalRequest`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('proof/goals', params=params, return_result=return_result)

    def coq_get_document(self, params: FlecheDocumentParams, return_result=False) -> Union[FlecheDocument, Id]:
        """The `proof/goals` request is sent from the client to the server to get the goals at a given position.

        @since 0.1.0

        :param params: The parameters to send with the request. An instance of `GoalRequest`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('coq/getDocument', params=params, return_result=return_result)

    def coq_save_vo(self, params: FlecheSaveParams, return_result=False) -> Union[None, Id]:
        """The `coq/saveVo` request is sent from the client to the server to save a file to disk.

        @since 0.1.6

        :param params: The parameters to send with the request. An instance of `FlecheSaveParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('coq/saveVo', params=params, return_result=return_result)


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
    client.text_document_did_open(params=lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri=(new_workspace_path / 'DebugSimpleArith.v').as_uri(),
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
        uri=(new_workspace_path / 'DebugSimpleArith.v').as_uri(),
        version=1
    ), position=lsp_types.Position(line=4, character=4)))

    print(f'Goals: {client.wait_for_response(id)}')

    # close client
    client.close()
    print('Tests passed!')



def example_coq_lsp():
    # test coq-lsp
    config = get_default_coq_lsp_config()
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
    #
    # print(client.wait_for_response(id))
    # print('Initialized')

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
            text="""
                Theorem add_easy_induct_1:
                forall n:nat,
                  n + 0 = n.
                Proof.
                  intros.
                  Show Proof.
                  induction n as [| n' IH].
                  - simpl.
                    reflexivity.
                  - simpl.
                    rewrite -> IH.
                    reflexivity.
                Qed."""
            # 'Require Import Arith.\n'
            #      'Theorem plus_0_n : forall n : nat, 0 + n = n.\n'
            #      'Proof.\n'
            #      '  intros n.\n'
            #      '  simpl.\n'
            #      '  reflexivity.\n'
            #      '  Show Proof.\n'
            #      'Qed.'
        )
    ))

    # get goals
    # id = client.proof_goals(params=GoalRequest(text_document=lsp_types.VersionedTextDocumentIdentifier(
    #     uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
    #         '/DebugSimpleArith.v',
    #     version=1
    # ), position=lsp_types.Position(line=4, character=4)))
    #
    # print(f'\nGoals: {client.wait_for_response(id)}')
    #
    import time
    time.sleep(1)
    print('==================')
    client.text_document_did_change(params=lsp_types.DidChangeTextDocumentParams(
        text_document=lsp_types.VersionedTextDocumentIdentifier(
            uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                '/DebugSimpleArith.v',
            version=2
        ),
        content_changes=[lsp_types.TextDocumentContentChangeEvent_Type2(
            text="""
                Theorem add_easy_induct_1:
                forall n:nat,
                  n + 0 = n.
                Proof.
                  intros.
                  Show Proof.
                  induction n as [| n' IH].
                  - simpl.
                    reflexivity.
                  - simpl.
                    rewrite -> IH.
                    reflexivity.
                    Show Proof.
                Qed.""")]
        )
    )

    # import time
    # time.sleep(1)

    document = client.coq_get_document(FlecheDocumentParams(
            textDocument=VersionedTextDocumentIdentifier(
                uri='file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith'
                    '/DebugSimpleArith.v',
                version=1
            )
        ), return_result=True)
    print(document)
    # close client
    client.close()
    print('Tests passed!')


if __name__ == '__main__':
    winston_coq_lsp()
