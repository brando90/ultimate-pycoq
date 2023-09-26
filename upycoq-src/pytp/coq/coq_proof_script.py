import bisect
import enum
import threading
from pathlib import Path
from typing import Optional

import attrs
from lsprotocol.types import TextDocumentPublishDiagnosticsNotification, Range, DiagnosticSeverity, \
    VersionedTextDocumentIdentifier, DidChangeTextDocumentParams, TextDocumentContentChangeEvent, Position

from pytp.coq.coq_lsp_client import CoqLSPClient
from pytp.coq.coq_types import FlecheDocumentParams, FlecheDocument, RangedSpan, CoqFileProgressNotification, \
    CoqFileProgressProcessingInfo
from pytp.proof_script import ProofScript, Statement

from pytp.coq.coq_lsp_client import CoqLSPClient, get_default_coq_lsp_config, get_extract_coq_lsp_config


def get_statements_from_fleche_document(document: str, spans: list[RangedSpan],
                                        offset: Optional[int] = None) -> list[Statement]:
    """
    Returns a list of statements from a fleche document. If offset is given, only returns statements after the offset.
    :param document: The document as a string.
    :param spans: The spans of the statements.
    :param offset: The offset to start from or None if all statements should be returned.
    :return: A list of statements.
    """
    if offset is None:
        idx = 0
    else:
        idx = offset

    statements = []
    while idx < len(spans):
        span = spans[idx]
        start = span.range.start
        end = span.range.end
        statement = Statement(statement=document[start.offset:end.offset], range=span.range,
                              info={'statement_type': span.span['v']['expr'][0]})  # the statement type
        statements.append(statement)

    return statements


def find_span_at_offset(spans: list[RangedSpan], offset: int) -> int:
    """
    Finds the span at the given character offset.
    :param spans: The spans to search through. Assumed to be in sorted order and non-overlapping.
    :param offset: The offset to find the span at.
    :return: The index of the span at the given offset.
    """
    if offset <= spans[0].range.start.offset:
        return 0
    elif offset >= spans[-1].range.end.offset:
        return len(spans) - 1
    # find first span in spans that contains offset using binary search
    idx = len(spans) // 2
    while True:
        if spans[idx].range.start.offset > offset:
            idx = idx // 2
        elif spans[idx].range.end.offset < offset:
            idx = idx + (len(spans) - idx) // 2
        else:
            break
    return idx


class CoqProofScript(ProofScript):

    def __init__(self, path: Optional[Path], lsp_client: CoqLSPClient, workspace: Optional[Path] = None):
        super().__init__(path, lsp_client, workspace)

        # self.check_lsp_config()

        self.augmented_document = self.document

        self.proof_terms: dict[Range, str] = {}

        # self.received_diagnostics_event = threading.Event()
        # self.lsp_client.register_notification_callback('textDocument/publishDiagnostics', self.parse_diagnostics)

        # self.check_progress_event = threading.Event()
        # self.lsp_client.register_notification_callback('$/coq/fileProgress', self.amount_changed)
        # self.amount_changed: CoqFileProgressProcessingInfo


    def check_lsp_config(self):
        """ensure proper lsp configuration is set"""
        config = self.lsp_client.config.lsp_settings['initializationOptions']
        assert not config.eager_diagnostics
        assert config.show_coq_info_messages

    def parse_diagnostics(self, notification: TextDocumentPublishDiagnosticsNotification):
        diagnostics = notification.params.diagnostics
        for diagnostic in diagnostics:
            if diagnostic.severity != DiagnosticSeverity.Information:
                continue
            # make sure this is a proof term TODO: is the best way to do this?
            if diagnostic.message.startswith('(fun') or diagnostic.message.startswith('?Goal'):
                self.proof_terms[diagnostic.range] = diagnostic.message
        self.received_diagnostics_event.set()

    def amount_changed(self, notification: CoqFileProgressNotification):
        if self.check_progress_event.is_set():
            return
        if len(notification.params.processing) != 1:
            raise ValueError(f'Expected exactly one processing info, got {len(notification.params.processing)}. '
                             'coq-lsp might have changed document processing since version 0.1.6.')
        self.amount_changed = notification.params.processing[0]
        self.check_progress_event.set()

    def statements_from_document(self, document: str) -> list[Statement]:
        """
        Returns a list of statements from a document.
        """
        fleche_document: FlecheDocument = self.lsp_client.wait_for_response(self.lsp_client.coq_get_document(FlecheDocumentParams(
            textDocument=VersionedTextDocumentIdentifier(
                uri=self.path.as_uri(),
                version=self.version
            )
        ), return_result=True))
        print(fleche_document)
        spans: list[RangedSpan] = fleche_document.spans
        statements = get_statements_from_fleche_document(document, spans)
        return statements

    def get_augmented_document(self):
        # find sections of document that have changed
        # self.check_progress_event.clear()
        # self.lsp_client.text_document_did_change(DidChangeTextDocumentParams(
        #     text_document=VersionedTextDocumentIdentifier(
        #         uri=self.path.as_uri(),
        #         version=self.version
        #     ),
        #     content_changes=[TextDocumentContentChangeEvent(
        #         text=self.augmented_document
        #     )]
        # ))
        # self.check_progress_event.wait()
        # parse the document and get the statement ranges
        print('hello')
        document: FlecheDocument = self.lsp_client.wait_for_response(self.lsp_client.coq_get_document(FlecheDocumentParams(
            textDocument=VersionedTextDocumentIdentifier(
                uri=self.path.as_uri(),
                version=self.version
            )
        ), return_result=False))
        spans: list[RangedSpan] = document.spans

        print(document)

        # find the index of the first statement that has changed
        idx = find_span_at_offset(spans, self.amount_changed.range.start.offset)
        self.statements = self.statements[:idx]
        new_statements = get_statements_from_fleche_document(self.document, spans, offset=idx)

        # update the in_proof info for the new statements
        in_proof = self.statements[idx].info['in_proof']
        for statement in new_statements:
            if statement.info['statement_type'] == 'VernacStartTheoremProof':
                in_proof = True
            elif statement.info['statement_type'] == 'VernacEndProof':
                in_proof = False

            statement.info['in_proof'] = in_proof

        # update the augmented document to include the new statements and augmentations
        updated_statements = []
        for statement in new_statements:
            updated_statements.append(statement.statement)
            if statement.info['in_proof']:
                updated_statements.append('Show Proof.')
                updated_statements.append('Show Goals.')

        self.augmented_document = self.augmented_document[:self.amount_changed.range.start.offset]
        self.augmented_document += '\n'.join(updated_statements)

        print(self.augmented_document)

    def update_document(self):
        """
        Updates the lsp server's open document to the given document and updates the internal representation of the
        proof script including the statements.
        """
        self.received_diagnostics_event.clear()
        self.document_changed()
        self.received_diagnostics_event.wait()
        self.update_statements()

    def update_statements(self):
        """
        Updates the proof script's statements.
        """
        document: FlecheDocument = self.lsp_client.coq_get_document(FlecheDocumentParams(
            textDocument=VersionedTextDocumentIdentifier(
                uri=self.path.as_uri(),
                version=self.version
            )
        ), return_result=True)


if __name__ == "__main__":
    config = get_extract_coq_lsp_config()
    config.lsp_settings['switch'] = 'coq-8.17'
    config.lsp_settings['flags'] = ['--bt']
    client = CoqLSPClient('coq-lsp', '0.1.0', config=config)
    project_path = Path('/home/jizej/proverbot9001/coq-projects/InfSeqExt/')
    workspace_path = project_path.expanduser()

    import lsprotocol.types as lsp_types

    # change workspace folder
    client.workspace_did_change_workspace_folders(params=lsp_types.DidChangeWorkspaceFoldersParams(
        event=lsp_types.WorkspaceFoldersChangeEvent(
            added=[lsp_types.WorkspaceFolder(
                uri=workspace_path.as_uri(),
                name=f'{workspace_path.name}')],
            removed=[]
        )
    ))

    proof_path = Path('/home/jizej/proverbot9001/coq-projects/InfSeqExt/subseq.v').expanduser()
    print(proof_path)

    proof_script = CoqProofScript(proof_path, client, workspace_path)    
    proof_script.get_augmented_document()
