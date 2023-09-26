"""
Defines the proof script class. Allows for the management and editing of proof scripts.
"""
from pathlib import Path
from typing import Optional, Any

from attr import dataclass
from lsprotocol.types import Range, DidChangeWorkspaceFoldersParams, WorkspaceFoldersChangeEvent, WorkspaceFolder, \
    DidOpenTextDocumentParams, TextDocumentItem, DidChangeTextDocumentParams, VersionedTextDocumentIdentifier, \
    TextDocumentContentChangeEvent, TextDocumentContentChangeEvent_Type2

from pytp.coq.coq_types import Goal, Span
from pytp.lsp_client import LSPClient


@dataclass
class Statement:
    statement: str
    range: Span
    info: Optional[Any] = None
    proof_status: Optional[str] = None
    partial_proof_term: Optional[str] = None
    goals: Optional[list[Goal]] = None


def document_from_path(path: Optional[Path]) -> str:
    """
    Returns the document from a given path. If the path is empty or None, returns an empty string.
    :param path: The path to the document or an empty string/None.
    :return: The document as a string.
    """
    if path is None:
        return ''
    else:
        return open(path, 'r').read()


class ProofScript:
    def __init__(self, path: Optional[Path], lsp_client: LSPClient, workspace: Optional[Path] = None):
        self.path = path
        self.workspace = workspace if workspace is not None else self.path.parent

        self.version = 1

        self.lsp_client = lsp_client

        # self.lsp_client.register_notification_callback('$/coq/fileProgress', lambda notification: print(notification))

        self.document = document_from_path(self.path)
        # self.statements: list[Statement] = self.statements_from_document(self.document)
        self.statements = []
        # TODO: make dummy document for empty path
        self.set_document()

    def set_workspace(self):
        """
        Adds the workspace to the lsp server.
        """
        # TODO: workout the current workspaces to remove? In coq-lsp they do not implement this request
        self.lsp_client.workspace_did_change_workspace_folders(
            DidChangeWorkspaceFoldersParams(
                event=WorkspaceFoldersChangeEvent(
                    added=[WorkspaceFolder(
                        uri=self.workspace.as_uri(),
                        name='workspace')],
                    removed=[]
                )
            )
        )

    def set_document(self):
        """
        Sets the lsp server's open document to the given document.
        """
        self.set_workspace()

        self.lsp_client.text_document_did_open(
            DidOpenTextDocumentParams(
                text_document=TextDocumentItem(
                    uri=self.path.as_uri(),
                    language_id='coq',
                    version=self.version,
                    text=self.document
                )
            )
        )

    def document_changed(self):
        """
        Notifies the LSP client of a document change.
        """
        self.version += 1
        self.lsp_client.text_document_did_change(
            DidChangeTextDocumentParams(
                text_document=VersionedTextDocumentIdentifier(
                    uri=self.path.as_uri(),
                    version=self.version
                ),
                content_changes=[
                    TextDocumentContentChangeEvent_Type2(
                        text=self.document,
                    )
                ]
            )
        )

    def update_document(self):
        """
        Updates the lsp server's open document to the given document and updates the internal representation of the
        proof script including the statements.
        """
        raise NotImplementedError

    def statements_from_document(self, document: str) -> list[Statement]:
        raise NotImplementedError

def example_proof_script():
    lsp_client = None  # todo
    proof_script = ProofScript('', lsp_client)
    # Edit the proof script
    proof_script.document += "reflexivity.\nQed."
    proof_script.update_document()

    for statement in proof_script.statements:
        # where in proof_script.script is the statement located
        statement_range = statement.range

        # Retrieve proof status
        proof_status = statement.proof_status

        # Handle proof-related metadata
        partial_proof_term = statement.partial_proof_term
        goals = statement.goals


if __name__ == '__main__':
    example_proof_script()
