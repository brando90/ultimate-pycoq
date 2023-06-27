"""
****** THIS IS A GENERATED FILE, DO NOT EDIT. ******
To regenerate file, run scripts/generate_client.py -o ../pytp/lsp_client.py
"""

from lsprotocol.types import (
    CallHierarchyIncomingCall,
    CallHierarchyIncomingCallsParams,
    CallHierarchyItem,
    CallHierarchyOutgoingCall,
    CallHierarchyOutgoingCallsParams,
    CallHierarchyPrepareParams,
    CancelParams,
    CodeAction,
    CodeActionParams,
    CodeLens,
    CodeLensParams,
    ColorInformation,
    ColorPresentation,
    ColorPresentationParams,
    Command,
    CompletionItem,
    CompletionList,
    CompletionParams,
    CreateFilesParams,
    DeclarationParams,
    DefinitionParams,
    DeleteFilesParams,
    DidChangeConfigurationParams,
    DidChangeNotebookDocumentParams,
    DidChangeTextDocumentParams,
    DidChangeWatchedFilesParams,
    DidChangeWorkspaceFoldersParams,
    DidCloseNotebookDocumentParams,
    DidCloseTextDocumentParams,
    DidOpenNotebookDocumentParams,
    DidOpenTextDocumentParams,
    DidSaveNotebookDocumentParams,
    DidSaveTextDocumentParams,
    DocumentColorParams,
    DocumentDiagnosticParams,
    DocumentFormattingParams,
    DocumentHighlight,
    DocumentHighlightParams,
    DocumentLink,
    DocumentLinkParams,
    DocumentOnTypeFormattingParams,
    DocumentRangeFormattingParams,
    DocumentSymbol,
    DocumentSymbolParams,
    ExecuteCommandParams,
    FoldingRange,
    FoldingRangeParams,
    Hover,
    HoverParams,
    ImplementationParams,
    InitializeParams,
    InitializeResult,
    InitializedParams,
    InlayHint,
    InlayHintParams,
    InlineValueEvaluatableExpression,
    InlineValueParams,
    InlineValueText,
    InlineValueVariableLookup,
    LinkedEditingRangeParams,
    LinkedEditingRanges,
    Location,
    LocationLink,
    Moniker,
    MonikerParams,
    PrepareRenameParams,
    PrepareRenameResult_Type1,
    PrepareRenameResult_Type2,
    ProgressParams,
    Range,
    ReferenceParams,
    RelatedFullDocumentDiagnosticReport,
    RelatedUnchangedDocumentDiagnosticReport,
    RenameFilesParams,
    RenameParams,
    SelectionRange,
    SelectionRangeParams,
    SemanticTokens,
    SemanticTokensDelta,
    SemanticTokensDeltaParams,
    SemanticTokensParams,
    SemanticTokensRangeParams,
    SetTraceParams,
    SignatureHelp,
    SignatureHelpParams,
    SymbolInformation,
    TextEdit,
    TypeDefinitionParams,
    TypeHierarchyItem,
    TypeHierarchyPrepareParams,
    TypeHierarchySubtypesParams,
    TypeHierarchySupertypesParams,
    WillSaveTextDocumentParams,
    WorkDoneProgressCancelParams,
    WorkspaceDiagnosticParams,
    WorkspaceDiagnosticReport,
    WorkspaceEdit,
    WorkspaceSymbol,
    WorkspaceSymbolParams
)
from typing import (
    Any,
    List,
    Optional,
    Union
)

from pytp.base_client import BaseClient
from pytp.lsp_config import LSPConfig, default_lsp_config

Id = int


class LSPClient(BaseClient):
    def __init__(
        self,
        name: str,
        version: str,
        stdin,
        stdout,
        config: LSPConfig = default_lsp_config,
    ):
        self.name = name
        self.version = version
        super().__init__(stdin, stdout, config)

    def cancel_request(self, params: CancelParams) -> None:
        """
        Make a `$/cancelRequest` notification.
    
        :param params: The parameters to send with the notification. An instance of `CancelParams`.
        :return: None
        """
        self.send_notification('$/cancelRequest', params)

    def progress(self, params: ProgressParams) -> None:
        """
        Make a `$/progress` notification.
    
        :param params: The parameters to send with the notification. An instance of `ProgressParams`.
        :return: None
        """
        self.send_notification('$/progress', params)

    def set_trace(self, params: SetTraceParams) -> None:
        """
        Make a `$/setTrace` notification.
    
        :param params: The parameters to send with the notification. An instance of `SetTraceParams`.
        :return: None
        """
        self.send_notification('$/setTrace', params)

    def call_hierarchy_incoming_calls(self, params: CallHierarchyIncomingCallsParams, return_result=False) -> Union[Optional[List[CallHierarchyIncomingCall]], Id]:
        """
        Make a `callHierarchy/incomingCalls` request.
    
        A request to resolve the incoming calls for a given `CallHierarchyItem`.

        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `CallHierarchyIncomingCallsParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('callHierarchy/incomingCalls', params, return_result=return_result)

    def call_hierarchy_outgoing_calls(self, params: CallHierarchyOutgoingCallsParams, return_result=False) -> Union[Optional[List[CallHierarchyOutgoingCall]], Id]:
        """
        Make a `callHierarchy/outgoingCalls` request.
    
        A request to resolve the outgoing calls for a given `CallHierarchyItem`.

        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `CallHierarchyOutgoingCallsParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('callHierarchy/outgoingCalls', params, return_result=return_result)

    def code_action_resolve(self, params: CodeAction, return_result=False) -> Union[CodeAction, Id]:
        """
        Make a `codeAction/resolve` request.
    
        Request to resolve additional information for a given code action.The request's
        parameter is of type {@link CodeAction} the response is of type {@link CodeAction}
        or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `CodeAction`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('codeAction/resolve', params, return_result=return_result)

    def code_lens_resolve(self, params: CodeLens, return_result=False) -> Union[CodeLens, Id]:
        """
        Make a `codeLens/resolve` request.
    
        A request to resolve a command for a given code lens.
    
        :param params: The parameters to send with the request. An instance of `CodeLens`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('codeLens/resolve', params, return_result=return_result)

    def completion_item_resolve(self, params: CompletionItem, return_result=False) -> Union[CompletionItem, Id]:
        """
        Make a `completionItem/resolve` request.
    
        Request to resolve additional information for a given completion item.The
        request's parameter is of type {@link CompletionItem} the response is of type {@link
        CompletionItem} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `CompletionItem`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('completionItem/resolve', params, return_result=return_result)

    def document_link_resolve(self, params: DocumentLink, return_result=False) -> Union[DocumentLink, Id]:
        """
        Make a `documentLink/resolve` request.
    
        Request to resolve additional information for a given document link.

        The request's parameter is of type {@link DocumentLink} the response is of type
        {@link DocumentLink} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `DocumentLink`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('documentLink/resolve', params, return_result=return_result)

    def exit(self, params: None) -> None:
        """
        Make a `exit` notification.
    
        The exit event is sent from the client to the server to ask the server to exit
        its process.
    
        :param params: The parameters to send with the notification. An instance of `None`.
        :return: None
        """
        self.send_notification('exit', params)

    def initialize(self, params: InitializeParams, return_result=False) -> Union[InitializeResult, Id]:
        """
        Make a `initialize` request.
    
        The initialize request is sent from the client to the server.

        It is sent once as the request after starting up the server. The requests parameter
        is of type {@link InitializeParams} the response if of type {@link InitializeResult}
        of a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `InitializeParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('initialize', params, return_result=return_result)

    def initialized(self, params: InitializedParams) -> None:
        """
        Make a `initialized` notification.
    
        The initialized notification is sent from the client to the server after the
        client is fully initialized and the server is allowed to send requests from the
        server to the client.
    
        :param params: The parameters to send with the notification. An instance of `InitializedParams`.
        :return: None
        """
        self.send_notification('initialized', params)

    def inlay_hint_resolve(self, params: InlayHint, return_result=False) -> Union[InlayHint, Id]:
        """
        Make a `inlayHint/resolve` request.
    
        A request to resolve additional properties for an inlay hint. The request's
        parameter is of type {@link InlayHint}, the response is of type {@link InlayHint} or
        a Thenable that resolves to such.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `InlayHint`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('inlayHint/resolve', params, return_result=return_result)

    def notebook_document_did_change(self, params: DidChangeNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didChange` notification.
    
        :param params: The parameters to send with the notification. An instance of `DidChangeNotebookDocumentParams`.
        :return: None
        """
        self.send_notification('notebookDocument/didChange', params)

    def notebook_document_did_close(self, params: DidCloseNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didClose` notification.
    
        A notification sent when a notebook closes.

        @since 3.17.0
    
        :param params: The parameters to send with the notification. An instance of `DidCloseNotebookDocumentParams`.
        :return: None
        """
        self.send_notification('notebookDocument/didClose', params)

    def notebook_document_did_open(self, params: DidOpenNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didOpen` notification.
    
        A notification sent when a notebook opens.

        @since 3.17.0
    
        :param params: The parameters to send with the notification. An instance of `DidOpenNotebookDocumentParams`.
        :return: None
        """
        self.send_notification('notebookDocument/didOpen', params)

    def notebook_document_did_save(self, params: DidSaveNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didSave` notification.
    
        A notification sent when a notebook document is saved.

        @since 3.17.0
    
        :param params: The parameters to send with the notification. An instance of `DidSaveNotebookDocumentParams`.
        :return: None
        """
        self.send_notification('notebookDocument/didSave', params)

    def shutdown(self, params: None, return_result=False) -> Union[None, Id]:
        """
        Make a `shutdown` request.
    
        A shutdown request is sent from the client to the server.

        It is sent once when the client decides to shutdown the server. The only
        notification that is sent after a shutdown request is the exit event.
    
        :param params: The parameters to send with the request. An instance of `None`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('shutdown', params, return_result=return_result)

    def text_document_code_action(self, params: CodeActionParams, return_result=False) -> Union[Optional[List[Union[Command, CodeAction]]], Id]:
        """
        Make a `textDocument/codeAction` request.
    
        A request to provide commands for the given text document and range.
    
        :param params: The parameters to send with the request. An instance of `CodeActionParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/codeAction', params, return_result=return_result)

    def text_document_code_lens(self, params: CodeLensParams, return_result=False) -> Union[Optional[List[CodeLens]], Id]:
        """
        Make a `textDocument/codeLens` request.
    
        A request to provide code lens for the given text document.
    
        :param params: The parameters to send with the request. An instance of `CodeLensParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/codeLens', params, return_result=return_result)

    def text_document_color_presentation(self, params: ColorPresentationParams, return_result=False) -> Union[List[ColorPresentation], Id]:
        """
        Make a `textDocument/colorPresentation` request.
    
        A request to list all presentation for a color.

        The request's parameter is of type {@link ColorPresentationParams} the response is
        of type {@link ColorInformation ColorInformation[]} or a Thenable that resolves to
        such.
    
        :param params: The parameters to send with the request. An instance of `ColorPresentationParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/colorPresentation', params, return_result=return_result)

    def text_document_completion(self, params: CompletionParams, return_result=False) -> Union[Optional[Union[List[CompletionItem], CompletionList]], Id]:
        """
        Make a `textDocument/completion` request.
    
        Request to request completion at a given text document position. The request's
        parameter is of type {@link TextDocumentPosition} the response is of type {@link
        CompletionItem CompletionItem[]} or {@link CompletionList} or a Thenable that
        resolves to such.

        The request can delay the computation of the {@link CompletionItem.detail `detail`}
        and {@link CompletionItem.documentation `documentation`} properties to the
        `completionItem/resolve` request. However, properties that are needed for the
        initial sorting and filtering, like `sortText`, `filterText`, `insertText`, and
        `textEdit`, must not be changed during resolve.
    
        :param params: The parameters to send with the request. An instance of `CompletionParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/completion', params, return_result=return_result)

    def text_document_declaration(self, params: DeclarationParams, return_result=False) -> Union[Optional[Union[List[Location], List[LocationLink], Location]], Id]:
        """
        Make a `textDocument/declaration` request.
    
        A request to resolve the type definition locations of a symbol at a given text
        document position.

        The request's parameter is of type [TextDocumentPositionParams]
        (#TextDocumentPositionParams) the response is of type {@link Declaration} or a typed
        array of {@link DeclarationLink} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `DeclarationParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/declaration', params, return_result=return_result)

    def text_document_definition(self, params: DefinitionParams, return_result=False) -> Union[Optional[Union[List[Location], List[LocationLink], Location]], Id]:
        """
        Make a `textDocument/definition` request.
    
        A request to resolve the definition location of a symbol at a given text document
        position.

        The request's parameter is of type [TextDocumentPosition] (#TextDocumentPosition)
        the response is of either type {@link Definition} or a typed array of {@link
        DefinitionLink} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `DefinitionParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/definition', params, return_result=return_result)

    def text_document_diagnostic(self, params: DocumentDiagnosticParams, return_result=False) -> Union[RelatedUnchangedDocumentDiagnosticReport, RelatedFullDocumentDiagnosticReport, Id]:
        """
        Make a `textDocument/diagnostic` request.
    
        The document diagnostic request definition.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `DocumentDiagnosticParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/diagnostic', params, return_result=return_result)

    def text_document_did_change(self, params: DidChangeTextDocumentParams) -> None:
        """
        Make a `textDocument/didChange` notification.
    
        The document change notification is sent from the client to the server to signal
        changes to a text document.
    
        :param params: The parameters to send with the notification. An instance of `DidChangeTextDocumentParams`.
        :return: None
        """
        self.send_notification('textDocument/didChange', params)

    def text_document_did_close(self, params: DidCloseTextDocumentParams) -> None:
        """
        Make a `textDocument/didClose` notification.
    
        The document close notification is sent from the client to the server when the
        document got closed in the client.

        The document's truth now exists where the document's uri points to (e.g. if the
        document's uri is a file uri the truth now exists on disk). As with the open
        notification the close notification is about managing the document's content.
        Receiving a close notification doesn't mean that the document was open in an editor
        before. A close notification requires a previous open notification to be sent.
    
        :param params: The parameters to send with the notification. An instance of `DidCloseTextDocumentParams`.
        :return: None
        """
        self.send_notification('textDocument/didClose', params)

    def text_document_did_open(self, params: DidOpenTextDocumentParams) -> None:
        """
        Make a `textDocument/didOpen` notification.
    
        The document open notification is sent from the client to the server to signal
        newly opened text documents.

        The document's truth is now managed by the client and the server must not try to
        read the document's truth using the document's uri. Open in this sense means it is
        managed by the client. It doesn't necessarily mean that its content is presented in
        an editor. An open notification must not be sent more than once without a
        corresponding close notification send before. This means open and close notification
        must be balanced and the max open count is one.
    
        :param params: The parameters to send with the notification. An instance of `DidOpenTextDocumentParams`.
        :return: None
        """
        self.send_notification('textDocument/didOpen', params)

    def text_document_did_save(self, params: DidSaveTextDocumentParams) -> None:
        """
        Make a `textDocument/didSave` notification.
    
        The document save notification is sent from the client to the server when the
        document got saved in the client.
    
        :param params: The parameters to send with the notification. An instance of `DidSaveTextDocumentParams`.
        :return: None
        """
        self.send_notification('textDocument/didSave', params)

    def text_document_document_color(self, params: DocumentColorParams, return_result=False) -> Union[List[ColorInformation], Id]:
        """
        Make a `textDocument/documentColor` request.
    
        A request to list all color symbols found in a given text document.

        The request's parameter is of type {@link DocumentColorParams} the response is of
        type {@link ColorInformation ColorInformation[]} or a Thenable that resolves to
        such.
    
        :param params: The parameters to send with the request. An instance of `DocumentColorParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/documentColor', params, return_result=return_result)

    def text_document_document_highlight(self, params: DocumentHighlightParams, return_result=False) -> Union[Optional[List[DocumentHighlight]], Id]:
        """
        Make a `textDocument/documentHighlight` request.
    
        Request to resolve a {@link DocumentHighlight} for a given text document
        position.

        The request's parameter is of type [TextDocumentPosition] (#TextDocumentPosition)
        the request response is of type [DocumentHighlight[]] (#DocumentHighlight) or a
        Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `DocumentHighlightParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/documentHighlight', params, return_result=return_result)

    def text_document_document_link(self, params: DocumentLinkParams, return_result=False) -> Union[Optional[List[DocumentLink]], Id]:
        """
        Make a `textDocument/documentLink` request.
    
        A request to provide document links.
    
        :param params: The parameters to send with the request. An instance of `DocumentLinkParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/documentLink', params, return_result=return_result)

    def text_document_document_symbol(self, params: DocumentSymbolParams, return_result=False) -> Union[Optional[Union[List[DocumentSymbol], List[SymbolInformation]]], Id]:
        """
        Make a `textDocument/documentSymbol` request.
    
        A request to list all symbols found in a given text document.

        The request's parameter is of type {@link TextDocumentIdentifier} the response is of
        type {@link SymbolInformation SymbolInformation[]} or a Thenable that resolves to
        such.
    
        :param params: The parameters to send with the request. An instance of `DocumentSymbolParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/documentSymbol', params, return_result=return_result)

    def text_document_folding_range(self, params: FoldingRangeParams, return_result=False) -> Union[Optional[List[FoldingRange]], Id]:
        """
        Make a `textDocument/foldingRange` request.
    
        A request to provide folding ranges in a document.

        The request's parameter is of type {@link FoldingRangeParams}, the response is of
        type {@link FoldingRangeList} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `FoldingRangeParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/foldingRange', params, return_result=return_result)

    def text_document_formatting(self, params: DocumentFormattingParams, return_result=False) -> Union[Optional[List[TextEdit]], Id]:
        """
        Make a `textDocument/formatting` request.
    
        A request to format a whole document.
    
        :param params: The parameters to send with the request. An instance of `DocumentFormattingParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/formatting', params, return_result=return_result)

    def text_document_hover(self, params: HoverParams, return_result=False) -> Union[Optional[Hover], Id]:
        """
        Make a `textDocument/hover` request.
    
        Request to request hover information at a given text document position.

        The request's parameter is of type {@link TextDocumentPosition} the response is of
        type {@link Hover} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `HoverParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/hover', params, return_result=return_result)

    def text_document_implementation(self, params: ImplementationParams, return_result=False) -> Union[Optional[Union[List[Location], List[LocationLink], Location]], Id]:
        """
        Make a `textDocument/implementation` request.
    
        A request to resolve the implementation locations of a symbol at a given text
        document position.

        The request's parameter is of type [TextDocumentPositionParams]
        (#TextDocumentPositionParams) the response is of type {@link Definition} or a
        Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `ImplementationParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/implementation', params, return_result=return_result)

    def text_document_inlay_hint(self, params: InlayHintParams, return_result=False) -> Union[Optional[List[InlayHint]], Id]:
        """
        Make a `textDocument/inlayHint` request.
    
        A request to provide inlay hints in a document. The request's parameter is of
        type {@link InlayHintsParams}, the response is of type {@link InlayHint InlayHint[]}
        or a Thenable that resolves to such.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `InlayHintParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/inlayHint', params, return_result=return_result)

    def text_document_inline_value(self, params: InlineValueParams, return_result=False) -> Union[Optional[List[Union[InlineValueText, InlineValueVariableLookup, InlineValueEvaluatableExpression]]], Id]:
        """
        Make a `textDocument/inlineValue` request.
    
        A request to provide inline values in a document. The request's parameter is of
        type {@link InlineValueParams}, the response is of type {@link InlineValue
        InlineValue[]} or a Thenable that resolves to such.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `InlineValueParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/inlineValue', params, return_result=return_result)

    def text_document_linked_editing_range(self, params: LinkedEditingRangeParams, return_result=False) -> Union[Optional[LinkedEditingRanges], Id]:
        """
        Make a `textDocument/linkedEditingRange` request.
    
        A request to provide ranges that can be edited together.

        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `LinkedEditingRangeParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/linkedEditingRange', params, return_result=return_result)

    def text_document_moniker(self, params: MonikerParams, return_result=False) -> Union[Optional[List[Moniker]], Id]:
        """
        Make a `textDocument/moniker` request.
    
        A request to get the moniker of a symbol at a given text document position.

        The request parameter is of type {@link TextDocumentPositionParams}. The response is
        of type {@link Moniker Moniker[]} or `null`.
    
        :param params: The parameters to send with the request. An instance of `MonikerParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/moniker', params, return_result=return_result)

    def text_document_on_type_formatting(self, params: DocumentOnTypeFormattingParams, return_result=False) -> Union[Optional[List[TextEdit]], Id]:
        """
        Make a `textDocument/onTypeFormatting` request.
    
        A request to format a document on type.
    
        :param params: The parameters to send with the request. An instance of `DocumentOnTypeFormattingParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/onTypeFormatting', params, return_result=return_result)

    def text_document_prepare_call_hierarchy(self, params: CallHierarchyPrepareParams, return_result=False) -> Union[Optional[List[CallHierarchyItem]], Id]:
        """
        Make a `textDocument/prepareCallHierarchy` request.
    
        A request to result a `CallHierarchyItem` in a document at a given position. Can
        be used as an input to an incoming or outgoing call hierarchy.

        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `CallHierarchyPrepareParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/prepareCallHierarchy', params, return_result=return_result)

    def text_document_prepare_rename(self, params: PrepareRenameParams, return_result=False) -> Union[Optional[Union[Range, PrepareRenameResult_Type1, PrepareRenameResult_Type2]], Id]:
        """
        Make a `textDocument/prepareRename` request.
    
        A request to test and perform the setup necessary for a rename.

        @since 3.16 - support for default behavior
    
        :param params: The parameters to send with the request. An instance of `PrepareRenameParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/prepareRename', params, return_result=return_result)

    def text_document_prepare_type_hierarchy(self, params: TypeHierarchyPrepareParams, return_result=False) -> Union[Optional[List[TypeHierarchyItem]], Id]:
        """
        Make a `textDocument/prepareTypeHierarchy` request.
    
        A request to result a `TypeHierarchyItem` in a document at a given position. Can
        be used as an input to a subtypes or supertypes type hierarchy.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `TypeHierarchyPrepareParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/prepareTypeHierarchy', params, return_result=return_result)

    def text_document_range_formatting(self, params: DocumentRangeFormattingParams, return_result=False) -> Union[Optional[List[TextEdit]], Id]:
        """
        Make a `textDocument/rangeFormatting` request.
    
        A request to format a range in a document.
    
        :param params: The parameters to send with the request. An instance of `DocumentRangeFormattingParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/rangeFormatting', params, return_result=return_result)

    def text_document_references(self, params: ReferenceParams, return_result=False) -> Union[Optional[List[Location]], Id]:
        """
        Make a `textDocument/references` request.
    
        A request to resolve project-wide references for the symbol denoted by the given
        text document position.

        The request's parameter is of type {@link ReferenceParams} the response is of type
        {@link Location Location[]} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `ReferenceParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/references', params, return_result=return_result)

    def text_document_rename(self, params: RenameParams, return_result=False) -> Union[Optional[WorkspaceEdit], Id]:
        """
        Make a `textDocument/rename` request.
    
        A request to rename a symbol.
    
        :param params: The parameters to send with the request. An instance of `RenameParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/rename', params, return_result=return_result)

    def text_document_selection_range(self, params: SelectionRangeParams, return_result=False) -> Union[Optional[List[SelectionRange]], Id]:
        """
        Make a `textDocument/selectionRange` request.
    
        A request to provide selection ranges in a document.

        The request's parameter is of type {@link SelectionRangeParams}, the response is of
        type {@link SelectionRange SelectionRange[]} or a Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `SelectionRangeParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/selectionRange', params, return_result=return_result)

    def text_document_semantic_tokens_full(self, params: SemanticTokensParams, return_result=False) -> Union[Optional[SemanticTokens], Id]:
        """
        Make a `textDocument/semanticTokens/full` request.
    
        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `SemanticTokensParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/semanticTokens/full', params, return_result=return_result)

    def text_document_semantic_tokens_full_delta(self, params: SemanticTokensDeltaParams, return_result=False) -> Union[Optional[Union[SemanticTokens, SemanticTokensDelta]], Id]:
        """
        Make a `textDocument/semanticTokens/full/delta` request.
    
        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `SemanticTokensDeltaParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/semanticTokens/full/delta', params, return_result=return_result)

    def text_document_semantic_tokens_range(self, params: SemanticTokensRangeParams, return_result=False) -> Union[Optional[SemanticTokens], Id]:
        """
        Make a `textDocument/semanticTokens/range` request.
    
        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `SemanticTokensRangeParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/semanticTokens/range', params, return_result=return_result)

    def text_document_signature_help(self, params: SignatureHelpParams, return_result=False) -> Union[Optional[SignatureHelp], Id]:
        """
        Make a `textDocument/signatureHelp` request.
    
        :param params: The parameters to send with the request. An instance of `SignatureHelpParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/signatureHelp', params, return_result=return_result)

    def text_document_type_definition(self, params: TypeDefinitionParams, return_result=False) -> Union[Optional[Union[List[Location], List[LocationLink], Location]], Id]:
        """
        Make a `textDocument/typeDefinition` request.
    
        A request to resolve the type definition locations of a symbol at a given text
        document position.

        The request's parameter is of type [TextDocumentPositionParams]
        (#TextDocumentPositionParams) the response is of type {@link Definition} or a
        Thenable that resolves to such.
    
        :param params: The parameters to send with the request. An instance of `TypeDefinitionParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/typeDefinition', params, return_result=return_result)

    def text_document_will_save(self, params: WillSaveTextDocumentParams) -> None:
        """
        Make a `textDocument/willSave` notification.
    
        A document will save notification is sent from the client to the server before
        the document is actually saved.
    
        :param params: The parameters to send with the notification. An instance of `WillSaveTextDocumentParams`.
        :return: None
        """
        self.send_notification('textDocument/willSave', params)

    def text_document_will_save_wait_until(self, params: WillSaveTextDocumentParams, return_result=False) -> Union[Optional[List[TextEdit]], Id]:
        """
        Make a `textDocument/willSaveWaitUntil` request.
    
        A document will save request is sent from the client to the server before the
        document is actually saved.

        The request can return an array of TextEdits which will be applied to the text
        document before it is saved. Please note that clients might drop results if
        computing the text edits took too long or if a server constantly fails on this
        request. This is done to keep the save fast and reliable.
    
        :param params: The parameters to send with the request. An instance of `WillSaveTextDocumentParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('textDocument/willSaveWaitUntil', params, return_result=return_result)

    def type_hierarchy_subtypes(self, params: TypeHierarchySubtypesParams, return_result=False) -> Union[Optional[List[TypeHierarchyItem]], Id]:
        """
        Make a `typeHierarchy/subtypes` request.
    
        A request to resolve the subtypes for a given `TypeHierarchyItem`.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `TypeHierarchySubtypesParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('typeHierarchy/subtypes', params, return_result=return_result)

    def type_hierarchy_supertypes(self, params: TypeHierarchySupertypesParams, return_result=False) -> Union[Optional[List[TypeHierarchyItem]], Id]:
        """
        Make a `typeHierarchy/supertypes` request.
    
        A request to resolve the supertypes for a given `TypeHierarchyItem`.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `TypeHierarchySupertypesParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('typeHierarchy/supertypes', params, return_result=return_result)

    def window_work_done_progress_cancel(self, params: WorkDoneProgressCancelParams) -> None:
        """
        Make a `window/workDoneProgress/cancel` notification.
    
        The `window/workDoneProgress/cancel` notification is sent from  the client to the
        server to cancel a progress initiated on the server side.
    
        :param params: The parameters to send with the notification. An instance of `WorkDoneProgressCancelParams`.
        :return: None
        """
        self.send_notification('window/workDoneProgress/cancel', params)

    def workspace_diagnostic(self, params: WorkspaceDiagnosticParams, return_result=False) -> Union[WorkspaceDiagnosticReport, Id]:
        """
        Make a `workspace/diagnostic` request.
    
        The workspace diagnostic request definition.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `WorkspaceDiagnosticParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('workspace/diagnostic', params, return_result=return_result)

    def workspace_did_change_configuration(self, params: DidChangeConfigurationParams) -> None:
        """
        Make a `workspace/didChangeConfiguration` notification.
    
        The configuration change notification is sent from the client to the server when
        the client's configuration has changed.

        The notification contains the changed configuration as defined by the language
        client.
    
        :param params: The parameters to send with the notification. An instance of `DidChangeConfigurationParams`.
        :return: None
        """
        self.send_notification('workspace/didChangeConfiguration', params)

    def workspace_did_change_watched_files(self, params: DidChangeWatchedFilesParams) -> None:
        """
        Make a `workspace/didChangeWatchedFiles` notification.
    
        The watched files notification is sent from the client to the server when the
        client detects changes to file watched by the language client.
    
        :param params: The parameters to send with the notification. An instance of `DidChangeWatchedFilesParams`.
        :return: None
        """
        self.send_notification('workspace/didChangeWatchedFiles', params)

    def workspace_did_change_workspace_folders(self, params: DidChangeWorkspaceFoldersParams) -> None:
        """
        Make a `workspace/didChangeWorkspaceFolders` notification.
    
        The `workspace/didChangeWorkspaceFolders` notification is sent from the client to
        the server when the workspace folder configuration changes.
    
        :param params: The parameters to send with the notification. An instance of `DidChangeWorkspaceFoldersParams`.
        :return: None
        """
        self.send_notification('workspace/didChangeWorkspaceFolders', params)

    def workspace_did_create_files(self, params: CreateFilesParams) -> None:
        """
        Make a `workspace/didCreateFiles` notification.
    
        The did create files notification is sent from the client to the server when
        files were created from within the client.

        @since 3.16.0
    
        :param params: The parameters to send with the notification. An instance of `CreateFilesParams`.
        :return: None
        """
        self.send_notification('workspace/didCreateFiles', params)

    def workspace_did_delete_files(self, params: DeleteFilesParams) -> None:
        """
        Make a `workspace/didDeleteFiles` notification.
    
        The will delete files request is sent from the client to the server before files
        are actually deleted as long as the deletion is triggered from within the client.

        @since 3.16.0
    
        :param params: The parameters to send with the notification. An instance of `DeleteFilesParams`.
        :return: None
        """
        self.send_notification('workspace/didDeleteFiles', params)

    def workspace_did_rename_files(self, params: RenameFilesParams) -> None:
        """
        Make a `workspace/didRenameFiles` notification.
    
        The did rename files notification is sent from the client to the server when
        files were renamed from within the client.

        @since 3.16.0
    
        :param params: The parameters to send with the notification. An instance of `RenameFilesParams`.
        :return: None
        """
        self.send_notification('workspace/didRenameFiles', params)

    def workspace_execute_command(self, params: ExecuteCommandParams, return_result=False) -> Union[Optional[Any], Id]:
        """
        Make a `workspace/executeCommand` request.
    
        A request send from the client to the server to execute a command.

        The request might return a workspace edit which the client will apply to the
        workspace.
    
        :param params: The parameters to send with the request. An instance of `ExecuteCommandParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('workspace/executeCommand', params, return_result=return_result)

    def workspace_symbol(self, params: WorkspaceSymbolParams, return_result=False) -> Union[Optional[Union[List[SymbolInformation], List[WorkspaceSymbol]]], Id]:
        """
        Make a `workspace/symbol` request.
    
        A request to list project-wide symbols matching the query string given by the
        {@link WorkspaceSymbolParams}. The response is of type {@link SymbolInformation
        SymbolInformation[]} or a Thenable that resolves to such.

        @since 3.17.0 - support for WorkspaceSymbol in the returned data. Clients
         need to advertise support for WorkspaceSymbols via the client capability
         `workspace.symbol.resolveSupport`.
    
        :param params: The parameters to send with the request. An instance of `WorkspaceSymbolParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('workspace/symbol', params, return_result=return_result)

    def workspace_will_create_files(self, params: CreateFilesParams, return_result=False) -> Union[Optional[WorkspaceEdit], Id]:
        """
        Make a `workspace/willCreateFiles` request.
    
        The will create files request is sent from the client to the server before files
        are actually created as long as the creation is triggered from within the client.

        The request can return a `WorkspaceEdit` which will be applied to workspace before the
        files are created. Hence the `WorkspaceEdit` can not manipulate the content of the file
        to be created.

        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `CreateFilesParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('workspace/willCreateFiles', params, return_result=return_result)

    def workspace_will_delete_files(self, params: DeleteFilesParams, return_result=False) -> Union[Optional[WorkspaceEdit], Id]:
        """
        Make a `workspace/willDeleteFiles` request.
    
        The did delete files notification is sent from the client to the server when
        files were deleted from within the client.

        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `DeleteFilesParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('workspace/willDeleteFiles', params, return_result=return_result)

    def workspace_will_rename_files(self, params: RenameFilesParams, return_result=False) -> Union[Optional[WorkspaceEdit], Id]:
        """
        Make a `workspace/willRenameFiles` request.
    
        The will rename files request is sent from the client to the server before files
        are actually renamed as long as the rename is triggered from within the client.

        @since 3.16.0
    
        :param params: The parameters to send with the request. An instance of `RenameFilesParams`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('workspace/willRenameFiles', params, return_result=return_result)

    def workspace_symbol_resolve(self, params: WorkspaceSymbol, return_result=False) -> Union[WorkspaceSymbol, Id]:
        """
        Make a `workspaceSymbol/resolve` request.
    
        A request to resolve the range inside the workspace symbol's location.

        @since 3.17.0
    
        :param params: The parameters to send with the request. An instance of `WorkspaceSymbol`.
        :param return_result: Whether to return the result of the request. If `True`, the method will block until the
        result is received. If `False`, the method will return the request's id.
        :return: The result of the request if `return_result` is `True`, otherwise the request's id.
        """
        return self.send_request('workspaceSymbol/resolve', params, return_result=return_result)

