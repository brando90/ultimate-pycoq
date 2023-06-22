"""
****** THIS IS A GENERATED FILE, DO NOT EDIT. ******
To regenerate file, run scripts/genclient.py
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

from k_pycoq.base_client import BaseClient


def check_stopped(func):
    async def wrapper(self, *args, **kwargs):
        if self.stopped:
            raise RuntimeError("Client has been stopped.")
        return await func(self, *args, **kwargs)
    return wrapper


class LSPClient(BaseClient):
    def __init__(
        self,
        name: str,
        version: str,
        stdin,
        stdout,
    ):
        self.name = name
        self.version = version
        super().__init__(stdin, stdout)

    @check_stopped
    async def call_hierarchy_incoming_calls(self, params: CallHierarchyIncomingCallsParams) -> Optional[List[CallHierarchyIncomingCall]]:
        """
        Make a `callHierarchy/incomingCalls` request.
    
        A request to resolve the incoming calls for a given `CallHierarchyItem`.

        @since 3.16.0
        """
        return await self.send_request('callHierarchy/incomingCalls', params)

    @check_stopped
    async def call_hierarchy_outgoing_calls(self, params: CallHierarchyOutgoingCallsParams) -> Optional[List[CallHierarchyOutgoingCall]]:
        """
        Make a `callHierarchy/outgoingCalls` request.
    
        A request to resolve the outgoing calls for a given `CallHierarchyItem`.

        @since 3.16.0
        """
        return await self.send_request('callHierarchy/outgoingCalls', params)

    @check_stopped
    async def code_action_resolve(self, params: CodeAction) -> CodeAction:
        """
        Make a `codeAction/resolve` request.
    
        Request to resolve additional information for a given code action.The
        request's parameter is of type {@link CodeAction} the response is of type.

        {@link CodeAction} or a Thenable that resolves to such.
        """
        return await self.send_request('codeAction/resolve', params)

    @check_stopped
    async def code_lens_resolve(self, params: CodeLens) -> CodeLens:
        """
        Make a `codeLens/resolve` request.
    
        A request to resolve a command for a given code lens.
        """
        return await self.send_request('codeLens/resolve', params)

    @check_stopped
    async def completion_item_resolve(self, params: CompletionItem) -> CompletionItem:
        """
        Make a `completionItem/resolve` request.
    
        Request to resolve additional information for a given completion
        item.The request's parameter is of type {@link CompletionItem} the response
        is of type {@link CompletionItem} or a Thenable that resolves to such.
        """
        return await self.send_request('completionItem/resolve', params)

    @check_stopped
    async def document_link_resolve(self, params: DocumentLink) -> DocumentLink:
        """
        Make a `documentLink/resolve` request.
    
        Request to resolve additional information for a given document link.

        The request's parameter is of type {@link DocumentLink} the response
        is of type {@link DocumentLink} or a Thenable that resolves to such.
        """
        return await self.send_request('documentLink/resolve', params)

    @check_stopped
    async def initialize(self, params: InitializeParams) -> InitializeResult:
        """
        Make a `initialize` request.
    
        The initialize request is sent from the client to the server.

        It is sent once as the request after starting up the server. The
        requests parameter is of type {@link InitializeParams} the response
        if of type {@link InitializeResult} of a Thenable that resolves to
        such.
        """
        return await self.send_request('initialize', params)

    @check_stopped
    async def inlay_hint_resolve(self, params: InlayHint) -> InlayHint:
        """
        Make a `inlayHint/resolve` request.
    
        A request to resolve additional properties for an inlay hint. The
        request's parameter is of type {@link InlayHint}, the response is of type.

        {@link InlayHint} or a Thenable that resolves to such.

        @since 3.17.0
        """
        return await self.send_request('inlayHint/resolve', params)

    @check_stopped
    async def shutdown(self, params: None) -> None:
        """
        Make a `shutdown` request.
    
        A shutdown request is sent from the client to the server.

        It is sent once when the client decides to shutdown the server. The
        only notification that is sent after a shutdown request is the exit
        event.
        """
        return await self.send_request('shutdown', params)

    @check_stopped
    async def text_document_code_action(self, params: CodeActionParams) -> Optional[List[Union[Command, CodeAction]]]:
        """
        Make a `textDocument/codeAction` request.
    
        A request to provide commands for the given text document and range.
        """
        return await self.send_request('textDocument/codeAction', params)

    @check_stopped
    async def text_document_code_lens(self, params: CodeLensParams) -> Optional[List[CodeLens]]:
        """
        Make a `textDocument/codeLens` request.
    
        A request to provide code lens for the given text document.
        """
        return await self.send_request('textDocument/codeLens', params)

    @check_stopped
    async def text_document_color_presentation(self, params: ColorPresentationParams) -> List[ColorPresentation]:
        """
        Make a `textDocument/colorPresentation` request.
    
        A request to list all presentation for a color.

        The request's parameter is of type {@link ColorPresentationParams}
        the response is of type {@link ColorInformation ColorInformation[]}
        or a Thenable that resolves to such.
        """
        return await self.send_request('textDocument/colorPresentation', params)

    @check_stopped
    async def text_document_completion(self, params: CompletionParams) -> Optional[Union[List[CompletionItem], CompletionList]]:
        """
        Make a `textDocument/completion` request.
    
        Request to request completion at a given text document position. The
        request's parameter is of type {@link TextDocumentPosition} the response is
        of type {@link CompletionItem CompletionItem[]} or {@link CompletionList}
        or a Thenable that resolves to such.

        The request can delay the computation of the {@link
        CompletionItem.detail `detail`} and {@link
        CompletionItem.documentation `documentation`} properties to the
        `completionItem/resolve` request. However, properties that are
        needed for the initial sorting and filtering, like `sortText`,
        `filterText`, `insertText`, and `textEdit`, must not be changed
        during resolve.
        """
        return await self.send_request('textDocument/completion', params)

    @check_stopped
    async def text_document_declaration(self, params: DeclarationParams) -> Optional[Union[List[LocationLink], Location, List[Location]]]:
        """
        Make a `textDocument/declaration` request.
    
        A request to resolve the type definition locations of a symbol at a
        given text document position.

        The request's parameter is of type [TextDocumentPositionParams]
        (#TextDocumentPositionParams) the response is of type {@link
        Declaration} or a typed array of {@link DeclarationLink} or a
        Thenable that resolves to such.
        """
        return await self.send_request('textDocument/declaration', params)

    @check_stopped
    async def text_document_definition(self, params: DefinitionParams) -> Optional[Union[List[LocationLink], Location, List[Location]]]:
        """
        Make a `textDocument/definition` request.
    
        A request to resolve the definition location of a symbol at a given text
        document position.

        The request's parameter is of type [TextDocumentPosition]
        (#TextDocumentPosition) the response is of either type {@link
        Definition} or a typed array of {@link DefinitionLink} or a Thenable
        that resolves to such.
        """
        return await self.send_request('textDocument/definition', params)

    @check_stopped
    async def text_document_diagnostic(self, params: DocumentDiagnosticParams) -> Union[RelatedFullDocumentDiagnosticReport, RelatedUnchangedDocumentDiagnosticReport]:
        """
        Make a `textDocument/diagnostic` request.
    
        The document diagnostic request definition.

        @since 3.17.0
        """
        return await self.send_request('textDocument/diagnostic', params)

    @check_stopped
    async def text_document_document_color(self, params: DocumentColorParams) -> List[ColorInformation]:
        """
        Make a `textDocument/documentColor` request.
    
        A request to list all color symbols found in a given text document.

        The request's parameter is of type {@link DocumentColorParams} the
        response is of type {@link ColorInformation ColorInformation[]} or a
        Thenable that resolves to such.
        """
        return await self.send_request('textDocument/documentColor', params)

    @check_stopped
    async def text_document_document_highlight(self, params: DocumentHighlightParams) -> Optional[List[DocumentHighlight]]:
        """
        Make a `textDocument/documentHighlight` request.
    
        Request to resolve a {@link DocumentHighlight} for a given text document
        position.

        The request's parameter is of type [TextDocumentPosition]
        (#TextDocumentPosition) the request response is of type
        [DocumentHighlight[]] (#DocumentHighlight) or a Thenable that
        resolves to such.
        """
        return await self.send_request('textDocument/documentHighlight', params)

    @check_stopped
    async def text_document_document_link(self, params: DocumentLinkParams) -> Optional[List[DocumentLink]]:
        """
        Make a `textDocument/documentLink` request.
    
        A request to provide document links.
        """
        return await self.send_request('textDocument/documentLink', params)

    @check_stopped
    async def text_document_document_symbol(self, params: DocumentSymbolParams) -> Optional[Union[List[SymbolInformation], List[DocumentSymbol]]]:
        """
        Make a `textDocument/documentSymbol` request.
    
        A request to list all symbols found in a given text document.

        The request's parameter is of type {@link TextDocumentIdentifier}
        the response is of type {@link SymbolInformation
        SymbolInformation[]} or a Thenable that resolves to such.
        """
        return await self.send_request('textDocument/documentSymbol', params)

    @check_stopped
    async def text_document_folding_range(self, params: FoldingRangeParams) -> Optional[List[FoldingRange]]:
        """
        Make a `textDocument/foldingRange` request.
    
        A request to provide folding ranges in a document.

        The request's parameter is of type {@link FoldingRangeParams}, the
        response is of type {@link FoldingRangeList} or a Thenable that
        resolves to such.
        """
        return await self.send_request('textDocument/foldingRange', params)

    @check_stopped
    async def text_document_formatting(self, params: DocumentFormattingParams) -> Optional[List[TextEdit]]:
        """
        Make a `textDocument/formatting` request.
    
        A request to to format a whole document.
        """
        return await self.send_request('textDocument/formatting', params)

    @check_stopped
    async def text_document_hover(self, params: HoverParams) -> Optional[Hover]:
        """
        Make a `textDocument/hover` request.
    
        Request to request hover information at a given text document position.

        The request's parameter is of type {@link TextDocumentPosition} the
        response is of type {@link Hover} or a Thenable that resolves to
        such.
        """
        return await self.send_request('textDocument/hover', params)

    @check_stopped
    async def text_document_implementation(self, params: ImplementationParams) -> Optional[Union[List[LocationLink], Location, List[Location]]]:
        """
        Make a `textDocument/implementation` request.
    
        A request to resolve the implementation locations of a symbol at a given
        text document position.

        The request's parameter is of type [TextDocumentPositionParams]
        (#TextDocumentPositionParams) the response is of type {@link
        Definition} or a Thenable that resolves to such.
        """
        return await self.send_request('textDocument/implementation', params)

    @check_stopped
    async def text_document_inlay_hint(self, params: InlayHintParams) -> Optional[List[InlayHint]]:
        """
        Make a `textDocument/inlayHint` request.
    
        A request to provide inlay hints in a document. The request's parameter
        is of type {@link InlayHintsParams}, the response is of type.

        {@link InlayHint InlayHint[]} or a Thenable that resolves to such.

        @since 3.17.0
        """
        return await self.send_request('textDocument/inlayHint', params)

    @check_stopped
    async def text_document_inline_value(self, params: InlineValueParams) -> Optional[List[Union[InlineValueEvaluatableExpression, InlineValueVariableLookup, InlineValueText]]]:
        """
        Make a `textDocument/inlineValue` request.
    
        A request to provide inline values in a document. The request's
        parameter is of type {@link InlineValueParams}, the response is of type.

        {@link InlineValue InlineValue[]} or a Thenable that resolves to such.

        @since 3.17.0
        """
        return await self.send_request('textDocument/inlineValue', params)

    @check_stopped
    async def text_document_linked_editing_range(self, params: LinkedEditingRangeParams) -> Optional[LinkedEditingRanges]:
        """
        Make a `textDocument/linkedEditingRange` request.
    
        A request to provide ranges that can be edited together.

        @since 3.16.0
        """
        return await self.send_request('textDocument/linkedEditingRange', params)

    @check_stopped
    async def text_document_moniker(self, params: MonikerParams) -> Optional[List[Moniker]]:
        """
        Make a `textDocument/moniker` request.
    
        A request to get the moniker of a symbol at a given text document
        position.

        The request parameter is of type {@link TextDocumentPositionParams}.
        The response is of type {@link Moniker Moniker[]} or `null`.
        """
        return await self.send_request('textDocument/moniker', params)

    @check_stopped
    async def text_document_on_type_formatting(self, params: DocumentOnTypeFormattingParams) -> Optional[List[TextEdit]]:
        """
        Make a `textDocument/onTypeFormatting` request.
    
        A request to format a document on type.
        """
        return await self.send_request('textDocument/onTypeFormatting', params)

    @check_stopped
    async def text_document_prepare_call_hierarchy(self, params: CallHierarchyPrepareParams) -> Optional[List[CallHierarchyItem]]:
        """
        Make a `textDocument/prepareCallHierarchy` request.
    
        A request to result a `CallHierarchyItem` in a document at a given
        position. Can be used as an input to an incoming or outgoing call
        hierarchy.

        @since 3.16.0
        """
        return await self.send_request('textDocument/prepareCallHierarchy', params)

    @check_stopped
    async def text_document_prepare_rename(self, params: PrepareRenameParams) -> Optional[Union[PrepareRenameResult_Type1, PrepareRenameResult_Type2, Range]]:
        """
        Make a `textDocument/prepareRename` request.
    
        A request to test and perform the setup necessary for a rename.

        @since 3.16 - support for default behavior
        """
        return await self.send_request('textDocument/prepareRename', params)

    @check_stopped
    async def text_document_prepare_type_hierarchy(self, params: TypeHierarchyPrepareParams) -> Optional[List[TypeHierarchyItem]]:
        """
        Make a `textDocument/prepareTypeHierarchy` request.
    
        A request to result a `TypeHierarchyItem` in a document at a given
        position. Can be used as an input to a subtypes or supertypes type
        hierarchy.

        @since 3.17.0
        """
        return await self.send_request('textDocument/prepareTypeHierarchy', params)

    @check_stopped
    async def text_document_range_formatting(self, params: DocumentRangeFormattingParams) -> Optional[List[TextEdit]]:
        """
        Make a `textDocument/rangeFormatting` request.
    
        A request to to format a range in a document.
        """
        return await self.send_request('textDocument/rangeFormatting', params)

    @check_stopped
    async def text_document_references(self, params: ReferenceParams) -> Optional[List[Location]]:
        """
        Make a `textDocument/references` request.
    
        A request to resolve project-wide references for the symbol denoted by
        the given text document position. The request's parameter is of type {@link
        ReferenceParams} the response is of type.

        {@link Location Location[]} or a Thenable that resolves to such.
        """
        return await self.send_request('textDocument/references', params)

    @check_stopped
    async def text_document_rename(self, params: RenameParams) -> Optional[WorkspaceEdit]:
        """
        Make a `textDocument/rename` request.
    
        A request to rename a symbol.
        """
        return await self.send_request('textDocument/rename', params)

    @check_stopped
    async def text_document_selection_range(self, params: SelectionRangeParams) -> Optional[List[SelectionRange]]:
        """
        Make a `textDocument/selectionRange` request.
    
        A request to provide selection ranges in a document.

        The request's parameter is of type {@link SelectionRangeParams}, the
        response is of type {@link SelectionRange SelectionRange[]} or a
        Thenable that resolves to such.
        """
        return await self.send_request('textDocument/selectionRange', params)

    @check_stopped
    async def text_document_semantic_tokens_full(self, params: SemanticTokensParams) -> Optional[SemanticTokens]:
        """
        Make a `textDocument/semanticTokens/full` request.
    
        @since 3.16.0
        """
        return await self.send_request('textDocument/semanticTokens/full', params)

    @check_stopped
    async def text_document_semantic_tokens_full_delta(self, params: SemanticTokensDeltaParams) -> Optional[Union[SemanticTokensDelta, SemanticTokens]]:
        """
        Make a `textDocument/semanticTokens/full/delta` request.
    
        @since 3.16.0
        """
        return await self.send_request('textDocument/semanticTokens/full/delta', params)

    @check_stopped
    async def text_document_semantic_tokens_range(self, params: SemanticTokensRangeParams) -> Optional[SemanticTokens]:
        """
        Make a `textDocument/semanticTokens/range` request.
    
        @since 3.16.0
        """
        return await self.send_request('textDocument/semanticTokens/range', params)

    @check_stopped
    async def text_document_signature_help(self, params: SignatureHelpParams) -> Optional[SignatureHelp]:
        """
        Make a `textDocument/signatureHelp` request.
        """
        return await self.send_request('textDocument/signatureHelp', params)

    @check_stopped
    async def text_document_type_definition(self, params: TypeDefinitionParams) -> Optional[Union[List[LocationLink], Location, List[Location]]]:
        """
        Make a `textDocument/typeDefinition` request.
    
        A request to resolve the type definition locations of a symbol at a
        given text document position.

        The request's parameter is of type [TextDocumentPositionParams]
        (#TextDocumentPositionParams) the response is of type {@link
        Definition} or a Thenable that resolves to such.
        """
        return await self.send_request('textDocument/typeDefinition', params)

    @check_stopped
    async def text_document_will_save_wait_until(self, params: WillSaveTextDocumentParams) -> Optional[List[TextEdit]]:
        """
        Make a `textDocument/willSaveWaitUntil` request.
    
        A document will save request is sent from the client to the server
        before the document is actually saved.

        The request can return an array of TextEdits which will be applied
        to the text document before it is saved. Please note that clients
        might drop results if computing the text edits took too long or if a
        server constantly fails on this request. This is done to keep the
        save fast and reliable.
        """
        return await self.send_request('textDocument/willSaveWaitUntil', params)

    @check_stopped
    async def type_hierarchy_subtypes(self, params: TypeHierarchySubtypesParams) -> Optional[List[TypeHierarchyItem]]:
        """
        Make a `typeHierarchy/subtypes` request.
    
        A request to resolve the subtypes for a given `TypeHierarchyItem`.

        @since 3.17.0
        """
        return await self.send_request('typeHierarchy/subtypes', params)

    @check_stopped
    async def type_hierarchy_supertypes(self, params: TypeHierarchySupertypesParams) -> Optional[List[TypeHierarchyItem]]:
        """
        Make a `typeHierarchy/supertypes` request.
    
        A request to resolve the supertypes for a given `TypeHierarchyItem`.

        @since 3.17.0
        """
        return await self.send_request('typeHierarchy/supertypes', params)

    @check_stopped
    async def workspace_diagnostic(self, params: WorkspaceDiagnosticParams) -> WorkspaceDiagnosticReport:
        """
        Make a `workspace/diagnostic` request.
    
        The workspace diagnostic request definition.

        @since 3.17.0
        """
        return await self.send_request('workspace/diagnostic', params)

    @check_stopped
    async def workspace_execute_command(self, params: ExecuteCommandParams) -> Optional[Any]:
        """
        Make a `workspace/executeCommand` request.
    
        A request send from the client to the server to execute a command.

        The request might return a workspace edit which the client will
        apply to the workspace.
        """
        return await self.send_request('workspace/executeCommand', params)

    @check_stopped
    async def workspace_symbol(self, params: WorkspaceSymbolParams) -> Optional[Union[List[SymbolInformation], List[WorkspaceSymbol]]]:
        """
        Make a `workspace/symbol` request.
    
        A request to list project-wide symbols matching the query string given
        by the {@link WorkspaceSymbolParams}. The response is of type {@link
        SymbolInformation SymbolInformation[]} or a Thenable that resolves to such.

        @since 3.17.0 - support for WorkspaceSymbol in the returned data. Clients
         need to advertise support for WorkspaceSymbols via the client capability
         `workspace.symbol.resolveSupport`.
        """
        return await self.send_request('workspace/symbol', params)

    @check_stopped
    async def workspace_symbol_resolve(self, params: WorkspaceSymbol) -> WorkspaceSymbol:
        """
        Make a `workspaceSymbol/resolve` request.
    
        A request to resolve the range inside the workspace symbol's location.

        @since 3.17.0
        """
        return await self.send_request('workspaceSymbol/resolve', params)

    @check_stopped
    async def workspace_will_create_files(self, params: CreateFilesParams) -> Optional[WorkspaceEdit]:
        """
        Make a `workspace/willCreateFiles` request.
    
        The will create files request is sent from the client to the server
        before files are actually created as long as the creation is triggered from
        within the client.

        @since 3.16.0
        """
        return await self.send_request('workspace/willCreateFiles', params)

    @check_stopped
    async def workspace_will_delete_files(self, params: DeleteFilesParams) -> Optional[WorkspaceEdit]:
        """
        Make a `workspace/willDeleteFiles` request.
    
        The did delete files notification is sent from the client to the server
        when files were deleted from within the client.

        @since 3.16.0
        """
        return await self.send_request('workspace/willDeleteFiles', params)

    @check_stopped
    async def workspace_will_rename_files(self, params: RenameFilesParams) -> Optional[WorkspaceEdit]:
        """
        Make a `workspace/willRenameFiles` request.
    
        The will rename files request is sent from the client to the server
        before files are actually renamed as long as the rename is triggered from
        within the client.

        @since 3.16.0
        """
        return await self.send_request('workspace/willRenameFiles', params)

    @check_stopped
    async def cancel_request(self, params: CancelParams) -> None:
        """
        Make a `$/cancelRequest` notification.
        """
        return await self.send_notification('$/cancelRequest', params)

    @check_stopped
    async def exit(self, params: None) -> None:
        """
        Make a `exit` notification.
    
        The exit event is sent from the client to the server to ask the server
        to exit its process.
        """
        return await self.send_notification('exit', params)

    @check_stopped
    async def initialized(self, params: InitializedParams) -> None:
        """
        Make a `initialized` notification.
    
        The initialized notification is sent from the client to the server after
        the client is fully initialized and the server is allowed to send requests
        from the server to the client.
        """
        return await self.send_notification('initialized', params)

    @check_stopped
    async def notebook_document_did_change(self, params: DidChangeNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didChange` notification.
        """
        return await self.send_notification('notebookDocument/didChange', params)

    @check_stopped
    async def notebook_document_did_close(self, params: DidCloseNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didClose` notification.
    
        A notification sent when a notebook closes.

        @since 3.17.0
        """
        return await self.send_notification('notebookDocument/didClose', params)

    @check_stopped
    async def notebook_document_did_open(self, params: DidOpenNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didOpen` notification.
    
        A notification sent when a notebook opens.

        @since 3.17.0
        """
        return await self.send_notification('notebookDocument/didOpen', params)

    @check_stopped
    async def notebook_document_did_save(self, params: DidSaveNotebookDocumentParams) -> None:
        """
        Make a `notebookDocument/didSave` notification.
    
        A notification sent when a notebook document is saved.

        @since 3.17.0
        """
        return await self.send_notification('notebookDocument/didSave', params)

    @check_stopped
    async def progress(self, params: ProgressParams) -> None:
        """
        Make a `$/progress` notification.
        """
        return await self.send_notification('$/progress', params)

    @check_stopped
    async def set_trace(self, params: SetTraceParams) -> None:
        """
        Make a `$/setTrace` notification.
        """
        return await self.send_notification('$/setTrace', params)

    @check_stopped
    async def text_document_did_change(self, params: DidChangeTextDocumentParams) -> None:
        """
        Make a `textDocument/didChange` notification.
    
        The document change notification is sent from the client to the server
        to signal changes to a text document.
        """
        return await self.send_notification('textDocument/didChange', params)

    @check_stopped
    async def text_document_did_close(self, params: DidCloseTextDocumentParams) -> None:
        """
        Make a `textDocument/didClose` notification.
    
        The document close notification is sent from the client to the server
        when the document got closed in the client.

        The document's truth now exists where the document's uri points to
        (e.g. if the document's uri is a file uri the truth now exists on
        disk). As with the open notification the close notification is about
        managing the document's content. Receiving a close notification
        doesn't mean that the document was open in an editor before. A close
        notification requires a previous open notification to be sent.
        """
        return await self.send_notification('textDocument/didClose', params)

    @check_stopped
    async def text_document_did_open(self, params: DidOpenTextDocumentParams) -> None:
        """
        Make a `textDocument/didOpen` notification.
    
        The document open notification is sent from the client to the server to
        signal newly opened text documents.

        The document's truth is now managed by the client and the server
        must not try to read the document's truth using the document's uri.
        Open in this sense means it is managed by the client. It doesn't
        necessarily mean that its content is presented in an editor. An open
        notification must not be sent more than once without a corresponding
        close notification send before. This means open and close
        notification must be balanced and the max open count is one.
        """
        return await self.send_notification('textDocument/didOpen', params)

    @check_stopped
    async def text_document_did_save(self, params: DidSaveTextDocumentParams) -> None:
        """
        Make a `textDocument/didSave` notification.
    
        The document save notification is sent from the client to the server
        when the document got saved in the client.
        """
        return await self.send_notification('textDocument/didSave', params)

    @check_stopped
    async def text_document_will_save(self, params: WillSaveTextDocumentParams) -> None:
        """
        Make a `textDocument/willSave` notification.
    
        A document will save notification is sent from the client to the server
        before the document is actually saved.
        """
        return await self.send_notification('textDocument/willSave', params)

    @check_stopped
    async def window_work_done_progress_cancel(self, params: WorkDoneProgressCancelParams) -> None:
        """
        Make a `window/workDoneProgress/cancel` notification.
    
        The `window/workDoneProgress/cancel` notification is sent from  the
        client to the server to cancel a progress initiated on the server side.
        """
        return await self.send_notification('window/workDoneProgress/cancel', params)

    @check_stopped
    async def workspace_did_change_configuration(self, params: DidChangeConfigurationParams) -> None:
        """
        Make a `workspace/didChangeConfiguration` notification.
    
        The configuration change notification is sent from the client to the
        server when the client's configuration has changed.

        The notification contains the changed configuration as defined by
        the language client.
        """
        return await self.send_notification('workspace/didChangeConfiguration', params)

    @check_stopped
    async def workspace_did_change_watched_files(self, params: DidChangeWatchedFilesParams) -> None:
        """
        Make a `workspace/didChangeWatchedFiles` notification.
    
        The watched files notification is sent from the client to the server
        when the client detects changes to file watched by the language client.
        """
        return await self.send_notification('workspace/didChangeWatchedFiles', params)

    @check_stopped
    async def workspace_did_change_workspace_folders(self, params: DidChangeWorkspaceFoldersParams) -> None:
        """
        Make a `workspace/didChangeWorkspaceFolders` notification.
    
        The `workspace/didChangeWorkspaceFolders` notification is sent from the
        client to the server when the workspace folder configuration changes.
        """
        return await self.send_notification('workspace/didChangeWorkspaceFolders', params)

    @check_stopped
    async def workspace_did_create_files(self, params: CreateFilesParams) -> None:
        """
        Make a `workspace/didCreateFiles` notification.
    
        The did create files notification is sent from the client to the server
        when files were created from within the client.

        @since 3.16.0
        """
        return await self.send_notification('workspace/didCreateFiles', params)

    @check_stopped
    async def workspace_did_delete_files(self, params: DeleteFilesParams) -> None:
        """
        Make a `workspace/didDeleteFiles` notification.
    
        The will delete files request is sent from the client to the server
        before files are actually deleted as long as the deletion is triggered from
        within the client.

        @since 3.16.0
        """
        return await self.send_notification('workspace/didDeleteFiles', params)

    @check_stopped
    async def workspace_did_rename_files(self, params: RenameFilesParams) -> None:
        """
        Make a `workspace/didRenameFiles` notification.
    
        The did rename files notification is sent from the client to the server
        when files were renamed from within the client.

        @since 3.16.0
        """
        return await self.send_notification('workspace/didRenameFiles', params)

