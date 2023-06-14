from enum import Enum
from typing import Any, Optional, Union, Literal

from pydantic import BaseModel, Field
from typing_extensions import Annotated

# ----------------------------------
# Basic JSON structures used by the LSP protocol.
# ----------------------------------

JSON = dict[str, Any]
Params = Union[JSON, list[Any]]
Id = Union[int, str]
URI = str


class Position(BaseModel):
    """
    Position in a text document expressed as zero-based line and character offset. A position is between two
    characters like an 'insert' cursor in an editor.

    :param line: Line position in document (zero-based).
    :param character: Character offset in line (zero-based).
    :param offset: Optional character offset in document (zero-based).
    """
    line: int
    character: int
    offset: Optional[int]


class Range(BaseModel):
    """
    A range in a text document expressed as (zero-based) start and end positions. A range is comparable to a
    selection in an editor. Therefore the end position is exclusive. If you want to specify a range that
    contains a line including the line ending character(s) then use an end position denoting the start of
    the next line.

    :param start: The range's start position.
    :param end: The range's end position.
    """
    start: Position
    end: Position


class Location(BaseModel):
    """
    Represents a location inside a resource, such as a line inside a text file.

    :param uri: The URI of the document.
    :param range: The range in side the document.
    """
    uri: URI
    range: Range


class LocationLink(BaseModel):
    """
    Represents a link between a source and a target location.

    :param originSelectionRange: The span of the origin of this link.
    :param targetUri: The target resource identifier of this link.
    :param targetRange: The full target range of this link.
    :param targetSelectionRange: The range that should be selected and revealed when this link is being followed.
    """
    originSelectionRange: Optional[Range]
    targetUri: URI
    targetRange: Range
    targetSelectionRange: Range


# ----------------------------------
# Interaction methods between the client and the server.
# ----------------------------------


class Request(BaseModel):
    """
    A request is a method invocation from the client to the server. It consists of a method name to invoke,
    along with optional parameters to pass to the method. The server returns a response containing the result
    of the method invocation, along with optional response-specific metadata.

    :param jsonrpc: A String specifying the version of the JSON-RPC protocol. MUST be exactly "2.0".
    :param id: An identifier established by the Client that is associated with the request. Server responses
    corresponding with this request MUST contain the same value as the original request.
    :param method: The name of the method to be invoked.
    :param params: The parameters of the invoked method.
    """
    jsonrpc: str
    id: Id
    method: str
    params: Optional[Params]


class Notification(BaseModel):
    """
    A notification is a method invocation that does not require a response. As such, it cannot return
    useful information to the client. The Client MAY send notifications to the Server.

    :param jsonrpc: A String specifying the version of the JSON-RPC protocol. MUST be exactly "2.0".
    :param method: A String containing the name of the method to be invoked.
    :param params: A Structured value that holds the parameter values to be used during the invocation of the method.
    """
    jsonrpc: str
    method: str
    params: Optional[Params]


class ErrorCodes(Enum):
    """
    https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#errorCodes
    """
    ParseError = -32700
    InvalidRequest = -32600
    MethodNotFound = -32601
    InvalidParams = -32602
    InternalError = -32603

    serverErrorStart = -32099
    serverErrorEnd = -32000
    ServerNotInitialized = -32002
    UnknownErrorCode = -32001

    lspReservedErrorRangeStart = -32899
    RequestFailed = -32803
    ServerCancelled = -32802
    ContentModified = -32801
    RequestCancelled = -32800
    lspReservedErrorRangeEnd = -32800


class ResponseError(BaseModel):
    """
    :param code: A number indicating the error type that occurred.
    :param message: A string providing a short description of the error.
    :param data: A primitive or structured value that contains additional information about the error.
    """
    code: ErrorCodes
    message: str
    data: Optional[Any]


class Response(BaseModel):
    """
    A response is returned by the server to the client. It is the result of a request.

    :param jsonrpc: A String specifying the version of the JSON-RPC protocol. MUST be exactly "2.0".
    :param id: An identifier established by the Client that is associated with the request. Server responses
    corresponding with this request MUST contain the same value as the original request.
    :param result: This member is REQUIRED on success.
    :param error: This member is REQUIRED on error.
    """
    jsonrpc: str
    id: Id
    # result and error must be mutually exclusive
    result: Optional[JSON]
    error: Optional[ResponseError]


# ----------------------------------
# LSP protocol method parameters.
# ----------------------------------

ProgressToken = Union[int, str]


class WorkDoneProgressParams(BaseModel):
    """
    :param workDoneToken: An optional token that a server can use to report work done progress.
    """
    workDoneToken: Optional[ProgressToken]


class TraceValues(Enum):
    off = 'off'
    messages = 'messages'
    verbose = 'verbose'


class WorkspaceFolder(BaseModel):
    """
    :param uri: The associated URI for this workspace folder.
    :param name: The name of the workspace folder. Defaults to the uri's basename.
    """
    uri: URI
    name: str


class InitializeParams(WorkDoneProgressParams):
    """
    :param processId: The process Id of the parent process that started the server. Is None if the process has not been
    started by another process. If the parent process is not alive then the server should exit (see exit notification)
    its process.
    :param clientInfo: Information about the client
    :param local: The locale the client is currently showing the user interface in. This must not necessarily be the
    locale of the operating system.
    :param rootUri: The rootPath of the workspace. Is None if no folder is open.
    :param initializationOptions: User provided initialization options.
    :param capabilities: The capabilities provided by the client (editor or tool)
    :param trace: The initial trace setting. If omitted trace is disabled ('off').
    :param workspaceFolders: The workspace folders configured in the client when the server starts. This property is
    only available if the client supports workspace folders. It can be `None` if the client supports workspace folders
    but none are configured.
    """
    processId: Id
    clientInfo: Optional[JSON]
    local: Optional[str]
    rootUri: Optional[URI]
    initializationOptions: Any  # TODO: use pydantic model
    capabilities: JSON  # TODO: use pydantic model
    trace: Optional[TraceValues]
    workspaceFolders: Optional[WorkspaceFolder]


class SetTraceParams(BaseModel):
    """
    :param value: The new value that should be assigned to the trace setting.
    """
    value: TraceValues


class LogTraceParams(BaseModel):
    """
    :param message: The message to be logged.
    :param verbose: Additional information that can be computed if the `trace` configuration is set to `'verbose'`.
    """
    message: str
    verbose: Optional[str]


class TextDocumentItem(BaseModel):
    """
    :param uri: The text document's URI.
    :param languageId: The text document's language identifier.
    :param version: The version number of this document (it will increase after each change, including undo/redo).
    :param text: The content of the opened text document.
    """
    uri: URI
    languageId: str
    version: int
    text: str


class TextDocumentIdentifier(BaseModel):
    """
    :param uri: The text document's URI.
    """
    uri: URI


class VersionedTextDocumentIdentifier(TextDocumentIdentifier):
    """
    :param uri: The text document's URI.
    :param version: The version number of this document. If a versioned text document identifier is sent from the
    server to the client and the file is not open in the editor (the server has not received an open notification
    before) the server can send `null` to indicate that the version is known and the content on disk is the
    truth (as speced with document content ownership).

    The version number of a document will increase after each change, including undo/redo. The number doesn't need to
    be consecutive.
    """
    version: Optional[int]


class TextDocumentContentChangeEvent(BaseModel):
    """
    :param range: The range of the document that changed.
    :param rangeLength: Deprecated. The optional length of the range that got replaced.
    :param text: The new text of the range/document.

    If range and rangeLength are omitted the new text is considered to be the full content of the document.
    """
    range: Optional[Range]
    rangeLength: Optional[int]
    text: str


TextDocumentContentChangeEvent = Union[TextDocumentContentChangeEvent, str]


class TextDocumentPositionParams(BaseModel):
    """
    :param textDocument: The text document.
    :param position: The position inside the text document.
    """
    textDocument: TextDocumentIdentifier
    position: Position


class DidOpenTextDocumentParams(BaseModel):
    """
    :param textDocument: The document that was opened.
    """
    textDocument: TextDocumentItem


class DidChangeTextDocumentParams(BaseModel):
    """
    :param textDocument: The document that did change. The version number points to the version after all provided
    content changes have been applied.
    :param contentChanges: The actual content changes. The content changes describe single state changes to the
    document. So if there are two content changes c1 (at array index 0) and c2 (at array index 1) for a document in
    state S then c1 moves the document from S to S' and c2 from S' to S''. So c1 is computed on the state S and c2 is
    computed on the state S'.
    """
    textDocument: VersionedTextDocumentIdentifier
    contentChanges: list[TextDocumentContentChangeEvent]


class DidSaveTextDocumentParams(BaseModel):
    """
    :param textDocument: The document that was saved.
    :param text: Optional the content when saved (we will probably not use this).
    """
    textDocument: TextDocumentIdentifier
    text: Optional[str]


class DidCloseTextDocumentParams(BaseModel):
    """
    :param textDocument: The document that was closed.
    """
    textDocument: TextDocumentIdentifier


class DefinitionParams(TextDocumentPositionParams, WorkDoneProgressParams):  # PartialResultParams
    """
    :param textDocument: The text document.
    :param position: The position inside the text document.
    :param workDoneToken: An optional token that a server can use to report work done progress.
    """


class HoverParams(TextDocumentPositionParams, WorkDoneProgressParams):
    """
    :param textDocument: The text document.
    :param position: The position inside the text document.
    :param workDoneToken: An optional token that a server can use to report work done progress.
    """


class DocumentSymbolParams(WorkDoneProgressParams):  # PartialResultParams
    """
    :param textDocument: The text document.
    :param workDoneToken: An optional token that a server can use to report work done progress.
    """
    textDocument: TextDocumentIdentifier


class CompletionTriggerKind(Enum):
    """
    How a completion was triggered

    :param INVOKED: Completion was triggered by typing an identifier (24x7 code
    complete), manual invocation (e.g Ctrl+Space) or via API.
    :param TRIGGER_CHARACTER: Completion was triggered by a trigger character specified by
    the `triggerCharacters` properties of the `CompletionRegistrationOptions`.
    :param TRIGGER_FOR_INCOMPLETE_COMPLETIONS: Completion was re-triggered as the current completion list is incomplete.
    """
    INVOKED = 1
    TRIGGER_CHARACTER = 2
    TRIGGER_FOR_INCOMPLETE_COMPLETIONS = 3


class CompletionContext(BaseModel):
    """
    :param triggerKind: How the completion was triggered.
    :param triggerCharacter: The trigger character (a single character) that has trigger code complete. Is undefined if
    `triggerKind !== CompletionTriggerKind.TriggerCharacter`
    """
    triggerKind: CompletionTriggerKind
    triggerCharacter: Optional[str]


class CompletionParams(TextDocumentPositionParams, WorkDoneProgressParams):  # PartialResultParams
    """
    :param textDocument: The text document.
    :param position: The position inside the text document.
    :param context: The completion context. This is only available if the client specifies to send this using
    `ClientCapabilities.textDocument.completion.contextSupport === true`
    :param workDoneToken: An optional token that a server can use to report work done progress.
    """
    context: Optional[CompletionContext]


class DiagnosticSeverity(Enum):
    """
    The diagnostic's severity.

    :param ERROR: Reports an error.
    :param WARNING: Reports a warning.
    :param INFORMATION: Reports an information.
    :param HINT: Reports a hint.
    """
    ERROR = 1
    WARNING = 2
    INFORMATION = 3
    HINT = 4


class CodeDescription(BaseModel):
    """
    :param href: The URI to open with the user default browser.
    """
    href: URI


class DiagnosticTag(Enum):
    """
    :param UNNECESSARY: Unused or unnecessary code.
    :param DEPRECATED: Deprecated or obsolete code.
    """
    UNNECESSARY = 1
    DEPRECATED = 2


class DiagnosticRelatedInformation(BaseModel):
    """
    :param location: The location of this related diagnostic information.
    :param message: The message of this related diagnostic information.
    """
    location: Location
    message: str


class Diagnostic(BaseModel):
    """
    :param range: The range at which the message applies.
    :param severity: The diagnostic's severity. Can be omitted. If omitted it is up to the
    client to interpret diagnostics as error, warning, info or hint.
    :param code: The diagnostic's code, which might appear in the user interface.
    :param codeDescription: An optional property to describe the error code.
    :param source: A human-readable string describing the source of this
    diagnostic, e.g. 'typescript' or 'super lint'.
    :param message: The diagnostic's message.
    :param tags: Additional metadata about the diagnostic.
    :param relatedInformation: An array of related diagnostic information, e.g. when symbol-names within
    a scope collide all definitions can be marked via this property.
    :param data: A data entry field that is preserved between a `textDocument/publishDiagnostics`
    notification and `textDocument/codeAction` request.
    """
    range: Range
    severity: Optional[DiagnosticSeverity]
    code: Optional[Union[int, str]]
    codeDescription: Optional[CodeDescription]
    source: Optional[str]
    message: str
    tags: Optional[list[DiagnosticTag]]
    relatedInformation: Optional[list[DiagnosticRelatedInformation]]
    data: Optional[Any]


class PublishDiagnosticsParams(BaseModel):
    """
    :param uri: The URI for which diagnostic information is reported.
    :param version: Optional the version number of the document the diagnostics are published for.
    :param diagnostics: An array of diagnostic information items.
    """
    uri: URI
    version: Optional[int]
    diagnostics: list[Diagnostic]


class WorkspaceFoldersChangeEvent(BaseModel):
    """
    :param added: The array of added workspace folders
    :param removed: The array of the removed workspace folders
    """
    added: list[WorkspaceFolder]
    removed: list[WorkspaceFolder]


class DidChangeWorkspaceFoldersParams(BaseModel):
    """
    :param event: The actual workspace folder change event.
    """
    event: WorkspaceFoldersChangeEvent


class GoalsParams(BaseModel):  # called GoalsRequest in coqlsp spec, renamed for consistency with standard lsp
    """
    :param textDocument: The text document.
    :param position: The position inside the text document.
    """
    textDocument: VersionedTextDocumentIdentifier
    position: Position


class CoqFileProgressKind(Enum):
    """
    :param PROCESSING: The file is being processed.
    :param FATAL_ERROR: The file has encountered a fatal error.
    """
    PROCESSING = 1
    FATAL_ERROR = 2


class CoqFileProgressProcessingInfo(BaseModel):
    """
    :param range: The range of the file that is being processed.
    :param kind: The kind of progress that is being reported.
    """
    range: Range
    kind: Optional[CoqFileProgressKind]


class CoqFileProgressParams(BaseModel):
    """
    :param textDocument: The text document.
    :param processing: Array containing the parts of the file which are still being processed.
    The array should be empty if and only if the server is finished processing.
    """
    textDocument: VersionedTextDocumentIdentifier
    processing: list[CoqFileProgressProcessingInfo]


class FlecheDocumentParams(BaseModel):
    """
    :param textDocument: The text document.
    """
    textDocument: VersionedTextDocumentIdentifier


class FlecheSaveParams(BaseModel):
    """
    :param textDocument: The text document.
    """
    textDocument: VersionedTextDocumentIdentifier


class Loc(BaseModel):  # special to coqlsp (different from Location type)
    """
    :param fname: The file name. # TODO: work out the format of this
    :param line_nb: The start line number.
    :param bol_pos: The beginning of line position in terms of character offset.
    :param line_nb_last: The last line number.
    :param bol_pos_last: The last beginning of last line position in terms of character offset.
    :param bp: The beginning of position in terms of character offset.
    :param ep: The end of position in terms of character offset.
    """
    fname: Any
    line_nb: int
    bol_pos: int
    line_nb_last: int
    bol_pos_last: int
    bp: int
    ep: int


class SentencePerfParams(BaseModel):
    """
    :param loc: The location of the sentence.
    :param time: The time taken to process the sentence.
    :param mem: The memory used to process the sentence.
    """
    loc: Loc
    time: int  # TODO: are these ints or floats?
    mem: int


class DocumentPerfParams(BaseModel):
    """
    :param summary: A summary of the performance of the document.
    :param timings: The performance of each sentence in the document.
    """
    summary: str
    timings: list[SentencePerfParams]


# ----------------------------------
# LSP protocol response structures
# ----------------------------------


class ServerInfo(BaseModel):
    """
    :param name: The name of the server as defined by the server.
    :param version: The server's version as defined by the server.
    """
    name: str
    version: Optional[str]


class InitializeResult(BaseModel):
    """
    :param capabilities: The capabilities the language server provides.
    """
    capabilities: JSON  # TODO: this is a ServerCapabilities object, but it's not defined yet
    serverInfo: Optional[ServerInfo]


LocationResult = Union[Location, list[Location], LocationLink, None]


class MarkedString(BaseModel):
    """
    :param language: The language in which the string is represented.
    :param value: The value of the string.
    """
    language: Optional[str]
    value: str


MarkedString = Union[str, MarkedString]


class MarkupKind(Enum):
    """
    :param PLAINTEXT: Plain text is supported as a content format
    :param MARKDOWN: Markdown is supported as a content format
    """
    PLAINTEXT = 'plaintext'
    MARKDOWN = 'markdown'


class MarkupContent(BaseModel):
    """
    :param kind: The type of the Markup
    :param value: The content itself
    """
    kind: MarkupKind
    value: str


class HoverResult(BaseModel):
    """
    :param contents: The hover's content
    :param range: An optional range is a range inside a text document
    that is used to visualize a hover, e.g. by changing the background color.
    :param range: An optional range is a range inside a text document
    that is used to visualize a hover, e.g. by changing the background color.
    """
    contents: Union[MarkedString, list[MarkedString], MarkupContent]
    range: Optional[Range]


HoverResult = Optional[HoverResult]


class SymbolKind(Enum):
    File = 1
    Module = 2
    Namespace = 3
    Package = 4
    Class = 5
    Method = 6
    Property = 7
    Field = 8
    Constructor = 9
    Enum = 10
    Interface = 11
    Function = 12
    Variable = 13
    Constant = 14
    String = 15
    Number = 16
    Boolean = 17
    Array = 18
    Object = 19
    Key = 20
    Null = 21
    EnumMember = 22
    Struct = 23
    Event = 24
    Operator = 25
    TypeParameter = 26


class SymbolTag(Enum):
    Deprecated = 1


class DocumentSymbol(BaseModel):
    """
    :param name: The name of this symbol. Will be displayed in the user interface and therefore must not be
    an empty string or a string only consisting of white spaces.
    :param detail: More detail for this symbol, e.g the signature of a function. If not provided the
    name is used.
    :param kind: The kind of this symbol.
    :param tags: Tags for this document symbol.
    :param range: The range enclosing this symbol not including leading/trailing whitespace but everything else
    like comments. This information is typically used to determine if the clients cursor is inside the symbol
    to reveal in the symbol in the UI.
    :param selectionRange: The range that should be selected and revealed when this symbol is being picked, e.g the
    name of a function. Must be contained by the `range`.
    :param children: Children of this symbol, e.g. properties of a class.
    """
    name: str
    detail: Optional[str]
    kind: SymbolKind
    tags: Optional[list[SymbolTag]]
    range: Range
    selectionRange: Range
    children: Optional[list['DocumentSymbol']]


class SymbolInformation(BaseModel):
    """
    :param name: The name of this symbol.
    :param kind: The kind of this symbol.
    :param tags: Tags for this symbol.
    :param location: The location of this symbol.
    :param containerName: The name of the symbol containing this symbol.
    """
    name: str
    kind: SymbolKind
    tags: Optional[list[SymbolTag]]
    location: Location
    containerName: Optional[str]


SymbolResult = Union[list[DocumentSymbol], list[SymbolInformation], None]


class CompletionItemLabelDetails(BaseModel):
    """
    :param detail: An optional string which is rendered less prominently directly after
    {@link CompletionItem.label label}, without any spacing. Should be used for function
    signatures or type annotations.
    :param description: An optional string which is rendered less prominently after
    {@link CompletionItemLabelDetails.detail}. Should be used for fully qualified
    names or file path.
    """
    detail: Optional[str]
    description: Optional[str]


class CompletionItemKind(Enum):
    Text = 1
    Method = 2
    Function = 3
    Constructor = 4
    Field = 5
    Variable = 6
    Class = 7
    Interface = 8
    Module = 9
    Property = 10
    Unit = 11
    Value = 12
    Enum = 13
    Keyword = 14
    Snippet = 15
    Color = 16
    File = 17
    Reference = 18
    Folder = 19
    EnumMember = 20
    Constant = 21
    Struct = 22
    Event = 23
    Operator = 24
    TypeParameter = 25


class CompletionItemTag(Enum):
    Deprecated = 1


class InsertTextFormat(Enum):
    PlainText = 1
    Snippet = 2


class InsertTextMode(Enum):
    AsIs = 1
    AdjustIndentation = 2


class TextEdit(BaseModel):
    """
    :param range: The range of the text document to be manipulated. To insert
    text into a document create a range where start === end.
    :param newText: The string to be inserted. For delete operations use an
    empty string.
    """
    range: Range
    newText: str


class InsertReplaceEdit(BaseModel):
    """
    :param newText: The string to be inserted if the insert is requested.
    :param insert: The string to be inserted.
    :param replace: The range if the insert is requested
    """
    newText: str
    insert: Range
    replace: Range


class Command(BaseModel):
    """
    :param title: Title of the command, like `save`.
    :param command: The identifier of the actual command handler.
    :param arguments: Arguments that the command handler should be
    invoked with.
    """
    title: str
    command: str
    arguments: Optional[list[Any]]


class CompletionItem(BaseModel):
    """
    :param label: The label of this completion item. By default
    also the text that is inserted when selecting this completion.
    :param kind: The kind of this completion item. Based of the kind
    an icon is chosen by the editor. The standardized set of available
    values is defined in `CompletionItemKind`.
    :param tags: Tags for this completion item.
    :param detail: A human-readable string with additional information
    about this item, like type or symbol information.
    :param documentation: A human-readable string that represents a doc-comment.
    :param preselect: Select this item when showing.
    :param sortText: A string that should be used when comparing this item
    with other items. When `falsy` the label is used.
    :param filterText: A string that should be used when filtering a set of
    completion items. When `falsy` the label is used.
    :param insertText: A string that should be inserted into a document when
    selecting this completion. When `falsy` the label is used.
    :param insertTextFormat: The format of the insert text. The format applies
    to both the `insertText` property and the `newText` property of a provided
    `textEdit`. If omitted defaults to `InsertTextFormat.PlainText`.
    :param insertTextMode: How whitespace and indentation is handled during completion.
    :param textEdit: An edit which is applied to a document when selecting this completion.
    When an edit is provided the value of `insertText` is ignored.
    :param textEditText: The edit text used if the completion item is part of a CompletionList and
    CompletionList defines an item default for the text edit range.
    :param additionalTextEdits: An optional array of additional text edits that are applied when
    selecting this completion. Edits must not overlap with the main edit nor with themselves.
    :param commitCharacters: An optional set of characters that when pressed while this completion is active will accept
    it first and then type that character. *Note* that all commit characters should have `length=1` and that superfluous
    characters will be ignored.
    :param command: An optional command that is executed *after* inserting this completion. *Note* that
    additional modifications to the current document should be described with the additionalTextEdits-property.
    :param data: A data entry field that is preserved on a completion item between
    a completion and a completion resolve request.
    """
    label: str
    labelDetails: Optional[CompletionItemLabelDetails]
    kind: Optional[CompletionItemKind]
    tags: Optional[list[CompletionItemTag]]
    detail: Optional[str]
    documentation: Optional[Union[str, MarkupContent]]
    preselect: Optional[bool]
    sortText: Optional[str]
    filterText: Optional[str]
    insertText: Optional[str]
    insertTextFormat: Optional[InsertTextFormat]
    insertTextMode: Optional[InsertTextMode]
    textEdit: Optional[Union[TextEdit, InsertReplaceEdit]]
    textEditText: Optional[str]
    additionalTextEdits: Optional[list[TextEdit]]
    commitCharacters: Optional[list[str]]
    command: Optional[Command]
    data: Optional[Any]


class CompletionList(BaseModel):
    """
    :param isIncomplete: This list it not complete. Further typing should result in recomputing
    this list.
    :param itemDefaults: The default text edit for inserting a completion item. This must be
    :param items: The completion items.
    """
    isIncomplete: bool
    itemDefaults: Optional[JSON]
    items: list[CompletionItem]


CompletionResult = Union[list[CompletionItem], CompletionList, None]

WorkspaceFolderResult = list[WorkspaceFolder]


class Pp_empty(BaseModel):
    type: str = Literal['Pp_empty']


class Pp_string(BaseModel):
    type = Literal['Pp_string']
    value: str


class Pp_glue(BaseModel):
    type = Literal['Pp_glue']
    elements: list['Pp']


class Pp_box(BaseModel):
    type = Literal['Pp_box']
    box: Any
    content: 'Pp'


class Pp_tag(BaseModel):
    type = Literal['Pp_tag']
    tag: Any
    content: 'Pp'


class Pp_print_break(BaseModel):
    type = Literal['Pp_print_break']
    num_spaces: int
    indent: int


class Pp_force_newline(BaseModel):
    type = Literal['Pp_force_newline']


class Pp_comment(BaseModel):
    type = Literal['Pp_comment']
    value: list[str]


Pp = Annotated[
    Union[Pp_empty, Pp_string, Pp_glue, Pp_box, Pp_tag, Pp_print_break, Pp_force_newline, Pp_comment],
    Field(discriminator='type')
]


class Hyp(BaseModel):
    names: list[Pp]
    def_: Field(Optional[Pp], alias='def')
    ty: Pp


class Goal(BaseModel):
    hyps: list[Hyp]
    ty: JSON


class GoalConfig(BaseModel):
    goals: list[Goal]
    stack: list[list[Goal]]  # TODO: should be [Goal<Pp>[], Goal<Pp>[]][]??
    bullet: Optional[JSON]
    shelf: list[Goal]
    given_up: list[Goal]


class Message(BaseModel):
    range: Optional[Range]
    level: int
    text: JSON


class Obligation(BaseModel):
    name: Id
    loc: Optional[Loc]
    status: tuple[bool, Any]
    solved: bool


class ObligationsView(BaseModel):
    opaque: bool
    remaining: int
    obligations: list[Obligation]


class ProgramInfo(BaseModel):
    id: Id
    obligations: ObligationsView


class GoalResult(BaseModel):
    textDocument: VersionedTextDocumentIdentifier
    position: Position
    goals: Optional[GoalConfig]
    messages: Union[list[JSON], list[Message]]
    error: Optional[JSON]
    program: Optional[list[ProgramInfo]]


class CompletionStatus(BaseModel):
    """
    :param status: The status of the document.
    :param range: The range of the document.
    """
    status: Literal['Yes', 'Stopped', 'Failed']
    range: Range


# Implementation-specific span information, for now the serialized Ast if present.
SpanInfo = Any


class RangedSpan(BaseModel):
    """
    :param range: The range of the span.
    :param span: The span info.
    """
    range: Range
    span: Optional[SpanInfo]


class FlecheDocumentResult(BaseModel):
    """
    :param spans: The spans of the document.
    :param completed: The completion status of the document.
    """
    spans: list[RangedSpan]
    completed: CompletionStatus


if __name__ == '__main__':
    # test LogTrace on:
    # {
    #   "jsonrpc": "2.0",
    #   "method": "$/logTrace",
    #   "params": { "message": "[cache]: cache hit rate: 0.00" }
    # }

    import json

    result = {
        "jsonrpc": "2.0",
        "method": "$/logTrace",
        "params": {"message": "[cache]: cache hit rate: 0.00"}
    }

    trace_result = LogTraceParams(**result['params'])
    print(trace_result.dict())
    print(result['params'])

    result = {
        "jsonrpc": "2.0",
        "method": "$/coq/fileProgress",
        "params": {
            "textDocument": {
                "uri": "file:///Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug/debug_simple_arith/SimpleArith.v",
                "version": 1
            },
            "processing": [
                {
                    "range": {
                        "start": {"line": 2, "character": 18, "offset": 41},
                        "end": {"line": 6, "character": 4, "offset": 84}
                    },
                    "kind": 1
                }
            ]
        }
    }

    file_progress_result = CoqFileProgressParams(**result['params'])
    print(file_progress_result.dict())
    print(result['params'])
