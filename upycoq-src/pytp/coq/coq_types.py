"""
Implements the custom message/data types for coqlsp.
"""
import enum
from typing import Optional, Any, Union

import attrs
import lsprotocol.types
from lsprotocol.types import VersionedTextDocumentIdentifier, Position, Range


@enum.unique
class PpFormat(enum.Enum):
    Pp = 'Pp'
    Str = 'Str'


@attrs.define
class GoalRequest:
    text_document: VersionedTextDocumentIdentifier = attrs.field()
    """The text document."""
    position: Position = attrs.field()
    """The position inside the text document."""
    pp_format: Optional[PpFormat] = attrs.field(default=None)
    """The format of the response. If `None`, the server will use the default"""


@attrs.define
class Hyp:
    names: list[str] = attrs.field()
    ty: str = attrs.field()
    # use def_ to avoid reserved keyword, lsprotocol.converters.get_converter() will convert it to/from def in json
    def_: Optional[str] = attrs.field(default=None)


@attrs.define
class Goal:
    info: Any = attrs.field()  # TODO: figure out what this is
    hyps: list[Hyp] = attrs.field()
    ty: str = attrs.field()


@attrs.define
class GoalConfig:
    goals: list[Goal] = attrs.field()
    stack: list[tuple[list[Goal], list[Goal]]] = attrs.field()
    shelf: list[Goal] = attrs.field()
    given_up: list[Goal] = attrs.field(alias='given_up')
    bullet: Optional[str] = attrs.field(default=None)


@attrs.define
class Message:
    level: int = attrs.field()
    text: str = attrs.field()
    range: Optional[Range] = attrs.field(default=None)


@attrs.define
class GoalAnswer:
    textDocument: VersionedTextDocumentIdentifier = attrs.field()
    position: Position = attrs.field()
    messages: list[Message] = attrs.field()
    goals: Optional[GoalConfig] = attrs.field(default=None)
    error: Optional[str] = attrs.field(default=None)
    # program: Optional[dict[str, str]] = attrs.field(default=None)
    program: list[Any] = attrs.field(default=None)


@enum.unique
class CoqFileProgressKind(enum.Enum):
    Processing = 1
    FatalError = 2

@attrs.define
class Position2:
    line: int = attrs.field()
    character: int = attrs.field()
    offset: int = attrs.field()


@attrs.define
class Span:
    start: Position2 = attrs.field()
    end: Position2 = attrs.field()


@attrs.define
class CoqFileProgressProcessingInfo:
    range: Span = attrs.field()
    """Range for which the processing info was reported."""
    kind: Optional[int] = attrs.field(default=None)
    """Kind of progress that was reported."""


@attrs.define
class CoqFileProgressParams:
    textDocument: VersionedTextDocumentIdentifier = attrs.field()
    """The text document to which this progress notification applies."""
    processing: list[CoqFileProgressProcessingInfo] = attrs.field()
    """Array containing the parts of the file which are still being processed.
    The array should be empty if and only if the server is finished processing."""


@attrs.define
class FlecheDocumentParams:
    textDocument: VersionedTextDocumentIdentifier = attrs.field()


@enum.unique
class CompletionStatusKind(enum.Enum):
    Yes = 'Yes'
    Stopped = 'Stopped'
    Failed = 'Failed'


@attrs.define
class CompletionStatus:
    status: list[CompletionStatusKind] = attrs.field()
    range: Range = attrs.field()


SpanInfo = Any


@attrs.define
class RangedSpan:
    range: Span = attrs.field()
    span: Optional[SpanInfo] = attrs.field(default=None)


@attrs.define
class FlecheDocument:
    spans: list[RangedSpan] = attrs.field()
    completed: CompletionStatus = attrs.field()


@attrs.define
class FlecheSaveParams:
    textDocument: VersionedTextDocumentIdentifier = attrs.field()


@attrs.define
class SentencePerfParams:
    loc: dict[str, str] = attrs.field()
    time: float = attrs.field()
    mem: float = attrs.field()


@attrs.define
class DocumentPerfParams:
    summary: str = attrs.field()
    timings: list[SentencePerfParams] = attrs.field()


@attrs.define
class CoqFileProgressNotification:
    """The `$/coq/fileProgress` notification is sent from the server to the client to
    report progress in processing a file.

    @sine 0.1.1
    """

    params: CoqFileProgressParams = attrs.field()
    method: str = attrs.field(
        validator=attrs.validators.in_(['$/coq/fileProgress']),
        default='$/coq/fileProgress',
    )
    """The method to be invoked."""
    jsonrpc: str = attrs.field(default='2.0')


@attrs.define
class ProofGoalsRequest:
    """The `proof/goals` request is sent from the client to the server to get the goals at a given position.

    @since 0.1.0
    """
    id: int = attrs.field()
    params: GoalRequest = attrs.field()
    method: str = attrs.field(
        validator=attrs.validators.in_(['proof/goals']), default='proof/goals'
    )
    """The method to be invoked."""
    jsonrpc: str = attrs.field(default='2.0')


@attrs.define
class ProofGoalResponse:
    id: int = attrs.field()
    result: GoalAnswer = attrs.field()
    jsonrpc: str = attrs.field(default='2.0')


@attrs.define
class CoqGetDocumentRequest:
    """The `coq/getDocument` request is sent from the client to the server to get a serialized version of
    the Flèche document. It is modelled after LSP's standard `textDocument/documentSymbol`, but returns
    instead the full document contents as understood by Flèche.

    Caveats: Flèche notion of document is evolving, in particular you should not assume that the document
    will remain a list, but it will become a tree at some point.

    @since 0.1.6
    """
    id: int = attrs.field()
    params: FlecheDocumentParams = attrs.field()
    method: str = attrs.field(
        validator=attrs.validators.in_(['coq/getDocument']), default='coq/getDocument'
    )
    """The method to be invoked."""
    jsonrpc: str = attrs.field(default='2.0')


@attrs.define
class CoqGetDocumentResponse:
    id: int = attrs.field()
    result: FlecheDocument = attrs.field()
    jsonrpc: str = attrs.field(default='2.0')


@attrs.define
class CoqSaveRequest:
    """The `coq/saveVo` request is sent from the client to the server to save a file to disk.

    @since 0.1.6
    """
    id: int = attrs.field()
    params: FlecheSaveParams = attrs.field()
    method: str = attrs.field(
        validator=attrs.validators.in_(['coq/saveVo']), default='coq/saveVo'
    )
    """The method to be invoked."""
    jsonrpc: str = attrs.field(default='2.0')


@attrs.define
class CoqFilePerfDataNotification:
    """The $/coq/filePerfData notification is sent from the server to the client when
    file checking completes, and includes information about execution hotspots and
    memory use by sentences.

    @since 0.1.7
    """

    params: DocumentPerfParams = attrs.field()
    method: str = attrs.field(
        validator=attrs.validators.in_(['$/coq/filePerfData']),
        default='$/coq/filePerfData',
    )
    """The method to be invoked."""
    jsonrpc: str = attrs.field(default='2.0')


@enum.unique
class UnicodeCompletion(enum.Enum):
    OFF = 'off'
    INTERNAL_SMALL = 'internal_small'
    NORMAL = 'normal'
    EXTENDED = 'extended'


@attrs.define
class CoqInitializationOptions:
    mem_stats: bool = attrs.field(default=False)
    """[mem_stats] Call [Obj.reachable_words] for every sentence. This is
    very slow and not very useful, so disabled by default"""
    gc_quick_stats: bool = attrs.field(default=True)
    """[gc_quick_stats] Show the diff of [Gc.quick_stats] data for each sentence"""
    client_version: str = attrs.field(default='any')
    eager_diagnostics: bool = attrs.field(default=False)
    """Send diagnostics as document is processed; if false, diagnostics are
    only sent when Coq finishes processing the file"""
    goal_after_tactic: bool = attrs.field(default=False)
    """When showing goals and the cursor is in a tactic, if false, show
    goals before executing the tactic, if true, show goals after"""
    show_coq_info_messages: bool = attrs.field(default=True)  # when True, overrides show_notices_as_diagnostics
    """Show Coq's "Info" messages as diagnostics, such as 'foo has been defined.'
    and miscellaneous operational messages."""
    show_notices_as_diagnostics: bool = attrs.field(default=False)
    """Show Coq's "Notice" messages as diagnostics, such as `About` and `Search` output."""
    admit_on_bad_qed: bool = attrs.field(default=True)
    """If a `Qed.` command fails, admit the proof automatically."""
    debug: bool = attrs.field(default=False)
    """Enable debug on Coq side, including backtraces"""
    unicode_completion: UnicodeCompletion = attrs.field(default=UnicodeCompletion.NORMAL)
    """Enable Server-Side Unicode Completion. Coq-lsp provides two character sets,
    a regular one, and an extended one with more than 1000 symbols."""
    max_errors: int = attrs.field(default=150)
    """Maximum number of errors per file, after that, coq-lsp will stop checking the file."""
    pp_type: int = attrs.field(default=0)
    """Pretty-printing type in Info Panel Request, 0 = string; 1 = Pp.t; 2 = Coq Layout Engine (experimental)"""
    show_stats_on_hover: bool = attrs.field(default=False)
    """Show timing and memory stats for a sentence on hover."""
    # TODO: uncomment in version 0.1.7
    # verbosity: int = attrs.field(default=2)
    # pp_json: bool = attrs.field(default=False)


# Requests
PROOF_GOALS = 'proof/goals'
COQ_GET_DOCUMENT = 'coq/getDocument'
COQ_SAVE = 'coq/saveVo'
# Notifications
COQ_FILE_PROGRESS = '$/coq/fileProgress'
COQ_FILE_PERF_DATA = '$/coq/filePerfData'

METHOD_TO_TYPES = lsprotocol.types.METHOD_TO_TYPES.copy()
COQ_METHOD_TO_TYPES = {
    # Requests
    PROOF_GOALS: (ProofGoalsRequest, ProofGoalResponse, GoalRequest, None),
    COQ_GET_DOCUMENT: (
        CoqGetDocumentRequest,
        CoqGetDocumentResponse,
        FlecheDocumentParams,
        None
    ),
    COQ_SAVE: (CoqSaveRequest, None, FlecheSaveParams, None),
    # Notifications
    COQ_FILE_PROGRESS: (CoqFileProgressNotification, None, CoqFileProgressParams, None),
    COQ_FILE_PERF_DATA: (CoqFilePerfDataNotification, None, DocumentPerfParams, None),
}
METHOD_TO_TYPES.update(COQ_METHOD_TO_TYPES)

COQ_MESSAGE_TYPES = {k: v[0] for k, v in METHOD_TO_TYPES.items()}
COQ_RESPONSE_TYPES = {k: v[1] for k, v in METHOD_TO_TYPES.items()}

REQUESTS = Union[lsprotocol.types.REQUESTS, ProofGoalsRequest, CoqGetDocumentRequest, CoqSaveRequest]
RESPONSES = Union[lsprotocol.types.RESPONSES, ProofGoalResponse, CoqGetDocumentResponse]
NOTIFICATIONS = Union[lsprotocol.types.NOTIFICATIONS, CoqFileProgressNotification, CoqFilePerfDataNotification]
ResponseErrorMessage = lsprotocol.types.ResponseErrorMessage

MESSAGE_TYPES = Union[REQUESTS, RESPONSES, NOTIFICATIONS, ResponseErrorMessage]

ALL_TYPES_MAP = lsprotocol.types.ALL_TYPES_MAP
COQ_TYPES_MAP = {
    'PpFormat': PpFormat,
    'GoalRequest': GoalRequest,
    'Hyp': Hyp,
    'Goal': Goal,
    'GoalConfig': GoalConfig,
    'Message': Message,
    'GoalAnswer': GoalAnswer,
    'CoqFileProgressKind': CoqFileProgressKind,
    'CoqFileProgressProcessingInfo': CoqFileProgressProcessingInfo,
    'CoqFileProgressParams': CoqFileProgressParams,
    'FlecheDocumentParams': FlecheDocumentParams,
    'CompletionStatusKind': CompletionStatusKind,
    'CompletionStatus': CompletionStatus,
    'SpanInfo': SpanInfo,
    'RangedSpan': RangedSpan,
    'FlecheDocument': FlecheDocument,
    'FlecheSaveParams': FlecheSaveParams,
    'SentencePerfParams': SentencePerfParams,
    'DocumentPerfParams': DocumentPerfParams,
    'CoqFilePerfDataNotification': CoqFilePerfDataNotification,
    'ProofGoalsRequest': ProofGoalsRequest,
    'ProofGoalResponse': ProofGoalResponse,
    'CoqGetDocumentRequest': CoqGetDocumentRequest,
    'CoqGetDocumentResponse': CoqGetDocumentResponse,
    'CoqSaveRequest': CoqSaveRequest,
    'CowFilePerfDataNotification': CoqFilePerfDataNotification,
}
ALL_TYPES_MAP.update(COQ_TYPES_MAP)

lsprotocol.types._SPECIAL_CLASSES.extend([
    ProofGoalsRequest,
    ProofGoalResponse,
    CoqGetDocumentRequest,
    CoqGetDocumentResponse,
    CoqSaveRequest,
    CoqFileProgressNotification,
    CoqFilePerfDataNotification,
])

lsprotocol.types._SPECIAL_PROPERTIES.extend([
    'ProofGoalsRequest.jsonrpc',
    'ProofGoalsRequest.method',
    'ProofGoalResponse.jsonrpc',
    'ProofGoalResponse.method',
    'CoqGetDocumentRequest.jsonrpc',
    'CoqGetDocumentRequest.method',
    'CoqGetDocumentResponse.jsonrpc',
    'CoqGetDocumentResponse.method',
    'CoqSaveRequest.jsonrpc',
    'CoqSaveRequest.method',
    'CoqFileProgressNotification.jsonrpc',
    'CoqFileProgressNotification.method',
    'CoqFilePerfDataNotification.jsonrpc',
    'CoqFilePerfDataNotification.method',
])

lsprotocol.types._MESSAGE_DIRECTION.update({
    # Requests
    PROOF_GOALS: 'clientToServer',
    COQ_GET_DOCUMENT: 'clientToServer',
    COQ_SAVE: 'clientToServer',
    # Notifications
    COQ_FILE_PROGRESS: 'serverToClient',
    COQ_FILE_PERF_DATA: 'serverToClient',
})
