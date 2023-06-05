from enum import Enum
from typing import Any, Optional, Union

from pydantic import BaseModel

JSON = dict[str, Any]
Params = Union[JSON, list[Any]]
Id = Union[int, str]


class CancelParams(BaseModel):
    """
    The parameters sent with $/cancelRequest

    :param id: The request id to cancel.
    """
    id: Id


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
    code: int  # TODO: use enum
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
