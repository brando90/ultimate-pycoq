from dataclasses import dataclass
from typing import Any, Optional

import cattrs
import lsprotocol
from lsprotocol import converters


@dataclass
class LSPConfig:
    message_types: dict[str, Any]
    response_types: dict[str, Any]
    error_type: Any
    lsp_settings: Optional[dict[str, Any]] = None
    converter: cattrs.Converter = converters.get_converter()
    ignore_server_errors: bool = False  # TODO: ignore_server_errors
    logging: bool = False  # TODO: logging
    log_file: Optional[str] = None


MESSAGE_TYPES = {k: v[0] for k, v in lsprotocol.types.METHOD_TO_TYPES.items()}
RESPONSE_TYPES = {k: v[1] for k, v in lsprotocol.types.METHOD_TO_TYPES.items()}


def default_lsp_config():
    return LSPConfig(
        message_types=MESSAGE_TYPES,
        response_types=RESPONSE_TYPES,
        error_type=lsprotocol.types.ResponseErrorMessage,
        converter=converters.get_converter(),
    )
