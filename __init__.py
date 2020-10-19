import datetime
import json
from decimal import Decimal
from io import StringIO
from typing import *

from .sqlserver_handler import SqlServerHandler


def ndjson_encode(data: Iterable[Dict[str, Any]]) -> StringIO:
    """
    Encode a collection of python dictiories to NDJSON

    Raises TypeError if a data value cannot be encoded.

    :param data: Iterable[Dict[str, Any]], the data to encode
    :return: StringIO, the NDJSON encoded data
    """

    def json_encoder(value):
        """
        Convert values that are not natively serializable to JSON.  Unknown
        value types raise a TypeError.
        """
        if isinstance(value, Decimal):
            return float(value)
        elif isinstance(value, (datetime.date, datetime.datetime)):
            return str(value)
        elif isinstance(value, bytes):
            try:
                return value.decode()
            except UnicodeDecodeError:
                return str(value)
        else:
            raise TypeError(
                f'Cannot serialize "{value}" of type {type(value)}'
            )

    encoded: List[str] = list()
    for entry in data:
        encoded.append(json.dumps(entry, default=json_encoder))
    return StringIO('\n'.join(encoded))


class_map = {
    "sqlserver": SqlServerHandler,
}
