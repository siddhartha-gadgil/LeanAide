"""Helpers for looking up Lean/Mathlib theorems with LeanSearch.

The request shape mirrors LeanSearchClient's `#leansearch "query"` command:
queries are strings ending in `.` or `?`, and the default endpoint receives a
POST body of the form `{"query": ["..."], "num_results": n}`.
"""

from __future__ import annotations

import json
import os
import ssl
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any


DEFAULT_LEANSEARCH_API_URL = "https://leansearch.net/search"
DEFAULT_USER_AGENT = "mathdoc_agent leansearch helper"
DEFAULT_LEANSEARCH_TIMEOUT_SECONDS = 10.0


class LeanSearchError(RuntimeError):
    """Raised when a LeanSearch request or response cannot be handled."""


@dataclass(frozen=True)
class LeanSearchResult:
    """One theorem or declaration returned by LeanSearch."""

    name: str
    type: str | None = None
    docstring: str | None = None
    doc_url: str | None = None
    kind: str | None = None

    @classmethod
    def from_leansearch_json(cls, item: Any) -> "LeanSearchResult | None":
        """Parse the result object used by LeanSearchClient."""
        if not isinstance(item, dict):
            return None
        result = item.get("result")
        if not isinstance(result, dict):
            return None
        name_value = result.get("name")
        if isinstance(name_value, list) and all(
            isinstance(part, str) for part in name_value
        ):
            name = ".".join(name_value)
        elif isinstance(name_value, str):
            name = name_value
        else:
            return None
        docstring = result.get("docstring")
        if docstring == "":
            docstring = None
        return cls(
            name=name,
            type=_optional_str(result.get("type")),
            docstring=_optional_str(docstring),
            doc_url=_optional_str(result.get("doc_url")),
            kind=_optional_str(result.get("kind")),
        )

    def as_check_command(self) -> str:
        """Return a Lean command that checks this declaration."""
        return f"#check {self.name}"


def _optional_str(value: Any) -> str | None:
    return value if isinstance(value, str) else None


def normalize_leansearch_query(query: str) -> str:
    """Return a query accepted by the `#leansearch` command syntax."""
    normalized = " ".join(query.strip().split())
    if not normalized:
        raise ValueError("LeanSearch query must be nonempty.")
    if normalized.endswith((".", "?")):
        return normalized
    return f"{normalized}."


def leansearch_command(query: str) -> str:
    """Return the corresponding Lean `#leansearch` command."""
    return f"#leansearch {json.dumps(normalize_leansearch_query(query))}"


def leansearch_payload(query: str, num_results: int = 6) -> dict[str, Any]:
    """Return the JSON payload used by LeanSearchClient for LeanSearch."""
    if num_results <= 0:
        raise ValueError("num_results must be positive.")
    return {
        "query": [normalize_leansearch_query(query)],
        "num_results": num_results,
    }


def _leansearch_api_url(api_url: str | None = None) -> str:
    return (
        api_url
        or os.environ.get("LEANSEARCHCLIENT_LEANSEARCH_API_URL")
        or DEFAULT_LEANSEARCH_API_URL
    )


def leansearch_timeout_seconds(timeout: float | None = None) -> float:
    """Return the explicit or configured remote LeanSearch timeout."""
    if timeout is not None:
        return timeout
    value = os.environ.get("MATHDOC_AGENT_LEANSEARCH_TIMEOUT_SECONDS")
    if value is None:
        return DEFAULT_LEANSEARCH_TIMEOUT_SECONDS
    try:
        configured = float(value)
    except ValueError:
        return DEFAULT_LEANSEARCH_TIMEOUT_SECONDS
    return configured if configured > 0 else DEFAULT_LEANSEARCH_TIMEOUT_SECONDS


def _https_context() -> ssl.SSLContext | None:
    try:
        import certifi
    except ImportError:
        return None
    return ssl.create_default_context(cafile=certifi.where())


def query_leansearch(
    query: str,
    *,
    num_results: int = 6,
    api_url: str | None = None,
    timeout: float | None = None,
    user_agent: str = DEFAULT_USER_AGENT,
) -> list[LeanSearchResult]:
    """Look up Lean/Mathlib declarations with the LeanSearch API.

    This performs the same LeanSearch lookup that `#leansearch "query"` performs
    in LeanSearchClient, but returns parsed Python objects for agent code.
    """
    payload = leansearch_payload(query, num_results)
    request_timeout = leansearch_timeout_seconds(timeout)
    request = urllib.request.Request(
        _leansearch_api_url(api_url),
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "accept": "application/json",
            "Content-Type": "application/json",
            "User-Agent": user_agent,
        },
        method="POST",
    )
    try:
        context = _https_context()
        if context is None:
            response_cm = urllib.request.urlopen(request, timeout=request_timeout)
        else:
            response_cm = urllib.request.urlopen(
                request,
                timeout=request_timeout,
                context=context,
            )
        with response_cm as response:
            response_data = response.read().decode("utf-8")
    except (urllib.error.URLError, TimeoutError, OSError) as error:
        raise LeanSearchError(f"LeanSearch request failed: {error}") from error

    try:
        data = json.loads(response_data)
    except json.JSONDecodeError as error:
        raise LeanSearchError(
            f"LeanSearch returned invalid JSON: {error}"
        ) from error

    return parse_leansearch_response(data)


def parse_leansearch_response(data: Any) -> list[LeanSearchResult]:
    """Parse the nested result array returned by LeanSearch."""
    if not isinstance(data, list):
        raise LeanSearchError(f"LeanSearch response must be a list, got {type(data).__name__}.")
    if not data:
        return []
    result_items = data[0] if isinstance(data[0], list) else data
    if not isinstance(result_items, list):
        raise LeanSearchError("LeanSearch response does not contain a result list.")
    return [
        result
        for item in result_items
        if (result := LeanSearchResult.from_leansearch_json(item)) is not None
    ]


def lookup_theorems(
    query: str,
    *,
    num_results: int = 6,
    api_url: str | None = None,
    timeout: float | None = None,
) -> list[LeanSearchResult]:
    """Alias for theorem lookup in Lean/Mathlib via LeanSearch."""
    return query_leansearch(
        query,
        num_results=num_results,
        api_url=api_url,
        timeout=timeout,
    )
