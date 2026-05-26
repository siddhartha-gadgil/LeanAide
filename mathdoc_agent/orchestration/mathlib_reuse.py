"""LeanSearch-backed reuse of existing Mathlib declarations."""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path
from typing import Iterable

from mathdoc_agent.mathagents.leansearch import (
    LeanSearchError,
    LeanSearchResult,
    lookup_theorems,
)
from mathdoc_agent.models.base import DocumentKind
from mathdoc_agent.models.document import DocumentNode, MathDocument
from mathdoc_agent.models.payloads import DefinitionData
from mathdoc_agent.orchestration.worklist import kind_key


DEFINITION_LIKE_KINDS = {
    "abbrev",
    "class",
    "def",
    "definition",
    "inductive",
    "instance",
    "structure",
}

IGNORABLE_NAME_TOKENS = {
    "a",
    "an",
    "add",
    "additive",
    "abelian",
    "function",
    "group",
    "is",
    "map",
    "multiplicative",
    "predicate",
    "property",
    "subgroup",
    "the",
}

_LEANSEARCH_DEFINITION_QUERY_CACHE: dict[str, list[LeanSearchResult] | None] = {}
_PERSISTENT_CACHE_LOADED = False


def _ascii_words(value: str) -> list[str]:
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    return [
        word
        for word in re.split(r"[^A-Za-z0-9]+", value)
        if word
    ]


def lean_identifier_from_text(value: str, *, fallback: str = "generated_name") -> str:
    """Return a deterministic Lean-style ASCII identifier from a label or id."""
    words = _ascii_words(value)
    if not words:
        words = _ascii_words(fallback)
    if not words:
        return "generated_name"
    identifier = "_".join(word.lower() for word in words)
    if not identifier[0].isalpha():
        identifier = f"n_{identifier}"
    return identifier


def _name_tokens(name: str) -> set[str]:
    return {token.lower() for token in _ascii_words(name)}


def _meaningful_name_tokens(name: str) -> set[str]:
    return _name_tokens(name) - IGNORABLE_NAME_TOKENS


def _result_kind(result: LeanSearchResult) -> str:
    return (result.kind or "").strip().lower()


def _is_definition_like(result: LeanSearchResult) -> bool:
    kind = _result_kind(result)
    return kind in DEFINITION_LIKE_KINDS or any(
        marker in kind for marker in DEFINITION_LIKE_KINDS
    )


def _name_is_compatible(
    result_name: str,
    requested_name: str | None,
    definition_text: str,
) -> bool:
    if not requested_name:
        return True
    requested = requested_name.strip()
    if not requested:
        return True
    result_tail = result_name.split(".")[-1]
    if result_tail.casefold() == requested.casefold():
        return True
    requested_tokens = _name_tokens(requested)
    result_tokens = _name_tokens(result_tail)
    definition_tokens = _name_tokens(definition_text)
    if not requested_tokens:
        return True
    if "subgroup" in requested_tokens and result_tokens & definition_tokens:
        return True
    meaningful_requested = _meaningful_name_tokens(requested)
    if meaningful_requested and meaningful_requested.issubset(result_tokens):
        return True
    return requested_tokens.issubset(result_tokens)


def _type_is_compatible(result: LeanSearchResult, definition_text: str) -> bool:
    text = definition_text.casefold()
    result_type = result.type or ""

    if "subgroup" in text:
        return "Subgroup" in result_type
    if "quotient" in text or "abelianization" in text:
        return True
    if "for elements" in text and "commutator" in text:
        return (
            "Subgroup" not in result_type
            and "Set " not in result_type
            and ("→ G → G" in result_type or "Bracket G G" in result_type)
        )
    return True


def _cache_key(query: str) -> str:
    return " ".join(query.strip().split())


def _cache_path() -> Path:
    value = os.environ.get("MATHDOC_AGENT_LEANSEARCH_DEFINITION_CACHE")
    if value:
        return Path(value)
    return Path(".cache") / "mathdoc_agent" / "leansearch_definition_cache.json"


def _seed_cache_path() -> Path | None:
    value = os.environ.get("MATHDOC_AGENT_LEANSEARCH_DEFINITION_SEED")
    return Path(value) if value else None


def _result_to_json(result: LeanSearchResult) -> dict[str, str]:
    return {
        key: value
        for key, value in {
            "name": result.name,
            "type": result.type,
            "docstring": result.docstring,
            "doc_url": result.doc_url,
            "kind": result.kind,
        }.items()
        if value is not None
    }


def _result_from_json(value: object) -> LeanSearchResult | None:
    if not isinstance(value, dict):
        return None
    name = value.get("name")
    if not isinstance(name, str) or not name.strip():
        return None
    return LeanSearchResult(
        name=name,
        type=value.get("type") if isinstance(value.get("type"), str) else None,
        docstring=(
            value.get("docstring")
            if isinstance(value.get("docstring"), str)
            else None
        ),
        doc_url=value.get("doc_url") if isinstance(value.get("doc_url"), str) else None,
        kind=value.get("kind") if isinstance(value.get("kind"), str) else None,
    )


def _load_cache_file(path: Path) -> dict[str, list[LeanSearchResult] | None]:
    if not path.is_file():
        return {}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print(
            f"[mathdoc_agent] could not read LeanSearch definition cache {path}: {error}",
            file=sys.stderr,
            flush=True,
        )
        return {}
    if not isinstance(raw, dict):
        return {}
    loaded: dict[str, list[LeanSearchResult] | None] = {}
    for query, value in raw.items():
        if not isinstance(query, str):
            continue
        key = _cache_key(query)
        if value is None:
            loaded[key] = None
            continue
        if not isinstance(value, list):
            continue
        results = [
            result
            for item in value
            if (result := _result_from_json(item)) is not None
        ]
        loaded[key] = results
    return loaded


def _load_persistent_definition_cache() -> None:
    global _PERSISTENT_CACHE_LOADED
    if _PERSISTENT_CACHE_LOADED:
        return
    _PERSISTENT_CACHE_LOADED = True
    seed_path = _seed_cache_path()
    if seed_path is not None:
        _LEANSEARCH_DEFINITION_QUERY_CACHE.update(_load_cache_file(seed_path))
    _LEANSEARCH_DEFINITION_QUERY_CACHE.update(_load_cache_file(_cache_path()))


def _write_persistent_definition_cache() -> None:
    path = _cache_path()
    payload = {
        query: None
        if results is None
        else [_result_to_json(result) for result in results]
        for query, results in sorted(_LEANSEARCH_DEFINITION_QUERY_CACHE.items())
        if results is not None
    }
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    except OSError as error:
        print(
            f"[mathdoc_agent] could not write LeanSearch definition cache {path}: {error}",
            file=sys.stderr,
            flush=True,
        )


def _definition_query_results(
    query: str,
    *,
    num_results: int,
    timeout: float,
) -> list[LeanSearchResult] | None:
    _load_persistent_definition_cache()
    key = _cache_key(query)
    if key in _LEANSEARCH_DEFINITION_QUERY_CACHE:
        return _LEANSEARCH_DEFINITION_QUERY_CACHE[key]
    try:
        results = lookup_theorems(query, num_results=num_results, timeout=timeout)
    except (LeanSearchError, ValueError, OSError) as error:
        print(
            f"[mathdoc_agent] leansearch definition lookup failed for {query!r}: {error}",
            file=sys.stderr,
            flush=True,
        )
        _LEANSEARCH_DEFINITION_QUERY_CACHE[key] = None
        return None
    _LEANSEARCH_DEFINITION_QUERY_CACHE[key] = results
    _write_persistent_definition_cache()
    return results


def _definition_queries(data: DefinitionData, text: str) -> Iterable[str]:
    term = (data.term or "").strip()
    definition = (data.definitions or text or "").strip()
    if term and definition:
        yield f"Mathlib definition named {term}: {definition}"
    if term:
        yield f"Mathlib declaration or definition named {term}"
        yield term
    if definition:
        yield definition


def find_mathlib_definition(
    data: DefinitionData,
    text: str,
    *,
    num_results: int = 5,
    timeout: float = 10.0,
) -> LeanSearchResult | None:
    """Return a conservative Mathlib declaration match for a definition."""
    requested_name = data.term
    for query in _definition_queries(data, text):
        results = _definition_query_results(
            query,
            num_results=num_results,
            timeout=timeout,
        )
        if results is None:
            continue
        match = next(
            (
                result
                for result in results
                if _is_definition_like(result)
                and _name_is_compatible(result.name, requested_name, text)
                and _type_is_compatible(result, text)
            ),
            None,
        )
        if match is not None:
            return match
    return None


def _record_mathlib_definition_on_node(node: DocumentNode) -> DocumentNode:
    if kind_key(node.kind) != DocumentKind.definition.value:
        return node
    try:
        data = DefinitionData.model_validate(node.data)
    except Exception:
        return node
    if data.lean_name:
        return node
    match = find_mathlib_definition(data, node.text)
    if match is None:
        return node
    updated = data.model_copy(
        update={
            "lean_name": match.name,
            "mathlib_kind": match.kind,
            "mathlib_type": match.type,
        }
    )
    return node.model_copy(
        update={
            "data": updated.model_dump(exclude_none=True),
            "notes": node.notes
            + [f"Reusing existing Mathlib declaration {match.name} for definition."],
        }
    )


def record_mathlib_definitions(document: MathDocument) -> MathDocument:
    """Annotate definition nodes that should reuse existing Mathlib names."""

    def visit(node: DocumentNode) -> DocumentNode:
        children = [visit(child) for child in node.children]
        node = node.model_copy(update={"children": children})
        return _record_mathlib_definition_on_node(node)

    return document.model_copy(update={"root": visit(document.root)})
