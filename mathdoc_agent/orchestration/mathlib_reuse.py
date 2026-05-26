"""LeanSearch-backed reuse of existing Mathlib declarations."""

from __future__ import annotations

import re
import sys
from typing import Iterable

from mathdoc_agent.mathagents.leansearch import LeanSearchError, LeanSearchResult, lookup_theorems
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
    "structure",
}

_MATHLIB_DEFINITION_CACHE: dict[tuple[str, str], LeanSearchResult | None] = {}


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
        cache_key = (requested_name or "", query)
        if cache_key in _MATHLIB_DEFINITION_CACHE:
            cached = _MATHLIB_DEFINITION_CACHE[cache_key]
            if cached is not None:
                return cached
            continue
        try:
            results = lookup_theorems(query, num_results=num_results, timeout=timeout)
        except (LeanSearchError, ValueError, OSError) as error:
            print(
                f"[mathdoc_agent] leansearch definition lookup failed for {query!r}: {error}",
                file=sys.stderr,
                flush=True,
            )
            _MATHLIB_DEFINITION_CACHE[cache_key] = None
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
        _MATHLIB_DEFINITION_CACHE[cache_key] = match
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
