"""LeanSearch-backed reuse of existing Mathlib declarations."""

from __future__ import annotations

import json
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Iterable

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
_LOCAL_DEFINITION_QUERY_CACHE: dict[str, list[LeanSearchResult] | None] = {}
_PERSISTENT_CACHE_LOADED = False
LOCAL_CACHE_VERSION = "local-v2"

DEFAULT_LOCAL_SIMILARITY_URL = "http://localhost:7654/run-sim-search"
DEFAULT_LOCAL_MATCH_MODEL = "gpt-5.5"


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


def _local_cache_path() -> Path:
    value = os.environ.get("MATHDOC_AGENT_LOCAL_DEFINITION_CACHE")
    if value:
        return Path(value)
    return Path(".cache") / "mathdoc_agent" / "local_definition_cache.json"


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
    _LOCAL_DEFINITION_QUERY_CACHE.update(_load_cache_file(_local_cache_path()))


def _write_cache(path: Path, cache: dict[str, list[LeanSearchResult] | None]) -> None:
    payload = {
        query: None
        if results is None
        else [_result_to_json(result) for result in results]
        for query, results in sorted(cache.items())
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
            f"[mathdoc_agent] could not write definition cache {path}: {error}",
            file=sys.stderr,
            flush=True,
        )


def _write_persistent_definition_cache() -> None:
    _write_cache(_cache_path(), _LEANSEARCH_DEFINITION_QUERY_CACHE)


def _write_persistent_local_cache() -> None:
    _write_cache(_local_cache_path(), _LOCAL_DEFINITION_QUERY_CACHE)


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


def _similarity_url() -> str:
    return os.environ.get(
        "MATHDOC_AGENT_LOCAL_SIMILARITY_URL",
        DEFAULT_LOCAL_SIMILARITY_URL,
    )


def _local_match_model() -> str:
    return os.environ.get(
        "MATHDOC_AGENT_LOCAL_LEANSEARCH_MODEL",
        DEFAULT_LOCAL_MATCH_MODEL,
    )


def _post_json(url: str, payload: dict[str, Any], *, timeout: float) -> dict[str, Any]:
    request = urllib.request.Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            data = json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, json.JSONDecodeError) as error:
        raise RuntimeError(f"local similarity request failed: {error}") from error
    if not isinstance(data, dict):
        raise RuntimeError(f"local similarity response must be an object, got {type(data).__name__}")
    return data


def _run_similarity_search(
    query: str,
    *,
    num_results: int,
    timeout: float,
) -> list[dict[str, Any]]:
    response = _post_json(
        _similarity_url(),
        {"num": num_results, "query": query, "descField": "docString"},
        timeout=timeout,
    )
    output = response.get("output")
    if not isinstance(output, list):
        raise RuntimeError("local similarity response has no output array")
    return [item for item in output if isinstance(item, dict)]


def _record_summary(record: dict[str, Any], index: int) -> dict[str, Any]:
    return {
        "index": index,
        "name": record.get("name"),
        "kind": record.get("kind"),
        "type": record.get("type"),
        "statement": record.get("statement"),
        "docString": record.get("docString"),
        "distance": record.get("distance"),
    }


def _candidate_to_result(record: dict[str, Any]) -> LeanSearchResult | None:
    name = record.get("name")
    if not isinstance(name, str) or not name.strip():
        return None
    kind = record.get("kind")
    if not isinstance(kind, str):
        statement = record.get("statement")
        if isinstance(statement, str):
            words = statement.split(maxsplit=2)
            if len(words) >= 2 and words[0] == "noncomputable":
                kind = words[1]
            elif words:
                kind = words[0]
            else:
                kind = None
        else:
            kind = None
    return LeanSearchResult(
        name=name,
        type=record.get("type") if isinstance(record.get("type"), str) else None,
        docstring=(
            record.get("docString")
            if isinstance(record.get("docString"), str)
            else None
        ),
        kind=kind,
    )


def _leansearch_result_summary(result: LeanSearchResult, index: int) -> dict[str, Any]:
    return {
        "index": index,
        "name": result.name,
        "kind": result.kind,
        "type": result.type,
        "docString": result.docstring,
    }


def _parse_llm_json(content: str) -> dict[str, Any]:
    text = content.strip()
    fenced = re.fullmatch(r"```(?:json)?\s*(.*?)\s*```", text, flags=re.DOTALL)
    if fenced:
        text = fenced.group(1).strip()
    data = json.loads(text)
    if not isinstance(data, dict):
        raise ValueError("LLM match response must be a JSON object")
    return data


def _llm_exact_match_index(
    query: str,
    candidates: list[dict[str, Any]],
    *,
    timeout: float,
) -> int | None:
    if not candidates:
        return None
    try:
        from openai import OpenAI
    except ImportError as error:
        raise RuntimeError("openai package is required for local LeanSearch matching") from error
    prompt = {
        "query": query,
        "candidates": candidates,
        "instructions": (
            "Decide whether any candidate is exactly the Lean/Mathlib declaration "
            "described by the query. Match mathematical content, declaration name, "
            "and type when available. Return JSON only with fields: "
            "match: boolean, index: integer or null, name: string or null, "
            "reason: string. If the query names a declaration, do not match a "
            "constructor, helper, theorem, namespace-qualified variant, or nearby "
            "API unless it is exactly that declaration or the same declaration "
            "under a known namespace."
        ),
    }
    client = OpenAI(api_key=os.environ["OPENAI_API_KEY"], timeout=timeout)
    response = client.chat.completions.create(
        model=_local_match_model(),
        messages=[
            {
                "role": "system",
                "content": (
                    "You identify exact Lean/Mathlib declaration matches. "
                    "Return only compact JSON."
                ),
            },
            {"role": "user", "content": json.dumps(prompt, ensure_ascii=False)},
        ],
        temperature=1,
    )
    content = response.choices[0].message.content or ""
    data = _parse_llm_json(content)
    if data.get("match") is not True:
        return None
    index = data.get("index")
    if not isinstance(index, int):
        return None
    return index


def _select_llm_match(
    query: str,
    results: list[LeanSearchResult],
    *,
    timeout: float,
) -> list[LeanSearchResult]:
    candidates = [
        _leansearch_result_summary(result, index)
        for index, result in enumerate(results)
    ]
    index = _llm_exact_match_index(query, candidates, timeout=timeout)
    if index is None or index < 0 or index >= len(results):
        return []
    return [results[index]]


def _local_definition_query_results(
    query: str,
    *,
    num_results: int,
    timeout: float,
) -> list[LeanSearchResult] | None:
    _load_persistent_definition_cache()
    key = _cache_key(f"{LOCAL_CACHE_VERSION}: {query}")
    if key in _LOCAL_DEFINITION_QUERY_CACHE:
        return _LOCAL_DEFINITION_QUERY_CACHE[key]
    try:
        records = _run_similarity_search(
            query,
            num_results=max(num_results, 10),
            timeout=timeout,
        )
        candidates = [
            _record_summary(record, index)
            for index, record in enumerate(records[:10])
        ]
        index = _llm_exact_match_index(query, candidates, timeout=timeout)
    except Exception as error:
        print(
            f"[mathdoc_agent] local definition lookup failed for {query!r}: {error}",
            file=sys.stderr,
            flush=True,
        )
        _LOCAL_DEFINITION_QUERY_CACHE[key] = None
        return None
    if index is None or index < 0 or index >= len(records):
        _LOCAL_DEFINITION_QUERY_CACHE[key] = []
        _write_persistent_local_cache()
        return []
    result = _candidate_to_result(records[index])
    results = [] if result is None else [result]
    _LOCAL_DEFINITION_QUERY_CACHE[key] = results
    _write_persistent_local_cache()
    return results


def local_definition_lookup(
    query: str,
    *,
    num_results: int = 10,
    timeout: float = 60.0,
) -> list[LeanSearchResult]:
    """Run local similarity search plus LLM exact-match adjudication."""
    return _local_definition_query_results(
        query,
        num_results=num_results,
        timeout=timeout,
    ) or []


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
    use_local: bool = True,
    use_leansearch: bool = True,
) -> LeanSearchResult | None:
    """Return a conservative Mathlib declaration match for a definition."""
    requested_name = data.term

    def compatible_match(results: list[LeanSearchResult]) -> LeanSearchResult | None:
        return next(
            (
                result
                for result in results
                if _is_definition_like(result)
                and _name_is_compatible(result.name, requested_name, text)
                and _type_is_compatible(result, text)
            ),
            None,
        )

    for query in _definition_queries(data, text):
        if use_local:
            local_results = _local_definition_query_results(
                query,
                num_results=max(num_results, 10),
                timeout=max(timeout, 60.0),
            )
            if local_results is not None:
                match = compatible_match(local_results)
                if match is not None:
                    return match

        if not use_leansearch:
            continue

        leansearch_results = _definition_query_results(
            query,
            num_results=num_results,
            timeout=timeout,
        )
        if not leansearch_results:
            continue
        leansearch_results = _select_llm_match(
            query,
            leansearch_results,
            timeout=max(timeout, 60.0),
        )
        match = compatible_match(leansearch_results)
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
