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
    leansearch_timeout_seconds,
    lookup_theorems,
    normalize_leansearch_query,
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

THEOREM_LIKE_KINDS = {"theorem", "lemma"}

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
_THEOREM_MATCH_QUERY_CACHE: dict[str, list[LeanSearchResult] | None] = {}
_PERSISTENT_CACHE_LOADED = False
_REMOTE_LEANSEARCH_FAILURES = 0
_REMOTE_LEANSEARCH_CIRCUIT_OPEN = False
LOCAL_CACHE_VERSION = "local-v3"
LOCAL_THEOREM_CACHE_VERSION = "local-theorem-v3"
THEOREM_MATCH_CACHE_VERSION = "theorem-match-v3"

DEFAULT_LOCAL_SIMILARITY_URL = "http://localhost:7654/run-sim-search"
DEFAULT_LOCAL_MATCH_MODEL = "gpt-5.5"
DEFAULT_LOCAL_LOOKUP_TIMEOUT_SECONDS = 60.0
DEFAULT_REMOTE_CIRCUIT_FAILURE_LIMIT = 1


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
    return normalize_leansearch_query(query)


def _env_flag(name: str, default: bool = True) -> bool:
    value = os.environ.get(name)
    if value is None:
        return default
    return value.strip().lower() not in {"0", "false", "no", "off"}


def _env_positive_float(name: str, default: float) -> float:
    value = os.environ.get(name)
    if value is None:
        return default
    try:
        parsed = float(value)
    except ValueError:
        return default
    return parsed if parsed > 0 else default


def _remote_circuit_failure_limit() -> int:
    value = os.environ.get("MATHDOC_AGENT_LEANSEARCH_CIRCUIT_FAILURES")
    if value is None:
        return DEFAULT_REMOTE_CIRCUIT_FAILURE_LIMIT
    try:
        parsed = int(value)
    except ValueError:
        return DEFAULT_REMOTE_CIRCUIT_FAILURE_LIMIT
    return max(1, parsed)


def _local_lookup_timeout_seconds(timeout: float | None = None) -> float:
    if timeout is not None:
        return timeout
    return _env_positive_float(
        "MATHDOC_AGENT_LOCAL_LEANSEARCH_TIMEOUT_SECONDS",
        DEFAULT_LOCAL_LOOKUP_TIMEOUT_SECONDS,
    )


def reset_leansearch_run_state() -> None:
    """Reset transient failures before processing a new document."""
    global _REMOTE_LEANSEARCH_CIRCUIT_OPEN, _REMOTE_LEANSEARCH_FAILURES

    _REMOTE_LEANSEARCH_FAILURES = 0
    _REMOTE_LEANSEARCH_CIRCUIT_OPEN = False
    for cache in (
        _LEANSEARCH_DEFINITION_QUERY_CACHE,
        _LOCAL_DEFINITION_QUERY_CACHE,
        _THEOREM_MATCH_QUERY_CACHE,
    ):
        failed_keys = [key for key, results in cache.items() if results is None]
        for key in failed_keys:
            cache.pop(key, None)


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


def _theorem_cache_path() -> Path:
    value = os.environ.get("MATHDOC_AGENT_THEOREM_MATCH_CACHE")
    if value:
        return Path(value)
    return Path(".cache") / "mathdoc_agent" / "theorem_match_cache.json"


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
    _THEOREM_MATCH_QUERY_CACHE.update(_load_cache_file(_theorem_cache_path()))


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


def _write_persistent_theorem_cache() -> None:
    _write_cache(_theorem_cache_path(), _THEOREM_MATCH_QUERY_CACHE)


def _remote_query_results(
    query: str,
    *,
    num_results: int,
    timeout: float | None = None,
) -> list[LeanSearchResult] | None:
    global _REMOTE_LEANSEARCH_CIRCUIT_OPEN, _REMOTE_LEANSEARCH_FAILURES

    _load_persistent_definition_cache()
    key = _cache_key(query)
    if key in _LEANSEARCH_DEFINITION_QUERY_CACHE:
        return _LEANSEARCH_DEFINITION_QUERY_CACHE[key]
    if _REMOTE_LEANSEARCH_CIRCUIT_OPEN:
        return None
    request_timeout = leansearch_timeout_seconds(timeout)
    try:
        results = lookup_theorems(
            query,
            num_results=num_results,
            timeout=request_timeout,
        )
    except (LeanSearchError, ValueError, OSError) as error:
        _REMOTE_LEANSEARCH_FAILURES += 1
        print(
            f"[mathdoc_agent] remote LeanSearch failed for {query!r}: {error}",
            file=sys.stderr,
            flush=True,
        )
        if _REMOTE_LEANSEARCH_FAILURES >= _remote_circuit_failure_limit():
            _REMOTE_LEANSEARCH_CIRCUIT_OPEN = True
            print(
                "[mathdoc_agent] remote LeanSearch circuit opened; "
                "remaining lookups in this run will use local search/cache only",
                file=sys.stderr,
                flush=True,
            )
        return None
    _REMOTE_LEANSEARCH_FAILURES = 0
    _LEANSEARCH_DEFINITION_QUERY_CACHE[key] = results
    _write_persistent_definition_cache()
    return results


def _definition_query_results(
    query: str,
    *,
    num_results: int,
    timeout: float | None = None,
) -> list[LeanSearchResult] | None:
    """Backward-compatible alias for cached remote declaration lookup."""
    return _remote_query_results(
        query,
        num_results=num_results,
        timeout=timeout,
    )


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
    except (urllib.error.URLError, TimeoutError, OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"local similarity request failed: {error}") from error
    if not isinstance(data, dict):
        raise RuntimeError(f"local similarity response must be an object, got {type(data).__name__}")
    return data


def _run_similarity_search(
    query: str,
    *,
    num_results: int,
    timeout: float,
    desc_field: str = "docString",
) -> list[dict[str, Any]]:
    response = _post_json(
        _similarity_url(),
        {"num": num_results, "query": query, "descField": desc_field},
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
            "described by the query. Match mathematical content and type, not merely "
            "topic or similar vocabulary. A name proposed in prose may be a generated "
            "local name, so accept a differently named canonical Mathlib declaration "
            "when its meaning and type are the same. Return JSON only with fields: "
            "match: boolean, index: integer or null, name: string or null, "
            "reason: string. Do not match a constructor, implementation helper, "
            "strictly weaker/stronger theorem, or nearby API."
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
    if index < 0 or index >= len(candidates):
        return None
    reported_name = data.get("name")
    candidate_name = candidates[index].get("name")
    if (
        isinstance(reported_name, str)
        and isinstance(candidate_name, str)
        and reported_name != candidate_name
    ):
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


def _is_theorem_like(result: LeanSearchResult) -> bool:
    name = result.name.strip()
    if not name:
        return False
    lowered_name = name.casefold()
    tail = lowered_name.split(".")[-1]
    if "noconfusion" in lowered_name or tail.startswith("inst"):
        return False
    kind = _result_kind(result)
    return not kind or kind in THEOREM_LIKE_KINDS


THEOREM_QUERY_STOPWORDS = {
    "a",
    "all",
    "an",
    "and",
    "any",
    "are",
    "be",
    "by",
    "for",
    "from",
    "if",
    "in",
    "is",
    "it",
    "of",
    "on",
    "or",
    "that",
    "the",
    "then",
    "to",
    "with",
}


def _search_tokens(value: str) -> set[str]:
    expanded = value
    symbolic_hints = [
        (r"≤|<=", " less equal "),
        (r"≥|>=", " greater equal "),
        (r"(?<![<>=])<(?![=])", " less "),
        (r"(?<![<>=])>(?![=])", " greater "),
        (r"\+\s*1\b", " successor "),
        (r"\^", " power "),
        (r"⁻¹", " inverse "),
    ]
    for pattern, hint in symbolic_hints:
        if re.search(pattern, expanded):
            expanded += hint

    aliases = {
        "inv": {"inverse"},
        "le": {"less", "equal"},
        "lt": {"less"},
        "mul": {"multiplication"},
        "nat": {"natural", "number"},
        "pow": {"power"},
        "succ": {"successor"},
        "zpow": {"integer", "power"},
    }
    tokens: set[str] = set()
    for raw_token in _ascii_words(expanded):
        token = raw_token.casefold()
        if len(token) <= 1 or token in THEOREM_QUERY_STOPWORDS:
            continue
        tokens.add(token)
        tokens.update(aliases.get(token, set()))
        if len(token) > 4 and token.endswith("s") and token != "less":
            tokens.add(token[:-1])
    return tokens


def _rerank_theorem_results(
    query: str,
    results: list[LeanSearchResult],
    *,
    limit: int,
) -> list[LeanSearchResult]:
    """Lexically rerank a broad semantic result set before LLM adjudication."""
    query_tokens = _search_tokens(query)
    if not query_tokens:
        return results[:limit]

    def score(index_result: tuple[int, LeanSearchResult]) -> tuple[int, int, int]:
        index, result = index_result
        name_tokens = _search_tokens(result.name.replace("_", " "))
        text_tokens = _search_tokens(
            " ".join(
                part
                for part in (result.type, result.docstring)
                if isinstance(part, str)
            )
        )
        name_overlap = len(query_tokens & name_tokens)
        text_overlap = len(query_tokens & text_tokens)
        return (name_overlap, text_overlap, -index)

    ranked = sorted(enumerate(results), key=score, reverse=True)
    return [result for _, result in ranked[:limit]]


def _local_theorem_query_results(
    query: str,
    *,
    num_results: int,
    timeout: float | None = None,
) -> list[LeanSearchResult] | None:
    _load_persistent_definition_cache()
    key = _cache_key(f"{LOCAL_THEOREM_CACHE_VERSION}: {query}")
    if key in _LOCAL_DEFINITION_QUERY_CACHE:
        return _LOCAL_DEFINITION_QUERY_CACHE[key]
    request_timeout = _local_lookup_timeout_seconds(timeout)
    try:
        records = _run_similarity_search(
            query,
            num_results=max(num_results, 200),
            timeout=request_timeout,
            desc_field="description",
        )
        broad_candidates = [
            result
            for record in records
            if (result := _candidate_to_result(record)) is not None
            and _is_theorem_like(result)
        ]
        candidates = _rerank_theorem_results(
            query,
            broad_candidates,
            limit=max(num_results, 12),
        )
        results = _select_llm_match(
            query,
            candidates,
            timeout=request_timeout,
        )
    except Exception as error:
        print(
            f"[mathdoc_agent] local theorem lookup failed for {query!r}: {error}",
            file=sys.stderr,
            flush=True,
        )
        return None
    _LOCAL_DEFINITION_QUERY_CACHE[key] = results
    _write_persistent_local_cache()
    return results


def local_theorem_lookup(
    query: str,
    *,
    num_results: int = 10,
    timeout: float | None = None,
) -> list[LeanSearchResult]:
    """Run local similarity search and return only an exact theorem match."""
    return _local_theorem_query_results(
        query,
        num_results=num_results,
        timeout=timeout,
    ) or []


def _theorem_search_query(theorem: dict[str, Any]) -> str | None:
    for key in ("claim", "name", "description"):
        value = theorem.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return None


def find_mathlib_theorem(
    theorem: dict[str, Any],
    *,
    num_results: int = 10,
    timeout: float | None = None,
    use_local: bool = True,
    use_remote: bool = True,
) -> LeanSearchResult | None:
    """Return a semantically exact Mathlib theorem candidate, local-first."""
    query = _theorem_search_query(theorem)
    if query is None:
        return None

    _load_persistent_definition_cache()
    key = _cache_key(f"{THEOREM_MATCH_CACHE_VERSION}: {query}")
    cached = _THEOREM_MATCH_QUERY_CACHE.get(key)
    if cached is not None:
        return cached[0] if cached else None

    local_completed = False
    if use_local and _env_flag("MATHDOC_AGENT_LOCAL_THEOREM_SEARCH"):
        local_results = _local_theorem_query_results(
            query,
            num_results=max(num_results, 10),
            timeout=_local_lookup_timeout_seconds(),
        )
        if local_results is not None:
            local_completed = True
            if local_results:
                _THEOREM_MATCH_QUERY_CACHE[key] = local_results
                _write_persistent_theorem_cache()
                return local_results[0]

    remote_completed = False
    if use_remote and _env_flag("MATHDOC_AGENT_REMOTE_LEANSEARCH"):
        remote_results = _remote_query_results(
            query,
            num_results=num_results,
            timeout=timeout,
        )
        if remote_results is not None:
            remote_completed = True
            theorem_results = [
                result for result in remote_results if _is_theorem_like(result)
            ]
            selected = _select_llm_match(
                query,
                theorem_results,
                timeout=_local_lookup_timeout_seconds(),
            )
            if selected:
                _THEOREM_MATCH_QUERY_CACHE[key] = selected
                _write_persistent_theorem_cache()
                return selected[0]

    if remote_completed or (local_completed and not use_remote):
        _THEOREM_MATCH_QUERY_CACHE[key] = []
        _write_persistent_theorem_cache()
    return None


def enrich_theorem_dependencies(data: dict[str, Any]) -> dict[str, Any]:
    """Annotate final theorem dependencies with semantically matched candidates.

    A matched declaration is deliberately recorded as a candidate. It is not
    promoted to `lean_name` without an instantiated `lean_term` proving the
    particular local step.
    """
    search_enabled = _env_flag("MATHDOC_AGENT_LEANSEARCH_DEDUCED_THEOREMS")

    local_declarations: dict[str, str] = {}

    def collect_local_declarations(value: Any) -> None:
        if isinstance(value, list):
            for item in value:
                collect_local_declarations(item)
            return
        if not isinstance(value, dict):
            return
        if value.get("type") == "theorem":
            name = value.get("name")
            labels = [value.get("label")]
            source = value.get("source")
            if isinstance(source, dict):
                labels.append(source.get("label"))
            if isinstance(name, str) and name.strip():
                for label in labels:
                    if isinstance(label, str) and label.strip():
                        local_declarations[label.strip().casefold()] = name.strip()
        for item in value.values():
            collect_local_declarations(item)

    collect_local_declarations(data)

    def visit(value: Any) -> Any:
        if isinstance(value, list):
            return [visit(item) for item in value]
        if not isinstance(value, dict):
            return value

        enriched = {
            key: visit(item)
            for key, item in value.items()
            if key != "deduced_from_theorem"
        }
        dependencies = value.get("deduced_from_theorem")
        if not isinstance(dependencies, list):
            return enriched

        enriched_dependencies: list[Any] = []
        for dependency in dependencies:
            dependency = visit(dependency)
            if not isinstance(dependency, dict):
                enriched_dependencies.append(dependency)
                continue
            existing_name = dependency.get("lean_name")
            existing_term = dependency.get("lean_term")
            existing_candidate = dependency.get("lean_name_candidate")
            has_executable_name = (
                isinstance(existing_name, str)
                and existing_name.strip()
                and isinstance(existing_term, str)
                and existing_term.strip()
            )
            has_semantic_candidate = (
                isinstance(existing_candidate, str)
                and existing_candidate.strip()
                and dependency.get("verification_status")
                in {"semantic_match", "local_declaration_match"}
            )
            if not has_executable_name and not has_semantic_candidate:
                dependency_name = dependency.get("name")
                local_name = (
                    local_declarations.get(dependency_name.strip().casefold())
                    if isinstance(dependency_name, str)
                    else None
                )
                if local_name is not None:
                    dependency = {
                        **dependency,
                        "lean_name_candidate": local_name,
                        "verification_status": "local_declaration_match",
                    }
                elif search_enabled:
                    match = find_mathlib_theorem(dependency)
                    if match is not None:
                        dependency = {
                            **dependency,
                            "lean_name_candidate": match.name,
                            "verification_status": "semantic_match",
                        }
            enriched_dependencies.append(dependency)
        enriched["deduced_from_theorem"] = enriched_dependencies
        return enriched

    enriched_data = visit(data)
    return enriched_data if isinstance(enriched_data, dict) else data


def _local_definition_query_results(
    query: str,
    *,
    num_results: int,
    timeout: float | None = None,
) -> list[LeanSearchResult] | None:
    _load_persistent_definition_cache()
    key = _cache_key(f"{LOCAL_CACHE_VERSION}: {query}")
    if key in _LOCAL_DEFINITION_QUERY_CACHE:
        return _LOCAL_DEFINITION_QUERY_CACHE[key]
    request_timeout = _local_lookup_timeout_seconds(timeout)
    try:
        records = _run_similarity_search(
            query,
            num_results=max(num_results, 10),
            timeout=request_timeout,
        )
        candidates = [
            _record_summary(record, index)
            for index, record in enumerate(records[:10])
        ]
        index = _llm_exact_match_index(query, candidates, timeout=request_timeout)
    except Exception as error:
        print(
            f"[mathdoc_agent] local definition lookup failed for {query!r}: {error}",
            file=sys.stderr,
            flush=True,
        )
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
    timeout: float | None = None,
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
    timeout: float | None = None,
    use_local: bool = True,
    use_leansearch: bool = True,
) -> LeanSearchResult | None:
    """Return a conservative Mathlib declaration match for a definition."""
    requested_name = data.term
    remote_timeout = leansearch_timeout_seconds(timeout)
    local_timeout = _local_lookup_timeout_seconds()

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
                timeout=local_timeout,
            )
            if local_results is not None:
                match = compatible_match(local_results)
                if match is not None:
                    return match

        if not use_leansearch or not _env_flag("MATHDOC_AGENT_REMOTE_LEANSEARCH"):
            continue

        leansearch_results = _definition_query_results(
            query,
            num_results=num_results,
            timeout=remote_timeout,
        )
        if not leansearch_results:
            continue
        leansearch_results = _select_llm_match(
            query,
            leansearch_results,
            timeout=local_timeout,
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
