"""Execution helpers for live and test math-document refinement agents."""

from __future__ import annotations

import asyncio
import inspect
import json
import os
import sys
from typing import Any, TypeVar

from pydantic import BaseModel

from mathdoc_agent.mathagents.leansearch import LeanSearchError, lookup_theorems

T = TypeVar("T", bound=BaseModel)
_LEANSEARCH_CACHE: dict[str, str | None] = {}
DEFAULT_AGENT_TIMEOUT_SECONDS = 600.0
DEFAULT_AGENT_RETRY_COUNT = 1
THEOREM_LIKE_LEANSEARCH_KINDS = {"theorem", "lemma"}


def _agent_name(agent: Any) -> str:
    """Return a stable human-readable name for SDK agents and test doubles."""
    name = getattr(agent, "name", None)
    if isinstance(name, str) and name:
        return name
    callable_name = getattr(agent, "__name__", None)
    if isinstance(callable_name, str) and callable_name:
        return callable_name
    return agent.__class__.__name__


def _payload_summary(payload: Any) -> str:
    """Return a compact description of the agent payload for progress logging."""
    if isinstance(payload, BaseModel):
        payload = payload.model_dump()
    if not isinstance(payload, dict):
        return f"payload={type(payload).__name__}"

    parts: list[str] = []
    node = payload.get("node")
    if isinstance(node, dict):
        node_id = node.get("id")
        kind = node.get("kind")
        if node_id:
            parts.append(f"node={node_id}")
        if kind:
            parts.append(f"kind={kind}")
    proof_kind = payload.get("proof_kind")
    if proof_kind:
        parts.append(f"proof_kind={proof_kind}")
    document = payload.get("document")
    if isinstance(document, dict) and document.get("id"):
        parts.append(f"document={document['id']}")
    return ", ".join(parts) if parts else f"keys={','.join(sorted(payload.keys()))}"


def _log_agent_event(event: str, agent: Any, output_type: type[BaseModel], payload: Any) -> None:
    """Print one progress line to stderr without contaminating JSON stdout."""
    print(
        f"[mathdoc_agent] {event} {_agent_name(agent)} -> {output_type.__name__}"
        f" ({_payload_summary(payload)})",
        file=sys.stderr,
        flush=True,
    )


def _log_leansearch_failure(query: str, error: Exception) -> None:
    """Log a non-fatal LeanSearch enrichment failure."""
    print(
        f"[mathdoc_agent] leansearch failed for {query!r}: {error}",
        file=sys.stderr,
        flush=True,
    )


async def _maybe_await(value: Any) -> Any:
    """Await awaitable values and pass through synchronous values unchanged."""
    if inspect.isawaitable(value):
        return await value
    return value


def _agent_timeout_seconds() -> float | None:
    value = os.environ.get("MATHDOC_AGENT_AGENT_TIMEOUT_SECONDS")
    if value is None:
        return DEFAULT_AGENT_TIMEOUT_SECONDS
    try:
        timeout = float(value)
    except ValueError:
        return DEFAULT_AGENT_TIMEOUT_SECONDS
    return None if timeout <= 0 else timeout


def _agent_retry_count() -> int:
    value = os.environ.get("MATHDOC_AGENT_AGENT_RETRIES")
    if value is None:
        return DEFAULT_AGENT_RETRY_COUNT
    try:
        retries = int(value)
    except ValueError:
        return DEFAULT_AGENT_RETRY_COUNT
    return max(0, retries)


def _leansearch_enabled() -> bool:
    value = os.environ.get("MATHDOC_AGENT_LEANSEARCH_DEDUCED_THEOREMS", "1")
    return value.strip().lower() not in {"0", "false", "no", "off"}


def _theorem_search_query(theorem: dict[str, Any]) -> str | None:
    """Build a LeanSearch query from a deduced_from_theorem object."""
    for key in ("claim", "name", "description"):
        value = theorem.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return None


def _is_usable_theorem_result(result: Any) -> bool:
    name = getattr(result, "name", "")
    if not isinstance(name, str) or not name.strip():
        return False
    lowered_name = name.casefold()
    if "noconfusion" in lowered_name or lowered_name.split(".")[-1].startswith("inst"):
        return False
    kind = getattr(result, "kind", None)
    if kind is None:
        return True
    kind_text = str(kind).strip().casefold()
    return kind_text in THEOREM_LIKE_LEANSEARCH_KINDS


def _lean_name_for_theorem(theorem: dict[str, Any]) -> str | None:
    """Return an exact Lean/Mathlib name for a theorem dependency if found."""
    lean_name = theorem.get("lean_name")
    if isinstance(lean_name, str) and lean_name.strip():
        return lean_name
    query = _theorem_search_query(theorem)
    if query is None:
        return None
    if query in _LEANSEARCH_CACHE:
        return _LEANSEARCH_CACHE[query]
    try:
        results = lookup_theorems(query, num_results=5, timeout=10.0)
    except (LeanSearchError, ValueError, OSError) as error:
        _log_leansearch_failure(query, error)
        _LEANSEARCH_CACHE[query] = None
        return None
    lean_name = next(
        (result.name for result in results if _is_usable_theorem_result(result)),
        None,
    )
    _LEANSEARCH_CACHE[query] = lean_name
    return lean_name


def _enrich_deduced_from_theorems_data(value: Any) -> Any:
    """Add `lean_name` to deduced_from_theorem objects using LeanSearch."""
    if isinstance(value, list):
        return [_enrich_deduced_from_theorems_data(item) for item in value]
    if not isinstance(value, dict):
        return value

    enriched = {
        key: _enrich_deduced_from_theorems_data(item)
        for key, item in value.items()
    }
    dependencies = enriched.get("deduced_from_theorem")
    if isinstance(dependencies, list):
        enriched_dependencies = []
        for item in dependencies:
            if isinstance(item, dict):
                lean_name = _lean_name_for_theorem(item)
                if lean_name:
                    item = {**item, "lean_name": lean_name}
            enriched_dependencies.append(item)
        enriched["deduced_from_theorem"] = enriched_dependencies
    return enriched


def enrich_deduced_from_theorems(model: T) -> T:
    """Resolve theorem dependency objects to Lean names using LeanSearch."""
    if not _leansearch_enabled():
        return model
    data = model.model_dump(mode="json")
    enriched = _enrich_deduced_from_theorems_data(data)
    if enriched == data:
        return model
    return type(model).model_validate(enriched)


async def run_agent_typed(
    agent: Any,
    payload: BaseModel | dict[str, Any],
    output_type: type[T],
) -> T:
    """Run a bounded refinement agent and coerce its output to a Pydantic model.

    The wrapper accepts fake test agents, simple callables, objects exposing
    `.run(payload)`, and OpenAI Agents SDK Agent objects when the SDK is installed.
    It logs start, finish, and failure events to stderr so command-line JSON
    written to stdout remains parseable.
    """
    if isinstance(payload, BaseModel):
        input_payload: Any = payload.model_dump()
    else:
        input_payload = payload

    async def _run_agent_raw() -> Any:
        if callable(agent) and not hasattr(agent, "instructions"):
            return await _maybe_await(agent(input_payload))
        if hasattr(agent, "run"):
            return await _maybe_await(agent.run(input_payload))
        try:
            from agents import Runner
        except ImportError as exc:
            raise RuntimeError(
                "No runnable fake agent was provided and the OpenAI Agents SDK is not installed."
            ) from exc
        sdk_input = input_payload if isinstance(input_payload, str) else json.dumps(input_payload)
        result = await Runner.run(agent, sdk_input)
        return result.final_output

    timeout = _agent_timeout_seconds()
    retries = _agent_retry_count()
    for attempt in range(retries + 1):
        _log_agent_event("calling" if attempt == 0 else "retrying", agent, output_type, input_payload)
        try:
            if timeout is None:
                output = await _run_agent_raw()
            else:
                output = await asyncio.wait_for(_run_agent_raw(), timeout=timeout)
            break
        except asyncio.TimeoutError as exc:
            _log_agent_event("timed out", agent, output_type, input_payload)
            if attempt < retries:
                continue
            raise TimeoutError(
                f"Agent {_agent_name(agent)} timed out after {timeout} seconds"
            ) from exc
        except Exception:
            _log_agent_event("failed", agent, output_type, input_payload)
            raise
    try:
        if isinstance(output, output_type):
            coerced = output
        elif isinstance(output, BaseModel):
            coerced = output_type.model_validate(output.model_dump())
        elif isinstance(output, dict):
            coerced = output_type.model_validate(output)
        elif isinstance(output, str):
            coerced = output_type.model_validate_json(output)
        elif hasattr(output, "final_output"):
            coerced = await run_agent_typed(lambda _: output.final_output, {}, output_type)
        else:
            coerced = output_type.model_validate(output)
    except Exception:
        _log_agent_event("failed", agent, output_type, input_payload)
        raise
    coerced = enrich_deduced_from_theorems(coerced)
    _log_agent_event("completed", agent, output_type, input_payload)
    return coerced
