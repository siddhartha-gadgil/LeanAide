"""Repair informal local notation in Lean-facing JSON string fields."""

from __future__ import annotations

import os
import re
from copy import deepcopy
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.refinement_specs import InformalNotationRepairSpec
from mathdoc_agent.orchestration.claim_audit import (
    _child_path,
    _container_summary,
    _resolve_path,
)


CODEGEN_STRING_FIELDS = {
    "claim",
    "definition",
    "construction",
    "witness",
    "variable_name",
    "variable_type",
    "statement",
    "lhs",
    "rhs",
    "from",
    "to",
    "lean_term",
}

INFORMAL_NOTATION_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"\b[A-Za-z]+_\{[^}]+\}"),
    re.compile(r"\b[A-Za-z]+_[A-Za-z0-9]+"),
    re.compile(r"\\[A-Za-z]+"),
    re.compile(r"\|\|.+?\|\|(?:_[A-Za-z0-9]+)?"),
    re.compile(r"‖.+?‖"),
    re.compile(r"\btensor_Z\b"),
    re.compile(r"\b[A-Za-z]+\([^)]*,[^)]*\)"),
    re.compile(r"\b[A-Za-z]+/[A-Za-z]+\([^)]+\)"),
    re.compile(r":="),
)

_DEFAULT_BATCH_SIZE = 40


def _batch_size() -> int:
    raw = os.environ.get("MATHDOC_AGENT_INFORMAL_NOTATION_BATCH_SIZE")
    if raw is None:
        return _DEFAULT_BATCH_SIZE
    try:
        value = int(raw)
    except ValueError:
        return _DEFAULT_BATCH_SIZE
    return max(1, value)


def _has_informal_notation(value: str) -> bool:
    return any(pattern.search(value) for pattern in INFORMAL_NOTATION_PATTERNS)


def _nearby_context(value: dict[str, Any]) -> dict[str, Any]:
    context = _container_summary(value)
    for key in ("name", "label", "header", "proof_method", "text", "source", "type"):
        item = value.get(key)
        if item is not None and key not in context:
            context[key] = item
    return context


def _informal_entries(
    value: Any,
    *,
    path: str = "",
    parent: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    if isinstance(value, dict):
        for key, item in value.items():
            item_path = _child_path(path, key)
            if (
                key in CODEGEN_STRING_FIELDS
                and isinstance(item, str)
                and _has_informal_notation(item)
            ):
                entries.append(
                    {
                        "path": item_path,
                        "field": key,
                        "text": item,
                        "container_type": value.get("type"),
                        "container": _nearby_context(value),
                        "parent_type": parent.get("type") if parent else None,
                    }
                )
            if isinstance(item, (dict, list)):
                entries.extend(_informal_entries(item, path=item_path, parent=value))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            entries.extend(
                _informal_entries(item, path=_child_path(path, index), parent=parent)
            )
    return entries


def _replace_text(root: Any, path: str, replacement: str) -> None:
    parent, key = _resolve_path(root, path)
    if isinstance(parent, dict) and isinstance(key, str):
        parent[key] = replacement
    elif isinstance(parent, list) and isinstance(key, int):
        parent[key] = replacement


def apply_informal_notation_patches(
    data: dict[str, Any],
    specs: list[InformalNotationRepairSpec],
) -> dict[str, Any]:
    result = deepcopy(data)
    for spec in specs:
        for patch in spec.patches:
            try:
                if patch.replacement.strip():
                    _replace_text(result, patch.path, patch.replacement.strip())
            except (KeyError, IndexError, TypeError, ValueError):
                continue
    return result


def _camel_token(value: str) -> str:
    parts = [part for part in re.split(r"[^A-Za-z0-9]+", value) if part]
    if not parts:
        return ""
    return "".join(part[:1].upper() + part[1:] for part in parts)


def _ascii_subscript_replacement(match: re.Match[str]) -> str:
    base = match.group(1)
    raw_subscript = match.group(2) if match.lastindex and match.lastindex >= 2 else ""
    return f"{base}{_camel_token(raw_subscript)}"


def _replace_norm_bars(text: str) -> str:
    text = re.sub(
        r"\|\|(.+?)\|\|_([A-Za-z0-9]+)",
        lambda m: f"norm{_camel_token(m.group(2))}({m.group(1).strip()})",
        text,
    )
    text = re.sub(
        r"\|\|(.+?)\|\|",
        lambda m: f"norm({m.group(1).strip()})",
        text,
    )
    text = re.sub(
        r"‖(.+?)‖",
        lambda m: f"norm({m.group(1).strip()})",
        text,
    )
    return text


def _replace_function_call_with_comma(match: re.Match[str]) -> str:
    name = match.group(1)
    args = " and ".join(part.strip() for part in match.group(2).split(","))
    return f"{name} applied to {args}"


def deterministic_repair_text(text: str) -> str:
    """Best-effort cleanup for any informal notation an agent leaves behind."""
    text = _replace_norm_bars(text)
    text = re.sub(
        r"\b([A-Za-z]+)_\{([^}]+)\}",
        _ascii_subscript_replacement,
        text,
    )
    text = re.sub(
        r"\b([A-Za-z]+)_([A-Za-z0-9]+)",
        _ascii_subscript_replacement,
        text,
    )
    text = text.replace("tensorZ", "tensor over Z")
    text = text.replace("tensor_Z", "tensor over Z")
    text = re.sub(
        r"\b([A-Za-z]+)/([A-Za-z]+)\(([^)]+)\)",
        lambda m: f"{m.group(1)} modulo {m.group(2)} applied to {m.group(3).strip()}",
        text,
    )
    text = text.replace(":=", " is defined as ")
    text = re.sub(r"\\mathbb\{([^}]+)\}", r"\1", text)
    text = re.sub(r"\\operatorname\{([^}]+)\}", r"\1", text)
    text = re.sub(r"\\([A-Za-z]+)", r"\1", text)
    previous = None
    while previous != text:
        previous = text
        text = re.sub(
            r"\b([A-Za-z]+)\(([^)]*,[^)]*)\)",
            _replace_function_call_with_comma,
            text,
        )
    return text


def deterministic_repair_remaining_informal_notation(data: dict[str, Any]) -> dict[str, Any]:
    result = deepcopy(data)

    def visit(value: Any) -> None:
        if isinstance(value, dict):
            for key, item in list(value.items()):
                if (
                    key in CODEGEN_STRING_FIELDS
                    and isinstance(item, str)
                    and _has_informal_notation(item)
                ):
                    value[key] = deterministic_repair_text(item)
                elif isinstance(item, (dict, list)):
                    visit(item)
        elif isinstance(value, list):
            for item in value:
                visit(item)

    visit(result)
    return result


async def repair_informal_notation_for_lean(
    data: dict[str, Any],
    agent: Any | None,
) -> dict[str, Any]:
    """Repair display-only/local informal notation before Lean-facing JSON export."""
    entries = _informal_entries(data)
    if not entries:
        return data

    specs: list[InformalNotationRepairSpec] = []
    if agent is not None:
        batch_size = _batch_size()
        for start in range(0, len(entries), batch_size):
            batch = entries[start : start + batch_size]
            spec = await run_agent_typed(
                agent,
                {
                    "task": (
                        "Repair informal local notation in generated PaperStructure "
                        "JSON string fields before Lean codegen."
                    ),
                    "notation_entries": batch,
                    "repair_rules": {
                        "replacement": (
                            "Return text for the same field with scoped ASCII "
                            "identifiers or precise prose; do not use pseudo-subscripts, "
                            "LaTeX commands, norm bars, tensor_Z, or f(x,y)-style "
                            "informal multi-argument calls."
                        )
                    },
                },
                InformalNotationRepairSpec,
            )
            specs.append(spec)

    repaired = apply_informal_notation_patches(data, specs) if specs else data
    return deterministic_repair_remaining_informal_notation(repaired)
