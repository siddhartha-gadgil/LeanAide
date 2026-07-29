"""Consolidated LLM-backed repair pass for Lean-facing JSON.

This pass is intentionally patch-based. Deterministic linters identify
paraphrase-sensitive high-risk locations, and the LLM returns small JSON-pointer
patches rather than a rewritten document.
"""

from __future__ import annotations

import os
import re
from copy import deepcopy
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.refinement_specs import (
    LeanJsonRepairPatchSpec,
    LeanJsonRepairSpec,
)


_DEFAULT_BATCH_SIZE = 20


def _batch_size() -> int:
    raw = os.environ.get("MATHDOC_AGENT_LEAN_JSON_REPAIR_BATCH_SIZE")
    if raw is None:
        return _DEFAULT_BATCH_SIZE
    try:
        value = int(raw)
    except ValueError:
        return _DEFAULT_BATCH_SIZE
    return max(1, value)


def _escape_pointer_part(part: str) -> str:
    return part.replace("~", "~0").replace("/", "~1")


def _unescape_pointer_part(part: str) -> str:
    return part.replace("~1", "/").replace("~0", "~")


def _child_path(path: str, part: str | int) -> str:
    segment = str(part) if isinstance(part, int) else _escape_pointer_part(part)
    return f"{path}/{segment}" if path else f"/{segment}"


def _resolve_path(root: Any, path: str) -> tuple[Any, str | int]:
    if not path.startswith("/"):
        raise ValueError(f"Expected JSON pointer path, got {path!r}")
    parts = [_unescape_pointer_part(part) for part in path.split("/")[1:]]
    if not parts:
        raise ValueError("Cannot patch the JSON root")
    parent = root
    for part in parts[:-1]:
        if isinstance(parent, list):
            parent = parent[int(part)]
        elif isinstance(parent, dict):
            parent = parent[part]
        else:
            raise TypeError("Cannot descend through scalar JSON value")
    final = parts[-1]
    if isinstance(parent, list):
        return parent, int(final)
    return parent, final


def _compact_object(value: dict[str, Any]) -> dict[str, Any]:
    keys = (
        "type",
        "name",
        "label",
        "header",
        "claim",
        "assumption",
        "statement",
        "variable_name",
        "variable_type",
        "properties",
        "value",
        "proof_method",
        "formalization_status",
        "source",
        "deduced_from_theorem",
        "full_claim",
        "construction",
        "verification",
        "witness",
    )
    return {key: value[key] for key in keys if key in value}


def _has_source_context(value: dict[str, Any]) -> bool:
    source = value.get("source")
    text = source.get("text") if isinstance(source, dict) else None
    if not isinstance(text, str):
        return False
    return bool(re.search(r"\b(let|fix|assume|suppose)\b", text, flags=re.IGNORECASE))


def _has_theorem_dependency_risk(value: dict[str, Any]) -> bool:
    dependencies = value.get("deduced_from_theorem")
    if not isinstance(dependencies, list):
        return False
    for dependency in dependencies:
        if not isinstance(dependency, dict):
            continue
        lean_term = dependency.get("lean_term")
        if isinstance(lean_term, str) and lean_term.strip():
            continue
        if any(
            isinstance(dependency.get(key), str) and dependency.get(key).strip()
            for key in ("lean_name", "lean_name_candidate", "name", "description")
        ):
            return True
    return False


def _has_string_risk(value: dict[str, Any]) -> bool:
    risky_fields = (
        "claim",
        "assumption",
        "statement",
        "construction",
        "verification",
        "full_claim",
        "proof_method",
    )
    for key in risky_fields:
        item = value.get(key)
        if not isinstance(item, str):
            continue
        if (
            "applied to" in item
            or " is conjugate to " in item
            or re.search(r"\S+\s*(?:=|≤|<=|≥|>=|<|>)\s*\S+\s*(?:=|≤|<=|≥|>=|<|>)", item)
        ):
            return True
    return False


def _is_materialized_obligation(value: dict[str, Any]) -> bool:
    source = value.get("source")
    return (
        value.get("proof_method") == "Materialized from deduced_from_claim."
        or value.get("proof_method") == "Named local obligation from unresolved claim dependency."
        or (
            isinstance(source, dict)
            and source.get("kind") == "deduced_from_claim"
            and value.get("type") in {"assert_statement", "theorem"}
        )
    )


def _is_complex_construction(value: dict[str, Any]) -> bool:
    if value.get("type") not in {"construction_proof", "existence_proof"}:
        return False
    text = " ".join(
        item
        for key in ("full_claim", "construction", "verification", "witness")
        if isinstance((item := value.get(key)), str)
    ).casefold()
    return any(
        marker in text
        for marker in (
            "quotient",
            "tensor",
            "completion",
            "banach",
            "induced",
            "lifted",
            "there exists",
        )
    )


def lean_json_repair_entries(data: Any) -> list[dict[str, Any]]:
    """Return compact high-risk entries for the consolidated LLM repair pass."""
    entries: list[dict[str, Any]] = []

    def visit(value: Any, path: str = "") -> None:
        if isinstance(value, list):
            for index, item in enumerate(value):
                visit(item, _child_path(path, index))
            return
        if not isinstance(value, dict):
            return

        reasons: list[str] = []
        if value.get("type") == "theorem" and _has_source_context(value):
            reasons.append("source_context")
        if _has_theorem_dependency_risk(value):
            reasons.append("theorem_dependency")
        if _has_string_risk(value):
            reasons.append("informal_or_compound_string")
        if _is_materialized_obligation(value):
            reasons.append("materialized_claim_obligation")
        if _is_complex_construction(value):
            reasons.append("complex_construction")
        if reasons:
            entries.append(
                {
                    "path": path or "/",
                    "reasons": reasons,
                    "object": _compact_object(value),
                }
            )
        for key, item in value.items():
            visit(item, _child_path(path, key))

    visit(data)
    return entries


def _apply_patch(root: Any, patch: LeanJsonRepairPatchSpec) -> None:
    if patch.action == "replace_object":
        if patch.value is None:
            return
        parent, key = _resolve_path(root, patch.path)
        if isinstance(parent, list) and isinstance(key, int):
            parent[key] = deepcopy(patch.value)
        elif isinstance(parent, dict) and isinstance(key, str):
            parent[key] = deepcopy(patch.value)
        return
    if patch.action == "replace_string":
        if patch.text is None:
            return
        parent, key = _resolve_path(root, patch.path)
        if isinstance(parent, list) and isinstance(key, int):
            parent[key] = patch.text
        elif isinstance(parent, dict) and isinstance(key, str):
            parent[key] = patch.text
        return
    if patch.action == "insert_before":
        if patch.value is None:
            return
        parent, key = _resolve_path(root, patch.path)
        if isinstance(parent, list) and isinstance(key, int):
            parent.insert(key, deepcopy(patch.value))
        return
    if patch.action == "remove_object":
        parent, key = _resolve_path(root, patch.path)
        if isinstance(parent, list) and isinstance(key, int):
            del parent[key]
        elif isinstance(parent, dict) and isinstance(key, str):
            parent.pop(key, None)
        return
    if patch.action == "append_hypothesis":
        if patch.value is None:
            return
        parent, key = _resolve_path(root, patch.path)
        if isinstance(parent, list) and isinstance(key, int):
            target = parent[key]
        elif isinstance(parent, dict) and isinstance(key, str):
            target = parent[key]
        else:
            return
        if not isinstance(target, dict) or target.get("type") != "theorem":
            return
        hypotheses = target.get("hypothesis")
        if not isinstance(hypotheses, list):
            hypotheses = []
        hypotheses.append(deepcopy(patch.value))
        target["hypothesis"] = hypotheses


def apply_lean_json_repair_patches(
    data: dict[str, Any],
    patches: list[LeanJsonRepairPatchSpec],
) -> dict[str, Any]:
    result = deepcopy(data)
    for patch in patches:
        try:
            _apply_patch(result, patch)
        except (KeyError, IndexError, TypeError, ValueError):
            continue
    return result


async def repair_lean_json_with_llm(data: dict[str, Any], agent: Any | None) -> dict[str, Any]:
    """Run the consolidated LLM repair pass over high-risk JSON entries."""
    if agent is None:
        return data
    entries = lean_json_repair_entries(data)
    if not entries:
        return data
    batch_size = _batch_size()
    repaired = data
    for start in range(0, len(entries), batch_size):
        batch = entries[start : start + batch_size]
        spec = await run_agent_typed(
            agent,
            {
                "task": (
                    "Repair high-risk exported PaperStructure JSON before Lean "
                    "code generation. Return only JSON-pointer patches."
                ),
                "repair_entries": batch,
                "patch_rules": {
                    "replace_object": "Use for malformed or understructured JSON objects.",
                    "replace_string": "Use for one bad Lean-facing string field.",
                    "insert_before": "Use to add a local theorem, let, or assumption before use.",
                    "remove_object": "Use only for duplicate context facts already available.",
                    "append_hypothesis": "Use to add missing theorem context from source.",
                },
            },
            LeanJsonRepairSpec,
        )
        repaired = apply_lean_json_repair_patches(repaired, spec.patches)
    return repaired
