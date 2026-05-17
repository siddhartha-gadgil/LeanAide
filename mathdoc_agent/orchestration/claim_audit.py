"""LLM-backed repair pass for exported claim fields.

The Lean code generator treats every public `claim` field as a proposition to
translate into a theorem or `have` type. This module keeps the check semantic by
asking a bounded agent for structured patches instead of relying on string
heuristics.
"""

from __future__ import annotations

from copy import deepcopy
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.payloads import LogicalProofStepData
from mathdoc_agent.models.refinement_specs import ClaimAuditSpec, ClaimPatchSpec


def _escape_pointer_part(part: str) -> str:
    """Escape one JSON pointer segment."""
    return part.replace("~", "~0").replace("/", "~1")


def _unescape_pointer_part(part: str) -> str:
    """Unescape one JSON pointer segment."""
    return part.replace("~1", "/").replace("~0", "~")


def _child_path(path: str, part: str | int) -> str:
    """Return a JSON pointer path extended by one object key or list index."""
    segment = str(part) if isinstance(part, int) else _escape_pointer_part(part)
    return f"{path}/{segment}" if path else f"/{segment}"


def _container_summary(value: dict[str, Any]) -> dict[str, Any]:
    """Return a small, JSON-serializable summary for the claim auditor."""
    summary: dict[str, Any] = {}
    for key in (
        "type",
        "header",
        "claim",
        "claim_label",
        "proof_method",
        "text",
        "status",
        "id",
    ):
        item = value.get(key)
        if item is not None:
            summary[key] = item
    return summary


def _claim_entries(value: Any, *, path: str = "", parent: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    """Collect public claim fields with enough context for an LLM audit."""
    entries: list[dict[str, Any]] = []
    if isinstance(value, dict):
        claim = value.get("claim")
        if isinstance(claim, str):
            entries.append(
                {
                    "path": _child_path(path, "claim"),
                    "claim": claim,
                    "container_type": value.get("type"),
                    "container": _container_summary(value),
                    "parent_type": parent.get("type") if parent else None,
                    "can_replace_assertion_with_steps": value.get("type") == "assert_statement",
                }
            )
        for key, item in value.items():
            entries.extend(_claim_entries(item, path=_child_path(path, key), parent=value))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            entries.extend(_claim_entries(item, path=_child_path(path, index), parent=parent))
    return entries


def _resolve_path(root: Any, path: str) -> tuple[Any, str | int]:
    """Return the parent container and final key/index for a JSON pointer."""
    if not path.startswith("/"):
        raise ValueError(f"Expected JSON pointer path, got {path!r}")
    parts = [_unescape_pointer_part(part) for part in path.split("/")[1:]]
    if not parts:
        raise ValueError("Cannot patch the document root")
    current = root
    for part in parts[:-1]:
        if isinstance(current, list):
            current = current[int(part)]
        elif isinstance(current, dict):
            current = current[part]
        else:
            raise ValueError(f"Cannot descend through {type(current).__name__} at {path!r}")
    key: str | int
    key = int(parts[-1]) if isinstance(current, list) else parts[-1]
    return current, key


def _step_data(step: LogicalProofStepData) -> dict[str, Any]:
    """Convert an agent proof step to compact public JSON."""
    data = step.model_dump(exclude_none=True)
    if not data.get("deduced_from_claim"):
        data.pop("deduced_from_claim", None)
    if not data.get("deduced_from_theorem"):
        data.pop("deduced_from_theorem", None)
    return data


def _replace_claim(root: Any, patch: ClaimPatchSpec) -> None:
    """Apply a claim-string replacement patch."""
    if patch.claim is None:
        return
    parent, key = _resolve_path(root, patch.path)
    if isinstance(parent, dict) and isinstance(key, str):
        parent[key] = patch.claim


def _replace_assertion_with_steps(root: Any, patch: ClaimPatchSpec) -> None:
    """Replace an enclosing assert_statement with a nested Proof node."""
    if not patch.proof_steps:
        _replace_claim(root, patch)
        return
    if not patch.path.endswith("/claim"):
        return
    assertion_path = patch.path[: -len("/claim")]
    parent, key = _resolve_path(root, assertion_path)
    replacement = {
        "type": "proof",
        "proof_steps": [_step_data(step) for step in patch.proof_steps],
    }
    if isinstance(parent, list) and isinstance(key, int):
        parent[key] = replacement
    elif isinstance(parent, dict) and isinstance(key, str):
        parent[key] = replacement


def apply_claim_patches(data: dict[str, Any], patches: list[ClaimPatchSpec]) -> dict[str, Any]:
    """Apply LLM-supplied claim patches to a copy of exported JSON data."""
    result = deepcopy(data)
    for patch in patches:
        try:
            if patch.action == "replace_claim":
                _replace_claim(result, patch)
            elif patch.action == "replace_assertion_with_steps":
                _replace_assertion_with_steps(result, patch)
        except (KeyError, IndexError, TypeError, ValueError):
            continue
    return result


async def audit_claims_for_lean(data: dict[str, Any], agent: Any | None) -> dict[str, Any]:
    """Use an LLM agent to repair claims that are not Lean proposition-shaped."""
    if agent is None:
        return data
    entries = _claim_entries(data)
    if not entries:
        return data
    spec = await run_agent_typed(
        agent,
        {
            "task": (
                "Audit generated PaperStructure JSON claim fields for Lean "
                "CodegenCore/PaperCodes proposition compatibility."
            ),
            "claim_entries": entries,
            "patch_rules": {
                "replace_claim": "Use when the field should remain one proposition.",
                "replace_assertion_with_steps": (
                    "Use only for assert_statement containers whose claim should "
                    "be refined into smaller proof steps."
                ),
            },
        },
        ClaimAuditSpec,
    )
    return apply_claim_patches(data, spec.patches)
