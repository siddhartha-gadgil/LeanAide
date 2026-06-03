"""LLM-backed sanity checks for generated proof-step assertions."""

from __future__ import annotations

import os
import re
from copy import deepcopy
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.payloads import LogicalProofStepData
from mathdoc_agent.models.refinement_specs import (
    ProofSanityAuditSpec,
    ProofSanityPatchSpec,
)
from mathdoc_agent.orchestration.claim_audit import (
    _child_path,
    _container_summary,
    _resolve_path,
)
from mathdoc_agent.orchestration.deduced_from_claim_rewrite import (
    _assumption_from_step,
    _claim_introduced_by_step,
)


_UNIVERSAL_RE = re.compile(r"\b(for all|for every|every|any|arbitrary)\b|∀", re.IGNORECASE)
_PSEUDO_LOCAL_RE = re.compile(
    r"\b[A-Za-z]+_\{[^}]+\}|\b[A-Za-z]+_[A-Za-z0-9]+|\\[A-Za-z]+|\|\|.+?\|\||‖.+?‖|"
    r"\b[A-Za-z]+\([^)]*,[^)]*\)"
)
_ASSIGNMENT_RE = re.compile(r":=| let | set ", re.IGNORECASE)
_DEFAULT_MAX_ENTRIES = 40


def _max_entries() -> int:
    value = os.environ.get("MATHDOC_AGENT_PROOF_SANITY_MAX_ENTRIES")
    if value is None:
        return _DEFAULT_MAX_ENTRIES
    try:
        parsed = int(value)
    except ValueError:
        return _DEFAULT_MAX_ENTRIES
    return max(0, parsed)


def _dependencies_summary(value: dict[str, Any]) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for key in ("deduced_from_theorem", "proof_method", "lean_term", "source_claim"):
        item = value.get(key)
        if item:
            summary[key] = item
    return summary


def _risk_reasons(value: dict[str, Any], claim: str, local_context: list[str]) -> list[str]:
    reasons: list[str] = []
    if _UNIVERSAL_RE.search(claim) and not (
        value.get("deduced_from_theorem") or value.get("deduced_from_claim")
    ):
        reasons.append("universal claim has no explicit dependency")
    if _PSEUDO_LOCAL_RE.search(claim):
        reasons.append("claim contains informal or display-style local notation")
    if _ASSIGNMENT_RE.search(claim):
        reasons.append("claim appears to contain a local definition or assignment")
    if any(
        token in claim
        for token in ("for all (c", "∀ (c", "for all c", "∀ c", "for every c")
    ) and not any(" c " in f" {context} " for context in local_context):
        reasons.append("claim quantifies over a new variable not visible in local context")
    if isinstance(value.get("proof_method"), str):
        method = value["proof_method"].lower()
        if any(word in method for word in ("obvious", "clear", "trivial")) and _UNIVERSAL_RE.search(claim):
            reasons.append("strong universal assertion justified only by a weak proof method")
    return reasons


def _sanity_entries(
    value: Any,
    *,
    path: str = "",
    local_context: list[str] | None = None,
    parent: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    local_context = local_context or []
    entries: list[dict[str, Any]] = []
    if isinstance(value, dict):
        current_context = [*local_context]
        assumption = _assumption_from_step(value)
        if assumption is not None:
            current_context.append(assumption)
        introduced = _claim_introduced_by_step(value)
        if introduced is not None and value.get("type") != "assert_statement":
            current_context.append(introduced)

        claim = value.get("claim")
        if value.get("type") == "assert_statement" and isinstance(claim, str) and claim.strip():
            reasons = _risk_reasons(value, claim, local_context)
            if reasons:
                entries.append(
                    {
                        "path": path or "/",
                        "claim": claim,
                        "risk_reasons": reasons,
                        "container": _container_summary(value),
                        "dependencies": _dependencies_summary(value),
                        "available_context": local_context[-12:],
                        "parent_type": parent.get("type") if parent else None,
                        "parent_claim": parent.get("claim") if parent else None,
                    }
                )

        for key, item in value.items():
            if key == "proof_steps" and isinstance(item, list):
                running_context = [*current_context]
                for index, step in enumerate(item):
                    entries.extend(
                        _sanity_entries(
                            step,
                            path=_child_path(_child_path(path, key), index),
                            local_context=running_context,
                            parent=value,
                        )
                    )
                    assumption = _assumption_from_step(step)
                    if assumption is not None:
                        running_context.append(assumption)
                        continue
                    introduced = _claim_introduced_by_step(step)
                    if introduced is not None:
                        running_context.append(introduced)
                continue
            entries.extend(
                _sanity_entries(
                    item,
                    path=_child_path(path, key),
                    local_context=current_context,
                    parent=value,
                )
            )
    elif isinstance(value, list):
        running_context = [*local_context]
        for index, item in enumerate(value):
            entries.extend(
                _sanity_entries(
                    item,
                    path=_child_path(path, index),
                    local_context=running_context,
                    parent=parent,
                )
            )
            assumption = _assumption_from_step(item)
            if assumption is not None:
                running_context.append(assumption)
                continue
            introduced = _claim_introduced_by_step(item)
            if introduced is not None:
                running_context.append(introduced)
    return entries


def _step_data(step: LogicalProofStepData) -> dict[str, Any]:
    data = step.model_dump(exclude_none=True)
    if not data.get("deduced_from_claim"):
        data.pop("deduced_from_claim", None)
    if not data.get("deduced_from_theorem"):
        data.pop("deduced_from_theorem", None)
    return data


def _mark_needs_review(root: Any, patch: ProofSanityPatchSpec) -> None:
    parent, key = _resolve_path(root, patch.path)
    if isinstance(parent, list) and isinstance(key, int):
        target = parent[key]
    elif isinstance(parent, dict) and isinstance(key, str):
        target = parent[key]
    else:
        return
    if not isinstance(target, dict):
        return
    issue = {
        "reason": patch.reason,
        "suggested_repair": patch.suggested_repair,
        "notes": patch.notes,
    }
    existing = target.get("proof_sanity")
    issues = []
    if isinstance(existing, dict) and isinstance(existing.get("issues"), list):
        issues = list(existing["issues"])
    target["proof_sanity"] = {
        "status": "needs_review",
        "issues": [*issues, issue],
    }
    if target.get("formalization_status") not in {"unsupported", "needs_named_lemmas"}:
        target["formalization_status"] = "needs_review"


def _replace_claim(root: Any, patch: ProofSanityPatchSpec) -> None:
    if patch.claim is None:
        _mark_needs_review(root, patch)
        return
    parent, key = _resolve_path(root, patch.path)
    if isinstance(parent, list) and isinstance(key, int) and isinstance(parent[key], dict):
        parent[key]["claim"] = patch.claim
    elif isinstance(parent, dict) and isinstance(key, str) and isinstance(parent[key], dict):
        parent[key]["claim"] = patch.claim


def _clear_proof_sanity_marker(value: dict[str, Any]) -> None:
    value.pop("proof_sanity", None)
    if value.get("formalization_status") == "needs_review":
        value.pop("formalization_status", None)


def _replace_claim_and_clear(root: Any, patch: ProofSanityPatchSpec) -> None:
    if patch.claim is None:
        return
    parent, key = _resolve_path(root, patch.path)
    target: Any
    if isinstance(parent, list) and isinstance(key, int):
        target = parent[key]
    elif isinstance(parent, dict) and isinstance(key, str):
        target = parent[key]
    else:
        return
    if not isinstance(target, dict):
        return
    target["claim"] = patch.claim
    _clear_proof_sanity_marker(target)


def _replace_assertion_with_steps(root: Any, patch: ProofSanityPatchSpec) -> None:
    if not patch.proof_steps:
        _mark_needs_review(root, patch)
        return
    parent, key = _resolve_path(root, patch.path)
    replacement = {
        "type": "proof",
        "proof_steps": [_step_data(step) for step in patch.proof_steps],
        "proof_sanity": {
            "status": "rewritten",
            "issues": [{"reason": patch.reason, "notes": patch.notes}],
        },
    }
    if isinstance(parent, list) and isinstance(key, int):
        parent[key] = replacement
    elif isinstance(parent, dict) and isinstance(key, str):
        parent[key] = replacement


def _replace_assertion_with_steps_and_clear(root: Any, patch: ProofSanityPatchSpec) -> None:
    if not patch.proof_steps:
        return
    parent, key = _resolve_path(root, patch.path)
    replacement = {
        "type": "proof",
        "proof_steps": [_step_data(step) for step in patch.proof_steps],
    }
    if isinstance(parent, list) and isinstance(key, int):
        parent[key] = replacement
    elif isinstance(parent, dict) and isinstance(key, str):
        parent[key] = replacement


def apply_proof_sanity_patches(
    data: dict[str, Any],
    patches: list[ProofSanityPatchSpec],
) -> dict[str, Any]:
    result = deepcopy(data)
    for patch in patches:
        try:
            if patch.action == "mark_needs_review":
                _mark_needs_review(result, patch)
            elif patch.action == "replace_claim":
                _replace_claim(result, patch)
            elif patch.action == "replace_assertion_with_steps":
                _replace_assertion_with_steps(result, patch)
        except (KeyError, IndexError, TypeError, ValueError):
            continue
    return result


def _marked_proof_sanity_entries(value: Any, *, path: str = "") -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    if isinstance(value, dict):
        proof_sanity = value.get("proof_sanity")
        claim = value.get("claim")
        if (
            value.get("type") == "assert_statement"
            and isinstance(claim, str)
            and isinstance(proof_sanity, dict)
            and proof_sanity.get("status") == "needs_review"
        ):
            entries.append(
                {
                    "path": path or "/",
                    "claim": claim,
                    "container": _container_summary(value),
                    "issues": proof_sanity.get("issues", []),
                }
            )
        for key, item in value.items():
            if isinstance(item, (dict, list)):
                entries.extend(_marked_proof_sanity_entries(item, path=_child_path(path, key)))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            if isinstance(item, (dict, list)):
                entries.extend(_marked_proof_sanity_entries(item, path=_child_path(path, index)))
    return entries


def apply_proof_sanity_repairs(
    data: dict[str, Any],
    patches: list[ProofSanityPatchSpec],
) -> dict[str, Any]:
    result = deepcopy(data)
    for patch in patches:
        try:
            if patch.action == "replace_claim":
                _replace_claim_and_clear(result, patch)
            elif patch.action == "replace_assertion_with_steps":
                _replace_assertion_with_steps_and_clear(result, patch)
        except (KeyError, IndexError, TypeError, ValueError):
            continue
    return result


async def repair_proof_sanity_issues(
    data: dict[str, Any],
    agent: Any | None,
) -> dict[str, Any]:
    """Repair assertions marked by the proof-sanity audit instead of exporting flags."""
    if agent is None:
        return data
    entries = _marked_proof_sanity_entries(data)
    if not entries:
        return data
    spec = await run_agent_typed(
        agent,
        {
            "task": (
                "Repair proof-step assertions that were marked risky before "
                "Lean codegen. Return concrete replacements, not review flags."
            ),
            "assertion_entries": entries,
            "patch_rules": {
                "replace_claim": "Use when one scoped replacement claim fixes the issue.",
                "replace_assertion_with_steps": (
                    "Use when a missing local definition/witness-introduction step "
                    "must be inserted before the repaired assertion."
                ),
            },
        },
        ProofSanityAuditSpec,
    )
    return apply_proof_sanity_repairs(data, spec.patches)


async def audit_proof_steps_for_counterexamples(
    data: dict[str, Any],
    agent: Any | None,
) -> dict[str, Any]:
    """Ask an agent to flag risky generated helper assertions."""
    if agent is None:
        return data
    entries = _sanity_entries(data)
    max_entries = _max_entries()
    if max_entries == 0 or not entries:
        return data
    entries = entries[:max_entries]
    spec = await run_agent_typed(
        agent,
        {
            "task": (
                "Audit generated proof-step assertions for counterexamples, "
                "over-strong claims, and unbound local variables before Lean codegen."
            ),
            "assertion_entries": entries,
            "patch_rules": {
                "mark_needs_review": "Use when the assertion is risky but the exact repair is unclear.",
                "replace_claim": "Use only when the intended weaker/local claim is obvious.",
                "replace_assertion_with_steps": "Use only when the assertion bundles smaller claims present in context.",
            },
        },
        ProofSanityAuditSpec,
    )
    return apply_proof_sanity_patches(data, spec.patches)
