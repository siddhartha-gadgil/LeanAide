"""LLM-backed rewrite pass for `deduced_from_claim` dependencies."""

from __future__ import annotations

from copy import deepcopy
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.payloads import LogicalProofStepData
from mathdoc_agent.models.refinement_specs import (
    DeducedFromClaimPatchSpec,
    DeducedFromClaimRewriteSpec,
)
from mathdoc_agent.orchestration.claim_audit import (
    _child_path,
    _container_summary,
    _resolve_path,
)


def _normalized_claim(value: str) -> str:
    return " ".join(value.strip().split())


def _same_claim(left: str, right: str) -> bool:
    return _normalized_claim(left) == _normalized_claim(right)


def _assumption_from_step(value: Any) -> str | None:
    if isinstance(value, dict) and value.get("type") == "assume_statement":
        assumption = value.get("assumption")
        if isinstance(assumption, str) and assumption.strip():
            return assumption
    return None


def _claim_introduced_by_step(value: Any) -> str | None:
    if not isinstance(value, dict):
        return None
    if value.get("type") in {"theorem", "specialize", "assert_statement"}:
        claim = value.get("claim")
        if isinstance(claim, str) and claim.strip():
            return claim
    return None


def _hypotheses_from_container(value: dict[str, Any]) -> list[str]:
    hypotheses: list[str] = []
    raw_hypotheses = value.get("hypothesis")
    if isinstance(raw_hypotheses, list):
        for item in raw_hypotheses:
            assumption = _assumption_from_step(item)
            if assumption is not None:
                hypotheses.append(assumption)
    assumption = value.get("assumption")
    if isinstance(assumption, str) and value.get("type") == "contradiction_statement":
        hypotheses.append(assumption)
    return hypotheses


def _dependency_entries(
    value: Any,
    *,
    path: str = "",
    hypotheses: list[str] | None = None,
    parent: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    hypotheses = hypotheses or []
    entries: list[dict[str, Any]] = []
    if isinstance(value, dict):
        local_hypotheses = [*hypotheses, *_hypotheses_from_container(value)]
        dependencies = value.get("deduced_from_claim")
        if isinstance(dependencies, list) and any(
            isinstance(item, str) and item.strip() for item in dependencies
        ):
            entries.append(
                {
                    "path": path or "/",
                    "deduced_from_claim": [
                        item for item in dependencies if isinstance(item, str)
                    ],
                    "available_hypotheses": local_hypotheses,
                    "container_type": value.get("type"),
                    "container": _container_summary(value),
                    "parent_type": parent.get("type") if parent else None,
                }
            )
        for key, item in value.items():
            if key == "proof_steps" and isinstance(item, list):
                entries.extend(
                    _dependency_entries(
                        item,
                        path=_child_path(path, key),
                        hypotheses=local_hypotheses,
                        parent=value,
                    )
                )
            else:
                entries.extend(
                    _dependency_entries(
                        item,
                        path=_child_path(path, key),
                        hypotheses=local_hypotheses,
                        parent=value,
                    )
                )
    elif isinstance(value, list):
        running_hypotheses = [*hypotheses]
        for index, item in enumerate(value):
            entries.extend(
                _dependency_entries(
                    item,
                    path=_child_path(path, index),
                    hypotheses=running_hypotheses,
                    parent=parent,
                )
            )
            assumption = _assumption_from_step(item)
            if assumption is not None:
                running_hypotheses.append(assumption)
                continue
            introduced_claim = _claim_introduced_by_step(item)
            if introduced_claim is not None:
                running_hypotheses.append(introduced_claim)
    return entries


def _remove_hypothesis_duplicates(value: Any, hypotheses: list[str] | None = None) -> Any:
    hypotheses = hypotheses or []
    if isinstance(value, list):
        running_hypotheses = [*hypotheses]
        cleaned = []
        for item in value:
            cleaned_item = _remove_hypothesis_duplicates(item, running_hypotheses)
            cleaned.append(cleaned_item)
            assumption = _assumption_from_step(cleaned_item)
            if assumption is not None:
                running_hypotheses.append(assumption)
                continue
            introduced_claim = _claim_introduced_by_step(cleaned_item)
            if introduced_claim is not None:
                running_hypotheses.append(introduced_claim)
        return cleaned
    if not isinstance(value, dict):
        return value

    local_hypotheses = [*hypotheses, *_hypotheses_from_container(value)]
    cleaned = {
        key: _remove_hypothesis_duplicates(item, local_hypotheses)
        for key, item in value.items()
    }
    dependencies = cleaned.get("deduced_from_claim")
    if isinstance(dependencies, list):
        remaining = [
            item
            for item in dependencies
            if not (
                isinstance(item, str)
                and any(_same_claim(item, hypothesis) for hypothesis in local_hypotheses)
            )
        ]
        if remaining:
            cleaned["deduced_from_claim"] = remaining
        else:
            cleaned.pop("deduced_from_claim", None)
    return cleaned


def _step_data(step: LogicalProofStepData) -> dict[str, Any]:
    data = step.model_dump(exclude_none=True)
    if not data.get("deduced_from_claim"):
        data.pop("deduced_from_claim", None)
    if not data.get("deduced_from_theorem"):
        data.pop("deduced_from_theorem", None)
    return data


def _remove_claims_from_dependency(parent: Any, key: str | int, patch: DeducedFromClaimPatchSpec) -> None:
    if isinstance(parent, list) and isinstance(key, int):
        target = parent[key]
    elif isinstance(parent, dict) and isinstance(key, str):
        target = parent[key]
    else:
        return
    if not isinstance(target, dict):
        return

    if patch.action == "replace_deduced_from_claim":
        remaining = patch.deduced_from_claim
    else:
        dependencies = target.get("deduced_from_claim")
        if not isinstance(dependencies, list):
            return
        remaining = [
            item
            for item in dependencies
            if not (
                isinstance(item, str)
                and any(_same_claim(item, removed) for removed in patch.remove_claims)
            )
        ]
    if remaining:
        target["deduced_from_claim"] = remaining
    else:
        target.pop("deduced_from_claim", None)


def _insert_before(root: Any, patch: DeducedFromClaimPatchSpec, item: dict[str, Any]) -> None:
    parent, key = _resolve_path(root, patch.path)
    if not isinstance(parent, list) or not isinstance(key, int):
        return
    parent.insert(key, item)
    _remove_claims_from_dependency(parent, key + 1, patch)


def _apply_patch(root: Any, patch: DeducedFromClaimPatchSpec) -> None:
    parent, key = _resolve_path(root, patch.path)
    if patch.action == "replace_deduced_from_claim":
        _remove_claims_from_dependency(parent, key, patch)
        return
    if patch.action == "insert_specialize_before":
        if not patch.name or not patch.lean_term:
            return
        _insert_before(
            root,
            patch,
            {
                key: value
                for key, value in {
                    "type": "specialize",
                    "name": patch.name,
                    "lean_term": patch.lean_term,
                    "claim": patch.claim,
                    "source_claim": patch.source_claim,
                    "arguments": patch.arguments or None,
                }.items()
                if value is not None
            },
        )
        return
    if patch.action == "insert_lemma_before":
        if not patch.name or not patch.claim or not patch.proof_steps:
            return
        _insert_before(
            root,
            patch,
            {
                "type": "theorem",
                "name": patch.name,
                "claim": patch.claim,
                "proof": {
                    "type": "proof",
                    "proof_steps": [_step_data(step) for step in patch.proof_steps],
                },
            },
        )


def apply_deduced_from_claim_patches(
    data: dict[str, Any],
    patches: list[DeducedFromClaimPatchSpec],
) -> dict[str, Any]:
    result = deepcopy(data)
    for patch in sorted(patches, key=_patch_sort_key, reverse=True):
        try:
            _apply_patch(result, patch)
        except (KeyError, IndexError, TypeError, ValueError):
            continue
    return result


def _patch_sort_key(patch: DeducedFromClaimPatchSpec) -> tuple[str, int]:
    parent_path, _, final = patch.path.rpartition("/")
    try:
        index = int(final)
    except ValueError:
        index = -1
    return (parent_path, index)


async def rewrite_deduced_from_claims_for_lean(
    data: dict[str, Any],
    agent: Any | None,
) -> dict[str, Any]:
    """Rewrite `deduced_from_claim` dependencies into Lean-friendly steps."""
    cleaned = _remove_hypothesis_duplicates(deepcopy(data))
    if agent is None:
        return cleaned
    entries = _dependency_entries(cleaned)
    if not entries:
        return cleaned
    spec = await run_agent_typed(
        agent,
        {
            "task": (
                "Rewrite generated PaperStructure JSON entries involving "
                "`deduced_from_claim` for Lean code generation."
            ),
            "dependency_entries": entries,
            "rewrite_rules": {
                "hypothesis_duplicate": (
                    "If a dependency claim is already present in available_hypotheses, "
                    "omit it from deduced_from_claim."
                ),
                "instantiation": (
                    "If the dependency is an instantiation of an available general "
                    "claim, insert a non-destructive `specialize` step before the "
                    "current object and remove the original dependency."
                ),
                "needs_proof": (
                    "If the dependency must first be proved and then used, insert a "
                    "separate local theorem before the current object and remove the "
                    "dependency from the current object."
                ),
            },
        },
        DeducedFromClaimRewriteSpec,
    )
    return apply_deduced_from_claim_patches(cleaned, spec.patches)
