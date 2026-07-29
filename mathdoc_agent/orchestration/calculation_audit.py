"""Close and audit exported calculation proofs before Lean generation."""

from __future__ import annotations

import re
from copy import deepcopy
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.refinement_specs import (
    CalculationAuditPatchSpec,
    CalculationAuditSpec,
)


RELATION_ALIASES = {
    "=": "=",
    "<=": "≤",
    "≤": "≤",
    "<": "<",
    ">=": "≥",
    "≥": "≥",
    ">": ">",
    "<->": "↔",
    "↔": "↔",
    "->": "→",
    "→": "→",
}


def _child_path(path: str, part: str | int) -> str:
    escaped = str(part).replace("~", "~0").replace("/", "~1")
    return f"{path}/{escaped}" if path else f"/{escaped}"


def _unescape_pointer_part(part: str) -> str:
    return part.replace("~1", "/").replace("~0", "~")


def _resolve_path(root: Any, path: str) -> tuple[Any, str | int]:
    if not path.startswith("/"):
        raise ValueError(f"Expected JSON pointer path, got {path!r}")
    parts = [_unescape_pointer_part(part) for part in path.split("/")[1:]]
    if not parts:
        raise ValueError("Cannot patch the root")
    current = root
    for part in parts[:-1]:
        current = current[int(part)] if isinstance(current, list) else current[part]
    key: str | int = int(parts[-1]) if isinstance(current, list) else parts[-1]
    return current, key


def _normalized_expression(value: str) -> str:
    normalized = value.casefold()
    normalized = normalized.replace("≤", "<=").replace("≥", ">=")
    normalized = normalized.replace("⁻¹", "^-1")
    normalized = re.sub(r"\bapplied\s+to\b", "", normalized)
    normalized = re.sub(r"\binverse\b", "^-1", normalized)
    normalized = re.sub(r"\\(?:left|right)", "", normalized)
    normalized = re.sub(r"[\s_{}()]", "", normalized)
    normalized = normalized.replace("*", "")
    return normalized.rstrip(".")


def _same_expression(left: str | None, right: str | None) -> bool:
    return (
        isinstance(left, str)
        and isinstance(right, str)
        and _normalized_expression(left) == _normalized_expression(right)
    )


def _linked_calculation_steps(
    value: dict[str, Any],
) -> list[tuple[int, dict[str, Any]]]:
    proof_steps = value.get("proof_steps")
    if not isinstance(proof_steps, list):
        return []
    return [
        (index, step)
        for index, step in enumerate(proof_steps)
        if isinstance(step, dict)
        and step.get("calculation_conclusion") is not True
        and isinstance(step.get("from"), str)
        and isinstance(step.get("relation"), str)
        and isinstance(step.get("to"), str)
    ]


def _claim_endpoints(value: dict[str, Any]) -> tuple[str, str, str] | None:
    label = value.get("claim_label")
    if not isinstance(label, str):
        return None
    relations = ("<->", "↔", "<=", "≤", ">=", "≥", "->", "→", "=", "<", ">")
    depths = {"(": 0, "[": 0, "{": 0}
    closers = {")": "(", "]": "[", "}": "{"}
    index = 0
    while index < len(label):
        character = label[index]
        if character in depths:
            depths[character] += 1
            index += 1
            continue
        if character in closers:
            opener = closers[character]
            depths[opener] = max(0, depths[opener] - 1)
            index += 1
            continue
        if not any(depths.values()):
            relation = next(
                (candidate for candidate in relations if label.startswith(candidate, index)),
                None,
            )
            if relation is not None:
                left = label[:index].strip()
                right = label[index + len(relation) :].strip()
                if left and right:
                    return left, RELATION_ALIASES.get(relation, relation), right
        index += 1
    return None


def _calculation_steps(value: dict[str, Any]) -> list[tuple[int, dict[str, Any]]]:
    """Return the linked chain proving the declared overall claim.

    Calculation proofs may contain auxiliary equations before or between the
    steps of the main chain. Select the first step starting at the overall
    claim's left endpoint (or the declared start) and then follow matching
    endpoints, leaving unrelated equations as ordinary supporting assertions.
    """
    linked = _linked_calculation_steps(value)
    if not linked:
        return []
    endpoints = _claim_endpoints(value)
    desired_start = endpoints[0] if endpoints is not None else value.get("start")
    start_offset = next(
        (
            offset
            for offset, (_, step) in enumerate(linked)
            if _same_expression(step.get("from"), desired_start)
        ),
        None,
    )
    if start_offset is None:
        return linked
    chain = [linked[start_offset]]
    for candidate in linked[start_offset + 1 :]:
        if _same_expression(chain[-1][1].get("to"), candidate[1].get("from")):
            chain.append(candidate)
    return chain


def _canonicalize_calculation_bounds(data: dict[str, Any]) -> dict[str, Any]:
    """Align start/target with claim_label when actual linked steps use them."""
    result = deepcopy(data)

    def visit(value: Any) -> None:
        if isinstance(value, dict):
            if value.get("type") == "proof" and isinstance(
                value.get("calculation_kind"), str
            ):
                endpoints = _claim_endpoints(value)
                linked = _linked_calculation_steps(value)
                if endpoints is not None:
                    left, overall_relation, right = endpoints
                    label = value.get("claim_label")
                    for _, step in linked:
                        step_relation = RELATION_ALIASES.get(
                            step.get("relation"),
                            step.get("relation"),
                        )
                        if (
                            _same_expression(step.get("from"), left)
                            and _same_expression(step.get("to"), right)
                            and step_relation == overall_relation
                            and _same_expression(step.get("claim"), label)
                            and isinstance(step.get("proof_method"), str)
                            and step["proof_method"].strip()
                        ):
                            # Some refiners already emitted the correct overall
                            # assertion as the final DAG node. Mark it instead of
                            # appending a duplicate transitivity assertion.
                            step["calculation_conclusion"] = True
                    if any(_same_expression(step.get("from"), left) for _, step in linked):
                        value["start"] = left
                    if any(_same_expression(step.get("to"), right) for _, step in linked):
                        value["target"] = right
            for item in value.values():
                visit(item)
        elif isinstance(value, list):
            for item in value:
                visit(item)

    visit(result)
    return result


def _infer_relation(steps: list[tuple[int, dict[str, Any]]]) -> str | None:
    relations = {
        RELATION_ALIASES.get(step["relation"], step["relation"])
        for _, step in steps
    }
    relations.discard("=")
    if not relations:
        return "=" if steps else None
    if relations <= {"≤", "<"}:
        return "<" if "<" in relations else "≤"
    if relations <= {"≥", ">"}:
        return ">" if ">" in relations else "≥"
    if len(relations) == 1:
        return next(iter(relations))
    return None


def _expected_claim(value: dict[str, Any], relation: str | None) -> str | None:
    label = value.get("claim_label")
    if isinstance(label, str) and label.strip():
        return label.strip()
    start = value.get("start")
    target = value.get("target")
    if isinstance(start, str) and isinstance(target, str) and relation:
        return f"{start} {relation} {target}"
    return None


def _has_terminal_conclusion(value: dict[str, Any], expected: str | None) -> bool:
    if expected is None:
        return False
    proof_steps = value.get("proof_steps")
    if not isinstance(proof_steps, list):
        return False
    return any(
        isinstance(step, dict)
        and step.get("calculation_conclusion") is True
        and _same_expression(step.get("claim"), expected)
        for step in proof_steps
    )


def _calculation_issues(value: dict[str, Any]) -> list[dict[str, str]]:
    issues: list[dict[str, str]] = []
    steps = _calculation_steps(value)
    start = value.get("start")
    target = value.get("target")
    relation = _infer_relation(steps)
    expected = _expected_claim(value, relation)
    has_terminal_conclusion = _has_terminal_conclusion(value, expected)
    if not steps:
        if has_terminal_conclusion:
            return issues
        issues.append({"code": "no_calculation_steps", "message": "No linked calculation steps."})
        return issues
    if not _same_expression(start, steps[0][1].get("from")):
        issues.append(
            {
                "code": "calculation_start_mismatch",
                "message": f"Declared start {start!r} does not match first endpoint {steps[0][1].get('from')!r}.",
            }
        )
    for offset in range(1, len(steps)):
        previous = steps[offset - 1][1]
        current = steps[offset][1]
        if not _same_expression(previous.get("to"), current.get("from")):
            issues.append(
                {
                    "code": "calculation_gap",
                    "message": f"Step {steps[offset - 1][0]} ends at {previous.get('to')!r}, but step {steps[offset][0]} starts at {current.get('from')!r}.",
                }
            )
    if (
        not has_terminal_conclusion
        and not _same_expression(steps[-1][1].get("to"), target)
    ):
        issues.append(
            {
                "code": "calculation_target_mismatch",
                "message": f"Last endpoint {steps[-1][1].get('to')!r} does not match target {target!r}.",
            }
        )
    if relation is None:
        issues.append(
            {
                "code": "incompatible_calculation_relations",
                "message": "The step relations do not compose to one conclusion relation.",
            }
        )
    if not has_terminal_conclusion:
        issues.append(
            {
                "code": "missing_calculation_conclusion",
                "message": f"The structured proof has no explicit terminal assertion {expected!r}.",
            }
        )
    return issues


def calculation_audit_entries(value: Any, *, path: str = "") -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    if isinstance(value, dict):
        if value.get("type") == "proof" and isinstance(value.get("calculation_kind"), str):
            issues = _calculation_issues(value)
            if issues:
                entries.append(
                    {
                        "path": path or "/",
                        "claim_label": value.get("claim_label"),
                        "calculation_kind": value.get("calculation_kind"),
                        "start": value.get("start"),
                        "target": value.get("target"),
                        "proof_text": value.get("text"),
                        "steps": [step for _, step in _calculation_steps(value)],
                        "issues": issues,
                    }
                )
        for key, item in value.items():
            entries.extend(calculation_audit_entries(item, path=_child_path(path, key)))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            entries.extend(calculation_audit_entries(item, path=_child_path(path, index)))
    return entries


def _append_conclusion(value: dict[str, Any], patch: CalculationAuditPatchSpec) -> None:
    conclusion = patch.conclusion
    if conclusion is None:
        return
    steps = value.get("proof_steps")
    if not isinstance(steps, list):
        return
    if any(
        isinstance(step, dict)
        and step.get("calculation_conclusion") is True
        and _same_expression(step.get("claim"), conclusion.claim)
        for step in steps
    ):
        return
    step: dict[str, Any] = {
        "type": "assert_statement",
        "claim": conclusion.claim,
        "proof_method": conclusion.proof_method,
        "calculation_conclusion": True,
    }
    if conclusion.start is not None:
        step["from"] = conclusion.start
    if conclusion.relation is not None:
        step["relation"] = conclusion.relation
    if conclusion.target is not None:
        step["to"] = conclusion.target
    if conclusion.side_conditions:
        step["side_conditions"] = conclusion.side_conditions
    steps.append(step)


def apply_calculation_audit_patches(
    data: dict[str, Any],
    patches: list[CalculationAuditPatchSpec],
) -> dict[str, Any]:
    result = deepcopy(data)
    for patch in patches:
        try:
            proof_parent, proof_key = _resolve_path(result, patch.path)
            proof = proof_parent[proof_key]
            if not isinstance(proof, dict):
                continue
            for string_patch in patch.string_patches:
                if not string_patch.path.startswith(f"{patch.path}/"):
                    continue
                parent, key = _resolve_path(result, string_patch.path)
                if isinstance(parent, dict) and isinstance(key, str):
                    parent[key] = string_patch.replacement
            _append_conclusion(proof, patch)
        except (KeyError, IndexError, TypeError, ValueError):
            continue
    return result


def _deterministic_closure_patches(data: dict[str, Any]) -> list[CalculationAuditPatchSpec]:
    patches: list[CalculationAuditPatchSpec] = []
    for entry in calculation_audit_entries(data):
        codes = {issue["code"] for issue in entry["issues"]}
        if codes != {"missing_calculation_conclusion"}:
            continue
        parent, key = _resolve_path(data, entry["path"])
        proof = parent[key]
        steps = _calculation_steps(proof)
        relation = _infer_relation(steps)
        expected = _expected_claim(proof, relation)
        if expected is None or relation is None:
            continue
        patches.append(
            CalculationAuditPatchSpec(
                path=entry["path"],
                conclusion={
                    "claim": expected,
                    "proof_method": "By transitivity of the preceding calculation steps.",
                    "start": proof.get("start"),
                    "relation": relation,
                    "target": proof.get("target"),
                },
            )
        )
    return patches


def _append_calculation_validation(
    data: dict[str, Any],
    entries: list[dict[str, Any]],
) -> dict[str, Any]:
    document = data.get("document")
    container = document if isinstance(document, dict) else data
    existing = container.get("lean_validation")
    calculation_codes = {
        "no_calculation_steps",
        "calculation_start_mismatch",
        "calculation_gap",
        "calculation_target_mismatch",
        "incompatible_calculation_relations",
        "missing_calculation_conclusion",
    }
    prior = (
        [
            issue
            for issue in existing.get("issues", [])
            if not (
                isinstance(issue, dict)
                and issue.get("code") in calculation_codes
            )
        ]
        if isinstance(existing, dict) and isinstance(existing.get("issues"), list)
        else []
    )
    issues = [
        {
            "path": entry["path"],
            "code": issue["code"],
            "message": issue["message"],
        }
        for entry in entries
        for issue in entry["issues"]
    ]
    combined = [*prior, *issues]
    if combined:
        container["lean_validation"] = {
            "status": "needs_review",
            "issues": combined,
        }
    else:
        container.pop("lean_validation", None)
    return data


async def audit_calculations_for_lean(
    data: dict[str, Any],
    agent: Any | None,
) -> dict[str, Any]:
    """Repair calculation gaps and require an explicit overall conclusion."""
    result = _canonicalize_calculation_bounds(data)
    result = apply_calculation_audit_patches(
        result,
        _deterministic_closure_patches(result),
    )
    entries = calculation_audit_entries(result)
    if entries and agent is not None:
        spec = await run_agent_typed(
            agent,
            {
                "task": (
                    "Audit every structured calculation for semantic continuity and "
                    "an explicit terminal assertion equal to its declared claim/target."
                ),
                "calculation_entries": entries,
                "patch_rules": {
                    "string_patches": (
                        "Repair a start, target, from, or to string only when the proof "
                        "text shows that the expressions are the same endpoint."
                    ),
                    "conclusion": (
                        "Append the complete overall relation proved by the chain. It "
                        "must match claim_label when present and cite transitivity plus "
                        "the preceding steps."
                    ),
                    "no_invention": (
                        "Do not bridge a genuine mathematical gap. Leave it unpatched "
                        "so deterministic validation marks it needs_review."
                    ),
                },
            },
            CalculationAuditSpec,
        )
        result = apply_calculation_audit_patches(result, spec.patches)
    return _append_calculation_validation(result, calculation_audit_entries(result))
