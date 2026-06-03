"""Final Lean-facing JSON normalization and linting.

This pass is intentionally conservative. It enforces schema invariants that the
Lean code generator expects, and records semantic-risk diagnostics without
trying to invent missing mathematics.
"""

from __future__ import annotations

import re
from copy import deepcopy
from typing import Any

from mathdoc_agent.orchestration.deduced_from_claim_rewrite import (
    materialize_remaining_deduced_from_claims,
)


_PSEUDO_NOTATION_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"\b[A-Za-z]+_\{[^}]+\}"),
    re.compile(r"\b[A-Za-z]+_[A-Za-z0-9]+"),
    re.compile(r"\\[A-Za-z]+"),
    re.compile(r"\|\|.+?\|\|"),
    re.compile(r"‖.+?‖"),
    re.compile(r"\btensor_Z\b"),
    re.compile(r"\b[A-Za-z]+\([^)]*,[^)]*\)"),
)

_CODEGEN_STRING_FIELDS = {
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

_BUNDLED_REPRESENTATION_TERMS = (
    "GroupSeminorm",
    "AddGroupSeminorm",
    "Seminorm",
    "LengthFunction",
    "HomogeneousLengthFunction",
)


def _escape_pointer_part(part: str) -> str:
    return part.replace("~", "~0").replace("/", "~1")


def _child_path(path: str, part: str | int) -> str:
    segment = str(part) if isinstance(part, int) else _escape_pointer_part(part)
    return f"{path}/{segment}" if path else f"/{segment}"


def _issue(
    path: str,
    code: str,
    message: str,
    *,
    severity: str = "warning",
) -> dict[str, str]:
    return {
        "severity": severity,
        "path": path or "/",
        "code": code,
        "message": message,
    }


def _is_lean_identifier(value: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", value.strip()))


def _lean_identifier_from_text(value: str, *, fallback: str = "generated_name") -> str:
    words = [word for word in re.split(r"[^A-Za-z0-9]+", value) if word]
    if not words:
        words = [word for word in re.split(r"[^A-Za-z0-9]+", fallback) if word]
    if not words:
        return "generated_name"
    identifier = "_".join(word.lower() for word in words)
    if not identifier[0].isalpha():
        identifier = f"n_{identifier}"
    return identifier


def _assignment_name(value: str) -> str | None:
    match = re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*(?::=|=)", value)
    if match:
        return match.group(1)
    return None


def _source_text(value: dict[str, Any]) -> str:
    source = value.get("source")
    if isinstance(source, dict):
        text = source.get("text")
        if isinstance(text, str):
            return text
    text = value.get("text")
    return text if isinstance(text, str) else ""


def _claim_text(value: dict[str, Any]) -> str:
    claim = value.get("claim")
    if isinstance(claim, str):
        return claim
    definition = value.get("definition")
    return definition if isinstance(definition, str) else ""


def _source_declares_unbundled_function(source: str) -> bool:
    return bool(
        re.search(r"\b[A-Za-z][A-Za-z0-9_']*\s*:\s*[A-Za-z][A-Za-z0-9_']*\s*(?:->|→)\s*(?:R|ℝ|\\mathbb\{R\})\b", source)
    )


def _mentions_integer_homogeneity(source: str) -> bool:
    lowered = source.lower()
    return "homogeneous" in lowered and (
        "integer" in lowered
        or "integers" in lowered
        or " in z" in lowered
        or " in ℤ" in lowered
        or "\\mathbb{z}" in lowered
        or " n in z" in lowered
    )


def _mentions_natural_homogeneity(claim: str) -> bool:
    lowered = claim.lower()
    return "homogeneous" in lowered and (
        "natural" in lowered or "ℕ" in claim or "nat" in lowered
    )


def _validate_semantics(value: dict[str, Any], path: str) -> list[dict[str, str]]:
    source = _source_text(value)
    claim = _claim_text(value)
    if not source or not claim:
        return []

    issues: list[dict[str, str]] = []
    if _source_declares_unbundled_function(source) and any(
        term in claim for term in _BUNDLED_REPRESENTATION_TERMS
    ):
        issues.append(
            _issue(
                path,
                "representation_drift",
                (
                    "Source uses an unbundled function type, but the generated "
                    "claim uses a bundled structure/class representation."
                ),
            )
        )
    if _mentions_integer_homogeneity(source) and _mentions_natural_homogeneity(claim):
        issues.append(
            _issue(
                path,
                "integer_to_natural_drift",
                (
                    "Source states integer homogeneity, but the generated claim "
                    "appears to use natural-number homogeneity."
                ),
            )
        )
    if "multiplicative" in source.lower() and "Additive" in claim:
        issues.append(
            _issue(
                path,
                "multiplicative_to_additive_drift",
                "Source uses multiplicative language, but the claim mentions Additive.",
            )
        )
    return issues


def _lint_string_field(key: str, value: str, path: str) -> list[dict[str, str]]:
    issues: list[dict[str, str]] = []
    if key == "variable_name":
        assignment = _assignment_name(value)
        if assignment:
            issues.append(
                _issue(
                    path,
                    "assignment_in_variable_name",
                    "Variable name contained assignment syntax; normalized to the assigned identifier.",
                )
            )
            return issues
        if not _is_lean_identifier(value):
            issues.append(
                _issue(
                    path,
                    "invalid_variable_name",
                    "Variable name is not a Lean-style identifier.",
                )
            )
        return issues

    if key in _CODEGEN_STRING_FIELDS and any(
        pattern.search(value) for pattern in _PSEUDO_NOTATION_PATTERNS
    ):
        issues.append(
            _issue(
                path,
                "informal_pseudo_notation",
                "Lean-facing string contains display notation or informal local notation.",
            )
        )
    return issues


def _annotate_object(value: dict[str, Any], issues: list[dict[str, str]]) -> dict[str, Any]:
    if not issues:
        return value
    existing = value.get("lean_validation")
    if isinstance(existing, dict):
        existing_issues = existing.get("issues")
        if isinstance(existing_issues, list):
            issues = [*existing_issues, *issues]
    annotated = {**value, "lean_validation": {"status": "needs_review", "issues": issues}}
    if value.get("formalization_status") not in {"unsupported", "needs_named_lemmas"}:
        annotated["formalization_status"] = "needs_review"
    return annotated


def _normalize_theorem_dependencies(
    value: dict[str, Any],
    path: str,
) -> tuple[dict[str, Any], list[dict[str, str]]]:
    dependencies = value.get("deduced_from_theorem")
    if not isinstance(dependencies, list):
        return value, []

    normalized_dependencies: list[Any] = []
    issues: list[dict[str, str]] = []
    changed = False
    for index, item in enumerate(dependencies):
        item_path = _child_path(_child_path(path, "deduced_from_theorem"), index)
        if not isinstance(item, dict):
            normalized_dependencies.append(item)
            continue
        lean_name = item.get("lean_name")
        lean_term = item.get("lean_term")
        if (
            isinstance(lean_name, str)
            and lean_name.strip()
            and not (isinstance(lean_term, str) and lean_term.strip())
            and item.get("requires_instantiation") is True
        ):
            item = {
                **item,
                "formalization_status": item.get("formalization_status", "unresolved_lean_term"),
            }
            changed = True
            issues.append(
                _issue(
                    item_path,
                    "lean_name_without_lean_term",
                    (
                        "`lean_name` is only a declaration hint here; no exact "
                        "`lean_term` was supplied for this theorem instance."
                    ),
                )
            )
        normalized_dependencies.append(item)

    if changed:
        return {**value, "deduced_from_theorem": normalized_dependencies}, issues
    return value, issues


def _normalize_value(value: Any, path: str = "") -> tuple[Any, list[dict[str, str]]]:
    if isinstance(value, list):
        normalized_items: list[Any] = []
        issues: list[dict[str, str]] = []
        for index, item in enumerate(value):
            normalized, item_issues = _normalize_value(item, _child_path(path, index))
            normalized_items.append(normalized)
            issues.extend(item_issues)
        return normalized_items, issues

    if not isinstance(value, dict):
        return value, []

    normalized: dict[str, Any] = {}
    issues: list[dict[str, str]] = []
    local_issues: list[dict[str, str]] = []

    for key, item in value.items():
        if key == "results_used":
            local_issues.append(
                _issue(
                    _child_path(path, key),
                    "removed_results_used",
                    "`results_used` is not Lean-facing; removed it.",
                )
            )
            continue
        if key == "deduced_from_claim":
            local_issues.append(
                _issue(
                    _child_path(path, key),
                    "residual_deduced_from_claim",
                    "Residual `deduced_from_claim` should have been materialized.",
                    severity="error",
                )
            )
        if key == "variable_name" and isinstance(item, str):
            assignment = _assignment_name(item)
            if assignment:
                normalized[key] = assignment
                local_issues.extend(_lint_string_field(key, item, _child_path(path, key)))
                continue
            if not _is_lean_identifier(item):
                replacement = _lean_identifier_from_text(item, fallback="witness")
                normalized[key] = replacement
                local_issues.extend(_lint_string_field(key, item, _child_path(path, key)))
                continue
        child, child_issues = _normalize_value(item, _child_path(path, key))
        normalized[key] = child
        issues.extend(child_issues)
        if isinstance(item, str):
            local_issues.extend(_lint_string_field(key, item, _child_path(path, key)))

    normalized, dependency_issues = _normalize_theorem_dependencies(normalized, path)
    local_issues.extend(dependency_issues)
    local_issues.extend(_validate_semantics(normalized, path))
    if local_issues:
        normalized = _annotate_object(normalized, local_issues)
        issues.extend(local_issues)
    return normalized, issues


def finalize_lean_facing_json(data: dict[str, Any]) -> dict[str, Any]:
    """Return JSON normalized for Lean codegen plus structured lint metadata."""
    materialized = materialize_remaining_deduced_from_claims(deepcopy(data))
    normalized, issues = _normalize_value(materialized)
    if not isinstance(normalized, dict):
        return {"document": normalized, "lean_validation": {"status": "needs_review", "issues": issues}}
    if issues:
        top_validation = normalized.get("lean_validation")
        top_issues: list[Any] = []
        if isinstance(top_validation, dict) and isinstance(top_validation.get("issues"), list):
            top_issues = list(top_validation["issues"])
        normalized["lean_validation"] = {
            "status": "needs_review",
            "issues": [*top_issues, *issues],
        }
    return normalized
