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
    "claim_label",
    "start",
    "target",
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

_SOURCE_CONTEXT_PREFIXES = (
    "let ",
    "assume ",
    "assume that ",
    "suppose ",
    "suppose that ",
    "fix ",
)

_LOCAL_DEFINITION_PREFIXES = (
    "let ",
    "define ",
    "set ",
    "put ",
    "write ",
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


def _camel_token(value: str) -> str:
    words = [word for word in re.split(r"[^A-Za-z0-9]+", value) if word]
    if not words:
        return ""
    return "".join(word[:1].upper() + word[1:] for word in words)


def _ascii_identifier(value: str, *, fallback: str = "localObject") -> str:
    value = value.strip().strip("$")
    value = re.sub(
        r"\\([A-Za-z]+)\s*\{([^{}]+)\}",
        lambda match: match.group(1) + _camel_token(match.group(2)),
        value,
    )
    value = re.sub(
        r"([A-Za-z]+)_\{([^{}]+)\}",
        lambda match: match.group(1) + _camel_token(match.group(2)),
        value,
    )
    value = re.sub(
        r"([A-Za-z]+)_([A-Za-z0-9]+)",
        lambda match: match.group(1) + _camel_token(match.group(2)),
        value,
    )
    value = re.sub(r"\\([A-Za-z]+)", r"\1", value)
    parts = [part for part in re.split(r"[^A-Za-z0-9_']+", value) if part]
    if not parts:
        return fallback
    identifier = "".join(parts)
    if not re.match(r"[A-Za-z_]", identifier):
        identifier = f"n{identifier}"
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


def _normalize_source_context_text(text: str) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    text = text.replace("\\(", "").replace("\\)", "")
    text = text.replace("$", "")
    return text[:-1].strip() if text.endswith(".") else text


def _split_source_context_sentences(source: str) -> list[str]:
    source = source.strip()
    if not source:
        return []
    source = re.sub(r"\s+", " ", source)
    source = re.sub(r"\$\$(.*?)\$\$", " ", source)
    return [
        sentence.strip()
        for sentence in re.split(r"(?<=[.!?])\s+", source)
        if sentence.strip()
    ]


def _definition_body(sentence: str) -> str | None:
    text = _normalize_source_context_text(sentence)
    lowered = text.lower()
    for prefix in _LOCAL_DEFINITION_PREFIXES:
        if lowered.startswith(prefix):
            return text[len(prefix) :].strip()
    return None


def _argument_names(raw_args: str) -> list[str]:
    args: list[str] = []
    for raw_arg in raw_args.split(","):
        arg = raw_arg.strip()
        if not arg:
            continue
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", arg):
            args.append(arg)
        else:
            args.append(_ascii_identifier(arg, fallback="arg"))
    return args


def _function_definition_step(body: str) -> dict[str, Any] | None:
    match = re.match(
        r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*\(([^()]*)\)\s*(?::=|=|is defined as)\s*(.+?)\s*$",
        body,
        flags=re.IGNORECASE,
    )
    if not match:
        return None
    name = _ascii_identifier(match.group(1))
    args = _argument_names(match.group(2))
    rhs = match.group(3).strip()
    value = f"fun {' '.join(args)} => {rhs}" if args else rhs
    return {
        "type": "let_statement",
        "variable_name": name,
        "value": value,
        "statement": f"Let {name} be defined by {name} applied to {' and '.join(args)} = {rhs}.",
    }


def _object_definition_step(body: str) -> dict[str, Any] | None:
    match = re.match(
        r"\s*([A-Za-z_][A-Za-z0-9_']*|[A-Za-z]+_\{[^{}]+\}|[A-Za-z]+_[A-Za-z0-9]+)\s*(?::=|=|is defined as)\s*(.+?)\s*$",
        body,
        flags=re.IGNORECASE,
    )
    if not match:
        return None
    name = _ascii_identifier(match.group(1))
    rhs = match.group(2).strip()
    return {
        "type": "let_statement",
        "variable_name": name,
        "value": rhs,
        "statement": f"Let {name} be defined as {rhs}.",
    }


def _definition_step_from_sentence(sentence: str) -> dict[str, Any] | None:
    body = _definition_body(sentence)
    if body is None:
        return None
    return _function_definition_step(body) or _object_definition_step(body)


def _source_context_steps(source: str) -> list[dict[str, Any]]:
    steps: list[dict[str, Any]] = []
    for sentence in _split_source_context_sentences(source):
        lowered = sentence.lower()
        if lowered.startswith(("then ", "therefore ", "hence ")):
            break
        if re.match(r"^(for every|for all|if)\b", lowered):
            break
        definition_step = _definition_step_from_sentence(sentence)
        if definition_step is not None:
            steps.append(definition_step)
            continue
        if lowered.startswith(_SOURCE_CONTEXT_PREFIXES):
            steps.append(
                {
                    "type": "assume_statement",
                    "assumption": _normalize_source_context_text(sentence),
                }
            )
            continue
        if steps:
            break
    return steps


def _same_text(left: str, right: str) -> bool:
    return " ".join(left.split()).casefold() == " ".join(right.split()).casefold()


def _promote_source_context_hypotheses(value: dict[str, Any]) -> dict[str, Any]:
    if value.get("type") != "theorem":
        return value
    context_steps = _source_context_steps(_source_text(value))
    if not context_steps:
        return value
    existing = value.get("hypothesis")
    hypotheses = list(existing) if isinstance(existing, list) else []
    existing_assumptions = [
        item.get("assumption")
        for item in hypotheses
        if isinstance(item, dict) and isinstance(item.get("assumption"), str)
    ]
    existing_defs = {
        item.get("variable_name")
        for item in hypotheses
        if isinstance(item, dict)
        and item.get("type") == "let_statement"
        and isinstance(item.get("variable_name"), str)
    }
    added = False
    for step in context_steps:
        if step.get("type") == "let_statement":
            variable_name = step.get("variable_name")
            if isinstance(variable_name, str) and variable_name in existing_defs:
                continue
            hypotheses.append(step)
            if isinstance(variable_name, str):
                existing_defs.add(variable_name)
            added = True
            continue
        assumption = step.get("assumption")
        if not isinstance(assumption, str):
            continue
        if any(_same_text(assumption, existing_item) for existing_item in existing_assumptions):
            continue
        hypotheses.append(step)
        existing_assumptions.append(assumption)
        added = True
    if not added:
        return value
    return {**value, "hypothesis": hypotheses}


def _repair_stale_materialized_claim_obligation(value: dict[str, Any]) -> dict[str, Any]:
    if (
        value.get("type") != "assert_statement"
        or value.get("proof_method") != "Materialized from deduced_from_claim."
    ):
        return value
    claim = value.get("claim")
    if not isinstance(claim, str) or not claim.strip():
        return value
    repaired = {
        **value,
        "proof_method": "Named local obligation from unresolved claim dependency.",
    }
    repaired.setdefault("name", _lean_identifier_from_text(claim, fallback="local_obligation"))
    source = repaired.get("source")
    if not isinstance(source, dict):
        repaired["source"] = {"text": claim, "kind": "deduced_from_claim"}
    else:
        repaired["source"] = {
            **source,
            "text": source.get("text") if isinstance(source.get("text"), str) else claim,
            "kind": source.get("kind") if isinstance(source.get("kind"), str) else "deduced_from_claim",
        }
    return repaired


def _local_definition_from_step(value: dict[str, Any]) -> dict[str, Any] | None:
    step_type = value.get("type")
    if step_type not in {"let_statement", "assume_statement", "assert_statement"}:
        return None
    text_key = {
        "let_statement": "statement",
        "assume_statement": "assumption",
        "assert_statement": "claim",
    }.get(str(step_type))
    text = value.get(text_key) if text_key is not None else None
    if not isinstance(text, str) or not text.strip():
        return None
    definition_step = _definition_step_from_sentence(text)
    if definition_step is None:
        return None
    preserved = {
        key: item
        for key, item in value.items()
        if key
        not in {
            "type",
            "claim",
            "assumption",
            "proof_method",
            "deduced_from_claim",
            "deduced_from_theorem",
        }
    }
    return {**preserved, **definition_step}


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
        ):
            item = {
                key: entry
                for key, entry in item.items()
                if key != "lean_name"
            }
            item.setdefault("lean_name_candidate", lean_name)
            item.setdefault("verification_status", "unverified")
            changed = True
            normalized_dependencies.append(item)
            continue
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
    local_definition = _local_definition_from_step(normalized)
    if local_definition is not None:
        normalized = local_definition
        local_issues = [
            issue
            for issue in local_issues
            if issue["code"] != "informal_pseudo_notation"
        ]
    normalized = _repair_stale_materialized_claim_obligation(normalized)
    normalized = _promote_source_context_hypotheses(normalized)
    local_issues.extend(dependency_issues)
    local_issues.extend(_validate_semantics(normalized, path))
    if local_issues:
        normalized = _annotate_object(normalized, local_issues)
        issues.extend(local_issues)
    return normalized, issues


def flatten_redundant_proof_wrappers(value: Any) -> Any:
    """Flatten unlabeled linear proof wrappers inside ``proof_steps`` lists.

    Late repair passes can materialize an assertion and its dependencies as an
    anonymous ``{"type": "proof", "proof_steps": [...]}`` item.  Such an item
    is only a sequential grouping: leaving it nested makes codegen treat the
    end of the group as the end of a proof.  Proof objects owned by structural
    nodes (for example induction branches) and labeled local proofs are kept.
    """
    if isinstance(value, list):
        return [flatten_redundant_proof_wrappers(item) for item in value]
    if not isinstance(value, dict):
        return value

    normalized = {
        key: flatten_redundant_proof_wrappers(item)
        for key, item in value.items()
    }
    proof_steps = normalized.get("proof_steps")
    if not isinstance(proof_steps, list):
        return normalized

    flattened: list[Any] = []
    for step in proof_steps:
        if not isinstance(step, dict) or step.get("type") != "proof":
            flattened.append(step)
            continue
        claim_label = step.get("claim_label")
        nested_steps = step.get("proof_steps")
        if (
            isinstance(claim_label, str) and claim_label.strip()
        ) or not isinstance(nested_steps, list):
            flattened.append(step)
            continue
        flattened.extend(nested_steps)
    normalized["proof_steps"] = flattened
    return normalized


def finalize_lean_facing_json(data: dict[str, Any]) -> dict[str, Any]:
    """Return JSON normalized for Lean codegen plus structured lint metadata."""
    materialized = materialize_remaining_deduced_from_claims(deepcopy(data))
    flattened = flatten_redundant_proof_wrappers(materialized)
    normalized, issues = _normalize_value(flattened)
    if not isinstance(normalized, dict):
        return {
            "document": normalized,
            "lean_validation": {"status": "needs_review", "issues": issues},
        }
    validation_container = normalized
    document = normalized.get("document")
    root_validation: Any = None
    if isinstance(document, dict):
        validation_container = document
        root_validation = normalized.pop("lean_validation", None)
    existing_validation = validation_container.get("lean_validation")
    prior_issues: list[Any] = []
    for validation in (root_validation, existing_validation):
        if isinstance(validation, dict) and isinstance(
            validation.get("issues"), list
        ):
            prior_issues.extend(validation["issues"])
    if issues or prior_issues:
        combined_issues: list[Any] = []
        seen: set[str] = set()
        for issue in [*prior_issues, *issues]:
            key = repr(issue)
            if key in seen:
                continue
            seen.add(key)
            combined_issues.append(issue)
        validation_container["lean_validation"] = {
            "status": "needs_review",
            "issues": combined_issues,
        }
    return normalized
