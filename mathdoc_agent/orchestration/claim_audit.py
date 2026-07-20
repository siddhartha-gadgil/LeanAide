"""LLM-backed repair pass for exported claim fields.

The Lean code generator treats every public `claim` field as a proposition to
translate into a theorem or `have` type. This module keeps the check semantic by
asking a bounded agent for structured patches instead of relying on string
heuristics.
"""

from __future__ import annotations

import os
import re
from copy import deepcopy
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.payloads import LogicalProofStepData
from mathdoc_agent.models.refinement_specs import ClaimAuditSpec, ClaimPatchSpec


_DEFAULT_BATCH_SIZE = 30


def _batch_size() -> int:
    """Return the bounded number of claims sent in one audit request."""
    raw = os.environ.get("MATHDOC_AGENT_CLAIM_AUDIT_BATCH_SIZE")
    if raw is None:
        return _DEFAULT_BATCH_SIZE
    try:
        value = int(raw)
    except ValueError:
        return _DEFAULT_BATCH_SIZE
    return max(1, value)


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


def _source_text(value: dict[str, Any]) -> str | None:
    """Return source prose attached to a generated object, when present."""
    source = value.get("source")
    if isinstance(source, dict):
        text = source.get("text")
        if isinstance(text, str) and text.strip():
            return text.strip()
    if isinstance(source, str) and source.strip():
        return source.strip()
    return None


def _hypothesis_summary(item: Any) -> dict[str, Any] | str | None:
    """Keep only formalization-relevant fields from one hypothesis entry."""
    if isinstance(item, str):
        return item
    if not isinstance(item, dict):
        return None
    summary: dict[str, Any] = {}
    for key in (
        "type",
        "name",
        "assumption",
        "statement",
        "claim",
        "variable_name",
        "variable_type",
        "value",
        "lean_term",
    ):
        value = item.get(key)
        if value is not None:
            summary[key] = value
    return summary or None


def _theorem_context(value: dict[str, Any], path: str) -> dict[str, Any]:
    """Build compact source/formal context for all claims inside a theorem."""
    context: dict[str, Any] = {
        "path": path or "/",
        "type": value.get("type"),
    }
    for key in ("name", "label", "header"):
        item = value.get(key)
        if item is not None:
            context[key] = item
    source = _source_text(value)
    if source is not None:
        context["source_text"] = source
    hypotheses = value.get("hypothesis")
    if isinstance(hypotheses, list):
        compact = [
            summary
            for item in hypotheses
            if (summary := _hypothesis_summary(item)) is not None
        ]
        if compact:
            context["hypotheses"] = compact
    return context


def _available_declarations(value: Any, *, path: str = "") -> list[dict[str, Any]]:
    """Collect compact summaries of named declarations visible in the document."""
    declarations: list[dict[str, Any]] = []
    if isinstance(value, dict):
        name = value.get("name")
        kind = value.get("type")
        if isinstance(name, str) and name.strip() and kind in {
            "definition",
            "theorem",
            "structure",
            "class",
            "inductive",
            "abbrev",
        }:
            declaration: dict[str, Any] = {
                "path": path or "/",
                "type": kind,
                "name": name,
            }
            for key in ("label", "claim", "definition", "statement"):
                item = value.get(key)
                if isinstance(item, str) and item.strip():
                    declaration[key] = item.strip()
            declarations.append(declaration)
        for key, item in value.items():
            declarations.extend(
                _available_declarations(item, path=_child_path(path, key))
            )
    elif isinstance(value, list):
        for index, item in enumerate(value):
            declarations.extend(
                _available_declarations(item, path=_child_path(path, index))
            )
    return declarations


def _claim_scope(value: dict[str, Any], theorem_path: str | None) -> str:
    """Describe which closure rule applies to a claim."""
    if value.get("type") == "theorem" and theorem_path is not None:
        return "theorem_statement"
    if theorem_path is not None:
        return "local_claim_inside_theorem"
    return "standalone_claim"


def _closure_risks(
    claim: str,
    scope: str,
    enclosing_theorem: dict[str, Any] | None,
) -> list[str]:
    """Describe generic evidence that a theorem claim needs explicit closure."""
    if scope != "theorem_statement" or enclosing_theorem is None:
        return []

    risks: list[str] = []
    hypotheses = enclosing_theorem.get("hypotheses")
    if isinstance(hypotheses, list):
        local_names = [
            item.get("variable_name")
            for item in hypotheses
            if isinstance(item, dict)
            and item.get("type") == "let_statement"
            and isinstance(item.get("variable_name"), str)
        ]
        missing_local_names = [
            name
            for name in local_names
            if not re.search(rf"\blet\s+{re.escape(name)}\b", claim)
        ]
        if missing_local_names:
            risks.append(
                "Structured local definitions must be reproduced as Lean `let` "
                f"binders with the same names: {', '.join(missing_local_names)}."
            )

    source = enclosing_theorem.get("source_text")
    if (
        isinstance(source, str)
        and (
            ":=" in source
            or re.search(r"\b(?:define|defined|set)\b", source, flags=re.IGNORECASE)
        )
        and not re.search(r"\blet\s+[A-Za-z_][A-Za-z0-9_']*[^;]*:=", claim)
    ):
        risks.append(
            "The source introduces local notation or an assigned value; source prose "
            "does not put that identifier in Lean scope."
        )

    if re.search(
        r"\b(?:expectation|finite average|random variable)\b",
        claim,
        re.IGNORECASE,
    ):
        risks.append(
            "The claim uses probability language that requires an explicit finite "
            "average or a fully bound probability context."
        )
    if re.search(r"\bdefined\s+as\b", claim, re.IGNORECASE):
        risks.append(
            "The claim contains an assignment-like phrase; use a Lean `let` binder."
        )
    return risks


def _claim_entries(
    value: Any,
    *,
    path: str = "",
    parent: dict[str, Any] | None = None,
    enclosing_theorem: dict[str, Any] | None = None,
    theorem_path: str | None = None,
) -> list[dict[str, Any]]:
    """Collect public claim fields with enough context for an LLM audit."""
    entries: list[dict[str, Any]] = []
    if isinstance(value, dict):
        if value.get("type") == "theorem":
            enclosing_theorem = _theorem_context(value, path)
            theorem_path = path
        claim = value.get("claim")
        if isinstance(claim, str):
            scope = _claim_scope(value, theorem_path)
            entry = {
                "path": _child_path(path, "claim"),
                "claim": claim,
                "claim_scope": scope,
                "container_type": value.get("type"),
                "container": _container_summary(value),
                "parent_type": parent.get("type") if parent else None,
                "can_replace_assertion_with_steps": (
                    value.get("type") == "assert_statement"
                ),
            }
            if enclosing_theorem is not None:
                entry["enclosing_theorem"] = enclosing_theorem
            risks = _closure_risks(claim, scope, enclosing_theorem)
            if risks:
                entry["requires_closed_lean_repair"] = True
                entry["closure_risks"] = risks
            entries.append(entry)
        for key, item in value.items():
            entries.extend(
                _claim_entries(
                    item,
                    path=_child_path(path, key),
                    parent=value,
                    enclosing_theorem=enclosing_theorem,
                    theorem_path=theorem_path,
                )
            )
    elif isinstance(value, list):
        for index, item in enumerate(value):
            entries.extend(
                _claim_entries(
                    item,
                    path=_child_path(path, index),
                    parent=parent,
                    enclosing_theorem=enclosing_theorem,
                    theorem_path=theorem_path,
                )
            )
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
    declarations = _available_declarations(data)
    specs: list[ClaimAuditSpec] = []
    batch_size = _batch_size()
    for start in range(0, len(entries), batch_size):
        batch = entries[start : start + batch_size]
        spec = await run_agent_typed(
            agent,
            {
                "task": (
                    "Audit generated PaperStructure JSON claim fields for Lean "
                    "CodegenCore/PaperCodes proposition compatibility and formal "
                    "context closure."
                ),
                "claim_entries": batch,
                "available_declarations": declarations,
                "closure_rules": {
                    "theorem_statement": (
                        "If closure repair is needed, replace the claim with a complete "
                        "Lean 4 proposition term: quantify every variable, include every "
                        "class/predicate hypothesis, and introduce each local definition "
                        "with `let`. English quantifier prose and assignment-shaped "
                        "antecedents do not count as closure."
                    ),
                    "required_repair": (
                        "Every entry with `requires_closed_lean_repair: true` must "
                        "receive a `replace_claim` patch containing a complete Lean 4 "
                        "proposition term that resolves every listed `closure_risks` item."
                    ),
                    "preserve_local_names": (
                        "Use the exact `variable_name` supplied by structured "
                        "`let_statement` hypotheses for the corresponding Lean `let`; "
                        "do not rename that local definition."
                    ),
                    "bundled_structures": (
                        "Bind bundled Lean objects (for example seminorms, morphisms, "
                        "linear maps, and measures) directly at their structure type and "
                        "use coercion; do not apply the structure type as a predicate to "
                        "a separately bound function."
                    ),
                    "local_claim_inside_theorem": (
                        "The claim may use actual binders from the enclosing closed "
                        "theorem and preceding structured local steps, but not names "
                        "introduced only in prose."
                    ),
                    "finite_probability": (
                        "When a source completely specifies a finite uniform experiment, "
                        "use Lean finite types/functions for the product sample space and "
                        "a `Fintype.card`-normalized `Finset.univ` sum. Otherwise bind the "
                        "required probability objects and assumptions explicitly; never "
                        "leave free expectation notation."
                    ),
                },
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
        specs.append(spec)
    patches = [patch for spec in specs for patch in spec.patches]
    return apply_claim_patches(data, patches)
