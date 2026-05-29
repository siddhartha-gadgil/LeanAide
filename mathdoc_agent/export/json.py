from __future__ import annotations

import json
import re
from typing import Any

from pydantic import BaseModel

from mathdoc_agent.models.base import DocumentKind, ProofKind
from mathdoc_agent.models.document import DocumentNode, MathDocument
from mathdoc_agent.models.payloads import (
    CalcStep,
    CalculationData,
    CasesData,
    DefinitionData,
    InductionData,
    InductiveTypeDefinitionData,
    InstanceDefinitionData,
    SimpleProofData,
    SpecializeData,
    StatementData,
    StructureDefinitionData,
    StructuredProofData,
)
from mathdoc_agent.models.proof import ProofNode, ProofTree
from mathdoc_agent.orchestration.worklist import kind_key


def _without_none(value: dict[str, Any]) -> dict[str, Any]:
    return {key: item for key, item in value.items() if item is not None}


def _model_dump_json(value: BaseModel) -> dict[str, Any]:
    return value.model_dump(mode="json", exclude_none=True)


def _lean_identifier_from_text(value: str, *, fallback: str = "generated_name") -> str:
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    words = [word for word in re.split(r"[^A-Za-z0-9]+", value) if word]
    if not words:
        words = [word for word in re.split(r"[^A-Za-z0-9]+", fallback) if word]
    if not words:
        return "generated_name"
    identifier = "_".join(word.lower() for word in words)
    if not identifier[0].isalpha():
        identifier = f"n_{identifier}"
    return identifier


def _type_is(value: dict[str, Any], expected: str) -> bool:
    type_value = value.get("type")
    return isinstance(type_value, str) and type_value.lower() == expected


def _statement_data(node: DocumentNode) -> StatementData | None:
    try:
        return StatementData.model_validate(node.data)
    except Exception:
        return None


def _theorem_header(kind: str) -> str:
    return {
        DocumentKind.lemma.value: "Lemma",
        DocumentKind.proposition.value: "Proposition",
        DocumentKind.corollary.value: "Corollary",
        DocumentKind.local_claim.value: "Claim",
    }.get(kind, "Theorem")


def _assumption_steps(assumptions: list[str]) -> list[dict[str, Any]]:
    return [
        {
            "type": "assume_statement",
            "assumption": assumption,
        }
        for assumption in assumptions
    ]


def _proof_details_data(proof: ProofTree | None) -> Any:
    if proof is None:
        return None
    return _proof_node_data(proof.root)


def _attached_proof_details_data(proof: ProofTree | None) -> Any:
    details = _proof_details_data(proof)
    if isinstance(details, dict) and _type_is(details, "proof"):
        return {key: value for key, value in details.items() if key != "claim_label"}
    return details


def _dependency_data(value: Any) -> dict[str, Any]:
    theorem_dependencies = [
        theorem.model_dump(exclude_none=True)
        for theorem in value.deduced_from_theorem
    ]
    return {
        "deduced_from_claim": value.deduced_from_claim or None,
        "deduced_from_theorem": theorem_dependencies or None,
    }


def _logical_step_data(step) -> dict[str, Any]:
    data = step.model_dump(exclude_none=True)
    if not data.get("deduced_from_claim"):
        data.pop("deduced_from_claim", None)
    if not data.get("deduced_from_theorem"):
        data.pop("deduced_from_theorem", None)
    return data


def _calculation_step_claim(step: CalcStep) -> str:
    return f"{step.lhs} {step.relation.value} {step.rhs}"


def _calculation_assertion_step_data(step: CalcStep) -> dict[str, Any]:
    return _without_none(
        {
            "type": "assert_statement",
            "claim": _calculation_step_claim(step),
            "proof_method": step.justification or "calculation step",
            "from": step.lhs,
            "relation": step.relation.value,
            "to": step.rhs,
            **_dependency_data(step),
            "side_conditions": step.side_conditions or None,
        }
    )


def _calculation_side_condition_data(condition: str, step: CalcStep) -> dict[str, Any]:
    return _without_none(
        {
            "type": "assert_statement",
            "claim": condition,
            "proof_method": f"side condition for {_calculation_step_claim(step)}",
        }
    )


def _goal_relation(data: CalculationData) -> str | None:
    if not data.steps:
        return None
    relations = {step.relation.value for step in data.steps}
    if len(relations) == 1:
        return data.steps[0].relation.value
    return "mixed"


INSTRUCTIONAL_CLAIM_PREFIXES = (
    "apply ",
    "choose ",
    "conclude ",
    "construct ",
    "derive ",
    "establish ",
    "extract ",
    "finish",
    "instantiate ",
    "introduce ",
    "negate ",
    "obtain ",
    "produce ",
    "prove ",
    "select ",
    "set up ",
    "show ",
    "take ",
    "use ",
    "verify ",
)


def _is_instructional_claim(text: str | None) -> bool:
    if text is None:
        return False
    stripped = text.strip().lower()
    return stripped.startswith(INSTRUCTIONAL_CLAIM_PREFIXES)


def _claim_or_text(node: ProofNode) -> str:
    if node.goal and not _is_instructional_claim(node.goal):
        return node.goal
    return node.text


def _proof_label(node: ProofNode) -> str | None:
    if node.goal and not _is_instructional_claim(node.goal):
        return node.goal
    return None


def _is_assumption_text(text: str | None) -> bool:
    if text is None:
        return False
    return text.strip().lower().startswith(("assume ", "assume for contradiction ", "suppose "))


def _normalize_assumption_text(text: str) -> str:
    stripped = text.strip()
    lower = stripped.lower()
    for prefix in (
        "assume for contradiction that ",
        "assume that ",
        "assume ",
        "suppose that ",
        "suppose ",
    ):
        if lower.startswith(prefix):
            stripped = stripped[len(prefix):].strip()
            break
    return stripped[:-1] if stripped.endswith(".") else stripped


def _assumption_step_from_text(step: dict[str, Any], text: str) -> dict[str, Any]:
    return _without_none(
        {
            "type": "assume_statement",
            "assumption": _normalize_assumption_text(text),
            "id": step.get("id"),
            "status": step.get("status"),
            "text": text,
        }
    )


def _clean_instructional_assertion(step: dict[str, Any]) -> dict[str, Any] | None:
    if step.get("type") != "assert_statement":
        return step
    claim = step.get("claim")
    if isinstance(claim, str) and _is_assumption_text(claim):
        return _assumption_step_from_text(step, claim)
    if not _is_instructional_claim(claim):
        return step
    text = step.get("text")
    if not isinstance(text, str) or _is_instructional_claim(text):
        return None
    if _is_assumption_text(text):
        return _assumption_step_from_text(step, text)
    return {**step, "claim": text}


def _claim_step_from_proof(step: dict[str, Any], claim: str, proof_steps: list[Any]) -> dict[str, Any]:
    label = step.get("id")
    name_source = label if isinstance(label, str) and label.strip() else claim
    return _without_none(
        {
            "type": "theorem",
            "label": label,
            "header": "Claim",
            "name": _lean_identifier_from_text(name_source, fallback=claim),
            "claim": claim,
            "proof": _proof_object(proof_steps),
            "id": label,
            "status": step.get("status"),
            "text": step.get("text"),
        }
    )


def _deduplicate_single_child_claim(claim: str, proof_steps: list[Any]) -> list[Any]:
    if len(proof_steps) != 1:
        return proof_steps
    child = proof_steps[0]
    if not isinstance(child, dict):
        return proof_steps
    if not _type_is(child, "theorem") or child.get("header") != "Claim" or child.get("claim") != claim:
        return proof_steps
    proof = child.get("proof")
    if isinstance(proof, dict) and isinstance(proof.get("proof_steps"), list):
        return proof["proof_steps"]
    return proof_steps


def _same_claim(left: str | None, right: str | None) -> bool:
    if left is None or right is None:
        return False
    return left.strip() == right.strip()


def _flatten_proof_steps(steps: list[Any], *, assumed_claims: list[str] | None = None) -> list[Any]:
    assumed_claims = assumed_claims or []
    flattened: list[Any] = []
    for step in steps:
        if isinstance(step, dict) and _type_is(step, "proof"):
            nested = step.get("proof_steps")
            label = step.get("claim_label")
            if isinstance(nested, list) and (_is_instructional_claim(label) or label is None):
                flattened.extend(_flatten_proof_steps(nested, assumed_claims=assumed_claims))
                continue
            if isinstance(nested, list) and any(_same_claim(label, assumed) for assumed in assumed_claims):
                flattened.extend(_flatten_proof_steps(nested, assumed_claims=assumed_claims))
                continue
            if isinstance(nested, list):
                nested_steps = _flatten_proof_steps(nested, assumed_claims=assumed_claims)
                if isinstance(label, str):
                    nested_steps = _deduplicate_single_child_claim(label, nested_steps)
                    step = _claim_step_from_proof(step, label, nested_steps)
                else:
                    step = {**step, "proof_steps": nested_steps}
        elif isinstance(step, dict) and step.get("type") == "contradiction_statement":
            proof = step.get("proof")
            if isinstance(proof, dict) and isinstance(proof.get("proof_steps"), list):
                nested_assumptions = [*assumed_claims]
                assumption = step.get("assumption")
                if isinstance(assumption, str):
                    nested_assumptions.append(assumption)
                step = {
                    **step,
                    "proof": {
                        **proof,
                        "proof_steps": _flatten_proof_steps(
                            proof["proof_steps"],
                            assumed_claims=nested_assumptions,
                        ),
                    },
                }
        if isinstance(step, dict):
            step = _clean_instructional_assertion(step)
        if step is None:
            continue
        flattened.append(step)
    return flattened


def _proof_object(
    steps: list[Any],
    *,
    claim_label: str | None = None,
    assumed_claims: list[str] | None = None,
) -> dict[str, Any]:
    return _without_none(
        {
            "type": "proof",
            "claim_label": claim_label,
            "proof_steps": _flatten_proof_steps(steps, assumed_claims=assumed_claims),
        }
    )


def _document_node_data(node: DocumentNode) -> dict[str, Any]:
    kind = kind_key(node.kind)
    if kind in {
        DocumentKind.theorem.value,
        DocumentKind.lemma.value,
        DocumentKind.proposition.value,
        DocumentKind.corollary.value,
        DocumentKind.local_claim.value,
    }:
        statement = _statement_data(node)
        proof = _attached_proof_details_data(node.proof)
        name = node.data.get("name")
        if not isinstance(name, str) or not name.strip():
            name = _lean_identifier_from_text(
                node.label or node.id,
                fallback=node.id,
            )
        return _without_none(
            {
                "type": "theorem",
                "label": node.label or node.id,
                "header": _theorem_header(kind),
                "name": name,
                "claim": statement.statement if statement else node.text,
                "hypothesis": _assumption_steps(statement.assumptions) if statement and statement.assumptions else None,
                "proof": proof,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == DocumentKind.definition.value:
        data = DefinitionData.model_validate(node.data)
        if data.lean_name:
            return {"check": data.lean_name}
        return _without_none(
            {
                "type": "definition",
                "label": node.label or node.id,
                "header": "Definition",
                "definition": data.definitions or node.text,
                "name": data.term or node.title or node.label or node.id,
                "notation": data.notation,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == DocumentKind.structure_definition.value:
        data = StructureDefinitionData.model_validate(node.data)
        return _without_none(
            {
                "type": "structure-definition",
                "label": node.label or node.id,
                "name": data.name,
                "is_class": data.is_class,
                "isProp": data.is_prop,
                "parameters": [_model_dump_json(parameter) for parameter in data.parameters] or None,
                "extends": data.extends or None,
                "fields": [_model_dump_json(field) for field in data.fields] or None,
                "text": node.text or None,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == DocumentKind.instance_definition.value:
        data = InstanceDefinitionData.model_validate(node.data)
        return _without_none(
            {
                "type": "instance-definition",
                "label": node.label or node.id,
                "name": data.name,
                "class_name": data.class_name,
                "target": data.target,
                "parameters": [_model_dump_json(parameter) for parameter in data.parameters] or None,
                "gives": [_model_dump_json(give) for give in data.gives] or None,
                "value": data.value,
                "text": node.text or None,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == DocumentKind.inductive_type_definition.value:
        data = InductiveTypeDefinitionData.model_validate(node.data)
        return _without_none(
            {
                "type": "inductive-type-definition",
                "label": node.label or node.id,
                "name": data.name,
                "is_prop": data.is_prop,
                "parameters": [_model_dump_json(parameter) for parameter in data.parameters] or None,
                "indices": [_model_dump_json(index) for index in data.indices] or None,
                "constructors": [
                    _model_dump_json(constructor)
                    for constructor in data.constructors
                ],
                "text": node.text or None,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind in {DocumentKind.section.value, DocumentKind.subsection.value, DocumentKind.document.value}:
        return _without_none(
            {
                "type": "section" if kind != DocumentKind.document.value else "document",
                "label": node.label or node.id,
                "level": 2 if kind == DocumentKind.subsection.value else 1,
                "header": node.title or node.label or node.id,
                "content": [_document_node_data(child) for child in node.children],
                "id": node.id,
                "status": node.status.value,
            }
        )

    return _without_none(
        {
            "type": "paragraph",
            "text": node.text,
            "id": node.id,
            "status": node.status.value,
        }
    )


def _simple_proof_data(node: ProofNode) -> dict[str, Any]:
    try:
        data = SimpleProofData.model_validate(node.data)
    except Exception:
        data = SimpleProofData()
    if node.children:
        return _without_none(
            {
                "type": "proof",
                "claim_label": _proof_label(node),
                "proof_steps": _flatten_proof_steps([_proof_node_data(child) for child in node.children]),
                "id": node.id,
                "status": node.status.value,
                "text": node.text,
            }
        )
    if data.proof_steps:
        return _without_none(
            {
                "type": "proof",
                "claim_label": _proof_label(node),
                "proof_steps": _flatten_proof_steps([_logical_step_data(step) for step in data.proof_steps]),
                "id": node.id,
                "status": node.status.value,
                "text": node.text,
            }
        )
    return _without_none(
        {
            "type": "assert_statement",
            "claim": _claim_or_text(node),
            "proof_method": data.method,
            **_dependency_data(data),
            "id": node.id,
            "status": node.status.value,
            "text": node.text,
        }
    )


def _structured_data(node: ProofNode) -> StructuredProofData:
    try:
        return StructuredProofData.model_validate(node.data)
    except Exception:
        return StructuredProofData()


def _required_claim(data: StructuredProofData, node: ProofNode) -> str:
    return data.claim or _claim_or_text(node)


def _looks_existential(text: str | None) -> bool:
    if not text:
        return False
    lowered = text.lower()
    return "there exists" in lowered or "there is" in lowered or "∃" in text


def _existential_full_claim(data: StructuredProofData, node: ProofNode) -> str:
    if data.full_claim:
        return data.full_claim
    if _looks_existential(data.claim):
        return data.claim or _claim_or_text(node)
    return _claim_or_text(node)


def _extract_existential_parts(text: str | None) -> tuple[str | None, str | None]:
    if not text:
        return None, None

    symbolic = re.search(r"∃\s*([A-Za-z][A-Za-z0-9_']*)\s*,\s*(.+)", text)
    if symbolic:
        return symbolic.group(1), symbolic.group(2).strip()

    prose = re.search(
        r"\bthere exists\s+(?:a|an|some)?\s*(?P<description>.+?)\s+"
        r"(?P<variable>[A-Za-z][A-Za-z0-9_']*)\s+"
        r"(?P<link>such that|with|satisfying|so that)\s+(?P<property>.+)",
        text,
        flags=re.IGNORECASE,
    )
    if prose:
        variable = prose.group("variable")
        description = prose.group("description").strip()
        link = prose.group("link").lower()
        prop = prose.group("property").strip().rstrip(".")
        article = "an" if description[:1].lower() in {"a", "e", "i", "o", "u"} else "a"
        if description.startswith(("a ", "an ")):
            article = ""
        description_part = f" {description}" if not article else f" {article} {description}"
        return variable, f"{variable} is{description_part} {link} {prop}."

    unbound = re.search(
        r"\bthere exists\s+(?P<description>.+?)(?:\.|$)",
        text,
        flags=re.IGNORECASE,
    )
    if unbound:
        description = unbound.group("description").strip().rstrip(".")
        return None, f"witness is {description}."

    return None, None


def _constructed_variable_name(data: StructuredProofData, full_claim: str | None) -> str | None:
    if data.variable_name:
        return data.variable_name
    variable, _ = _extract_existential_parts(full_claim)
    if variable:
        return variable
    construction = data.construction or data.witness
    if not construction:
        return None
    match = re.search(r"\b([A-Za-z][A-Za-z0-9_']*)\s*(?:\(|:=|=)", construction)
    if match:
        return match.group(1)
    match = re.search(r"\b(?:function|map|polynomial|object|element|number)\s+([A-Za-z][A-Za-z0-9_']*)\b", construction)
    if match:
        return match.group(1)
    return None


def _constructed_property_claim(data: StructuredProofData, node: ProofNode, full_claim: str | None) -> str | None:
    if data.claim and not _looks_existential(data.claim):
        return data.claim
    _, property_claim = _extract_existential_parts(full_claim)
    if property_claim:
        variable_name = _constructed_variable_name(data, full_claim)
        if variable_name:
            return property_claim.replace("witness", variable_name, 1)
        return property_claim
    if data.conclusions:
        return " and ".join(data.conclusions)
    if data.claim and not _looks_existential(data.claim):
        return data.claim
    fallback = node.goal
    return fallback if fallback and not _looks_existential(fallback) else None


def _child_proof_object(node: ProofNode, *, claim_label: str | None = None) -> dict[str, Any]:
    return _proof_object(
        [_proof_node_data(child) for child in node.children],
        claim_label=claim_label,
    )


def _proof_node_data(node: ProofNode) -> Any:
    kind = kind_key(node.kind)
    if kind in {
        ProofKind.logical_sequence.value,
        ProofKind.simple.value,
        ProofKind.theorem_application.value,
        ProofKind.definition_unfolding.value,
    }:
        return _simple_proof_data(node)

    if kind == ProofKind.calculation.value:
        try:
            data = CalculationData.model_validate(node.data)
        except Exception:
            data = CalculationData()
        proof_steps: list[dict[str, Any]] = []
        for step in data.steps:
            proof_steps.extend(
                _calculation_side_condition_data(condition, step)
                for condition in step.side_conditions
            )
            proof_steps.append(_calculation_assertion_step_data(step))
        if not proof_steps:
            claim = (
                node.goal
                if node.goal and not _is_instructional_claim(node.goal)
                else node.text
            )
            proof_steps.append(
                {
                    "type": "assert_statement",
                    "claim": claim,
                    "proof_method": data.calculation_kind or "calculation",
                }
            )
        return _without_none(
            {
                "type": "proof",
                "claim_label": _proof_label(node),
                "calculation_kind": data.calculation_kind,
                "start": data.start,
                "target": data.target,
                "goal_relation": _goal_relation(data),
                "proof_steps": proof_steps,
                "id": node.id,
                "status": node.status.value,
                "text": node.text,
            }
        )

    if kind == ProofKind.induction.value:
        data = InductionData.model_validate(node.data)
        children = {child.id: child for child in node.children}
        base = [_proof_node_data(children[child_id]) for child_id in data.base_case_ids if child_id in children]
        steps = [_proof_node_data(children[child_id]) for child_id in data.step_case_ids if child_id in children]
        return _without_none(
            {
                "type": "induction_proof",
                "on": data.variable,
                "prev_var": data.metadata.get("prev_var") if hasattr(data, "metadata") else None,
                "base_case_proof": base[0] if len(base) == 1 else base,
                "induction_step_proof": steps[0] if len(steps) == 1 else steps,
                "id": node.id,
                "status": node.status.value,
                "text": node.text,
            }
        )

    if kind == ProofKind.cases.value:
        data = CasesData.model_validate(node.data)
        proof_cases = []
        for child in node.children:
            condition = child.hypotheses[0] if child.hypotheses else child.goal or child.text
            proof_cases.append(
                {
                    "type": "case",
                    "condition": condition,
                    "proof": _proof_node_data(child),
                }
            )
        return _without_none(
            {
                "type": "multi-condition_cases_proof",
                "proof_cases": proof_cases,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == ProofKind.specialize.value:
        data = SpecializeData.model_validate(node.data)
        proof_method = "Specialized an already available claim."
        if data.source_claim:
            proof_method = f"Specialized: {data.source_claim}"
        return _without_none(
            {
                "type": "assert_statement",
                "name": data.name,
                "claim": data.claim or node.goal,
                "proof_method": proof_method,
                "lean_term": data.lean_term,
                "source_claim": data.source_claim,
                "arguments": data.arguments or None,
                "id": node.id,
                "status": node.status.value,
                "text": node.text,
            }
        )

    if kind == ProofKind.contradiction.value:
        data = _structured_data(node)
        assumption = data.contradiction_assumption or (data.assumptions[0] if data.assumptions else None)
        proof = _proof_object(
            [_proof_node_data(child) for child in node.children],
            assumed_claims=[assumption] if assumption else None,
        )
        return _without_none(
            {
                "type": "contradiction_statement",
                "assumption": assumption,
                "proof": proof,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == ProofKind.equivalence.value and len(node.children) >= 2:
        return _without_none(
            {
                "type": "bi-implication_cases_proof",
                "if_proof": _proof_node_data(node.children[0]),
                "only_if_proof": _proof_node_data(node.children[1]),
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == ProofKind.existence.value:
        data = _structured_data(node)
        if data.full_claim or data.claim or data.variable_name or data.witness:
            full_claim = _existential_full_claim(data, node)
            claim = _constructed_property_claim(data, node, full_claim)
            variable_name = _constructed_variable_name(data, full_claim)
            return _without_none(
                {
                    "type": "existence_proof",
                    "full_claim": full_claim,
                    "variable_name": variable_name,
                    "claim": claim,
                    "witness": data.witness,
                    "proof": _child_proof_object(node),
                    "id": node.id,
                    "status": node.status.value,
                }
            )

    if kind == ProofKind.uniqueness.value:
        data = _structured_data(node)
        existence_children = [child for child in node.children if kind_key(child.kind) == ProofKind.existence.value]
        remaining_children = [child for child in node.children if child not in existence_children]
        existence_proof = (
            _proof_node_data(existence_children[0])
            if len(existence_children) == 1
            else (_proof_object([_proof_node_data(child) for child in existence_children]) if existence_children else None)
        )
        uniqueness_children = remaining_children or node.children
        uniqueness_proof = _proof_object([_proof_node_data(child) for child in uniqueness_children])
        return _without_none(
            {
                "type": "uniqueness_proof",
                "existence_proof": existence_proof,
                "uniqueness_proof": uniqueness_proof,
                "candidate_variables": data.candidate_variables or None,
                "claim": data.claim or node.goal,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == ProofKind.construction.value:
        data = _structured_data(node)
        if data.full_claim or data.claim or data.variable_name or data.construction:
            full_claim = _existential_full_claim(data, node)
            claim = _constructed_property_claim(data, node, full_claim)
            variable_name = _constructed_variable_name(data, full_claim)
            return _without_none(
                {
                    "type": "construction_proof",
                    "full_claim": full_claim,
                    "variable_name": variable_name,
                    "claim": claim,
                    "construction": data.construction,
                    "verification": _child_proof_object(node),
                    "id": node.id,
                    "status": node.status.value,
                }
            )

    if kind == ProofKind.epsilon_delta.value:
        data = _structured_data(node)
        delta = data.metadata.get("delta")
        epsilon_var = data.metadata.get("epsilon_var") or data.metadata.get("epsilon") or "epsilon"
        epsilon_positive = data.metadata.get("epsilon_positive")
        if epsilon_positive is None:
            epsilon_positive = next((item for item in data.assumptions if "epsilon" in item.lower() or "ε" in item), None)
        delta_positive_proof = _proof_node_data(node.children[0]) if node.children else None
        bound_proof_children = node.children[1:] if len(node.children) > 1 else node.children
        bound_proof = _proof_object([_proof_node_data(child) for child in bound_proof_children])
        return _without_none(
            {
                "type": "epsilon_delta_proof",
                "epsilon_var": epsilon_var,
                "epsilon_positive": epsilon_positive,
                "delta": delta,
                "delta_positive_proof": delta_positive_proof,
                "bound_claim": data.bound_claim or (data.conclusions[0] if data.conclusions else node.goal),
                "bound_proof": bound_proof,
                "id": node.id,
                "status": node.status.value,
            }
        )

    if kind == ProofKind.reduction.value:
        data = _structured_data(node)
        children = {child.id: child for child in node.children}
        proof_of_reduction = (
            children.get(data.proof_of_reduction_id)
            if data.proof_of_reduction_id
            else (node.children[0] if node.children else None)
        )
        reduced_goal_proof = (
            children.get(data.proof_id)
            if data.proof_id
            else (node.children[1] if len(node.children) > 1 else None)
        )
        return _without_none(
            {
                "type": "reduction_proof",
                "claim": data.claim or node.goal,
                "reduced_to": data.reduced_to,
                "proof_of_reduction": (
                    _proof_node_data(proof_of_reduction)
                    if proof_of_reduction is not None
                    else None
                ),
                "proof": (
                    _proof_node_data(reduced_goal_proof)
                    if reduced_goal_proof is not None
                    else None
                ),
                "id": node.id,
                "status": node.status.value,
            }
        )

    structured = _structured_data(node)
    proof_steps = _flatten_proof_steps([_proof_node_data(child) for child in node.children])
    if not proof_steps and structured.summary and not _is_instructional_claim(structured.summary):
        proof_steps = [{"type": "assert_statement", "claim": structured.summary}]
    if not proof_steps:
        proof_steps = [{"type": "assert_statement", "claim": _claim_or_text(node)}]
    return _without_none(
        {
            "type": "proof",
            "claim_label": _proof_label(node),
            "proof_steps": proof_steps,
            "id": node.id,
            "status": node.status.value,
        }
    )


def paper_structure_data(model: BaseModel) -> dict[str, Any]:
    """Return a compact PaperStructure-style document for Lean codegen."""
    if isinstance(model, MathDocument):
        document = {
            "type": "document",
            "body": [_document_node_data(child) for child in model.root.children],
        }
        if model.title is not None:
            document["title"] = model.title
        return {"document": document}
    if isinstance(model, DocumentNode):
        return _document_node_data(model)
    if isinstance(model, ProofTree):
        return _proof_details_data(model)
    if isinstance(model, ProofNode):
        return _proof_node_data(model)
    return _debug_data(model)


def _debug_data(value: Any) -> Any:
    """Return JSON-ready data with public `type` discriminators, not internal `kind`.

    The orchestration layer keeps `kind` as an internal dispatch key. Exported JSON is
    intended for downstream Lean processing and should look closer to
    `resources/PaperStructure.json`, where `type` is the discriminator.
    """
    if isinstance(value, BaseModel):
        value = value.model_dump(mode="json")
    if isinstance(value, list):
        return [_debug_data(item) for item in value]
    if not isinstance(value, dict):
        return value

    cleaned_items = []
    for key, item in value.items():
        if key == "kind":
            continue
        cleaned_items.append((key, _debug_data(item)))

    if "type" not in value:
        return dict(cleaned_items)

    result: dict[str, Any] = {"type": value["type"]}
    for key, item in cleaned_items:
        if key != "type":
            result[key] = item
    return result


def to_json(model: BaseModel, *, indent: int = 2) -> str:
    return json.dumps(paper_structure_data(model), indent=indent, ensure_ascii=False)


def to_debug_json(model: BaseModel, *, indent: int = 2) -> str:
    return json.dumps(_debug_data(model), indent=indent, ensure_ascii=False)
