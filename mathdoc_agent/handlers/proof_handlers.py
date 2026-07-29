from __future__ import annotations

import re
import sys
from typing import Union

from pydantic import BaseModel, Field, field_validator

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.builders.proof_builder import ProofBuilder
from mathdoc_agent.handlers.base import ProofRefinementHandler
from mathdoc_agent.models.base import NodeStatus, ProofKind
from mathdoc_agent.models.payloads import (
    CalculationData,
    CasesData,
    InductionData,
    LocalClaimData,
    LogicalProofStepData,
    SimpleProofData,
    SpecializeData,
    StructuredProofData,
)
from mathdoc_agent.models.proof import ProofNode
from mathdoc_agent.models.refinement_specs import (
    CalculationRefinementSpec,
    CasesRefinementSpec,
    InductionRefinementSpec,
    LocalClaimRefinementSpec,
    metadata_entries_to_dict,
    SimpleProofRefinementSpec,
    SpecializeRefinementSpec,
    StructuredProofRefinementSpec,
)
from mathdoc_agent.models.validation import ValidationIssue, ValidationReport
from mathdoc_agent.orchestration.context import ProofContext
from mathdoc_agent.orchestration.worklist import kind_key
from mathdoc_agent.validation.deterministic import validate_calculation_adjacency


class ClassificationSpec(BaseModel):
    kind: Union[ProofKind, str]
    confidence: float = Field(default=0.5, ge=0.0, le=1.0)
    notes: list[str] = Field(default_factory=list)

    @field_validator("notes", mode="before")
    @classmethod
    def _coerce_notes(cls, value):
        if value is None:
            return []
        if isinstance(value, str):
            return [value]
        return value


class UnknownProofHandler(ProofRefinementHandler[ClassificationSpec]):
    kind = ProofKind.unknown.value
    output_model = ClassificationSpec

    def __init__(self, agent) -> None:
        self.agent = agent

    def _normalized_kind(self, kind: ProofKind | str) -> ProofKind | str:
        key = kind_key(kind).strip().lower().replace("-", "_").replace(" ", "_")
        aliases = {
            "axiom_check": ProofKind.logical_sequence.value,
            "axiom_verification": ProofKind.logical_sequence.value,
            "biconditional": ProofKind.equivalence.value,
            "direct": ProofKind.logical_sequence.value,
            "direct_proof": ProofKind.logical_sequence.value,
            "double_inclusion": ProofKind.extensionality.value,
            "iff": ProofKind.equivalence.value,
            "iff_biconditional": ProofKind.equivalence.value,
            "proof_by_double_inclusion": ProofKind.extensionality.value,
            "simple_direct_proof": ProofKind.logical_sequence.value,
            "logical_step_sequence": ProofKind.logical_sequence.value,
            "logical_proof_sequence": ProofKind.logical_sequence.value,
            "logical_sequence": ProofKind.logical_sequence.value,
            "specialization": ProofKind.specialize.value,
            "specialise": ProofKind.specialize.value,
            "specialisation": ProofKind.specialize.value,
            "unknown": ProofKind.logical_sequence.value,
            "unknown_proof": ProofKind.logical_sequence.value,
        }
        normalized = aliases.get(key, key)
        try:
            return ProofKind(normalized)
        except ValueError:
            return ProofKind.logical_sequence

    def _log_classification(self, node: ProofNode, original: ProofKind | str, normalized: ProofKind | str, confidence: float) -> None:
        print(
            "[mathdoc_agent] proof classification "
            f"node={node.id} raw={kind_key(original)!r} normalized={kind_key(normalized)!r} "
            f"confidence={confidence:.2f}",
            file=sys.stderr,
            flush=True,
        )

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
                "task": "Classify this proof node by outermost proof structure.",
            },
            ClassificationSpec,
        )
        normalized_kind = self._normalized_kind(spec.kind)
        self._log_classification(node, spec.kind, normalized_kind, spec.confidence)
        return node.model_copy(
            update={
                "kind": normalized_kind,
                "status": NodeStatus.classified,
                "confidence": spec.confidence,
                "notes": node.notes + spec.notes,
            }
        )


class OpaqueProofHandler(ProofRefinementHandler[None]):
    kind = ProofKind.opaque.value

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        return node.model_copy(update={"status": NodeStatus.opaque})

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        return True


class StepLikeProofHandler(ProofRefinementHandler[None]):
    """Handle proof children that are already JSON proof-step statements."""

    kind = ProofKind.simple.value

    def __init__(self, step_type: str) -> None:
        self.step_type = step_type

    def _text(self, node: ProofNode) -> str:
        return " ".join((node.goal or node.text or "").split())

    def _let_step(self, node: ProofNode) -> LogicalProofStepData:
        text = self._text(node)
        variable_name: str | None = None
        variable_type: str | None = None
        match = re.match(
            r"(?i)\s*let\s+([A-Za-z_][A-Za-z0-9_']*)\s*(?::|be|denote|=)\s*(.*?)[.]?\s*$",
            text,
        )
        if match:
            variable_name = match.group(1)
            variable_type = match.group(2).strip() or None
        return LogicalProofStepData(
            type="let_statement",
            variable_name=variable_name,
            variable_type=variable_type,
            statement=text or None,
        )

    def _step(self, node: ProofNode) -> LogicalProofStepData:
        text = self._text(node)
        if self.step_type == "let_statement":
            return self._let_step(node)
        if self.step_type == "assume_statement":
            return LogicalProofStepData(type="assume_statement", assumption=text or None)
        return LogicalProofStepData(type="assert_statement", claim=text or None)

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        data = SimpleProofData(proof_steps=[self._step(node)])
        return node.model_copy(
            update={
                "kind": ProofKind.simple,
                "status": NodeStatus.resolved,
                "data": data.model_dump(),
            }
        )

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        return node.status == NodeStatus.resolved


class InductionHandler(ProofRefinementHandler[InductionRefinementSpec]):
    kind = ProofKind.induction.value
    output_model = InductionRefinementSpec

    def __init__(self, agent) -> None:
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        spec = await run_agent_typed(
            self.agent,
            {"node": node.model_dump(), "context": context.model_dump()},
            InductionRefinementSpec,
        )
        base_nodes = [
            ProofNode(
                id=f"{node.id}.{child.id_suffix}",
                kind=child.kind,
                status=NodeStatus.raw,
                text=child.text,
                goal=child.goal,
                hypotheses=child.hypotheses,
                notes=child.notes,
            )
            for child in spec.base_cases
        ]
        step_nodes = [
            ProofNode(
                id=f"{node.id}.{child.id_suffix}",
                kind=child.kind,
                status=NodeStatus.raw,
                text=child.text,
                goal=child.goal,
                hypotheses=child.hypotheses,
                notes=child.notes,
            )
            for child in spec.step_cases
        ]
        replacement = ProofBuilder.induction(
            id=node.id,
            text=node.text,
            variable=spec.variable,
            principle=spec.principle,
            induction_hypotheses=spec.induction_hypotheses,
            base_cases=base_nodes,
            step_cases=step_nodes,
            goal=node.goal,
            hypotheses=node.hypotheses,
        )
        return replacement.model_copy(update={"notes": node.notes + spec.notes})

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        issues: list[ValidationIssue] = []
        data = InductionData.model_validate(node.data)
        if not data.variable:
            issues.append(ValidationIssue(severity="error", path="data.variable", message="Induction node has no induction variable."))
        if not data.base_case_ids:
            issues.append(ValidationIssue(severity="error", path="data.base_case_ids", message="Induction node has no base cases."))
        if not data.step_case_ids:
            issues.append(ValidationIssue(severity="error", path="data.step_case_ids", message="Induction node has no step cases."))
        child_ids = {child.id for child in node.children}
        for child_id in data.base_case_ids + data.step_case_ids:
            if child_id not in child_ids:
                issues.append(ValidationIssue(severity="error", path="data", message=f"Referenced child id {child_id!r} is missing."))
        return ValidationReport.from_issues(issues)

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        return bool(node.children) and all(
            child.status in {NodeStatus.resolved, NodeStatus.opaque}
            for child in node.children
        )


class CasesHandler(ProofRefinementHandler[CasesRefinementSpec]):
    kind = ProofKind.cases.value
    output_model = CasesRefinementSpec

    def __init__(self, agent) -> None:
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        spec = await run_agent_typed(
            self.agent,
            {"node": node.model_dump(), "context": context.model_dump()},
            CasesRefinementSpec,
        )
        case_nodes = [
            ProofNode(
                id=f"{node.id}.{child.id_suffix}",
                kind=child.kind,
                status=NodeStatus.raw,
                text=child.text,
                goal=child.goal,
                hypotheses=child.hypotheses,
                notes=child.notes,
            )
            for child in spec.cases
        ]
        replacement = ProofBuilder.cases(
            id=node.id,
            text=node.text,
            split_on=spec.split_on,
            exhaustive_reason=spec.exhaustive_reason,
            cases=case_nodes,
            goal=node.goal,
            hypotheses=node.hypotheses,
        )
        return replacement.model_copy(update={"notes": node.notes + spec.notes})

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        issues: list[ValidationIssue] = []
        data = CasesData.model_validate(node.data)
        if not data.case_ids:
            issues.append(ValidationIssue(severity="error", path="data.case_ids", message="Cases node has no cases."))
        child_ids = {child.id for child in node.children}
        for child_id in data.case_ids:
            if child_id not in child_ids:
                issues.append(ValidationIssue(severity="error", path="data", message=f"Referenced child id {child_id!r} is missing."))
        return ValidationReport.from_issues(issues)

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        return bool(node.children) and all(
            child.status in {NodeStatus.resolved, NodeStatus.opaque}
            for child in node.children
        )


class SimpleProofHandler(ProofRefinementHandler[SimpleProofRefinementSpec]):
    kind = ProofKind.simple.value
    output_model = SimpleProofRefinementSpec

    def __init__(self, agent, *, kind: str | None = None) -> None:
        self.agent = agent
        if kind is not None:
            self.kind = kind

    def _looks_like_calculation(self, text: str) -> bool:
        return bool(re.search(r"(=|≤|>=|≥|<|>|\\le|\\ge)", text))

    def _is_complex_assertion(self, step: LogicalProofStepData) -> bool:
        if step.type != "assert_statement":
            return False
        claim_words = len((step.claim or "").split())
        method_words = len((step.proof_method or "").split())
        return (
            claim_words > 28
            or method_words > 28
            or bool(step.proof_method and len(step.proof_method) > 180)
        )

    def _is_generic_summary_assertion(self, step: LogicalProofStepData) -> bool:
        if step.type != "assert_statement":
            return False
        claim = (step.claim or "").casefold()
        return any(
            marker in claim
            for marker in (
                "whole proof",
                "preceding reasoning",
                "desired result follows",
                "desired conclusion follows",
                "all the preceding",
            )
        )

    def _fallback_fragment_step(self, text: str) -> LogicalProofStepData:
        stripped = " ".join(text.split())
        lowered = stripped.casefold()
        if lowered.startswith("let "):
            match = re.match(r"let\s+([A-Za-z_][A-Za-z0-9_']*)", stripped, re.IGNORECASE)
            return LogicalProofStepData(
                type="let_statement",
                variable_name=match.group(1) if match else None,
                statement=stripped,
            )
        if lowered.startswith(("fix ", "assume ", "suppose ")):
            return LogicalProofStepData(
                type="assume_statement",
                assumption=stripped,
            )
        return LogicalProofStepData(
            type="assert_statement",
            claim=stripped,
            proof_method="Refined from this source proof fragment.",
        )

    def _source_has_multiple_steps(self, text: str) -> bool:
        display_count = len(re.findall(r"\\\[.*?\\\]", text, flags=re.DOTALL))
        sentence_count = len(re.findall(r"(?<=[.!?])\s+", " ".join(text.split())))
        paragraph_count = len([part for part in re.split(r"\n\s*\n", text) if part.strip()])
        marker_count = len(
            re.findall(
                r"\b(first|next|then|therefore|hence|since|because|using|rewriting|combining|let|fix|assume)\b",
                text,
                flags=re.IGNORECASE,
            )
        )
        return display_count + sentence_count + paragraph_count + marker_count >= 4

    def _needs_further_refinement(
        self,
        node: ProofNode,
        proof_steps: list[LogicalProofStepData],
    ) -> bool:
        if not self._source_has_multiple_steps(node.text):
            return False
        if not proof_steps:
            return True
        if len(proof_steps) == 1 and proof_steps[0].type == "assert_statement":
            return True
        return any(self._is_complex_assertion(step) for step in proof_steps)

    def _proof_chunks(self, text: str) -> list[tuple[str, ProofKind]]:
        chunks: list[tuple[str, ProofKind]] = []
        parts = re.split(r"(\\\[.*?\\\])", text, flags=re.DOTALL)
        for part in parts:
            stripped = part.strip()
            if not stripped:
                continue
            display = re.fullmatch(r"\\\[(.*?)\\\]", stripped, flags=re.DOTALL)
            if display:
                equation = " ".join(display.group(1).split())
                kind = ProofKind.calculation if self._looks_like_calculation(equation) else ProofKind.simple
                chunks.append((equation, kind))
                continue

            paragraphs = [p.strip() for p in re.split(r"\n\s*\n", stripped) if p.strip()]
            for paragraph in paragraphs:
                normalized = " ".join(paragraph.split())
                sentences = [
                    sentence.strip()
                    for sentence in re.split(r"(?<=[.!?])\s+", normalized)
                    if sentence.strip()
                ]
                if len(sentences) > 1:
                    chunks.extend((sentence, ProofKind.simple) for sentence in sentences)
                else:
                    chunks.append((normalized, ProofKind.simple))
        return chunks

    def _decompose_for_refinement(self, node: ProofNode) -> list[ProofNode]:
        children: list[ProofNode] = []
        for index, (text, kind) in enumerate(self._proof_chunks(node.text), start=1):
            if text == node.text.strip():
                continue
            children.append(
                ProofNode(
                    id=f"{node.id}.step{index}",
                    kind=kind,
                    status=NodeStatus.raw,
                    text=text,
                    # These are mechanically split proof fragments, not named
                    # local theorems. Leaving the goal unset makes export flatten
                    # their refined steps into the surrounding proof.
                    goal=None,
                    hypotheses=node.hypotheses,
                )
            )
        return children

    def _fallback_proof_steps(self, text: str) -> list[LogicalProofStepData]:
        steps: list[LogicalProofStepData] = []
        pending_method: str | None = None
        parts = re.split(r"(\\\[.*?\\\])", text, flags=re.DOTALL)
        for part in parts:
            if not part.strip():
                continue
            match = re.fullmatch(r"\\\[(.*?)\\\]", part.strip(), flags=re.DOTALL)
            if match:
                equation = " ".join(match.group(1).split())
                steps.append(
                    LogicalProofStepData(
                        type="assert_statement",
                        claim=equation,
                        proof_method=pending_method or "displayed equation from the proof text",
                    )
                )
                pending_method = None
                continue
            sentences = [
                sentence.strip()
                for sentence in re.split(r"(?<=[.!?])\s+", " ".join(part.split()))
                if sentence.strip()
            ]
            for sentence in sentences:
                lowered = sentence.lower()
                if lowered.startswith("let "):
                    steps.append(
                        LogicalProofStepData(
                            type="let_statement",
                            variable_name="<anonymous>",
                            statement=sentence,
                        )
                    )
                    pending_method = sentence
                elif lowered.startswith("fix ") or lowered.startswith("assume "):
                    steps.append(
                        LogicalProofStepData(
                            type="assume_statement",
                            assumption=sentence,
                        )
                    )
                    pending_method = sentence
                elif any(marker in lowered for marker in ("we want to prove", "this shows", "therefore")):
                    steps.append(
                        LogicalProofStepData(
                            type="assert_statement",
                            claim=sentence,
                            proof_method="stated in the proof text",
                        )
                    )
                elif lowered.startswith(
                    ("by ", "since ", "using ", "rewriting ", "first,", "next,", "because ", "so")
                ):
                    pending_method = sentence
        if len(steps) < 2:
            return []
        return steps

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        spec = await run_agent_typed(
            self.agent,
            {"node": node.model_dump(), "context": context.model_dump()},
            SimpleProofRefinementSpec,
        )
        proof_steps = spec.proof_steps or self._fallback_proof_steps(node.text)
        if (
            node.goal is None
            and len(proof_steps) == 1
            and self._is_generic_summary_assertion(proof_steps[0])
        ):
            proof_steps = [self._fallback_fragment_step(node.text)]
        if self._needs_further_refinement(node, proof_steps):
            children = self._decompose_for_refinement(node)
            if len(children) >= 2:
                data = SimpleProofData(
                    method=spec.method,
                    hints=spec.hints,
                    referenced_lemmas=spec.referenced_lemmas,
                    referenced_hypotheses=spec.referenced_hypotheses,
                    deduced_from_claim=spec.deduced_from_claim,
                    deduced_from_theorem=spec.deduced_from_theorem,
                )
                return node.model_copy(
                    update={
                        "kind": self.kind,
                        "status": NodeStatus.decomposed,
                        "children": children,
                        "data": data.model_dump(),
                        "unresolved_details": node.unresolved_details + spec.unresolved_details,
                        "notes": node.notes + ["Decomposed coarse assert_statement for further refinement."],
                    }
                )
        data = SimpleProofData(
            method=spec.method,
            hints=spec.hints,
            referenced_lemmas=spec.referenced_lemmas,
            referenced_hypotheses=spec.referenced_hypotheses,
            deduced_from_claim=spec.deduced_from_claim,
            deduced_from_theorem=spec.deduced_from_theorem,
            proof_steps=proof_steps,
        )
        unresolved = node.unresolved_details + spec.unresolved_details
        status = NodeStatus.resolved if (data.hints or data.referenced_lemmas or data.referenced_hypotheses or data.proof_steps or unresolved) else NodeStatus.locally_refined
        return node.model_copy(
            update={
                "kind": self.kind,
                "status": status,
                "data": data.model_dump(),
                "unresolved_details": unresolved,
            }
        )

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        data = SimpleProofData.model_validate(node.data)
        if node.children:
            return all(
                child.status in {NodeStatus.resolved, NodeStatus.opaque}
                for child in node.children
            )
        return bool(
            data.hints
            or data.referenced_lemmas
            or data.referenced_hypotheses
            or data.proof_steps
            or node.unresolved_details
        )


class LogicalSequenceHandler(SimpleProofHandler):
    """Refine a broad direct proof as an explicit sequence of logical steps."""

    kind = ProofKind.logical_sequence.value


class CalculationHandler(ProofRefinementHandler[CalculationRefinementSpec]):
    kind = ProofKind.calculation.value
    output_model = CalculationRefinementSpec

    def __init__(self, agent) -> None:
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        spec = await run_agent_typed(
            self.agent,
            {"node": node.model_dump(), "context": context.model_dump()},
            CalculationRefinementSpec,
        )
        replacement = ProofBuilder.calculation(
            id=node.id,
            text=node.text,
            steps=spec.steps,
            goal=node.goal,
            hypotheses=node.hypotheses,
            calculation_kind=spec.calculation_kind,
        )
        return replacement.model_copy(
            update={"unresolved_details": node.unresolved_details + spec.unresolved_details}
        )

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        data = CalculationData.model_validate(node.data)
        return validate_calculation_adjacency(data)

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        data = CalculationData.model_validate(node.data)
        return bool(data.steps or node.unresolved_details)


class LocalClaimHandler(ProofRefinementHandler[LocalClaimRefinementSpec]):
    kind = ProofKind.local_claim.value
    output_model = LocalClaimRefinementSpec

    def __init__(self, agent=None) -> None:
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        if self.agent is None:
            return node.model_copy(update={"status": NodeStatus.decomposed if node.children else NodeStatus.resolved})
        spec = await run_agent_typed(
            self.agent,
            {"node": node.model_dump(), "context": context.model_dump()},
            LocalClaimRefinementSpec,
        )
        proof_node = None
        if spec.proof is not None:
            proof_node = ProofNode(
                id=f"{node.id}.{spec.proof.id_suffix}",
                kind=spec.proof.kind,
                status=NodeStatus.raw,
                text=spec.proof.text,
                goal=spec.proof.goal or spec.statement,
                hypotheses=spec.proof.hypotheses,
                notes=spec.proof.notes,
            )
        return ProofBuilder.local_claim(
            id=node.id,
            text=node.text,
            statement=spec.statement,
            proof_node=proof_node,
            label=spec.label,
        ).model_copy(update={"notes": node.notes + spec.notes})

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        issues: list[ValidationIssue] = []
        data = LocalClaimData.model_validate(node.data)
        if not data.statement:
            issues.append(ValidationIssue(severity="error", path="data.statement", message="Local claim has no statement."))
        if data.proof_node_id and data.proof_node_id not in {child.id for child in node.children}:
            issues.append(ValidationIssue(severity="error", path="data.proof_node_id", message="Local claim proof_node_id is not a child."))
        return ValidationReport.from_issues(issues)

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        if not node.children:
            return True
        return all(child.status in {NodeStatus.resolved, NodeStatus.opaque} for child in node.children)


class SpecializeHandler(ProofRefinementHandler[SpecializeRefinementSpec]):
    kind = ProofKind.specialize.value
    output_model = SpecializeRefinementSpec

    def __init__(self, agent=None) -> None:
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        if self.agent is None:
            if node.data:
                SpecializeData.model_validate(node.data)
                return node.model_copy(update={"status": NodeStatus.resolved})
            return node.model_copy(
                update={
                    "status": NodeStatus.locally_refined,
                    "unresolved_details": node.unresolved_details
                    + ["Specialize proof requires a name and lean_term."],
                }
            )
        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
                "task": (
                    "Create a named local lemma by specializing an already-proved "
                    "claim. Do not overwrite or forget the original claim."
                ),
            },
            SpecializeRefinementSpec,
        )
        data = SpecializeData(
            name=spec.name,
            lean_term=spec.lean_term,
            claim=spec.claim or node.goal,
            source_claim=spec.source_claim,
            arguments=spec.arguments,
        )
        return node.model_copy(
            update={
                "kind": self.kind,
                "status": NodeStatus.resolved,
                "goal": data.claim or node.goal,
                "data": data.model_dump(),
                "unresolved_details": node.unresolved_details + spec.unresolved_details,
                "notes": node.notes + spec.notes,
            }
        )

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        issues: list[ValidationIssue] = []
        data = SpecializeData.model_validate(node.data)
        if not data.name.strip():
            issues.append(ValidationIssue(severity="error", path="data.name", message="Specialize node has no new lemma name."))
        if not data.lean_term.strip():
            issues.append(ValidationIssue(severity="error", path="data.lean_term", message="Specialize node has no Lean term."))
        return ValidationReport.from_issues(issues)

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        try:
            data = SpecializeData.model_validate(node.data)
        except Exception:
            return False
        return bool(data.name.strip() and data.lean_term.strip())


class StructuredProofHandler(ProofRefinementHandler[StructuredProofRefinementSpec]):
    """Generic handler for proof families whose structure is a list of subproofs.

    This covers the reasonably decomposable proof types in `notes/proof_types.md`
    without adding duplicate orchestration code for every taxonomy entry.
    """

    output_model = StructuredProofRefinementSpec

    def __init__(self, kind: ProofKind | str, agent) -> None:
        self.kind = kind_key(kind)
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
                "proof_kind": self.kind,
                "task": "Refine this proof into its main logical components without expanding child proofs deeply.",
            },
            StructuredProofRefinementSpec,
        )
        def child_node(child) -> ProofNode:
            return ProofNode(
                id=f"{node.id}.{child.id_suffix}",
                kind=child.kind,
                status=NodeStatus.raw,
                text=child.text,
                goal=child.goal,
                hypotheses=child.hypotheses,
                notes=child.notes,
            )

        children = [child_node(child) for child in spec.components]
        proof_of_reduction = child_node(spec.proof_of_reduction) if spec.proof_of_reduction else None
        reduced_goal_proof = child_node(spec.proof) if spec.proof else None
        for child in (proof_of_reduction, reduced_goal_proof):
            if child is not None and child.id not in {existing.id for existing in children}:
                children.append(child)
        claim = spec.claim
        full_claim = spec.full_claim
        if self.kind in {ProofKind.existence.value, ProofKind.construction.value}:
            full_claim = full_claim or claim or node.goal
        data = StructuredProofData(
            strategy=spec.strategy,
            summary=spec.summary,
            component_ids=[child.id for child in children],
            assumptions=spec.assumptions,
            conclusions=spec.conclusions,
            witness=spec.witness,
            contradiction_assumption=spec.contradiction_assumption,
            full_claim=full_claim,
            claim=claim,
            variable_name=spec.variable_name,
            candidate_variables=spec.candidate_variables,
            bound_claim=spec.bound_claim,
            reduced_to=spec.reduced_to,
            proof_of_reduction_id=proof_of_reduction.id if proof_of_reduction else None,
            proof_id=reduced_goal_proof.id if reduced_goal_proof else None,
            invariant=spec.invariant,
            construction=spec.construction,
            metadata=metadata_entries_to_dict(spec.metadata),
        )
        status = NodeStatus.decomposed if children else NodeStatus.resolved
        if spec.unresolved_details and not children:
            status = NodeStatus.resolved
        return node.model_copy(
            update={
                "kind": self.kind,
                "status": status,
                "children": children,
                "data": data.model_dump(),
                "unresolved_details": node.unresolved_details + spec.unresolved_details,
                "notes": node.notes + spec.notes,
            }
        )

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        issues: list[ValidationIssue] = []
        data = StructuredProofData.model_validate(node.data)
        child_ids = {child.id for child in node.children}
        for component_id in data.component_ids:
            if component_id not in child_ids:
                issues.append(
                    ValidationIssue(
                        severity="error",
                        path="data.component_ids",
                        message=f"Referenced component id {component_id!r} is missing.",
                    )
                )
        if self.kind == ProofKind.existence.value and not (data.witness or node.children):
            issues.append(
                ValidationIssue(
                    severity="warning",
                    path="data.witness",
                    message="Existence proof has no explicit witness or witness subproof.",
                )
            )
        if self.kind in {ProofKind.existence.value, ProofKind.construction.value} and not (data.full_claim or data.claim):
            issues.append(
                ValidationIssue(
                    severity="error",
                    path="data.full_claim",
                    message="Existence and construction proofs must include the full existential claim being proved.",
                )
            )
        if self.kind == ProofKind.contradiction.value and not (data.contradiction_assumption or node.children):
            issues.append(
                ValidationIssue(
                    severity="warning",
                    path="data.contradiction_assumption",
                    message="Contradiction proof has no negated assumption or contradiction subproof.",
                )
            )
        return ValidationReport.from_issues(issues)

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        if node.children:
            return all(
                child.status in {NodeStatus.resolved, NodeStatus.opaque}
                for child in node.children
            )
        return bool(node.data or node.unresolved_details)
