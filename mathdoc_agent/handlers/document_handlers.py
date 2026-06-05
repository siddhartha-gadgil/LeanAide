from __future__ import annotations

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.handlers.base import DocumentRefinementHandler
from mathdoc_agent.models.base import DocumentKind, NodeStatus, ProofKind
from mathdoc_agent.models.document import DocumentNode
from mathdoc_agent.models.payloads import (
    InductiveTypeDefinitionData,
    InstanceDefinitionData,
    StructureDefinitionData,
)
from mathdoc_agent.models.proof import ProofNode, ProofTree
from mathdoc_agent.models.refinement_specs import DocumentRefinementSpec, metadata_entries_to_dict
from mathdoc_agent.models.validation import ValidationIssue, ValidationReport
from mathdoc_agent.orchestration.context import DocumentContext
from mathdoc_agent.orchestration.worklist import kind_key


THEOREM_LIKE_KINDS = {
    DocumentKind.theorem.value,
    DocumentKind.lemma.value,
    DocumentKind.proposition.value,
    DocumentKind.corollary.value,
    DocumentKind.local_claim.value,
}


def _looks_like_proof_text(text: str) -> bool:
    stripped = text.lstrip().lower()
    return stripped.startswith("proof.") or stripped.startswith("proof:")


def _attach_adjacent_proof_children(spec: DocumentRefinementSpec) -> list:
    children = []
    for child in spec.children:
        child_kind = kind_key(child.kind)
        if (
            child_kind in {DocumentKind.paragraph.value, DocumentKind.proof.value}
            and _looks_like_proof_text(child.text)
            and children
            and kind_key(children[-1].kind) in THEOREM_LIKE_KINDS
            and not children[-1].proof_text
        ):
            previous = children[-1]
            children[-1] = previous.model_copy(
                update={
                    "text": f"{previous.text}\n\n{child.text}",
                    "proof_text": child.text,
                    "notes": previous.notes
                    + child.notes
                    + ["Attached adjacent proof paragraph to preceding theorem-like node."],
                }
            )
            continue
        children.append(child)
    return children


class UnknownDocumentHandler(DocumentRefinementHandler[DocumentRefinementSpec]):
    kind = DocumentKind.unknown.value
    output_model = DocumentRefinementSpec

    def __init__(self, agent) -> None:
        self.agent = agent

    async def refine(self, node: DocumentNode, context: DocumentContext) -> DocumentNode:
        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
                "task": "Decompose this mathematical document node into local child nodes.",
            },
            DocumentRefinementSpec,
        )
        children: list[DocumentNode] = []
        for child in _attach_adjacent_proof_children(spec):
            child_id = f"{node.id}.{child.id_suffix}"
            child_kind = kind_key(child.kind)
            data = metadata_entries_to_dict(child.data_entries)
            if child.statement is not None:
                data["statement"] = child.statement
            assumptions = [
                entry.value
                for entry in child.data_entries
                if entry.key == "assumption" and entry.value.strip()
            ]
            if assumptions and child_kind in THEOREM_LIKE_KINDS:
                data["assumptions"] = assumptions
            if child_kind == DocumentKind.structure_definition.value:
                data = StructureDefinitionData(
                    name=child.name or child.title or child.label or child.id_suffix,
                    is_class=bool(child.is_class),
                    is_prop=bool(child.is_prop),
                    parameters=child.parameters,
                    extends=child.extends,
                    fields=child.fields,
                ).model_dump()
            elif child_kind == DocumentKind.instance_definition.value:
                data = InstanceDefinitionData(
                    name=child.name,
                    class_name=child.class_name,
                    target=child.target,
                    parameters=child.parameters,
                    gives=child.gives
                    or [
                        {"name": field.name, "value": field.type}
                        for field in child.fields
                        if field.name is not None
                    ],
                    value=child.value,
                ).model_dump()
            elif child_kind == DocumentKind.inductive_type_definition.value:
                data = InductiveTypeDefinitionData(
                    name=child.name or child.title or child.label or child.id_suffix,
                    is_prop=bool(child.is_prop),
                    parameters=child.parameters,
                    indices=child.indices,
                    constructors=child.constructors,
                ).model_dump()
            proof = None
            if child.proof_text:
                statement = str(child.statement or data.get("statement") or child.text)
                proof = ProofTree(
                    id=f"{child_id}.proof",
                    theorem_statement=statement,
                    root=ProofNode(
                        id=f"{child_id}.proof.root",
                        kind=ProofKind.unknown,
                        status=NodeStatus.raw,
                        text=child.proof_text,
                        goal=statement,
                    ),
                )
            children.append(
                DocumentNode(
                    id=child_id,
                    kind=child.kind,
                    status=NodeStatus.decomposed if proof else NodeStatus.classified,
                    title=child.title,
                    label=child.label,
                    text=child.text,
                    data=data,
                    proof=proof,
                    notes=child.notes,
                )
            )
        return node.model_copy(
            update={
                "kind": DocumentKind.document,
                "status": NodeStatus.decomposed,
                "children": children,
                "notes": node.notes + spec.notes,
            }
        )

    def validate(self, node: DocumentNode, context: DocumentContext) -> ValidationReport:
        issues: list[ValidationIssue] = []
        if not node.children:
            issues.append(ValidationIssue(severity="warning", path="children", message="Document node has no children after refinement."))
        return ValidationReport(ok=True, issues=issues)

    def is_resolved(self, node: DocumentNode, context: DocumentContext) -> bool:
        return bool(node.children) and all(
            child.status in {NodeStatus.resolved, NodeStatus.opaque, NodeStatus.classified}
            for child in node.children
        )


class PassthroughDocumentHandler(DocumentRefinementHandler[None]):
    def __init__(self, kind: DocumentKind | str) -> None:
        self.kind = kind_key(kind)

    async def refine(self, node: DocumentNode, context: DocumentContext) -> DocumentNode:
        return node.model_copy(update={"status": NodeStatus.resolved})

    def is_resolved(self, node: DocumentNode, context: DocumentContext) -> bool:
        return not node.children and node.proof is None
