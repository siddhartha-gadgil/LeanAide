from __future__ import annotations

from typing import Any, Optional, Union

from pydantic import BaseModel, Field, computed_field

from mathdoc_agent.models.base import DocumentKind, NodeStatus
from mathdoc_agent.models.proof import ProofTree
from mathdoc_agent.models.references import Reference
from mathdoc_agent.models.runs import AgentRunRecord


class DocumentNode(BaseModel):
    id: str
    kind: Union[DocumentKind, str] = DocumentKind.unknown
    status: NodeStatus = NodeStatus.raw

    title: Optional[str] = None
    label: Optional[str] = None
    text: str = ""

    children: list["DocumentNode"] = Field(default_factory=list)
    proof: Optional[ProofTree] = None
    data: dict[str, Any] = Field(default_factory=dict)
    references: list[Reference] = Field(default_factory=list)

    confidence: float = Field(default=0.5, ge=0.0, le=1.0)
    notes: list[str] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)

    @computed_field(return_type=str)
    @property
    def type(self) -> str:
        kind = self.kind.value if hasattr(self.kind, "value") else str(self.kind)
        return {
            DocumentKind.document.value: "document",
            DocumentKind.section.value: "section",
            DocumentKind.subsection.value: "section",
            DocumentKind.paragraph.value: "paragraph",
            DocumentKind.definition.value: "definition",
            DocumentKind.structure_definition.value: "structure-definition",
            DocumentKind.instance_definition.value: "instance-definition",
            DocumentKind.inductive_type_definition.value: "inductive-type-definition",
            DocumentKind.theorem.value: "theorem",
            DocumentKind.lemma.value: "theorem",
            DocumentKind.proposition.value: "theorem",
            DocumentKind.corollary.value: "theorem",
            DocumentKind.example.value: "paragraph",
            DocumentKind.remark.value: "paragraph",
            DocumentKind.proof.value: "proof",
            DocumentKind.local_claim.value: "theorem",
            DocumentKind.calculation_block.value: "calculation",
            DocumentKind.opaque.value: "opaque",
        }.get(kind, kind)


class MathDocument(BaseModel):
    id: str
    title: Optional[str] = None
    root: DocumentNode
    run_log: list[AgentRunRecord] = Field(default_factory=list)

    @computed_field(return_type=str)
    @property
    def type(self) -> str:
        return "document"

    @computed_field(return_type=dict)
    @property
    def document(self) -> dict[str, Any]:
        body = [child.model_dump() for child in self.root.children]
        document: dict[str, Any] = {
            "type": "document",
            "body": body,
        }
        if self.title is not None:
            document["title"] = self.title
        return document


DocumentNode.model_rebuild()
