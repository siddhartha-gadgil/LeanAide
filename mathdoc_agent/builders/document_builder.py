from __future__ import annotations

from mathdoc_agent.models.base import DocumentKind, NodeStatus, ProofKind
from mathdoc_agent.models.document import DocumentNode
from mathdoc_agent.models.payloads import (
    DefinitionData,
    InductiveConstructorData,
    InductiveTypeDefinitionData,
    InstanceGiveData,
    InstanceDefinitionData,
    ParameterData,
    StatementData,
    StructureDefinitionData,
    StructureFieldData,
)
from mathdoc_agent.models.proof import ProofNode, ProofTree


class DocumentBuilder:
    @staticmethod
    def theorem_like(
        *,
        id: str,
        kind: DocumentKind,
        text: str,
        statement: str,
        proof_text: str | None = None,
        label: str | None = None,
        assumptions: list[str] | None = None,
        conclusion: str | None = None,
    ) -> DocumentNode:
        proof = None
        if proof_text:
            proof = ProofTree(
                id=f"{id}.proof",
                theorem_statement=statement,
                root=ProofNode(
                    id=f"{id}.proof.root",
                    kind=ProofKind.unknown,
                    status=NodeStatus.raw,
                    text=proof_text,
                    goal=statement,
                ),
            )
        return DocumentNode(
            id=id,
            kind=kind,
            status=NodeStatus.decomposed if proof else NodeStatus.classified,
            label=label,
            text=text,
            data=StatementData(
                statement=statement,
                assumptions=assumptions or [],
                conclusion=conclusion,
            ).model_dump(),
            proof=proof,
        )

    @staticmethod
    def definition(
        *,
        id: str,
        text: str,
        term: str | None = None,
        definitions: str | None = None,
        notation: str | None = None,
        label: str | None = None,
    ) -> DocumentNode:
        return DocumentNode(
            id=id,
            kind=DocumentKind.definition,
            status=NodeStatus.classified,
            label=label,
            text=text,
            data=DefinitionData(term=term, definitions=definitions, notation=notation).model_dump(),
        )

    @staticmethod
    def structure_definition(
        *,
        id: str,
        text: str,
        name: str,
        is_class: bool = False,
        is_prop: bool = False,
        fields: list[StructureFieldData] | None = None,
        parameters: list[ParameterData | str] | None = None,
        extends: list[str] | None = None,
        label: str | None = None,
    ) -> DocumentNode:
        return DocumentNode(
            id=id,
            kind=DocumentKind.structure_definition,
            status=NodeStatus.classified,
            label=label,
            text=text,
            data=StructureDefinitionData(
                name=name,
                is_class=is_class,
                is_prop=is_prop,
                parameters=parameters or [],
                extends=extends or [],
                fields=fields or [],
            ).model_dump(),
        )

    @staticmethod
    def instance_definition(
        *,
        id: str,
        text: str,
        class_name: str | None = None,
        target: str | None = None,
        name: str | None = None,
        parameters: list[ParameterData | str] | None = None,
        gives: list[InstanceGiveData] | None = None,
        fields: dict[str, str] | None = None,
        value: str | None = None,
        label: str | None = None,
    ) -> DocumentNode:
        return DocumentNode(
            id=id,
            kind=DocumentKind.instance_definition,
            status=NodeStatus.classified,
            label=label,
            text=text,
            data=InstanceDefinitionData(
                name=name,
                class_name=class_name,
                target=target,
                parameters=parameters or [],
                gives=gives or fields or [],
                value=value,
            ).model_dump(),
        )

    @staticmethod
    def inductive_type_definition(
        *,
        id: str,
        text: str,
        name: str,
        is_prop: bool = False,
        constructors: list[InductiveConstructorData] | None = None,
        parameters: list[ParameterData | str] | None = None,
        indices: list[ParameterData | str] | None = None,
        label: str | None = None,
    ) -> DocumentNode:
        return DocumentNode(
            id=id,
            kind=DocumentKind.inductive_type_definition,
            status=NodeStatus.classified,
            label=label,
            text=text,
            data=InductiveTypeDefinitionData(
                name=name,
                is_prop=is_prop,
                parameters=parameters or [],
                indices=indices or [],
                constructors=constructors or [],
            ).model_dump(),
        )
