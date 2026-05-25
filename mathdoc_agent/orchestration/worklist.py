from __future__ import annotations

from collections.abc import Iterator

from mathdoc_agent.models.base import NodeStatus, ProofKind
from mathdoc_agent.models.document import DocumentNode
from mathdoc_agent.models.proof import ProofNode


def kind_key(kind: object) -> str:
    return kind.value if hasattr(kind, "value") else str(kind)


def walk_proof_nodes(root: ProofNode) -> Iterator[ProofNode]:
    yield root
    for child in root.children:
        yield from walk_proof_nodes(child)


def walk_document_nodes(root: DocumentNode) -> Iterator[DocumentNode]:
    yield root
    for child in root.children:
        yield from walk_document_nodes(child)


def find_proof_node(root: ProofNode, node_id: str) -> ProofNode | None:
    for node in walk_proof_nodes(root):
        if node.id == node_id:
            return node
    return None


def replace_proof_node(root: ProofNode, node_id: str, replacement: ProofNode) -> ProofNode:
    if root.id == node_id:
        return replacement
    return root.model_copy(
        update={
            "children": [
                replace_proof_node(child, node_id, replacement)
                for child in root.children
            ]
        }
    )


def replace_document_node(root: DocumentNode, node_id: str, replacement: DocumentNode) -> DocumentNode:
    if root.id == node_id:
        return replacement
    return root.model_copy(
        update={
            "children": [
                replace_document_node(child, node_id, replacement)
                for child in root.children
            ]
        }
    )


def unresolved_proof_nodes(root: ProofNode) -> list[ProofNode]:
    return [
        node
        for node in walk_proof_nodes(root)
        if node.status not in {NodeStatus.resolved, NodeStatus.opaque}
    ]


def proof_node_priority(node: ProofNode) -> tuple[int, int, int]:
    status_rank = {
        NodeStatus.raw: 0,
        NodeStatus.classified: 1,
        NodeStatus.decomposed: 2,
        NodeStatus.locally_refined: 3,
        NodeStatus.validated: 4,
    }.get(node.status, 9)
    kind_rank = {
        ProofKind.unknown.value: 0,
        ProofKind.induction.value: 1,
        ProofKind.cases.value: 1,
        ProofKind.local_claim.value: 2,
        ProofKind.specialize.value: 2,
        ProofKind.extensionality.value: 2,
        ProofKind.existence.value: 2,
        ProofKind.uniqueness.value: 2,
        ProofKind.calculation.value: 3,
        ProofKind.logical_sequence.value: 4,
        ProofKind.simple.value: 4,
    }.get(kind_key(node.kind), 9)
    return (status_rank, kind_rank, -len(node.text))


def choose_next_proof_node(root: ProofNode) -> ProofNode | None:
    candidates = unresolved_proof_nodes(root)
    if not candidates:
        return None
    return sorted(candidates, key=proof_node_priority)[0]
