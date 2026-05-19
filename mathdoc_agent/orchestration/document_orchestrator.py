from __future__ import annotations

from uuid import uuid4

from mathdoc_agent.models.base import DocumentKind, NodeStatus
from mathdoc_agent.models.document import DocumentNode, MathDocument
from mathdoc_agent.models.payloads import StatementData
from mathdoc_agent.models.runs import AgentRunRecord
from mathdoc_agent.orchestration.context import DocumentContext
from mathdoc_agent.orchestration.proof_orchestrator import refine_proof_tree
from mathdoc_agent.orchestration.proof_resolution import resolve_and_refine_unhandled_proof_tree
from mathdoc_agent.orchestration.worklist import kind_key, replace_document_node, walk_document_nodes
from mathdoc_agent.registries.document_handlers import DocumentHandlerRegistry
from mathdoc_agent.registries.proof_handlers import ProofHandlerRegistry


def document_from_text(text: str, *, id: str = "doc", title: str | None = None) -> MathDocument:
    return MathDocument(
        id=id,
        title=title,
        root=DocumentNode(
            id=f"{id}.root",
            kind=DocumentKind.unknown,
            status=NodeStatus.raw,
            title=title,
            text=text,
        ),
    )


def available_document_results(root: DocumentNode) -> list[str]:
    results: list[str] = []
    theorem_kinds = {
        DocumentKind.theorem.value,
        DocumentKind.lemma.value,
        DocumentKind.proposition.value,
        DocumentKind.corollary.value,
    }
    for node in walk_document_nodes(root):
        if kind_key(node.kind) in theorem_kinds:
            try:
                data = StatementData.model_validate(node.data)
                label = f"{node.label}: " if node.label else ""
                results.append(f"{label}{data.statement}")
            except Exception:
                if node.text:
                    results.append(node.text)
    return results


def build_document_context(document: MathDocument, node: DocumentNode) -> DocumentContext:
    labels = [
        n.label
        for n in walk_document_nodes(document.root)
        if n.label is not None
    ]
    statements = available_document_results(document.root)
    return DocumentContext(
        document_title=document.title,
        ancestor_titles=[],
        available_labels=labels,
        nearby_statements=statements,
    )


def _document_node_resolved(node: DocumentNode) -> bool:
    if node.status == NodeStatus.opaque:
        return True
    if node.proof is not None and node.proof.root.status not in {NodeStatus.resolved, NodeStatus.opaque}:
        return False
    if node.children:
        return all(_document_node_resolved(child) for child in node.children)
    return node.status in {
        NodeStatus.classified,
        NodeStatus.decomposed,
        NodeStatus.resolved,
        NodeStatus.validated,
    }


def recompute_document_statuses(root: DocumentNode) -> DocumentNode:
    children = [recompute_document_statuses(child) for child in root.children]
    root = root.model_copy(update={"children": children})
    if root.status == NodeStatus.opaque:
        return root
    if _document_node_resolved(root):
        return root.model_copy(update={"status": NodeStatus.resolved})
    if root.children or root.proof is not None:
        return root.model_copy(update={"status": NodeStatus.decomposed})
    return root


def choose_next_document_node(root: DocumentNode) -> DocumentNode | None:
    for node in walk_document_nodes(root):
        if node.status == NodeStatus.raw:
            return node
        if (
            kind_key(node.kind) == DocumentKind.unknown.value
            and not node.children
            and node.proof is None
            and node.status not in {NodeStatus.resolved, NodeStatus.opaque}
        ):
            return node
    return None


async def refine_document_structure(
    document: MathDocument,
    registry: DocumentHandlerRegistry,
    max_iterations: int = 20,
) -> MathDocument:
    doc = document.model_copy(update={"root": recompute_document_statuses(document.root)})
    run_log = list(doc.run_log)
    for _ in range(max_iterations):
        node = choose_next_document_node(doc.root)
        if node is None:
            break
        context = build_document_context(doc, node)
        handler = registry.get(kind_key(node.kind))
        old_status = node.status.value
        candidate = await handler.refine(node, context)
        report = handler.validate(candidate, context)
        if not report.ok:
            candidate = node.model_copy(
                update={
                    "kind": DocumentKind.opaque,
                    "status": NodeStatus.opaque,
                    "notes": node.notes
                    + [
                        "Marked opaque after failed validation: "
                        + "; ".join(issue.message for issue in report.issues)
                    ],
                }
            )
        run_log.append(
            AgentRunRecord(
                run_id=str(uuid4()),
                agent_name=handler.__class__.__name__,
                target_node_id=node.id,
                target_node_kind=kind_key(node.kind),
                input_summary=node.text[:200],
                output_summary=candidate.text[:200],
                validation_ok=report.ok,
                issues=[issue.message for issue in report.issues],
                old_status=old_status,
                new_status=candidate.status.value,
            )
        )
        doc = doc.model_copy(
            update={
                "root": recompute_document_statuses(
                    replace_document_node(doc.root, node.id, candidate)
                ),
                "run_log": run_log,
            }
        )
    return doc.model_copy(update={"root": recompute_document_statuses(doc.root), "run_log": run_log})


async def refine_attached_proofs(
    document: MathDocument,
    proof_registry: ProofHandlerRegistry,
    max_iterations_per_proof: int = 100,
    proof_resolution_agents: dict[str, object] | None = None,
) -> MathDocument:
    root = document.root
    results = available_document_results(root)
    for node in list(walk_document_nodes(root)):
        if node.proof is None:
            continue
        refined_proof = await refine_proof_tree(
            node.proof,
            proof_registry,
            available_document_results=results,
            max_iterations=max_iterations_per_proof,
        )
        refined_proof = await resolve_and_refine_unhandled_proof_tree(
            refined_proof,
            proof_resolution_agents,
            proof_registry,
            available_document_results=results,
            max_iterations=max_iterations_per_proof,
        )
        root = replace_document_node(
            root,
            node.id,
            node.model_copy(update={"proof": refined_proof}),
        )
    return document.model_copy(update={"root": recompute_document_statuses(root)})


async def refine_math_document(
    document: MathDocument,
    document_registry: DocumentHandlerRegistry,
    proof_registry: ProofHandlerRegistry,
    *,
    document_iterations: int = 20,
    proof_iterations: int = 100,
    proof_resolution_agents: dict[str, object] | None = None,
) -> MathDocument:
    doc = await refine_document_structure(
        document,
        document_registry,
        max_iterations=document_iterations,
    )
    doc = await refine_attached_proofs(
        doc,
        proof_registry,
        max_iterations_per_proof=proof_iterations,
        proof_resolution_agents=proof_resolution_agents,
    )
    return doc.model_copy(update={"root": recompute_document_statuses(doc.root)})
