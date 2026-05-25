from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.base import NodeStatus, ProofKind
from mathdoc_agent.models.payloads import SimpleProofData, StructuredProofData
from mathdoc_agent.models.proof import ProofNode, ProofTree
from mathdoc_agent.models.refinement_specs import ProofResolutionSpec
from mathdoc_agent.orchestration.context import build_proof_context
from mathdoc_agent.orchestration.worklist import (
    kind_key,
    replace_proof_node,
    walk_proof_nodes,
)
from mathdoc_agent.registries.proof_handlers import ProofHandlerRegistry


DIRECT_CODEGEN_PROOF_KINDS = {
    ProofKind.logical_sequence.value,
    ProofKind.simple.value,
    ProofKind.calculation.value,
    ProofKind.cases.value,
    ProofKind.induction.value,
    ProofKind.contradiction.value,
    ProofKind.equivalence.value,
    ProofKind.existence.value,
    ProofKind.uniqueness.value,
    ProofKind.construction.value,
    ProofKind.minimal_counterexample.value,
    ProofKind.infinite_descent.value,
    ProofKind.exhaustion.value,
    ProofKind.reduction.value,
    ProofKind.epsilon_delta.value,
    ProofKind.local_claim.value,
    ProofKind.theorem_application.value,
    ProofKind.definition_unfolding.value,
    ProofKind.specialize.value,
    ProofKind.opaque.value,
}


SUPPORTED_RESOLUTION_CHILD_KINDS = {
    ProofKind.logical_sequence.value,
    ProofKind.simple.value,
    ProofKind.calculation.value,
    ProofKind.cases.value,
    ProofKind.induction.value,
    ProofKind.contradiction.value,
    ProofKind.equivalence.value,
    ProofKind.existence.value,
    ProofKind.uniqueness.value,
    ProofKind.construction.value,
    ProofKind.reduction.value,
    ProofKind.epsilon_delta.value,
    ProofKind.local_claim.value,
    ProofKind.theorem_application.value,
    ProofKind.definition_unfolding.value,
    ProofKind.specialize.value,
}


def proof_kind_needs_resolution(kind: ProofKind | str) -> bool:
    return kind_key(kind) not in DIRECT_CODEGEN_PROOF_KINDS


def _agent_for_kind(
    agents: Mapping[str, Any],
    kind: str,
) -> Any | None:
    return agents.get(kind) or agents.get("default")


def _valid_child_kind(kind: ProofKind | str) -> ProofKind | str:
    key = kind_key(kind)
    if key in SUPPORTED_RESOLUTION_CHILD_KINDS:
        return kind
    return ProofKind.logical_sequence


def _resolved_child(parent: ProofNode, index: int, child) -> ProofNode:
    return ProofNode(
        id=f"{parent.id}.resolved{index}.{child.id_suffix}",
        kind=_valid_child_kind(child.kind),
        status=NodeStatus.raw,
        text=child.text,
        goal=child.goal,
        hypotheses=child.hypotheses,
        notes=child.notes,
    )


def _original_kind_note(kind: str) -> str:
    return f"Resolved from original proof kind '{kind}' for Lean codegen."


async def resolve_unhandled_proof_node(
    proof_tree: ProofTree,
    node: ProofNode,
    agents: Mapping[str, Any],
) -> ProofNode:
    kind = kind_key(node.kind)
    agent = _agent_for_kind(agents, kind)
    if agent is None:
        return node
    context = build_proof_context(proof_tree, node.id)
    spec = await run_agent_typed(
        agent,
        {
            "node": node.model_dump(),
            "context": context.model_dump(),
            "proof_kind": kind,
            "supported_child_kinds": sorted(SUPPORTED_RESOLUTION_CHILD_KINDS),
            "task": (
                "Express this already-refined proof using simpler proof "
                "structures with Lean codegen handlers."
            ),
        },
        ProofResolutionSpec,
    )
    children = [
        _resolved_child(node, index, child)
        for index, child in enumerate(spec.components, start=1)
    ]
    data = SimpleProofData(
        method=spec.strategy,
        hints=[spec.summary] if spec.summary else [],
        proof_steps=spec.proof_steps,
    )
    original_data = (
        StructuredProofData.model_validate(node.data)
        if node.data
        else StructuredProofData()
    )
    original_metadata = dict(original_data.metadata)
    original_metadata.setdefault("original_proof_kind", kind)
    data_dump = data.model_dump()
    data_dump["resolution_metadata"] = original_metadata
    status = NodeStatus.decomposed if children else NodeStatus.resolved
    if not children and not (spec.proof_steps or spec.unresolved_details or spec.summary):
        status = NodeStatus.opaque
    return node.model_copy(
        update={
            "kind": ProofKind.logical_sequence,
            "status": status,
            "children": children,
            "data": data_dump,
            "notes": node.notes + [_original_kind_note(kind)] + spec.notes,
            "unresolved_details": node.unresolved_details + spec.unresolved_details,
        }
    )


async def resolve_unhandled_proof_tree(
    proof_tree: ProofTree,
    agents: Mapping[str, Any] | None,
) -> tuple[ProofTree, bool]:
    if not agents:
        return proof_tree, False
    tree = proof_tree
    changed = False
    nodes = sorted(
        list(walk_proof_nodes(tree.root)),
        key=lambda item: item.id.count("."),
        reverse=True,
    )
    for node in nodes:
        if node.status == NodeStatus.opaque or not proof_kind_needs_resolution(node.kind):
            continue
        replacement = await resolve_unhandled_proof_node(tree, node, agents)
        if replacement is node:
            continue
        tree = tree.model_copy(
            update={"root": replace_proof_node(tree.root, node.id, replacement)}
        )
        changed = True
    return tree, changed


async def resolve_and_refine_unhandled_proof_tree(
    proof_tree: ProofTree,
    agents: Mapping[str, Any] | None,
    proof_registry: ProofHandlerRegistry,
    *,
    available_document_results: list[str] | None = None,
    max_iterations: int = 100,
) -> ProofTree:
    tree, changed = await resolve_unhandled_proof_tree(proof_tree, agents)
    if not changed:
        return tree
    from mathdoc_agent.orchestration.proof_orchestrator import refine_proof_tree

    return await refine_proof_tree(
        tree,
        proof_registry,
        available_document_results=available_document_results,
        max_iterations=max_iterations,
    )
