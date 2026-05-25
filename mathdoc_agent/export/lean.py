from __future__ import annotations

from mathdoc_agent.models.base import ProofKind
from mathdoc_agent.models.payloads import InductionData, SimpleProofData, SpecializeData
from mathdoc_agent.models.proof import ProofNode, ProofTree
from mathdoc_agent.orchestration.worklist import kind_key


def render_proof_skeleton(node: ProofNode, indent: int = 1) -> list[str]:
    pad = "  " * indent
    kind = kind_key(node.kind)
    lines = [f"{pad}-- proof node {node.id}: {kind}"]
    if kind == ProofKind.induction.value:
        try:
            data = InductionData.model_validate(node.data)
            lines.append(f"{pad}-- induction on {data.variable}")
        except Exception:
            pass
    if kind in {ProofKind.logical_sequence.value, ProofKind.simple.value}:
        try:
            data = SimpleProofData.model_validate(node.data)
            for hint in data.hints:
                lines.append(f"{pad}-- hint: {hint}")
        except Exception:
            pass
    if kind == ProofKind.specialize.value:
        try:
            data = SpecializeData.model_validate(node.data)
            lines.append(f"{pad}have {data.name} := {data.lean_term}")
        except Exception:
            pass
    for child in node.children:
        lines.extend(render_proof_skeleton(child, indent + 1))
    return lines


def render_lean_skeleton(name: str, statement: str, proof_tree: ProofTree | None = None) -> str:
    lines = [f"theorem {name} : {statement} := by"]
    if proof_tree is None:
        lines.append("  -- proof unavailable")
        lines.append("  sorry")
        return "\n".join(lines)
    lines.extend(render_proof_skeleton(proof_tree.root))
    lines.append("  sorry")
    return "\n".join(lines)
