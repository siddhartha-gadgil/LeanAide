from __future__ import annotations

import asyncio
from pathlib import Path

from mathdoc_agent.export.json import to_json
from mathdoc_agent.models.base import DocumentKind, ProofKind
from mathdoc_agent.models.payloads import CalcRelation, CalcStep
from mathdoc_agent.models.refinement_specs import (
    CalculationRefinementSpec,
    ChildProofSpec,
    DocumentChildSpec,
    DocumentRefinementSpec,
    MetadataEntry,
    SimpleProofRefinementSpec,
    StructuredProofRefinementSpec,
)
from mathdoc_agent.orchestration.document_orchestrator import document_from_text, refine_math_document
from mathdoc_agent.plugins.document_types import default_document_handler_registry
from mathdoc_agent.plugins.proof_types import default_proof_handler_registry


SOURCE_TEXT = """Theorem. The function f(x)=2x has limit 6 as x tends to 3.

Proof. Let epsilon>0 and choose delta=epsilon/2. Since epsilon is positive,
delta is positive. If |x-3|<delta, then |2x-6|=2|x-3|<2delta=epsilon."""


class DocumentParserAgent:
    def __call__(self, payload):
        return DocumentRefinementSpec(
            children=[
                DocumentChildSpec(
                    id_suffix="thm_limit_two_x_at_three",
                    kind=DocumentKind.theorem,
                    label="thm:limit_two_x_at_three",
                    text=SOURCE_TEXT,
                    statement="The function f(x)=2x has limit 6 as x tends to 3.",
                    proof_text=(
                        "Let epsilon>0 and choose delta=epsilon/2. Since epsilon is positive, "
                        "delta is positive. If |x-3|<delta, then |2x-6|=2|x-3|<2delta=epsilon."
                    ),
                )
            ]
        )


class ProofClassifierAgent:
    def __call__(self, payload):
        return {
            "kind": ProofKind.epsilon_delta,
            "confidence": 0.99,
            "notes": ["Classified by explicit epsilon-delta proof structure."],
        }


class EpsilonDeltaAgent:
    def __call__(self, payload):
        return StructuredProofRefinementSpec(
            strategy="epsilon-delta proof",
            summary="Given epsilon, choose delta=epsilon/2 and verify the bound.",
            assumptions=["epsilon > 0"],
            conclusions=["|2x-6| < epsilon"],
            bound_claim="If |x-3| < delta, then |2x-6| < epsilon.",
            metadata=[
                MetadataEntry(key="epsilon_var", value="epsilon"),
                MetadataEntry(key="delta", value="epsilon/2"),
            ],
            components=[
                ChildProofSpec(
                    id_suffix="delta_positive",
                    kind=ProofKind.simple,
                    text="Since epsilon > 0 and delta=epsilon/2, delta is positive.",
                    goal="delta > 0.",
                    hypotheses=["epsilon > 0", "delta = epsilon/2"],
                ),
                ChildProofSpec(
                    id_suffix="verify_bound",
                    kind=ProofKind.calculation,
                    text="If |x-3|<delta, then |2x-6|=2|x-3|<2delta=epsilon.",
                    goal="|2x-6| < epsilon.",
                    hypotheses=["|x-3| < delta", "delta = epsilon/2"],
                ),
            ],
        )


class SimpleProofAgent:
    def __call__(self, payload):
        node = payload["node"]
        return SimpleProofRefinementSpec(
            method="direct proof",
            hints=[node["text"]],
            referenced_hypotheses=node.get("hypotheses", []),
        )


class CalculationAgent:
    def __call__(self, payload):
        return CalculationRefinementSpec(
            calculation_kind="epsilon_delta_bound",
            steps=[
                CalcStep(lhs="|2x-6|", relation=CalcRelation.eq, rhs="2|x-3|"),
                CalcStep(lhs="2|x-3|", relation=CalcRelation.lt, rhs="2 delta"),
                CalcStep(lhs="2 delta", relation=CalcRelation.eq, rhs="epsilon"),
            ],
        )


def build_registries():
    document_registry = default_document_handler_registry(parser_agent=DocumentParserAgent())
    proof_registry = default_proof_handler_registry(
        classifier_agent=ProofClassifierAgent(),
        structured_agent=EpsilonDeltaAgent(),
        simple_agent=SimpleProofAgent(),
        calculation_agent=CalculationAgent(),
    )
    return document_registry, proof_registry


async def build_document_json() -> str:
    document_registry, proof_registry = build_registries()
    document = document_from_text(
        SOURCE_TEXT,
        id="epsilon_delta_linear_limit",
        title="A Linear Epsilon-Delta Limit",
    )
    refined = await refine_math_document(
        document,
        document_registry,
        proof_registry,
        document_iterations=5,
        proof_iterations=10,
    )
    return to_json(refined, indent=2)


def main() -> None:
    output_path = Path(__file__).with_name("epsilon_delta_linear_limit.json")
    output_path.write_text(asyncio.run(build_document_json()), encoding="utf-8")
    print(output_path)


if __name__ == "__main__":
    main()
