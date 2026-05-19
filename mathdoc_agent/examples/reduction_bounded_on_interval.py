from __future__ import annotations

import asyncio
from pathlib import Path

from mathdoc_agent.export.json import to_json
from mathdoc_agent.models.base import DocumentKind, ProofKind
from mathdoc_agent.models.refinement_specs import (
    ChildProofSpec,
    DocumentChildSpec,
    DocumentRefinementSpec,
    SimpleProofRefinementSpec,
    StructuredProofRefinementSpec,
)
from mathdoc_agent.orchestration.document_orchestrator import document_from_text, refine_math_document
from mathdoc_agent.plugins.document_types import default_document_handler_registry
from mathdoc_agent.plugins.proof_types import default_proof_handler_registry


SOURCE_TEXT = """Theorem. Every continuous real-valued function on [0,1] is bounded.

Proof. Reduce to the theorem that a continuous function on a compact space is
bounded. The interval [0,1] is compact, so the compact-domain theorem applies
to the given function."""


class DocumentParserAgent:
    def __call__(self, payload):
        return DocumentRefinementSpec(
            children=[
                DocumentChildSpec(
                    id_suffix="thm_continuous_bounded_interval",
                    kind=DocumentKind.theorem,
                    label="thm:continuous_bounded_interval",
                    text=SOURCE_TEXT,
                    statement="Every continuous real-valued function on [0,1] is bounded.",
                    proof_text=(
                        "Reduce to the theorem that a continuous function on a compact space is "
                        "bounded. The interval [0,1] is compact, so the compact-domain theorem "
                        "applies to the given function."
                    ),
                )
            ]
        )


class ProofClassifierAgent:
    def __call__(self, payload):
        return {
            "kind": ProofKind.reduction,
            "confidence": 0.99,
            "notes": ["Classified by explicit reduction to a compact-domain theorem."],
        }


class ReductionAgent:
    def __call__(self, payload):
        return StructuredProofRefinementSpec(
            strategy="reduce to boundedness on compact spaces",
            summary="Use compactness of [0,1] and the compact-domain boundedness theorem.",
            claim="Every continuous real-valued function on [0,1] is bounded.",
            reduced_to="Every continuous real-valued function on a compact space is bounded.",
            proof_of_reduction=ChildProofSpec(
                id_suffix="proof_of_reduction",
                kind=ProofKind.simple,
                text=(
                    "The interval [0,1] is compact, so a continuous function on [0,1] "
                    "is a continuous function on a compact space."
                ),
                goal=(
                    "The boundedness claim for [0,1] reduces to boundedness of "
                    "continuous functions on compact spaces."
                ),
            ),
            proof=ChildProofSpec(
                id_suffix="compact_case",
                kind=ProofKind.simple,
                text="Apply the theorem that continuous functions on compact spaces are bounded.",
                goal="Every continuous real-valued function on a compact space is bounded.",
            ),
        )


class SimpleProofAgent:
    def __call__(self, payload):
        node = payload["node"]
        return SimpleProofRefinementSpec(
            method="direct proof",
            hints=[node["text"]],
            referenced_hypotheses=node.get("hypotheses", []),
        )


def build_registries():
    document_registry = default_document_handler_registry(parser_agent=DocumentParserAgent())
    proof_registry = default_proof_handler_registry(
        classifier_agent=ProofClassifierAgent(),
        structured_agent=ReductionAgent(),
        simple_agent=SimpleProofAgent(),
    )
    return document_registry, proof_registry


async def build_document_json() -> str:
    document_registry, proof_registry = build_registries()
    document = document_from_text(
        SOURCE_TEXT,
        id="reduction_bounded_on_interval",
        title="Boundedness by Reduction to Compactness",
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
    output_path = Path(__file__).with_name("reduction_bounded_on_interval.json")
    output_path.write_text(asyncio.run(build_document_json()), encoding="utf-8")
    print(output_path)


if __name__ == "__main__":
    main()
