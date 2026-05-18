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


SOURCE_TEXT = """Theorem. In an additive group, there is a unique additive identity.

Proof. Existence is given by the identity element 0. For uniqueness, suppose e
and e' are both additive identities. Since e is an identity, e+e'=e'. Since e'
is an identity, e+e'=e. Hence e=e'."""


class DocumentParserAgent:
    def __call__(self, payload):
        return DocumentRefinementSpec(
            children=[
                DocumentChildSpec(
                    id_suffix="thm_unique_additive_identity",
                    kind=DocumentKind.theorem,
                    label="thm:unique_additive_identity",
                    text=SOURCE_TEXT,
                    statement="In an additive group, there is a unique additive identity.",
                    proof_text=(
                        "Existence is given by the identity element 0. For uniqueness, suppose e "
                        "and e' are both additive identities. Since e is an identity, e+e'=e'. "
                        "Since e' is an identity, e+e'=e. Hence e=e'."
                    ),
                )
            ]
        )


class ProofClassifierAgent:
    def __call__(self, payload):
        text = payload["node"]["text"].lower()
        if "existence is given" in text and "for uniqueness" in text:
            return {
                "kind": ProofKind.uniqueness,
                "confidence": 0.99,
                "notes": ["Classified by explicit existence and uniqueness parts."],
            }
        if "identity element 0" in text:
            return {
                "kind": ProofKind.existence,
                "confidence": 0.99,
                "notes": ["Classified as the existence part of the unique existence proof."],
            }
        return {
            "kind": ProofKind.simple,
            "confidence": 0.9,
            "notes": ["Leaf uniqueness verification."],
        }


class StructuredAgent:
    def __call__(self, payload):
        proof_kind = payload["proof_kind"]
        if proof_kind == ProofKind.uniqueness.value:
            return StructuredProofRefinementSpec(
                strategy="split unique existence into existence and uniqueness",
                summary="Use 0 for existence, then compare two arbitrary additive identities.",
                claim="There is a unique additive identity.",
                candidate_variables=["e", "e'"],
                components=[
                    ChildProofSpec(
                        id_suffix="existence",
                        kind=ProofKind.existence,
                        text="Existence is given by the identity element 0.",
                        goal="There exists an additive identity e.",
                    ),
                    ChildProofSpec(
                        id_suffix="uniqueness",
                        kind=ProofKind.simple,
                        text=(
                            "Suppose e and e' are both additive identities. Since e is an identity, "
                            "e+e'=e'. Since e' is an identity, e+e'=e. Hence e=e'."
                        ),
                        goal="Any two additive identities are equal.",
                        hypotheses=["e is an additive identity", "e' is an additive identity"],
                    ),
                ],
            )
        if proof_kind == ProofKind.existence.value:
            return StructuredProofRefinementSpec(
                strategy="provide the identity witness",
                summary="Use 0 as the additive identity.",
                full_claim="There exists an element e such that e is an additive identity.",
                variable_name="e",
                claim="e is an additive identity.",
                witness="0",
                components=[
                    ChildProofSpec(
                        id_suffix="verify_identity",
                        kind=ProofKind.simple,
                        text="The element 0 is an additive identity.",
                        goal="0 is an additive identity.",
                    )
                ],
            )
        return StructuredProofRefinementSpec(
            strategy=f"structured {proof_kind} proof",
            unresolved_details=["No structured uniqueness example matched this proof fragment."],
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
        structured_agent=StructuredAgent(),
        simple_agent=SimpleProofAgent(),
    )
    return document_registry, proof_registry


async def build_document_json() -> str:
    document_registry, proof_registry = build_registries()
    document = document_from_text(
        SOURCE_TEXT,
        id="uniqueness_additive_identity",
        title="Uniqueness of the Additive Identity",
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
    output_path = Path(__file__).with_name("uniqueness_additive_identity.json")
    output_path.write_text(asyncio.run(build_document_json()), encoding="utf-8")
    print(output_path)


if __name__ == "__main__":
    main()
