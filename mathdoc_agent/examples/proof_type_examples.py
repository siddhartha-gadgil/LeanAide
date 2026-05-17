from __future__ import annotations

import asyncio
from dataclasses import dataclass
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


@dataclass(frozen=True)
class ProofExample:
    slug: str
    title: str
    label: str
    statement: str
    proof_kind: ProofKind
    proof_text: str
    structured_spec: StructuredProofRefinementSpec

    @property
    def source_text(self) -> str:
        return f"Theorem. {self.statement}\n\nProof. {self.proof_text}"


EXAMPLES: tuple[ProofExample, ...] = (
    ProofExample(
        slug="contradiction_infinitely_many_primes",
        title="Infinitely Many Primes",
        label="thm:infinitely_many_primes",
        statement="There are infinitely many prime numbers.",
        proof_kind=ProofKind.contradiction,
        proof_text=(
            "Suppose, for contradiction, that there are only finitely many primes "
            "p_1,...,p_r. Let N=p_1...p_r+1. Any prime divisor q of N is not equal "
            "to any p_i, since division by p_i leaves remainder 1. This contradicts "
            "the assumption that p_1,...,p_r list all primes."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="proof by contradiction",
            summary="Assume finitely many primes, construct N, and get a new prime divisor.",
            contradiction_assumption="There are only finitely many prime numbers.",
            components=[
                ChildProofSpec(
                    id_suffix="assume_finite_list",
                    kind=ProofKind.simple,
                    text="Assume the complete list of primes is p_1,...,p_r.",
                    hypotheses=["There are only finitely many primes."],
                ),
                ChildProofSpec(
                    id_suffix="construct_new_number",
                    kind=ProofKind.simple,
                    text="Let N=p_1...p_r+1; any prime divisor q of N is not any p_i.",
                    goal="There is a prime not on the list.",
                ),
                ChildProofSpec(
                    id_suffix="contradiction",
                    kind=ProofKind.simple,
                    text="This contradicts that p_1,...,p_r were all the primes.",
                    goal="Contradiction.",
                ),
            ],
        ),
    ),
    ProofExample(
        slug="contrapositive_square_even",
        title="Even Square Contrapositive",
        label="thm:square_even_contrapositive",
        statement="If n^2 is even, then n is even.",
        proof_kind=ProofKind.contrapositive,
        proof_text=(
            "We prove the contrapositive. Assume n is odd, so n=2k+1 for some integer k. "
            "Then n^2=(2k+1)^2=2(2k^2+2k)+1, which is odd. Therefore if n^2 is even, n is even."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="proof by contrapositive",
            summary="Show that odd n implies odd n^2.",
            assumptions=["n is odd"],
            conclusions=["n^2 is odd"],
            components=[
                ChildProofSpec(
                    id_suffix="odd_square",
                    kind=ProofKind.simple,
                    text="If n=2k+1, then n^2=2(2k^2+2k)+1, so n^2 is odd.",
                    goal="n odd implies n^2 odd.",
                    hypotheses=["n is odd"],
                )
            ],
        ),
    ),
    ProofExample(
        slug="existence_even_prime",
        title="An Even Prime Exists",
        label="thm:even_prime_exists",
        statement="There exists a prime number that is even.",
        proof_kind=ProofKind.existence,
        proof_text="Take the witness 2. The number 2 is prime, and 2 is even.",
        structured_spec=StructuredProofRefinementSpec(
            strategy="construct a witness",
            summary="Use 2 as the witness.",
            claim="There exists a prime number that is even.",
            witness="2",
            components=[
                ChildProofSpec(
                    id_suffix="verify_witness",
                    kind=ProofKind.simple,
                    text="The witness 2 is prime and even.",
                    goal="2 is prime and even.",
                )
            ],
        ),
    ),
    ProofExample(
        slug="uniqueness_additive_identity",
        title="Uniqueness of Additive Identity",
        label="thm:additive_identity_unique",
        statement="In a group, the additive identity is unique.",
        proof_kind=ProofKind.uniqueness,
        proof_text=(
            "Suppose e and e' are both additive identities. Since e is an identity, e+e'=e'. "
            "Since e' is an identity, e+e'=e. Hence e=e'."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="prove uniqueness from two arbitrary candidates",
            summary="Compare two identities by evaluating e+e'.",
            assumptions=["e is an additive identity", "e' is an additive identity"],
            conclusions=["e=e'"],
            components=[
                ChildProofSpec(
                    id_suffix="compare_candidates",
                    kind=ProofKind.simple,
                    text="Both identity laws give e+e'=e' and e+e'=e, hence e=e'.",
                    goal="Any two additive identities are equal.",
                )
            ],
        ),
    ),
    ProofExample(
        slug="equivalence_even_square",
        title="Evenness Equivalent to Square Evenness",
        label="thm:even_iff_square_even",
        statement="For an integer n, n is even if and only if n^2 is even.",
        proof_kind=ProofKind.equivalence,
        proof_text=(
            "For the forward direction, if n=2k then n^2=2(2k^2), so n^2 is even. "
            "For the reverse direction, use the contrapositive: if n is odd, then n^2 is odd."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="prove both implications",
            summary="Split the iff into forward and reverse directions.",
            components=[
                ChildProofSpec(
                    id_suffix="forward",
                    kind=ProofKind.simple,
                    text="If n=2k then n^2=2(2k^2), so n^2 is even.",
                    goal="n even implies n^2 even.",
                ),
                ChildProofSpec(
                    id_suffix="reverse",
                    kind=ProofKind.contrapositive,
                    text="For the reverse direction, prove the contrapositive: odd n implies odd n^2.",
                    goal="n^2 even implies n even.",
                ),
            ],
        ),
    ),
    ProofExample(
        slug="generic_element_set_commutativity",
        title="Intersection is Commutative",
        label="thm:intersection_comm",
        statement="For sets A and B, A ∩ B = B ∩ A.",
        proof_kind=ProofKind.generic_element,
        proof_text=(
            "Take an arbitrary element x. If x belongs to A∩B, then x belongs to A and to B, "
            "so x belongs to B∩A. Conversely, if x belongs to B∩A, then x belongs to B and to A, "
            "so x belongs to A∩B."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="generic element and mutual inclusion",
            summary="Take arbitrary x and prove both memberships.",
            components=[
                ChildProofSpec(
                    id_suffix="left_to_right",
                    kind=ProofKind.simple,
                    text="For arbitrary x, x∈A∩B implies x∈B∩A.",
                    goal="A∩B ⊆ B∩A.",
                ),
                ChildProofSpec(
                    id_suffix="right_to_left",
                    kind=ProofKind.simple,
                    text="For arbitrary x, x∈B∩A implies x∈A∩B.",
                    goal="B∩A ⊆ A∩B.",
                ),
            ],
        ),
    ),
    ProofExample(
        slug="construction_polynomial_with_root",
        title="Constructing a Polynomial with a Prescribed Root",
        label="thm:polynomial_with_prescribed_root",
        statement="For every real number a, there exists a nonzero polynomial p such that p(a)=0.",
        proof_kind=ProofKind.construction,
        proof_text=(
            "Construct the polynomial p(x)=x-a. This polynomial is nonzero, and evaluating at "
            "x=a gives p(a)=a-a=0."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="explicit construction",
            summary="Use the linear polynomial x-a and verify the required properties.",
            claim="For every real number a, there exists a nonzero polynomial p such that p(a)=0.",
            construction="p(x)=x-a",
            components=[
                ChildProofSpec(
                    id_suffix="verify_nonzero",
                    kind=ProofKind.simple,
                    text="The polynomial p(x)=x-a is nonzero.",
                    goal="p is nonzero.",
                ),
                ChildProofSpec(
                    id_suffix="verify_root",
                    kind=ProofKind.calculation,
                    text="Evaluating at a gives p(a)=a-a=0.",
                    goal="p(a)=0.",
                ),
            ],
        ),
    ),
    ProofExample(
        slug="epsilon_delta_linear_limit",
        title="A Linear Epsilon-Delta Limit",
        label="thm:limit_two_x_at_three",
        statement="The function f(x)=2x has limit 6 as x tends to 3.",
        proof_kind=ProofKind.epsilon_delta,
        proof_text=(
            "Let epsilon>0 and choose delta=epsilon/2. If |x-3|<delta, then "
            "|2x-6|=2|x-3|<2delta=epsilon."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="epsilon-delta proof",
            summary="Given epsilon, choose delta=epsilon/2 and verify the bound.",
            assumptions=["epsilon > 0"],
            conclusions=["|2x-6| < epsilon"],
            bound_claim="If |x-3| < delta, then |2x-6| < epsilon.",
            metadata=[MetadataEntry(key="delta", value="epsilon/2")],
            components=[
                ChildProofSpec(
                    id_suffix="choose_delta",
                    kind=ProofKind.simple,
                    text="Given epsilon>0, choose delta=epsilon/2.",
                    goal="Choose a positive delta.",
                    hypotheses=["epsilon > 0"],
                ),
                ChildProofSpec(
                    id_suffix="verify_bound",
                    kind=ProofKind.calculation,
                    text="If |x-3|<delta, then |2x-6|=2|x-3|<2delta=epsilon.",
                    goal="|2x-6| < epsilon.",
                ),
            ],
        ),
    ),
    ProofExample(
        slug="invariant_parity_reachability",
        title="Parity Invariant Reachability",
        label="thm:cannot_reach_one_by_twos",
        statement="Starting from 0 and repeatedly adding or subtracting 2, one cannot reach 1.",
        proof_kind=ProofKind.invariant,
        proof_text=(
            "The invariant is parity. Starting from 0, the current number is even. Adding or "
            "subtracting 2 preserves parity, so every reachable number is even. Since 1 is odd, "
            "1 is not reachable."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="invariant argument",
            summary="Use parity as an invariant under moves by 2.",
            invariant="parity is even",
            components=[
                ChildProofSpec(
                    id_suffix="initial_invariant",
                    kind=ProofKind.simple,
                    text="The initial value 0 is even.",
                    goal="The invariant holds initially.",
                ),
                ChildProofSpec(
                    id_suffix="preservation",
                    kind=ProofKind.simple,
                    text="Adding or subtracting 2 preserves parity.",
                    goal="The invariant is preserved by every move.",
                ),
                ChildProofSpec(
                    id_suffix="exclude_target",
                    kind=ProofKind.simple,
                    text="The target 1 is odd, so it cannot satisfy the invariant.",
                    goal="1 is not reachable.",
                ),
            ],
        ),
    ),
    ProofExample(
        slug="reduction_bounded_on_interval",
        title="Boundedness by Reduction to Compactness",
        label="thm:continuous_bounded_interval",
        statement="Every continuous real-valued function on [0,1] is bounded.",
        proof_kind=ProofKind.reduction,
        proof_text=(
            "Reduce to the theorem that a continuous function on a compact space is bounded. "
            "The interval [0,1] is compact, so the given continuous function is bounded."
        ),
        structured_spec=StructuredProofRefinementSpec(
            strategy="reduction to a known compactness theorem",
            summary="Use compactness of [0,1] and the boundedness theorem for compact domains.",
            claim="Every continuous real-valued function on [0,1] is bounded.",
            reduced_to="A continuous function on a compact space is bounded.",
            proof_of_reduction=ChildProofSpec(
                id_suffix="proof_of_reduction",
                kind=ProofKind.simple,
                text="The interval [0,1] is compact, so the compact-domain theorem applies.",
                goal=(
                    "The claim reduces to the theorem that a continuous function on "
                    "a compact space is bounded."
                ),
            ),
            proof=ChildProofSpec(
                id_suffix="reduced_goal",
                kind=ProofKind.simple,
                text="Apply the theorem that continuous functions on compact spaces are bounded.",
                goal="A continuous function on a compact space is bounded.",
            ),
        ),
    ),
)

EXAMPLES_BY_SLUG = {example.slug: example for example in EXAMPLES}
EXAMPLES_BY_SOURCE = {example.source_text: example for example in EXAMPLES}


class DocumentParserAgent:
    def __call__(self, payload):
        source_text = payload["node"]["text"]
        example = EXAMPLES_BY_SOURCE[source_text]
        return DocumentRefinementSpec(
            children=[
                DocumentChildSpec(
                    id_suffix=example.slug,
                    kind=DocumentKind.theorem,
                    label=example.label,
                    text=example.source_text,
                    statement=example.statement,
                    proof_text=example.proof_text,
                )
            ]
        )


class ProofClassifierAgent:
    def __call__(self, payload):
        proof_text = payload["node"]["text"]
        for example in EXAMPLES:
            if example.proof_text == proof_text:
                return {
                    "kind": example.proof_kind,
                    "confidence": 0.99,
                    "notes": [f"Classified as {example.proof_kind.value} from proof-type example metadata."],
                }
        return {"kind": ProofKind.simple, "confidence": 0.5}


class StructuredAgent:
    def __call__(self, payload):
        proof_text = payload["node"]["text"]
        for example in EXAMPLES:
            if example.proof_text == proof_text:
                return example.structured_spec
        return StructuredProofRefinementSpec(
            strategy=f"structured {payload['proof_kind']} proof",
            unresolved_details=["No example metadata matched this proof text."],
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
        text = payload["node"]["text"]
        if "|2x-6|" in text:
            return CalculationRefinementSpec(
                calculation_kind="epsilon_delta_bound",
                steps=[
                    CalcStep(lhs="|2x-6|", relation=CalcRelation.eq, rhs="2|x-3|"),
                    CalcStep(lhs="2|x-3|", relation=CalcRelation.lt, rhs="2 delta"),
                    CalcStep(lhs="2 delta", relation=CalcRelation.eq, rhs="epsilon"),
                ],
            )
        if "p(a)=a-a=0" in text:
            return CalculationRefinementSpec(
                calculation_kind="equality_chain",
                steps=[
                    CalcStep(lhs="p(a)", relation=CalcRelation.eq, rhs="a-a"),
                    CalcStep(lhs="a-a", relation=CalcRelation.eq, rhs="0"),
                ],
            )
        return CalculationRefinementSpec(
            calculation_kind="unparsed_calculation",
            unresolved_details=["No calculation metadata matched this proof text."],
        )


def build_registries():
    document_registry = default_document_handler_registry(parser_agent=DocumentParserAgent())
    proof_registry = default_proof_handler_registry(
        classifier_agent=ProofClassifierAgent(),
        simple_agent=SimpleProofAgent(),
        calculation_agent=CalculationAgent(),
        structured_agent=StructuredAgent(),
    )
    return document_registry, proof_registry


async def build_example_json(example: ProofExample) -> str:
    document_registry, proof_registry = build_registries()
    document = document_from_text(
        example.source_text,
        id=example.slug,
        title=example.title,
    )
    refined = await refine_math_document(
        document,
        document_registry,
        proof_registry,
        document_iterations=5,
        proof_iterations=20,
    )
    return to_json(refined, indent=2)


async def write_all_examples(output_dir: Path | None = None) -> list[Path]:
    target_dir = output_dir or Path(__file__).with_name("proof_type_examples")
    target_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for example in EXAMPLES:
        source_path = target_dir / f"{example.slug}.md"
        json_path = target_dir / f"{example.slug}.json"
        source_path.write_text(example.source_text + "\n", encoding="utf-8")
        json_path.write_text(await build_example_json(example), encoding="utf-8")
        written.extend([source_path, json_path])
    return written


def main() -> None:
    for path in asyncio.run(write_all_examples()):
        print(path)


if __name__ == "__main__":
    main()
