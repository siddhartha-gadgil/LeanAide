from __future__ import annotations

import unittest

from mathdoc_agent.models.base import DocumentKind, NodeStatus
from mathdoc_agent.models.document import DocumentNode, MathDocument
from mathdoc_agent.models.payloads import DefinitionData
from mathdoc_agent.models.refinement_specs import (
    CalculationAuditPatchSpec,
    CalculationAuditSpec,
    ClaimAuditSpec,
    ClaimPatchSpec,
    DocumentChildSpec,
    MetadataEntry,
    SourceCoverageAuditSpec,
    SourceCoveragePatchSpec,
)
from mathdoc_agent.orchestration.calculation_audit import (
    audit_calculations_for_lean,
    calculation_audit_entries,
)
from mathdoc_agent.orchestration.claim_audit import rewrite_informal_claims_for_lean
from mathdoc_agent.orchestration.source_coverage import (
    audit_source_coverage,
    source_coverage_entries,
)


class SourceCoverageAgent:
    def __init__(self) -> None:
        self.payloads: list[dict] = []

    def __call__(self, payload):
        self.payloads.append(payload)
        return SourceCoverageAuditSpec(
            patches=[
                SourceCoveragePatchSpec(
                    action="insert_child",
                    after_id="doc.root.title",
                    source_block_ids=["source-block-2"],
                    child=DocumentChildSpec(
                        id_suffix="motivation",
                        kind=DocumentKind.paragraph,
                        text=(
                            "This introductory paragraph states why the construction "
                            "matters."
                        ),
                    ),
                ),
                SourceCoveragePatchSpec(
                    action="replace_child",
                    target_id="doc.root.definition",
                    source_block_ids=["source-block-3"],
                    child=DocumentChildSpec(
                        id_suffix="definition",
                        kind=DocumentKind.definition,
                        text=(
                            "**Definition.** A pair is admissible precisely when both "
                            "equations hold:\n1. x + y = 0.\n2. x - y = 1."
                        ),
                        data_entries=[
                            MetadataEntry(
                                key="definition",
                                value=(
                                    "A pair is admissible precisely when both equations "
                                    "hold: 1. x + y = 0. 2. x - y = 1."
                                ),
                            )
                        ],
                    ),
                ),
            ]
        )


class InformalClaimAgent:
    def __init__(self) -> None:
        self.payloads: list[dict] = []

    def __call__(self, payload):
        self.payloads.append(payload)
        entry = payload["claim_entries"][0]
        return ClaimAuditSpec(
            patches=[
                ClaimPatchSpec(
                    path=entry["path"],
                    action="replace_claim",
                    claim="∀ (n : Nat), n ≤ n",
                )
            ]
        )


class CalculationRepairAgent:
    def __init__(self) -> None:
        self.payloads: list[dict] = []

    def __call__(self, payload):
        self.payloads.append(payload)
        entry = payload["calculation_entries"][0]
        return CalculationAuditSpec(
            patches=[
                CalculationAuditPatchSpec(
                    path=entry["path"],
                    string_patches=[
                        {
                            "path": f'{entry["path"]}/proof_steps/1/from',
                            "replacement": "b",
                        }
                    ],
                    conclusion={
                        "claim": "a ≤ c",
                        "proof_method": "By the two preceding steps and transitivity.",
                        "start": "a",
                        "relation": "≤",
                        "target": "c",
                    },
                )
            ]
        )


class QualityPassTests(unittest.IsolatedAsyncioTestCase):
    def test_definition_metadata_accepts_canonical_and_legacy_keys(self) -> None:
        for key in ("definitions", "definition", "definiens"):
            with self.subTest(key=key):
                data = DefinitionData.model_validate({key: "P x iff Q x"})
                self.assertEqual(data.definitions, "P x iff Q x")

    async def test_source_coverage_restores_omitted_and_truncated_blocks(self) -> None:
        source = (
            "# Demo\n\n"
            "This introductory paragraph states why the construction matters.\n\n"
            "**Definition.** A pair is admissible precisely when both equations hold:\n"
            "1. x + y = 0.\n"
            "2. x - y = 1.\n"
        )
        document = MathDocument(
            id="doc",
            root=DocumentNode(
                id="doc.root",
                kind=DocumentKind.document,
                status=NodeStatus.decomposed,
                text=source,
                children=[
                    DocumentNode(
                        id="doc.root.title",
                        kind=DocumentKind.section,
                        status=NodeStatus.classified,
                        # Section export keeps its heading, not incidental prose
                        # retained in the parser node's raw text.
                        text=(
                            "# Demo\n\nThis introductory paragraph states why the "
                            "construction matters."
                        ),
                    ),
                    DocumentNode(
                        id="doc.root.definition",
                        kind=DocumentKind.definition,
                        status=NodeStatus.classified,
                        # Retaining the source verbatim must not hide that the
                        # structured definition omitted its two equations.
                        text=(
                            "**Definition.** A pair is admissible precisely when both "
                            "equations hold:\n1. x + y = 0.\n2. x - y = 1."
                        ),
                        data={
                            "term": "admissible pair",
                            "definiens": "a pair satisfying the listed conditions",
                        },
                    ),
                ],
            ),
        )
        self.assertGreaterEqual(len(source_coverage_entries(document, source)), 2)
        agent = SourceCoverageAgent()

        repaired = await audit_source_coverage(document, source, agent)

        self.assertEqual(len(agent.payloads), 1)
        self.assertEqual(
            [child.id for child in repaired.root.children],
            ["doc.root.title", "doc.root.motivation", "doc.root.definition"],
        )
        self.assertIn("x - y = 1", repaired.root.children[-1].text)
        self.assertEqual(source_coverage_entries(repaired, source), [])

    async def test_informal_theorem_claim_is_mandatorily_rewritten_as_prop(self) -> None:
        agent = InformalClaimAgent()
        data = {
            "document": {
                "body": [
                    {
                        "type": "theorem",
                        "claim": "For every natural number n, n is at most itself.",
                    }
                ]
            }
        }

        repaired = await rewrite_informal_claims_for_lean(data, agent)

        self.assertEqual(
            repaired["document"]["body"][0]["claim"],
            "∀ (n : Nat), n ≤ n",
        )
        self.assertNotIn("lean_validation", repaired["document"])
        self.assertEqual(len(agent.payloads), 1)

    async def test_unrepaired_informal_claim_is_marked_for_review(self) -> None:
        data = {
            "document": {
                "body": [
                    {
                        "type": "theorem",
                        "claim": "There exists a natural number.",
                    }
                ]
            }
        }

        repaired = await rewrite_informal_claims_for_lean(data, None)

        issues = repaired["document"]["lean_validation"]["issues"]
        self.assertEqual(issues[0]["code"], "informal_theorem_claim")

    async def test_symbolic_theorem_claim_with_prose_hypotheses_is_reclosed(self) -> None:
        data = {
            "document": {
                "body": [
                    {
                        "type": "theorem",
                        "claim": "l(a) <= (l(y) + l(z)) / 2",
                        "hypothesis": [
                            {"type": "assume_statement", "assumption": "G is a group."},
                            {
                                "type": "assume_statement",
                                "assumption": "a,y,z are elements of G.",
                            },
                        ],
                        "source": {
                            "text": "Let G be a group and a,y,z in G. Then l(a) <= (l(y)+l(z))/2."
                        },
                    }
                ]
            }
        }
        agent = InformalClaimAgent()

        repaired = await rewrite_informal_claims_for_lean(data, agent)

        self.assertEqual(
            repaired["document"]["body"][0]["claim"],
            "∀ (n : Nat), n ≤ n",
        )
        risks = agent.payloads[0]["claim_entries"][0]["closure_risks"]
        self.assertTrue(any("ambient hypotheses" in risk for risk in risks))

    async def test_calculation_audit_adds_an_explicit_terminal_conclusion(self) -> None:
        data = {
            "document": {
                "body": [
                    {
                        "type": "theorem",
                        "claim": "a ≤ c",
                        "proof": {
                            "type": "proof",
                            "claim_label": "a ≤ c",
                            "calculation_kind": "inequality_chain",
                            "start": "a",
                            "target": "c",
                            "proof_steps": [
                                {"type": "assert_statement", "from": "a", "relation": "=", "to": "b"},
                                {"type": "assert_statement", "from": "b", "relation": "≤", "to": "c"},
                            ],
                        },
                    }
                ]
            }
        }

        repaired = await audit_calculations_for_lean(data, None)

        proof = repaired["document"]["body"][0]["proof"]
        self.assertTrue(proof["proof_steps"][-1]["calculation_conclusion"])
        self.assertEqual(proof["proof_steps"][-1]["claim"], "a ≤ c")
        self.assertEqual(calculation_audit_entries(repaired), [])

    async def test_calculation_audit_repairs_only_agent_confirmed_endpoint_gap(self) -> None:
        data = {
            "document": {
                "body": [
                    {
                        "type": "theorem",
                        "claim": "a ≤ c",
                        "proof": {
                            "type": "proof",
                            "claim_label": "a ≤ c",
                            "calculation_kind": "inequality_chain",
                            "start": "a",
                            "target": "c",
                            "proof_steps": [
                                {"type": "assert_statement", "from": "a", "relation": "=", "to": "b"},
                                {
                                    "type": "assert_statement",
                                    "from": "the quantity b from the previous line",
                                    "relation": "≤",
                                    "to": "c",
                                },
                            ],
                        },
                    }
                ]
            }
        }
        agent = CalculationRepairAgent()

        repaired = await audit_calculations_for_lean(data, agent)

        proof = repaired["document"]["body"][0]["proof"]
        self.assertEqual(proof["proof_steps"][1]["from"], "b")
        self.assertEqual(calculation_audit_entries(repaired), [])
        self.assertEqual(len(agent.payloads), 1)

    async def test_calculation_audit_keeps_auxiliary_equation_outside_main_chain(self) -> None:
        proof = {
            "type": "proof",
            "claim_label": "l(C_{n+1}) ≤ bound",
            "calculation_kind": "inequality_chain",
            # The calculation refiner initially chose the auxiliary group-valued
            # identity as its start, although the overall claim is real-valued.
            "start": "C_{n+1}",
            "target": "bound",
            "proof_steps": [
                {
                    "type": "assert_statement",
                    "from": "C applied to n + 1",
                    "relation": "=",
                    "to": "w * inner * w inverse",
                },
                {
                    "type": "assert_statement",
                    "from": "l applied to (C applied to n + 1)",
                    "relation": "=",
                    "to": "l(inner)",
                },
                {
                    "type": "assert_statement",
                    "from": "l(inner)",
                    "relation": "<=",
                    "to": "bound",
                },
            ],
        }
        data = {"document": {"body": [{"type": "theorem", "proof": proof}]}}

        repaired = await audit_calculations_for_lean(data, None)
        repaired_twice = await audit_calculations_for_lean(repaired, None)

        result = repaired_twice["document"]["body"][0]["proof"]
        self.assertEqual(result["start"], "l(C_{n+1})")
        self.assertEqual(calculation_audit_entries(repaired_twice), [])
        conclusions = [
            step
            for step in result["proof_steps"]
            if step.get("calculation_conclusion") is True
        ]
        self.assertEqual(len(conclusions), 1)
        self.assertEqual(conclusions[0]["claim"], "l(C_{n+1}) ≤ bound")

    async def test_calculation_audit_marks_existing_dag_conclusion(self) -> None:
        proof = {
            "type": "proof",
            "claim_label": "l(C_{n+1}) ≤ bound",
            "calculation_kind": "inequality_with_substitution",
            "start": "C_{n+1}",
            "target": "bound",
            "proof_steps": [
                {
                    "type": "assert_statement",
                    "claim": "l(C_{n+1}) = l(inner)",
                    "proof_method": "By conjugation invariance.",
                    "from": "l(C_{n+1})",
                    "relation": "=",
                    "to": "l(inner)",
                },
                {
                    "type": "assert_statement",
                    "claim": "l(C_n) ≤ previousBound",
                    "proof_method": "By the induction hypothesis.",
                    "from": "l(C_n)",
                    "relation": "<=",
                    "to": "previousBound",
                },
                {
                    "type": "assert_statement",
                    "claim": "l(C_{n+1}) ≤ bound",
                    "proof_method": (
                        "Combine the preceding estimate with the induction "
                        "hypothesis and simplify."
                    ),
                    "from": "l applied to C applied to n + 1",
                    "relation": "<=",
                    "to": "bound",
                },
            ],
        }
        data = {"document": {"body": [{"type": "theorem", "proof": proof}]}}

        repaired = await audit_calculations_for_lean(data, None)

        result = repaired["document"]["body"][0]["proof"]
        conclusions = [
            step
            for step in result["proof_steps"]
            if step.get("calculation_conclusion") is True
        ]
        self.assertEqual(len(conclusions), 1)
        self.assertEqual(conclusions[0]["proof_method"], proof["proof_steps"][2]["proof_method"])
        self.assertEqual(calculation_audit_entries(repaired), [])


if __name__ == "__main__":
    unittest.main()
