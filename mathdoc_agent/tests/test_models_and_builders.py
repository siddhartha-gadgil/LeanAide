from __future__ import annotations

import unittest
import json

from mathdoc_agent.builders.document_builder import DocumentBuilder
from mathdoc_agent.builders.proof_builder import ProofBuilder
from mathdoc_agent.export.json import to_json
from mathdoc_agent.models.base import DocumentKind, NodeStatus, ProofKind
from mathdoc_agent.models.document import DocumentNode
from mathdoc_agent.models.payloads import (
    CalcRelation,
    CalcStep,
    ConstructorArgumentData,
    DeducedFromTheoremData,
    InductionData,
    InductiveConstructorData,
    InstanceGiveData,
    LogicalProofStepData,
    ParameterData,
    SimpleProofData,
    SpecializeData,
    StructureFieldData,
)
from mathdoc_agent.models.proof import ProofNode, ProofTree
from mathdoc_agent.plugins.calculation_types import CORE_CALCULATION_SCHEMAS
from mathdoc_agent.registries.proof_registry import proof_payload_registry


class ModelAndBuilderTests(unittest.TestCase):
    def test_proof_node_json_round_trip(self) -> None:
        node = ProofBuilder.simple(
            id="p.root",
            text="The result follows from L.",
            hints=["use L"],
        )
        tree = ProofTree(id="p", theorem_statement="P", root=node)
        round_trip = ProofTree.model_validate_json(tree.model_dump_json())
        self.assertEqual(round_trip.root.id, "p.root")
        self.assertEqual(round_trip.root.status, NodeStatus.resolved)

    def test_assert_statement_dependencies_export(self) -> None:
        node = ProofNode(
            id="p.root",
            kind=ProofKind.simple,
            text="Therefore b is nonnegative.",
            data=SimpleProofData(
                proof_steps=[
                    LogicalProofStepData(
                        type="assert_statement",
                        claim="b ≥ 0",
                        proof_method="apply monotonicity",
                        deduced_from_claim=["a ≥ 0 and a ≤ b"],
                        deduced_from_theorem=[
                            DeducedFromTheoremData(
                                name="order transitivity",
                                claim="If x ≤ y and 0 ≤ x, then 0 ≤ y.",
                                lean_name="le_trans",
                                lean_term="(le_trans h0a hab)",
                            )
                        ],
                    )
                ]
            ).model_dump(),
        )
        exported = json.loads(to_json(ProofTree(id="p", theorem_statement="b ≥ 0", root=node)))
        self.assertEqual(exported["type"], "proof")
        step = exported["proof_steps"][0]
        self.assertEqual(step["type"], "assert_statement")
        self.assertEqual(step["deduced_from_claim"], ["a ≥ 0 and a ≤ b"])
        self.assertEqual(step["deduced_from_theorem"][0]["name"], "order transitivity")
        self.assertEqual(step["deduced_from_theorem"][0]["lean_name"], "le_trans")
        self.assertEqual(step["deduced_from_theorem"][0]["lean_term"], "(le_trans h0a hab)")
        self.assertNotIn("results_used", step)

    def test_single_assertion_simple_proof_dependencies_export(self) -> None:
        node = ProofBuilder.simple(
            id="p.root",
            text="The result follows by convexity.",
            goal="f is unbounded above",
            method="convexity argument",
            deduced_from_claim=["f''(x) > 0 for all x ∈ ℝ"],
            deduced_from_theorem=[
                DeducedFromTheoremData(
                    name="convexity from positive second derivative",
                    claim="If f'' is positive on an interval, then f is strictly convex there.",
                )
            ],
        )
        exported = json.loads(to_json(ProofTree(id="p", theorem_statement="f is unbounded above", root=node)))
        self.assertEqual(exported["type"], "assert_statement")
        self.assertEqual(exported["deduced_from_claim"], ["f''(x) > 0 for all x ∈ ℝ"])
        self.assertEqual(
            exported["deduced_from_theorem"][0]["claim"],
            "If f'' is positive on an interval, then f is strictly convex there.",
        )

    def test_document_node_with_proof_round_trip(self) -> None:
        node = DocumentBuilder.theorem_like(
            id="doc.thm1",
            kind=DocumentKind.theorem,
            text="Theorem. P. Proof. Trivial.",
            statement="P",
            proof_text="Trivial.",
            label="thm:p",
        )
        round_trip = DocumentNode.model_validate_json(node.model_dump_json())
        self.assertIsNotNone(round_trip.proof)
        self.assertEqual(round_trip.proof.root.kind, ProofKind.unknown)
        dumped = round_trip.model_dump()
        self.assertEqual(dumped["type"], "theorem")
        self.assertEqual(dumped["proof"]["type"], "proof_details")
        self.assertEqual(dumped["proof"]["root"]["type"], "proof")
        exported = json.loads(to_json(round_trip))
        self.assertEqual(exported["type"], "theorem")
        self.assertEqual(exported["claim"], "P")
        self.assertNotIn("kind", exported)
        self.assertNotIn("kind", exported["proof"])
        self.assertNotIn("theorem_statement", exported["proof"])

    def test_payload_registry_validates_known_and_ignores_unknown(self) -> None:
        data = proof_payload_registry.validate_data(
            ProofKind.induction,
            {"variable": "n", "base_case_ids": ["b"], "step_case_ids": ["s"]},
        )
        self.assertIsInstance(data, InductionData)
        specialized = proof_payload_registry.validate_data(
            ProofKind.specialize,
            {
                "name": "h_at_x",
                "lean_term": "(h x hx)",
                "claim": "P x",
                "source_claim": "For every y satisfying H y, P y.",
                "arguments": ["x", "hx"],
            },
        )
        self.assertIsInstance(specialized, SpecializeData)
        self.assertIsNone(proof_payload_registry.validate_data("custom_kind", {}))

    def test_specialize_proof_exports_named_have_instance(self) -> None:
        node = ProofBuilder.specialize(
            id="p.specialize",
            text="Specialize h to x.",
            name="h_at_x",
            lean_term="(h x hx)",
            claim="P x",
            source_claim="For every y satisfying H y, P y.",
            arguments=["x", "hx"],
        )
        exported = json.loads(to_json(ProofTree(id="p", theorem_statement="P x", root=node)))
        self.assertEqual(exported["type"], "assert_statement")
        self.assertEqual(exported["name"], "h_at_x")
        self.assertEqual(exported["lean_term"], "(h x hx)")
        self.assertEqual(exported["claim"], "P x")
        self.assertEqual(exported["source_claim"], "For every y satisfying H y, P y.")
        self.assertEqual(exported["arguments"], ["x", "hx"])

    def test_builders_create_expected_payloads(self) -> None:
        base = ProofNode(id="p.base", kind=ProofKind.simple, text="base")
        step = ProofNode(id="p.step", kind=ProofKind.simple, text="step")
        induction = ProofBuilder.induction(
            id="p",
            text="induct on n",
            variable="n",
            base_cases=[base],
            step_cases=[step],
        )
        data = InductionData.model_validate(induction.data)
        self.assertEqual(data.base_case_ids, ["p.base"])
        self.assertEqual(data.step_case_ids, ["p.step"])

        calc = ProofBuilder.calculation(
            id="c",
            text="a = b = c",
            steps=[
                CalcStep(lhs="a", relation=CalcRelation.eq, rhs="b"),
                CalcStep(lhs="b", relation=CalcRelation.eq, rhs="c"),
            ],
        )
        self.assertEqual(calc.data["start"], "a")
        self.assertEqual(calc.data["target"], "c")
        self.assertEqual(calc.model_dump()["type"], "calculation")

        calc_json = json.loads(to_json(ProofTree(id="calc", theorem_statement="a = c", root=calc)))
        self.assertEqual(calc_json["type"], "proof")
        self.assertEqual(calc_json["proof_steps"][0]["type"], "assert_statement")
        self.assertEqual(calc_json["proof_steps"][0]["claim"], "a = b")

        core_calc = ProofBuilder.calculation(
            id="core",
            text="a = b = c",
            calculation_kind="equality_chain",
            steps=[
                CalcStep(
                    lhs="a",
                    relation=CalcRelation.eq,
                    rhs="b",
                    justification="h1",
                    deduced_from_claim=["a = b follows from the local hypothesis h1"],
                    deduced_from_theorem=[
                        DeducedFromTheoremData(
                            name="substitution",
                            claim="Equal terms may be substituted in any expression.",
                        )
                    ],
                ),
                CalcStep(lhs="b", relation=CalcRelation.eq, rhs="c", justification="h2"),
            ],
        )
        core_json = json.loads(to_json(ProofTree(id="core", theorem_statement="a = c", root=core_calc)))
        self.assertEqual(core_json["type"], "proof")
        self.assertEqual(core_json["calculation_kind"], "equality_chain")
        self.assertEqual(core_json["goal_relation"], "=")
        self.assertEqual(core_json["proof_steps"][0]["type"], "assert_statement")
        self.assertEqual(core_json["proof_steps"][0]["claim"], "a = b")
        self.assertEqual(core_json["proof_steps"][0]["from"], "a")
        self.assertEqual(core_json["proof_steps"][0]["to"], "b")
        self.assertEqual(
            core_json["proof_steps"][0]["deduced_from_claim"],
            ["a = b follows from the local hypothesis h1"],
        )
        self.assertEqual(
            core_json["proof_steps"][0]["deduced_from_theorem"][0]["claim"],
            "Equal terms may be substituted in any expression.",
        )

        for calculation_kind in CORE_CALCULATION_SCHEMAS:
            root = ProofBuilder.calculation(
                id=calculation_kind,
                text="a = b",
                calculation_kind=calculation_kind,
                steps=[CalcStep(lhs="a", relation=CalcRelation.eq, rhs="b")],
            )
            exported = json.loads(to_json(ProofTree(id=calculation_kind, theorem_statement="a = b", root=root)))
            self.assertEqual(exported["type"], "proof")
            self.assertEqual(exported["calculation_kind"], calculation_kind)
            self.assertEqual(exported["proof_steps"][0]["type"], "assert_statement")
            self.assertEqual(exported["proof_steps"][0]["from"], "a")

    def test_definition_builders_create_lean_definition_payloads(self) -> None:
        structure = DocumentBuilder.structure_definition(
            id="doc.group",
            text="A group has multiplication, identity and inverses.",
            name="Group",
            is_class=True,
            is_prop=False,
            parameters=[ParameterData(name="G", type="Type", binder="implicit")],
            fields=[StructureFieldData(name="mul", type="G -> G -> G")],
        )
        self.assertEqual(structure.kind, DocumentKind.structure_definition)
        self.assertEqual(structure.model_dump()["type"], "structure-definition")
        self.assertTrue(structure.data["is_class"])
        self.assertEqual(structure.data["parameters"][0]["binder"], "implicit")
        self.assertFalse(structure.data["is_prop"])

        instance = DocumentBuilder.instance_definition(
            id="doc.int_group",
            text="The integers form a group under addition.",
            class_name="Group",
            target="Int",
            gives=[InstanceGiveData(name="mul", value="Int.add")],
        )
        self.assertEqual(instance.kind, DocumentKind.instance_definition)
        self.assertEqual(instance.model_dump()["type"], "instance-definition")
        self.assertEqual(instance.data["class_name"], "Group")
        self.assertEqual(instance.data["gives"][0]["value"], "Int.add")

        inductive = DocumentBuilder.inductive_type_definition(
            id="doc.even",
            text="Even is generated by zero and adding two.",
            name="Even",
            is_prop=True,
            indices=[ParameterData(name="n", type="Nat")],
            constructors=[
                InductiveConstructorData(name="zero", arguments=[]),
                InductiveConstructorData(
                    name="step",
                    arguments=[ConstructorArgumentData(name="h", type="Even n")],
                    index_args=["n + 2"],
                ),
            ],
        )
        self.assertEqual(inductive.kind, DocumentKind.inductive_type_definition)
        self.assertEqual(inductive.model_dump()["type"], "inductive-type-definition")
        self.assertTrue(inductive.data["is_prop"])
        self.assertEqual(inductive.data["indices"][0]["name"], "n")
        self.assertEqual(inductive.data["constructors"][1]["arguments"][0]["name"], "h")
        self.assertEqual(inductive.data["constructors"][1]["arguments"][0]["type"], "Even n")
        self.assertEqual(inductive.data["constructors"][1]["arguments"][0]["binder"], "default")
        self.assertEqual(inductive.data["constructors"][1]["index_args"], ["n + 2"])

    def test_inductive_constructor_accepts_legacy_string_arguments(self) -> None:
        constructor = InductiveConstructorData(name="step", arguments=["n : Nat", "h : Even n"])
        dumped = constructor.model_dump()
        self.assertEqual(
            dumped["arguments"],
            [
                {"name": "n", "type": "Nat", "binder": "default"},
                {"name": "h", "type": "Even n", "binder": "default"},
            ],
        )

    def test_inductive_constructor_arguments_accept_binders(self) -> None:
        constructor = InductiveConstructorData(
            name="step",
            arguments=[
                {"name": "α", "type": "Type", "binder": "implicit"},
                {"name": "inst", "type": "Inhabited α", "binder": "typeclass"},
                {"name": "x", "type": "α"},
            ],
        )
        dumped = constructor.model_dump()
        self.assertEqual(dumped["arguments"][0]["binder"], "implicit")
        self.assertEqual(dumped["arguments"][1]["binder"], "typeclass")
        self.assertEqual(dumped["arguments"][2]["binder"], "default")


if __name__ == "__main__":
    unittest.main()
