from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from mathdoc_agent.examples.proof_type_examples import EXAMPLES, write_all_examples
from mathdoc_agent.export.json import to_json
from mathdoc_agent.models.base import NodeStatus, ProofKind
from mathdoc_agent.models.payloads import StructuredProofData
from mathdoc_agent.models.proof import ProofNode, ProofTree


EXPECTED_PROOF_TYPES = {
    ProofKind.contradiction: "contradiction_statement",
    ProofKind.contrapositive: "proof",
    ProofKind.existence: "existence_proof",
    ProofKind.uniqueness: "uniqueness_proof",
    ProofKind.equivalence: "bi-implication_cases_proof",
    ProofKind.generic_element: "proof",
    ProofKind.construction: "construction_proof",
    ProofKind.epsilon_delta: "epsilon_delta_proof",
    ProofKind.invariant: "proof",
    ProofKind.reduction: "reduction_proof",
}

PRIORITY_PROOF_KINDS = {
    ProofKind.contrapositive,
    ProofKind.existence,
    ProofKind.generic_element,
    ProofKind.epsilon_delta,
    ProofKind.uniqueness,
    ProofKind.construction,
    ProofKind.invariant,
    ProofKind.reduction,
}


def contains_key(value, key: str) -> bool:
    if isinstance(value, dict):
        return key in value or any(contains_key(item, key) for item in value.values())
    if isinstance(value, list):
        return any(contains_key(item, key) for item in value)
    return False


class ProofTypeExampleTests(unittest.IsolatedAsyncioTestCase):
    async def test_examples_generate_paper_structure_json(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            output_dir = Path(tmp)
            written = await write_all_examples(output_dir)
            self.assertEqual(len(written), 2 * len(EXAMPLES))

            for example in EXAMPLES:
                source_path = output_dir / f"{example.slug}.md"
                json_path = output_dir / f"{example.slug}.json"
                self.assertTrue(source_path.exists())
                self.assertTrue(json_path.exists())

                data = json.loads(json_path.read_text(encoding="utf-8"))
                self.assertFalse(contains_key(data, "kind"))
                self.assertEqual(set(data.keys()), {"document"})
                self.assertEqual(data["document"]["type"], "document")
                theorem = data["document"]["body"][0]
                self.assertEqual(theorem["type"], "theorem")
                self.assertIn("claim", theorem)
                self.assertNotIn("root", data)
                self.assertNotIn("run_log", data)
                proof_root = theorem["proof"]
                self.assertEqual(proof_root["type"], EXPECTED_PROOF_TYPES[example.proof_kind])
                self.assertEqual(proof_root["status"], "resolved")
                if proof_root["type"] == "proof":
                    self.assertIn("proof_steps", proof_root)
                if proof_root["type"] == "contradiction_statement":
                    self.assertEqual(proof_root["proof"]["type"], "proof")
                    self.assertIn("proof_steps", proof_root["proof"])
                if proof_root["type"] == "multi-condition_cases_proof":
                    self.assertNotIn("exhaustiveness", proof_root)
                if proof_root["type"] == "reduction_proof":
                    self.assertIn("claim", proof_root)
                    self.assertIn("proof_of_reduction", proof_root)
                    self.assertIn("proof", proof_root)
                if proof_root["type"] == "uniqueness_proof":
                    self.assertIn("uniqueness_proof", proof_root)
                    self.assertIn("claim", proof_root)
                if proof_root["type"] == "existence_proof":
                    self.assertIn("full_claim", proof_root)
                    self.assertIn("variable_name", proof_root)
                    self.assertIn("claim", proof_root)
                    self.assertIn("witness", proof_root)
                    self.assertIn("proof", proof_root)
                if proof_root["type"] == "epsilon_delta_proof":
                    self.assertIn("bound_claim", proof_root)
                    self.assertIn("bound_proof", proof_root)
                if proof_root["type"] == "construction_proof":
                    self.assertIn("full_claim", proof_root)
                    self.assertIn("variable_name", proof_root)
                    self.assertIn("claim", proof_root)
                    self.assertIn("construction", proof_root)
                    self.assertIn("verification", proof_root)

    def test_priority_proof_kinds_have_examples(self) -> None:
        present = {example.proof_kind for example in EXAMPLES}
        self.assertLessEqual(PRIORITY_PROOF_KINDS, present)

    def test_saved_example_outputs_exist(self) -> None:
        output_dir = Path("mathdoc_agent/examples/proof_type_examples")
        for example in EXAMPLES:
            self.assertTrue((output_dir / f"{example.slug}.md").exists())
            self.assertTrue((output_dir / f"{example.slug}.json").exists())

    def test_existence_proof_exports_full_claim_and_property_claim(self) -> None:
        root = ProofNode(
            id="existence.root",
            kind=ProofKind.existence,
            status=NodeStatus.resolved,
            text="Take 2 as the witness and verify it has property P.",
            goal="There exists a number n with property P.",
            data=StructuredProofData(
                claim="There exists a number n with property P.",
                witness="2",
            ).model_dump(),
            children=[
                ProofNode(
                    id="existence.root.verify",
                    kind=ProofKind.simple,
                    status=NodeStatus.resolved,
                    text="The witness 2 has property P.",
                    goal="2 has property P.",
                )
            ],
        )
        exported = json.loads(to_json(ProofTree(id="existence", root=root)))
        self.assertEqual(exported["type"], "existence_proof")
        self.assertEqual(exported["full_claim"], "There exists a number n with property P.")
        self.assertEqual(exported["variable_name"], "n")
        self.assertEqual(exported["claim"], "n is a number with property P.")
        self.assertEqual(exported["witness"], "2")
        self.assertIn("proof", exported)

    def test_construction_proof_exports_required_claim(self) -> None:
        root = ProofNode(
            id="construction.root",
            kind=ProofKind.construction,
            status=NodeStatus.resolved,
            text="Construct a function f and verify it is continuous.",
            goal="There exists a continuous function f with property P.",
            data=StructuredProofData(
                claim="There exists a continuous function f with property P.",
                construction="the function f",
            ).model_dump(),
            children=[
                ProofNode(
                    id="construction.root.verify",
                    kind=ProofKind.simple,
                    status=NodeStatus.resolved,
                    text="The constructed function is continuous and has property P.",
                    goal="f is continuous and has property P.",
                )
            ],
        )
        exported = json.loads(to_json(ProofTree(id="construction", root=root)))
        self.assertEqual(exported["type"], "construction_proof")
        self.assertEqual(exported["full_claim"], "There exists a continuous function f with property P.")
        self.assertEqual(exported["variable_name"], "f")
        self.assertEqual(exported["claim"], "f is a continuous function with property P.")
        self.assertEqual(exported["construction"], "the function f")
        self.assertIn("verification", exported)


if __name__ == "__main__":
    unittest.main()
