from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from mathdoc_agent.examples.calculation_type_examples import EXAMPLES, write_all_examples
from mathdoc_agent.plugins.calculation_types import CORE_CALCULATION_SCHEMAS


def contains_key(value, key: str) -> bool:
    if isinstance(value, dict):
        return key in value or any(contains_key(item, key) for item in value.values())
    if isinstance(value, list):
        return any(contains_key(item, key) for item in value)
    return False


class CalculationTypeExampleTests(unittest.IsolatedAsyncioTestCase):
    async def test_examples_generate_core_calculation_json(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            output_dir = Path(tmp)
            written = await write_all_examples(output_dir)
            self.assertEqual(len(written), 2 * len(EXAMPLES))

            exported_types = set()
            for example in EXAMPLES:
                source_path = output_dir / f"{example.slug}.md"
                json_path = output_dir / f"{example.slug}.json"
                self.assertTrue(source_path.exists())
                self.assertTrue(json_path.exists())

                data = json.loads(json_path.read_text(encoding="utf-8"))
                self.assertFalse(contains_key(data, "kind"))
                theorem = data["document"]["body"][0]
                self.assertEqual(theorem["type"], "theorem")
                proof = theorem["proof"]
                self.assertEqual(proof["type"], example.calculation_kind)
                self.assertIn("steps", proof)
                self.assertTrue(proof["steps"])
                self.assertIn("from", proof["steps"][0])
                self.assertIn("relation", proof["steps"][0])
                self.assertIn("to", proof["steps"][0])
                exported_types.add(proof["type"])

            self.assertEqual(exported_types, CORE_CALCULATION_SCHEMAS)

    def test_saved_example_outputs_exist(self) -> None:
        output_dir = Path("mathdoc_agent/examples/calculation_type_examples")
        for example in EXAMPLES:
            self.assertTrue((output_dir / f"{example.slug}.md").exists())
            self.assertTrue((output_dir / f"{example.slug}.json").exists())


if __name__ == "__main__":
    unittest.main()
