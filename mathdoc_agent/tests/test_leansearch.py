from __future__ import annotations

import json
import unittest
import asyncio
from unittest.mock import Mock, patch

from mathdoc_agent.mathagents.leansearch import (
    LeanSearchError,
    LeanSearchResult,
    leansearch_command,
    leansearch_payload,
    lookup_theorems,
    normalize_leansearch_query,
    parse_leansearch_response,
)
from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.payloads import (
    DeducedFromTheoremData,
    LogicalProofStepData,
)
from mathdoc_agent.models.refinement_specs import SimpleProofRefinementSpec


class LeanSearchHelperTests(unittest.TestCase):
    def test_normalize_query_matches_leansearch_sentence_requirement(self) -> None:
        self.assertEqual(
            normalize_leansearch_query("  natural number less than successor  "),
            "natural number less than successor.",
        )
        self.assertEqual(
            normalize_leansearch_query("Which theorem proves Nat.succ_le_succ?"),
            "Which theorem proves Nat.succ_le_succ?",
        )

    def test_leansearch_command_uses_quoted_normalized_string(self) -> None:
        self.assertEqual(
            leansearch_command('If "n < m", then successor n is less than successor m'),
            '#leansearch "If \\"n < m\\", then successor n is less than successor m."',
        )

    def test_payload_matches_leansearch_client_shape(self) -> None:
        self.assertEqual(
            leansearch_payload("If n < m then Nat.succ n < Nat.succ m", 4),
            {
                "query": ["If n < m then Nat.succ n < Nat.succ m."],
                "num_results": 4,
            },
        )

    def test_parse_leansearch_response_extracts_result_fields(self) -> None:
        parsed = parse_leansearch_response(
            [
                [
                    {
                        "result": {
                            "name": ["Nat", "succ_lt_succ"],
                            "type": "n < m → n + 1 < m + 1",
                            "docstring": "",
                            "doc_url": "https://example.test/doc",
                            "kind": "theorem",
                        }
                    }
                ]
            ]
        )

        self.assertEqual(
            parsed,
            [
                LeanSearchResult(
                    name="Nat.succ_lt_succ",
                    type="n < m → n + 1 < m + 1",
                    docstring=None,
                    doc_url="https://example.test/doc",
                    kind="theorem",
                )
            ],
        )
        self.assertEqual(parsed[0].as_check_command(), "#check Nat.succ_lt_succ")

    def test_lookup_theorems_posts_to_leansearch(self) -> None:
        response = Mock()
        response.read.return_value = json.dumps(
            [
                [
                    {
                        "result": {
                            "name": ["Nat", "succ_le_succ"],
                            "type": "n ≤ m → n + 1 ≤ m + 1",
                            "docstring": "Monotonicity of successor.",
                            "kind": "theorem",
                        }
                    }
                ]
            ]
        ).encode("utf-8")
        response.__enter__ = Mock(return_value=response)
        response.__exit__ = Mock(return_value=None)

        with patch("urllib.request.urlopen", return_value=response) as urlopen:
            results = lookup_theorems(
                "successor preserves less or equal",
                num_results=3,
                api_url="https://leansearch.example/search",
                timeout=2,
            )

        self.assertEqual(results[0].name, "Nat.succ_le_succ")
        request = urlopen.call_args.args[0]
        self.assertEqual(request.full_url, "https://leansearch.example/search")
        self.assertEqual(request.get_method(), "POST")
        self.assertEqual(
            json.loads(request.data.decode("utf-8")),
            {
                "query": ["successor preserves less or equal."],
                "num_results": 3,
            },
        )
        self.assertEqual(request.headers["Content-type"], "application/json")

    def test_parse_rejects_non_list_response(self) -> None:
        with self.assertRaises(LeanSearchError):
            parse_leansearch_response({"error": "bad response"})

    def test_runner_enriches_deduced_theorems_with_lean_name(self) -> None:
        def agent(_payload):
            return SimpleProofRefinementSpec(
                proof_steps=[
                    LogicalProofStepData(
                        claim="n + 1 <= m + 1",
                        deduced_from_theorem=[
                            DeducedFromTheoremData(
                                name="successor monotonicity",
                                claim="If n <= m, then n + 1 <= m + 1.",
                            )
                        ],
                    )
                ]
            )

        with patch(
            "mathdoc_agent.mathagents.runner.lookup_theorems",
            return_value=[LeanSearchResult(name="Nat.succ_le_succ")],
        ) as lookup:
            result = asyncio.run(run_agent_typed(agent, {}, SimpleProofRefinementSpec))

        theorem = result.proof_steps[0].deduced_from_theorem[0]
        self.assertEqual(theorem.lean_name, "Nat.succ_le_succ")
        lookup.assert_called_once_with(
            "If n <= m, then n + 1 <= m + 1.",
            num_results=1,
            timeout=10.0,
        )

    def test_runner_preserves_existing_lean_name_without_search(self) -> None:
        def agent(_payload):
            return SimpleProofRefinementSpec(
                deduced_from_theorem=[
                    DeducedFromTheoremData(
                        name="known",
                        claim="Known theorem.",
                        lean_name="Known.theorem",
                    )
                ]
            )

        with patch("mathdoc_agent.mathagents.runner.lookup_theorems") as lookup:
            result = asyncio.run(run_agent_typed(agent, {}, SimpleProofRefinementSpec))

        self.assertEqual(result.deduced_from_theorem[0].lean_name, "Known.theorem")
        lookup.assert_not_called()


if __name__ == "__main__":
    unittest.main()
