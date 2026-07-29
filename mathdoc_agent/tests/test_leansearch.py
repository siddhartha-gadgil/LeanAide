from __future__ import annotations

import json
import os
import unittest
import asyncio
from unittest.mock import Mock, patch

from mathdoc_agent.mathagents.leansearch import (
    LeanSearchError,
    LeanSearchResult,
    leansearch_command,
    leansearch_payload,
    leansearch_timeout_seconds,
    lookup_theorems,
    normalize_leansearch_query,
    parse_leansearch_response,
)
from mathdoc_agent.orchestration import mathlib_reuse
from mathdoc_agent.orchestration.mathlib_reuse import (
    enrich_theorem_dependencies,
    find_mathlib_theorem,
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

    def test_configured_timeout_is_used_by_default(self) -> None:
        response = Mock()
        response.read.return_value = b"[]"
        response.__enter__ = Mock(return_value=response)
        response.__exit__ = Mock(return_value=None)

        with (
            patch.dict(
                os.environ,
                {"MATHDOC_AGENT_LEANSEARCH_TIMEOUT_SECONDS": "3.5"},
            ),
            patch("urllib.request.urlopen", return_value=response) as urlopen,
        ):
            lookup_theorems("a test theorem")

        self.assertEqual(leansearch_timeout_seconds(), 10.0)
        self.assertEqual(urlopen.call_args.kwargs["timeout"], 3.5)

    def test_timeout_is_wrapped_as_leansearch_error(self) -> None:
        with patch("urllib.request.urlopen", side_effect=TimeoutError("timed out")):
            with self.assertRaisesRegex(LeanSearchError, "timed out"):
                lookup_theorems("a test theorem", timeout=0.1)

    def test_parse_rejects_non_list_response(self) -> None:
        with self.assertRaises(LeanSearchError):
            parse_leansearch_response({"error": "bad response"})

    def test_runner_does_not_search_intermediate_agent_output(self) -> None:
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
            "mathdoc_agent.orchestration.mathlib_reuse.find_mathlib_theorem"
        ) as lookup:
            result = asyncio.run(run_agent_typed(agent, {}, SimpleProofRefinementSpec))

        theorem = result.proof_steps[0].deduced_from_theorem[0]
        self.assertIsNone(theorem.lean_name)
        lookup.assert_not_called()

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

        result = asyncio.run(run_agent_typed(agent, {}, SimpleProofRefinementSpec))

        self.assertEqual(result.deduced_from_theorem[0].lean_name, "Known.theorem")


class FinalTheoremEnrichmentTests(unittest.TestCase):
    def setUp(self) -> None:
        mathlib_reuse._LEANSEARCH_DEFINITION_QUERY_CACHE.clear()
        mathlib_reuse._LOCAL_DEFINITION_QUERY_CACHE.clear()
        mathlib_reuse._THEOREM_MATCH_QUERY_CACHE.clear()
        mathlib_reuse._PERSISTENT_CACHE_LOADED = True
        mathlib_reuse._REMOTE_LEANSEARCH_FAILURES = 0
        mathlib_reuse._REMOTE_LEANSEARCH_CIRCUIT_OPEN = False

    def test_final_pass_records_candidate_not_executable_lean_name(self) -> None:
        data = {
            "document": {
                "body": [
                    {
                        "type": "assert_statement",
                        "claim": "n + 1 <= m + 1",
                        "deduced_from_theorem": [
                            {
                                "name": "successor monotonicity",
                                "claim": "If n <= m, then n + 1 <= m + 1.",
                            }
                        ],
                    }
                ]
            }
        }
        match = LeanSearchResult(
            name="Nat.succ_le_succ",
            type="n ≤ m → n + 1 ≤ m + 1",
            kind="theorem",
        )

        with patch(
            "mathdoc_agent.orchestration.mathlib_reuse.find_mathlib_theorem",
            return_value=match,
        ):
            enriched = enrich_theorem_dependencies(data)

        dependency = enriched["document"]["body"][0]["deduced_from_theorem"][0]
        self.assertNotIn("lean_name", dependency)
        self.assertEqual(dependency["lean_name_candidate"], "Nat.succ_le_succ")
        self.assertEqual(dependency["verification_status"], "semantic_match")

    def test_final_pass_resolves_local_theorem_labels_without_search(self) -> None:
        data = {
            "document": {
                "body": [
                    {
                        "type": "theorem",
                        "label": "Lemma 1",
                        "name": "lemma_1",
                        "claim": "P",
                    },
                    {
                        "type": "theorem",
                        "label": "Lemma 2",
                        "name": "lemma_2",
                        "claim": "Q",
                        "proof": {
                            "type": "proof",
                            "deduced_from_theorem": [
                                {"name": "Lemma 1", "claim": "P"}
                            ],
                        },
                    },
                ]
            }
        }

        with (
            patch.dict(
                os.environ,
                {"MATHDOC_AGENT_LEANSEARCH_DEDUCED_THEOREMS": "0"},
            ),
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse.find_mathlib_theorem"
            ) as external_lookup,
        ):
            enriched = enrich_theorem_dependencies(data)

        dependency = enriched["document"]["body"][1]["proof"][
            "deduced_from_theorem"
        ][0]
        self.assertEqual(dependency["lean_name_candidate"], "lemma_1")
        self.assertEqual(
            dependency["verification_status"],
            "local_declaration_match",
        )
        external_lookup.assert_not_called()

    def test_local_exact_match_prevents_remote_request_and_is_cached(self) -> None:
        theorem = {
            "name": "successor monotonicity",
            "claim": "If n <= m, then n + 1 <= m + 1.",
        }
        match = LeanSearchResult(name="Nat.succ_le_succ", kind="theorem")

        with (
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._local_theorem_query_results",
                return_value=[match],
            ) as local_lookup,
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._remote_query_results"
            ) as remote_lookup,
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._write_persistent_theorem_cache"
            ),
        ):
            self.assertEqual(find_mathlib_theorem(theorem), match)
            self.assertEqual(find_mathlib_theorem(theorem), match)

        local_lookup.assert_called_once()
        remote_lookup.assert_not_called()

    def test_local_theorem_search_uses_descriptions_and_broad_reranking(self) -> None:
        query = "If n <= m, then n + 1 <= m + 1."
        record = {
            "name": "Nat.succ_le_succ",
            "statement": "theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m",
            "type": "n ≤ m → Nat.succ n ≤ Nat.succ m",
            "docString": "Successor preserves less than or equal.",
        }
        match = LeanSearchResult(
            name="Nat.succ_le_succ",
            type=record["type"],
            docstring=record["docString"],
            kind="theorem",
        )

        with (
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._run_similarity_search",
                return_value=[record],
            ) as similarity,
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._select_llm_match",
                return_value=[match],
            ),
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._write_persistent_local_cache"
            ),
        ):
            results = mathlib_reuse._local_theorem_query_results(
                query,
                num_results=10,
            )

        self.assertEqual(results, [match])
        self.assertEqual(similarity.call_args.kwargs["desc_field"], "description")
        self.assertEqual(similarity.call_args.kwargs["num_results"], 200)

    def test_remote_results_require_exact_match_selection(self) -> None:
        theorem = {"claim": "If n <= m, then n + 1 <= m + 1."}
        wrong = LeanSearchResult(name="Nat.le_add_right", kind="theorem")
        right = LeanSearchResult(name="Nat.succ_le_succ", kind="theorem")

        with (
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._local_theorem_query_results",
                return_value=[],
            ),
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._remote_query_results",
                return_value=[wrong, right],
            ),
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._select_llm_match",
                return_value=[right],
            ) as select_match,
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse._write_persistent_theorem_cache"
            ),
        ):
            result = find_mathlib_theorem(theorem)

        self.assertEqual(result, right)
        select_match.assert_called_once()

    def test_remote_timeout_opens_run_wide_circuit(self) -> None:
        with (
            patch.dict(
                os.environ,
                {"MATHDOC_AGENT_LEANSEARCH_CIRCUIT_FAILURES": "1"},
            ),
            patch(
                "mathdoc_agent.orchestration.mathlib_reuse.lookup_theorems",
                side_effect=LeanSearchError("timed out"),
            ) as lookup,
        ):
            first = mathlib_reuse._remote_query_results("first query", num_results=5)
            second = mathlib_reuse._remote_query_results("second query", num_results=5)

        self.assertIsNone(first)
        self.assertIsNone(second)
        lookup.assert_called_once()
        self.assertTrue(mathlib_reuse._REMOTE_LEANSEARCH_CIRCUIT_OPEN)

    def test_new_document_resets_transient_search_failures(self) -> None:
        mathlib_reuse._LEANSEARCH_DEFINITION_QUERY_CACHE["remote"] = None
        mathlib_reuse._LOCAL_DEFINITION_QUERY_CACHE["local"] = None
        mathlib_reuse._THEOREM_MATCH_QUERY_CACHE["match"] = None
        mathlib_reuse._REMOTE_LEANSEARCH_FAILURES = 3
        mathlib_reuse._REMOTE_LEANSEARCH_CIRCUIT_OPEN = True

        mathlib_reuse.reset_leansearch_run_state()

        self.assertEqual(mathlib_reuse._REMOTE_LEANSEARCH_FAILURES, 0)
        self.assertFalse(mathlib_reuse._REMOTE_LEANSEARCH_CIRCUIT_OPEN)
        self.assertNotIn("remote", mathlib_reuse._LEANSEARCH_DEFINITION_QUERY_CACHE)
        self.assertNotIn("local", mathlib_reuse._LOCAL_DEFINITION_QUERY_CACHE)
        self.assertNotIn("match", mathlib_reuse._THEOREM_MATCH_QUERY_CACHE)

    def test_cache_key_normalizes_whitespace_and_sentence_ending(self) -> None:
        self.assertEqual(
            mathlib_reuse._cache_key("  successor   monotonicity  "),
            mathlib_reuse._cache_key("successor monotonicity."),
        )


if __name__ == "__main__":
    unittest.main()
