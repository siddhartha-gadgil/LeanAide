"""Default live-agent definitions used by the document/proof registries.

The objects in this module are intentionally small wrappers around prompt
strings and output schemas. They can be replaced by fake callables in tests or
by custom agents in applications that build their own registries.
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Any

from mathdoc_agent.mathagents import prompts
from mathdoc_agent.models.refinement_specs import (
    CalculationRefinementSpec,
    ClaimAuditSpec,
    CasesRefinementSpec,
    DocumentRefinementSpec,
    InductionRefinementSpec,
    ProofResolutionSpec,
    SimpleProofRefinementSpec,
    SpecializeRefinementSpec,
    StructuredProofRefinementSpec,
)

MODEL = os.environ.get("MATHDOC_AGENT_MODEL", "gpt-5.5")


@dataclass
class MissingAgentsSDKAgent:
    """Placeholder that records agent configuration when the SDK is unavailable."""

    name: str
    model: str
    instructions: str
    output_type: type[Any] | None = None


def _agent(name: str, instructions: str, output_type: type[Any] | None = None) -> Any:
    """Build an OpenAI Agents SDK agent, or a placeholder if the SDK is absent."""
    try:
        from agents import Agent
    except ImportError:
        return MissingAgentsSDKAgent(
            name=name,
            model=MODEL,
            instructions=instructions,
            output_type=output_type,
        )
    return Agent(
        name=name,
        model=MODEL,
        instructions=instructions,
        output_type=output_type,
    )


document_parser_agent = _agent(
    "Document parser",
    prompts.DOCUMENT_PARSER_INSTRUCTIONS,
    DocumentRefinementSpec,
)
proof_classifier_agent = _agent(
    "Proof classifier",
    prompts.PROOF_CLASSIFIER_INSTRUCTIONS,
)
induction_agent = _agent(
    "Induction proof refiner",
    prompts.INDUCTION_INSTRUCTIONS,
    InductionRefinementSpec,
)
cases_agent = _agent(
    "Cases proof refiner",
    prompts.CASES_INSTRUCTIONS,
    CasesRefinementSpec,
)
simple_proof_agent = _agent(
    "Simple proof refiner",
    prompts.SIMPLE_PROOF_INSTRUCTIONS,
    SimpleProofRefinementSpec,
)
calculation_agent = _agent(
    "Calculation proof refiner",
    prompts.CALCULATION_INSTRUCTIONS,
    CalculationRefinementSpec,
)
specialize_agent = _agent(
    "Specialization proof refiner",
    prompts.SPECIALIZE_INSTRUCTIONS,
    SpecializeRefinementSpec,
)
structured_proof_agent = _agent(
    "Structured proof refiner",
    prompts.STRUCTURED_PROOF_INSTRUCTIONS,
    StructuredProofRefinementSpec,
)
proof_resolution_agent = _agent(
    "Unsupported proof resolver",
    prompts.PROOF_RESOLUTION_INSTRUCTIONS,
    ProofResolutionSpec,
)
combinatorial_proof_resolution_agent = _agent(
    "Combinatorial proof resolver",
    prompts.PROOF_RESOLUTION_INSTRUCTIONS,
    ProofResolutionSpec,
)
analytic_proof_resolution_agent = _agent(
    "Analytic proof resolver",
    prompts.PROOF_RESOLUTION_INSTRUCTIONS,
    ProofResolutionSpec,
)
structural_proof_resolution_agent = _agent(
    "Structural proof resolver",
    prompts.PROOF_RESOLUTION_INSTRUCTIONS,
    ProofResolutionSpec,
)
claim_audit_agent = _agent(
    "Lean claim auditor",
    prompts.CLAIM_AUDIT_INSTRUCTIONS,
    ClaimAuditSpec,
)

proof_resolution_agents = {
    "default": proof_resolution_agent,
    "counting": combinatorial_proof_resolution_agent,
    "pigeonhole": combinatorial_proof_resolution_agent,
    "probabilistic": combinatorial_proof_resolution_agent,
    "genericity_ae": combinatorial_proof_resolution_agent,
    "algorithmic": combinatorial_proof_resolution_agent,
    "invariant": analytic_proof_resolution_agent,
    "monotonicity_bounding": analytic_proof_resolution_agent,
    "maximal_minimal": analytic_proof_resolution_agent,
    "compactness": analytic_proof_resolution_agent,
    "density": analytic_proof_resolution_agent,
    "approximation": analytic_proof_resolution_agent,
    "extensionality": structural_proof_resolution_agent,
    "generic_element": structural_proof_resolution_agent,
    "diagram_chase": structural_proof_resolution_agent,
    "local_to_global": structural_proof_resolution_agent,
    "universal_property": structural_proof_resolution_agent,
    "diagrammatic_geometric": structural_proof_resolution_agent,
}
