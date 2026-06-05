from __future__ import annotations

from mathdoc_agent.mathagents import definitions
from mathdoc_agent.handlers.proof_handlers import (
    CalculationHandler,
    CasesHandler,
    InductionHandler,
    LocalClaimHandler,
    LogicalSequenceHandler,
    OpaqueProofHandler,
    SimpleProofHandler,
    SpecializeHandler,
    StepLikeProofHandler,
    StructuredProofHandler,
    UnknownProofHandler,
)
from mathdoc_agent.models.base import ProofKind
from mathdoc_agent.registries.proof_handlers import ProofHandlerRegistry


def default_proof_handler_registry(
    *,
    classifier_agent=definitions.proof_classifier_agent,
    induction_agent=definitions.induction_agent,
    cases_agent=definitions.cases_agent,
    simple_agent=definitions.simple_proof_agent,
    calculation_agent=definitions.calculation_agent,
    specialize_agent=definitions.specialize_agent,
    local_claim_agent=None,
    structured_agent=definitions.structured_proof_agent,
) -> ProofHandlerRegistry:
    registry = ProofHandlerRegistry()
    registry.register(ProofKind.unknown.value, UnknownProofHandler(classifier_agent))
    registry.register(ProofKind.opaque.value, OpaqueProofHandler())
    registry.register(ProofKind.logical_sequence.value, LogicalSequenceHandler(simple_agent))
    registry.register(ProofKind.induction.value, InductionHandler(induction_agent))
    registry.register(ProofKind.cases.value, CasesHandler(cases_agent))
    registry.register(ProofKind.simple.value, SimpleProofHandler(simple_agent))
    registry.register(
        ProofKind.theorem_application.value,
        SimpleProofHandler(simple_agent, kind=ProofKind.theorem_application.value),
    )
    registry.register(
        ProofKind.definition_unfolding.value,
        SimpleProofHandler(simple_agent, kind=ProofKind.definition_unfolding.value),
    )
    registry.register(ProofKind.calculation.value, CalculationHandler(calculation_agent))
    registry.register(ProofKind.local_claim.value, LocalClaimHandler(local_claim_agent))
    registry.register(ProofKind.specialize.value, SpecializeHandler(specialize_agent))
    for step_kind in ("let_statement", "assume_statement", "assert_statement"):
        registry.register(step_kind, StepLikeProofHandler(step_kind))
    for structured_kind in STRUCTURED_PROOF_KINDS:
        registry.register(structured_kind.value, StructuredProofHandler(structured_kind, structured_agent))
    return registry


STRUCTURED_PROOF_KINDS = (
    ProofKind.contradiction,
    ProofKind.contrapositive,
    ProofKind.extensionality,
    ProofKind.existence,
    ProofKind.uniqueness,
    ProofKind.equivalence,
    ProofKind.construction,
    ProofKind.minimal_counterexample,
    ProofKind.infinite_descent,
    ProofKind.exhaustion,
    ProofKind.counting,
    ProofKind.pigeonhole,
    ProofKind.invariant,
    ProofKind.monotonicity_bounding,
    ProofKind.reduction,
    ProofKind.diagram_chase,
    ProofKind.epsilon_delta,
    ProofKind.generic_element,
    ProofKind.local_to_global,
    ProofKind.maximal_minimal,
    ProofKind.compactness,
    ProofKind.density,
    ProofKind.approximation,
    ProofKind.universal_property,
    ProofKind.algorithmic,
    ProofKind.probabilistic,
    ProofKind.genericity_ae,
    ProofKind.diagrammatic_geometric,
)
