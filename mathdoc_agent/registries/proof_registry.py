from __future__ import annotations

from mathdoc_agent.models.base import ProofKind
from mathdoc_agent.models.payloads import (
    CalculationData,
    CasesData,
    InductionData,
    LocalClaimData,
    ProofKindData,
    SimpleProofData,
    SpecializeData,
    StructuredProofData,
)


def _kind_key(kind: str | ProofKind) -> str:
    return kind.value if isinstance(kind, ProofKind) else str(kind)


class ProofPayloadRegistry:
    def __init__(self) -> None:
        self._models: dict[str, type[ProofKindData]] = {}

    def register(self, kind: str | ProofKind, model: type[ProofKindData]) -> None:
        self._models[_kind_key(kind)] = model

    def get(self, kind: str | ProofKind) -> type[ProofKindData] | None:
        return self._models.get(_kind_key(kind))

    def validate_data(self, kind: str | ProofKind, data: dict) -> ProofKindData | None:
        model = self.get(kind)
        if model is None:
            return None
        return model.model_validate(data)


proof_payload_registry = ProofPayloadRegistry()
proof_payload_registry.register(ProofKind.logical_sequence, SimpleProofData)
proof_payload_registry.register(ProofKind.simple, SimpleProofData)
proof_payload_registry.register(ProofKind.theorem_application, SimpleProofData)
proof_payload_registry.register(ProofKind.definition_unfolding, SimpleProofData)
proof_payload_registry.register(ProofKind.induction, InductionData)
proof_payload_registry.register(ProofKind.cases, CasesData)
proof_payload_registry.register(ProofKind.calculation, CalculationData)
proof_payload_registry.register(ProofKind.local_claim, LocalClaimData)
proof_payload_registry.register(ProofKind.specialize, SpecializeData)

for structured_kind in (
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
):
    proof_payload_registry.register(structured_kind, StructuredProofData)
