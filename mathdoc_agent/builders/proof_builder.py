from __future__ import annotations

from mathdoc_agent.models.base import NodeStatus, ProofKind
from mathdoc_agent.models.payloads import (
    CalcStep,
    CalculationData,
    CasesData,
    DeducedFromTheoremData,
    InductionData,
    LocalClaimData,
    SimpleProofData,
    SpecializeData,
)
from mathdoc_agent.models.proof import ProofNode


class ProofBuilder:
    @staticmethod
    def simple(
        *,
        id: str,
        text: str,
        goal: str | None = None,
        hypotheses: list[str] | None = None,
        hints: list[str] | None = None,
        method: str | None = None,
        referenced_lemmas: list[str] | None = None,
        referenced_hypotheses: list[str] | None = None,
        deduced_from_claim: list[str] | None = None,
        deduced_from_theorem: list[DeducedFromTheoremData] | None = None,
    ) -> ProofNode:
        data = SimpleProofData(
            method=method,
            hints=hints or [],
            referenced_lemmas=referenced_lemmas or [],
            referenced_hypotheses=referenced_hypotheses or [],
            deduced_from_claim=deduced_from_claim or [],
            deduced_from_theorem=deduced_from_theorem or [],
        )
        return ProofNode(
            id=id,
            kind=ProofKind.simple,
            status=NodeStatus.resolved if data.hints or data.referenced_lemmas else NodeStatus.classified,
            text=text,
            goal=goal,
            hypotheses=hypotheses or [],
            data=data.model_dump(),
        )

    @staticmethod
    def induction(
        *,
        id: str,
        text: str,
        variable: str,
        base_cases: list[ProofNode],
        step_cases: list[ProofNode],
        goal: str | None = None,
        hypotheses: list[str] | None = None,
        principle: str | None = None,
        induction_hypotheses: list[str] | None = None,
    ) -> ProofNode:
        children = base_cases + step_cases
        data = InductionData(
            variable=variable,
            principle=principle,
            base_case_ids=[child.id for child in base_cases],
            step_case_ids=[child.id for child in step_cases],
            induction_hypotheses=induction_hypotheses or [],
        )
        return ProofNode(
            id=id,
            kind=ProofKind.induction,
            status=NodeStatus.decomposed,
            text=text,
            goal=goal,
            hypotheses=hypotheses or [],
            children=children,
            data=data.model_dump(),
        )

    @staticmethod
    def cases(
        *,
        id: str,
        text: str,
        split_on: str | None,
        cases: list[ProofNode],
        goal: str | None = None,
        hypotheses: list[str] | None = None,
        exhaustive_reason: str | None = None,
    ) -> ProofNode:
        data = CasesData(
            split_on=split_on,
            exhaustive_reason=exhaustive_reason,
            case_ids=[child.id for child in cases],
        )
        return ProofNode(
            id=id,
            kind=ProofKind.cases,
            status=NodeStatus.decomposed,
            text=text,
            goal=goal,
            hypotheses=hypotheses or [],
            children=cases,
            data=data.model_dump(),
        )

    @staticmethod
    def calculation(
        *,
        id: str,
        text: str,
        steps: list[CalcStep],
        goal: str | None = None,
        hypotheses: list[str] | None = None,
        calculation_kind: str | None = None,
    ) -> ProofNode:
        data = CalculationData(
            calculation_kind=calculation_kind,
            start=steps[0].lhs if steps else None,
            target=steps[-1].rhs if steps else None,
            steps=steps,
        )
        return ProofNode(
            id=id,
            kind=ProofKind.calculation,
            status=NodeStatus.resolved if steps else NodeStatus.classified,
            text=text,
            goal=goal,
            hypotheses=hypotheses or [],
            data=data.model_dump(),
        )

    @staticmethod
    def local_claim(
        *,
        id: str,
        text: str,
        statement: str,
        proof_node: ProofNode | None = None,
        label: str | None = None,
    ) -> ProofNode:
        data = LocalClaimData(
            statement=statement,
            proof_node_id=proof_node.id if proof_node else None,
            label=label,
        )
        return ProofNode(
            id=id,
            kind=ProofKind.local_claim,
            status=NodeStatus.decomposed if proof_node else NodeStatus.classified,
            text=text,
            goal=statement,
            children=[proof_node] if proof_node else [],
            data=data.model_dump(),
        )

    @staticmethod
    def specialize(
        *,
        id: str,
        text: str,
        name: str,
        lean_term: str,
        claim: str | None = None,
        source_claim: str | None = None,
        arguments: list[str] | None = None,
        hypotheses: list[str] | None = None,
    ) -> ProofNode:
        data = SpecializeData(
            name=name,
            lean_term=lean_term,
            claim=claim,
            source_claim=source_claim,
            arguments=arguments or [],
        )
        return ProofNode(
            id=id,
            kind=ProofKind.specialize,
            status=NodeStatus.resolved,
            text=text,
            goal=claim,
            hypotheses=hypotheses or [],
            data=data.model_dump(),
        )
