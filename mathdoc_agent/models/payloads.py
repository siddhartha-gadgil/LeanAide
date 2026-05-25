from __future__ import annotations

from enum import Enum
from typing import Optional

from pydantic import BaseModel, Field


class ProofKindData(BaseModel):
    pass


class DocumentKindData(BaseModel):
    pass


class StatementData(DocumentKindData):
    statement: str
    assumptions: list[str] = Field(default_factory=list)
    conclusion: Optional[str] = None


class DefinitionData(DocumentKindData):
    term: Optional[str] = None
    definitions: Optional[str] = None
    notation: Optional[str] = None


class StructureFieldData(BaseModel):
    name: Optional[str] = None
    type: str
    default: Optional[str] = None


class StructureDefinitionData(DocumentKindData):
    name: str
    is_class: bool = False
    parameters: list[str] = Field(default_factory=list)
    extends: list[str] = Field(default_factory=list)
    fields: list[StructureFieldData] = Field(default_factory=list)


class InstanceDefinitionData(DocumentKindData):
    name: Optional[str] = None
    class_name: Optional[str] = None
    target: Optional[str] = None
    parameters: list[str] = Field(default_factory=list)
    fields: dict[str, str] = Field(default_factory=dict)
    value: Optional[str] = None


class InductiveConstructorData(BaseModel):
    name: Optional[str] = None
    arguments: list[str] = Field(default_factory=list)


class InductiveTypeDefinitionData(DocumentKindData):
    name: str
    is_prop: bool = False
    parameters: list[str] = Field(default_factory=list)
    constructors: list[InductiveConstructorData] = Field(default_factory=list)


class CalcRelation(str, Enum):
    eq = "="
    le = "<="
    lt = "<"
    ge = ">="
    gt = ">"
    iff = "<->"
    implies = "->"
    equiv_mod = "equiv_mod"


class DeducedFromTheoremData(BaseModel):
    claim: str = Field(description="The general mathematical statement of the theorem used.")
    name: Optional[str] = Field(default=None, description="Optional standard name of the theorem.")
    description: Optional[str] = Field(default=None, description="Optional note on how the theorem is used.")


class DeducedFromDataMixin(BaseModel):
    deduced_from_claim: list[str] = Field(
        default_factory=list,
        description=(
            "Local/contextual claims used for this proof step, stated as mathematical assertions. "
            "Use for claims deduced from context but not exactly matching it."
        ),
    )
    deduced_from_theorem: list[DeducedFromTheoremData] = Field(
        default_factory=list,
        description="Standard theorem objects used for this proof step.",
    )


class LogicalProofStepData(DeducedFromDataMixin):
    type: str = "assert_statement"
    claim: Optional[str] = None
    proof_method: Optional[str] = None
    assumption: Optional[str] = None
    variable_name: Optional[str] = None
    variable_type: Optional[str] = None
    statement: Optional[str] = None


class SimpleProofData(DeducedFromDataMixin, ProofKindData):
    method: Optional[str] = None
    hints: list[str] = Field(default_factory=list)
    referenced_lemmas: list[str] = Field(default_factory=list)
    referenced_hypotheses: list[str] = Field(default_factory=list)
    proof_steps: list[LogicalProofStepData] = Field(default_factory=list)


class InductionData(ProofKindData):
    variable: Optional[str] = None
    principle: Optional[str] = None
    base_case_ids: list[str] = Field(default_factory=list)
    step_case_ids: list[str] = Field(default_factory=list)
    induction_hypotheses: list[str] = Field(default_factory=list)


class CasesData(ProofKindData):
    split_on: Optional[str] = None
    exhaustive_reason: Optional[str] = None
    case_ids: list[str] = Field(default_factory=list)


class CalcStep(DeducedFromDataMixin):
    lhs: str
    relation: CalcRelation
    rhs: str
    justification: Optional[str] = None
    side_conditions: list[str] = Field(default_factory=list)


class CalculationData(ProofKindData):
    calculation_kind: Optional[str] = None
    start: Optional[str] = None
    target: Optional[str] = None
    steps: list[CalcStep] = Field(default_factory=list)


class LocalClaimData(ProofKindData):
    statement: str
    proof_node_id: Optional[str] = None
    label: Optional[str] = None


class StructuredProofData(ProofKindData):
    strategy: Optional[str] = None
    summary: Optional[str] = None
    component_ids: list[str] = Field(default_factory=list)
    assumptions: list[str] = Field(default_factory=list)
    conclusions: list[str] = Field(default_factory=list)
    witness: Optional[str] = None
    contradiction_assumption: Optional[str] = None
    full_claim: Optional[str] = None
    claim: Optional[str] = None
    variable_name: Optional[str] = None
    candidate_variables: list[str] = Field(default_factory=list)
    bound_claim: Optional[str] = None
    reduced_to: Optional[str] = None
    proof_of_reduction_id: Optional[str] = None
    proof_id: Optional[str] = None
    invariant: Optional[str] = None
    construction: Optional[str] = None
    metadata: dict[str, str] = Field(default_factory=dict)
