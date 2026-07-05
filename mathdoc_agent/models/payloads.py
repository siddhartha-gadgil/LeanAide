from __future__ import annotations

from enum import Enum
from typing import Optional

from pydantic import AliasChoices, BaseModel, Field, field_validator, model_validator


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
    lean_name: Optional[str] = Field(
        default=None,
        description="Lean/Mathlib declaration name to use instead of regenerating this definition.",
    )
    mathlib_kind: Optional[str] = Field(
        default=None,
        description="Kind of the reused Mathlib declaration, when known.",
    )
    mathlib_type: Optional[str] = Field(
        default=None,
        description="Type of the reused Mathlib declaration, when known.",
    )


class BinderKind(str, Enum):
    default = "default"
    implicit = "implicit"
    typeclass = "typeclass"


class ParameterData(BaseModel):
    name: str
    type: str
    binder: BinderKind = BinderKind.default

    @model_validator(mode="before")
    @classmethod
    def _validate_parameter(cls, value: object) -> object:
        return _coerce_parameter(value)


def _coerce_parameter(value: object) -> object:
    if isinstance(value, ParameterData):
        return value
    if isinstance(value, str):
        name, separator, type_ = value.partition(":")
        if separator:
            return {
                "name": name.strip(),
                "type": type_.strip(),
                "binder": BinderKind.default.value,
            }
        return {
            "name": value.strip(),
            "type": "",
            "binder": BinderKind.default.value,
        }
    if isinstance(value, dict) and "binder" not in value:
        return {**value, "binder": BinderKind.default.value}
    return value


def _coerce_parameters(value: object) -> object:
    if value is None:
        return []
    if isinstance(value, list):
        return [_coerce_parameter(item) for item in value]
    return value


class StructureFieldData(BaseModel):
    name: Optional[str] = None
    type: str
    default: Optional[str] = None


class StructureDefinitionData(DocumentKindData):
    name: str
    is_class: bool = False
    is_prop: bool = Field(
        default=False,
        validation_alias=AliasChoices("is_prop", "isProp"),
    )
    parameters: list[ParameterData] = Field(default_factory=list)
    extends: list[str] = Field(default_factory=list)
    fields: list[StructureFieldData] = Field(default_factory=list)

    @field_validator("parameters", mode="before")
    @classmethod
    def _validate_parameters(cls, value: object) -> object:
        return _coerce_parameters(value)


class InstanceGiveData(BaseModel):
    name: str
    value: str

    @model_validator(mode="before")
    @classmethod
    def _validate_give(cls, value: object) -> object:
        if isinstance(value, StructureFieldData):
            return {"name": value.name, "value": value.type}
        if isinstance(value, dict) and "value" not in value and "type" in value:
            return {**value, "value": value["type"]}
        return value


def _coerce_instance_gives(value: object) -> object:
    if value is None:
        return []
    if isinstance(value, dict):
        return [{"name": str(name), "value": str(item)} for name, item in value.items()]
    if isinstance(value, list):
        items: list[object] = []
        for item in value:
            if isinstance(item, StructureFieldData):
                items.append({"name": item.name, "value": item.type})
            elif isinstance(item, dict) and "value" not in item and "type" in item:
                items.append({**item, "value": item["type"]})
            else:
                items.append(item)
        return items
    return value


class InstanceDefinitionData(DocumentKindData):
    name: Optional[str] = None
    class_name: Optional[str] = None
    target: Optional[str] = None
    parameters: list[ParameterData] = Field(default_factory=list)
    gives: list[InstanceGiveData] = Field(default_factory=list)
    value: Optional[str] = None

    @model_validator(mode="before")
    @classmethod
    def _coerce_legacy_fields(cls, value: object) -> object:
        if isinstance(value, dict) and "gives" not in value and "fields" in value:
            return {**value, "gives": value.get("fields")}
        return value

    @field_validator("parameters", mode="before")
    @classmethod
    def _validate_parameters(cls, value: object) -> object:
        return _coerce_parameters(value)

    @field_validator("gives", mode="before")
    @classmethod
    def _validate_gives(cls, value: object) -> object:
        return _coerce_instance_gives(value)


class ConstructorArgumentData(ParameterData):
    pass


def _coerce_constructor_arguments(value: object) -> object:
    if value is None:
        return []
    if not isinstance(value, list):
        return value
    result: list[object] = []
    for item in value:
        if isinstance(item, str):
            if ":" in item:
                name, type_ = item.split(":", 1)
                result.append(
                    {
                        "name": name.strip(),
                        "type": type_.strip(),
                        "binder": BinderKind.default.value,
                    }
                )
            else:
                result.append(
                    {
                        "name": "_",
                        "type": item.strip(),
                        "binder": BinderKind.default.value,
                    }
                )
        else:
            result.append(item)
    return result


class InductiveConstructorData(BaseModel):
    name: Optional[str] = None
    arguments: list[ConstructorArgumentData] = Field(default_factory=list)
    index_args: list[str] = Field(default_factory=list)

    @field_validator("arguments", mode="before")
    @classmethod
    def _validate_arguments(cls, value: object) -> object:
        return _coerce_constructor_arguments(value)


class InductiveTypeDefinitionData(DocumentKindData):
    name: str
    is_prop: bool = False
    parameters: list[ParameterData] = Field(default_factory=list)
    indices: list[ParameterData] = Field(default_factory=list)
    constructors: list[InductiveConstructorData] = Field(default_factory=list)

    @field_validator("parameters", "indices", mode="before")
    @classmethod
    def _validate_parameters(cls, value: object) -> object:
        return _coerce_parameters(value)


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
    lean_name: Optional[str] = Field(
        default=None,
        description="Optional Lean/Mathlib declaration name found by LeanSearch.",
    )
    lean_term: Optional[str] = Field(
        default=None,
        description=(
            "Optional Lean term for the specific theorem instance used in the proof, "
            "possibly depending on local variables or hypotheses."
        ),
    )


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
    name: Optional[str] = None
    claim: Optional[str] = None
    proof_method: Optional[str] = None
    lean_term: Optional[str] = None
    source_claim: Optional[str] = None
    arguments: list[str] = Field(default_factory=list)
    assumption: Optional[str] = None
    variable_name: Optional[str] = None
    variable_type: Optional[str] = None
    value: Optional[str] = None
    properties: Optional[str] = None
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


class SpecializeData(ProofKindData):
    name: str = Field(
        description="Name of the new local lemma created by specializing an existing claim."
    )
    lean_term: str = Field(
        description=(
            "Lean term proving the specialized lemma, typically an application "
            "of an existing theorem or hypothesis to local arguments."
        )
    )
    claim: Optional[str] = Field(
        default=None,
        description="Optional mathematical statement of the specialized lemma.",
    )
    source_claim: Optional[str] = Field(
        default=None,
        description="Optional already-proved general claim being instantiated.",
    )
    arguments: list[str] = Field(
        default_factory=list,
        description="Optional local values or hypotheses used for the specialization.",
    )


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
