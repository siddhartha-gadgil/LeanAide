from __future__ import annotations

from typing import Literal

from pydantic import AliasChoices, BaseModel, Field

from mathdoc_agent.models.base import DocumentKind, ProofKind
from mathdoc_agent.models.payloads import (
    CalcStep,
    DeducedFromTheoremData,
    InductiveConstructorData,
    InstanceGiveData,
    LogicalProofStepData,
    ParameterData,
    StructureFieldData,
)


class MetadataEntry(BaseModel):
    key: str
    value: str


def metadata_entries_to_dict(entries: list[MetadataEntry]) -> dict[str, str]:
    return {entry.key: entry.value for entry in entries}


class ChildProofSpec(BaseModel):
    id_suffix: str
    kind: ProofKind | str = ProofKind.unknown
    text: str
    goal: str | None = None
    hypotheses: list[str] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)


class InductionRefinementSpec(BaseModel):
    variable: str
    principle: str | None = None
    induction_hypotheses: list[str] = Field(default_factory=list)
    base_cases: list[ChildProofSpec]
    step_cases: list[ChildProofSpec]
    notes: list[str] = Field(default_factory=list)


class CasesRefinementSpec(BaseModel):
    split_on: str | None = None
    exhaustive_reason: str | None = None
    cases: list[ChildProofSpec]
    notes: list[str] = Field(default_factory=list)


class SimpleProofRefinementSpec(BaseModel):
    method: str | None = None
    hints: list[str] = Field(default_factory=list)
    referenced_lemmas: list[str] = Field(default_factory=list)
    referenced_hypotheses: list[str] = Field(default_factory=list)
    deduced_from_claim: list[str] = Field(default_factory=list)
    deduced_from_theorem: list[DeducedFromTheoremData] = Field(default_factory=list)
    proof_steps: list[LogicalProofStepData] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)


class CalculationRefinementSpec(BaseModel):
    calculation_kind: str | None = None
    steps: list[CalcStep] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)


class LocalClaimRefinementSpec(BaseModel):
    statement: str
    label: str | None = None
    proof: ChildProofSpec | None = None
    notes: list[str] = Field(default_factory=list)


class SpecializeRefinementSpec(BaseModel):
    name: str = Field(
        description="Name for the new specialized local lemma being created."
    )
    lean_term: str = Field(
        description="Lean term for the specialized instance, such as `(h x hx)`."
    )
    claim: str | None = Field(
        default=None,
        description="Mathematical statement of the specialized lemma.",
    )
    source_claim: str | None = Field(
        default=None,
        description="Already-proved general claim or hypothesis being instantiated.",
    )
    arguments: list[str] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)


class StructuredProofRefinementSpec(BaseModel):
    strategy: str | None = None
    summary: str | None = None
    components: list[ChildProofSpec] = Field(default_factory=list)
    assumptions: list[str] = Field(default_factory=list)
    conclusions: list[str] = Field(default_factory=list)
    witness: str | None = None
    contradiction_assumption: str | None = None
    full_claim: str | None = None
    claim: str | None = None
    variable_name: str | None = None
    candidate_variables: list[str] = Field(default_factory=list)
    bound_claim: str | None = None
    reduced_to: str | None = None
    proof_of_reduction: ChildProofSpec | None = None
    proof: ChildProofSpec | None = None
    invariant: str | None = None
    construction: str | None = None
    metadata: list[MetadataEntry] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)


class ProofResolutionSpec(BaseModel):
    strategy: str | None = None
    summary: str | None = None
    proof_steps: list[LogicalProofStepData] = Field(default_factory=list)
    components: list[ChildProofSpec] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)


class DocumentChildSpec(BaseModel):
    id_suffix: str
    kind: DocumentKind | str = DocumentKind.unknown
    title: str | None = None
    label: str | None = None
    text: str
    statement: str | None = None
    notes: list[str] = Field(default_factory=list)
    data_entries: list[MetadataEntry] = Field(default_factory=list)
    proof_text: str | None = None
    name: str | None = None
    is_class: bool | None = None
    is_prop: bool | None = Field(
        default=None,
        validation_alias=AliasChoices("is_prop", "isProp"),
    )
    parameters: list[ParameterData] = Field(default_factory=list)
    indices: list[ParameterData] = Field(default_factory=list)
    extends: list[str] = Field(default_factory=list)
    fields: list[StructureFieldData] = Field(default_factory=list)
    gives: list[InstanceGiveData] = Field(default_factory=list)
    class_name: str | None = None
    target: str | None = None
    value: str | None = None
    constructors: list[InductiveConstructorData] = Field(default_factory=list)


class DocumentRefinementSpec(BaseModel):
    children: list[DocumentChildSpec]
    notes: list[str] = Field(default_factory=list)


class ClaimPatchSpec(BaseModel):
    path: str = Field(
        description=(
            "JSON pointer path to the claim field being repaired, for example "
            "`/document/body/0/proof/proof_steps/1/claim`."
        )
    )
    action: Literal["replace_claim", "replace_assertion_with_steps"] = Field(
        description=(
            "`replace_claim` rewrites only the claim string. "
            "`replace_assertion_with_steps` replaces the enclosing assert_statement "
            "with a Proof containing smaller proof_steps."
        )
    )
    claim: str | None = Field(
        default=None,
        description="Clean proposition to use when action is `replace_claim`.",
    )
    proof_steps: list[LogicalProofStepData] = Field(
        default_factory=list,
        description=(
            "Smaller mathematical proof steps to use when an assert_statement claim "
            "contains several claims, a proof sketch, or an instruction."
        ),
    )
    notes: list[str] = Field(default_factory=list)


class ClaimAuditSpec(BaseModel):
    patches: list[ClaimPatchSpec] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)


class InformalNotationPatchSpec(BaseModel):
    path: str = Field(
        description=(
            "JSON pointer path to the string field being repaired, for example "
            "`/document/body/0/proof/proof_steps/1/claim`."
        )
    )
    replacement: str = Field(
        description=(
            "Replacement text with scoped ASCII identifiers/prose and no display-only "
            "notation, pseudo-subscripts, or informal function-call notation."
        )
    )
    notes: list[str] = Field(default_factory=list)


class InformalNotationRepairSpec(BaseModel):
    patches: list[InformalNotationPatchSpec] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)


class DeducedFromClaimPatchSpec(BaseModel):
    path: str = Field(
        description=(
            "JSON pointer path to the object containing `deduced_from_claim`, "
            "for example `/document/body/0/proof/proof_steps/2`."
        )
    )
    action: Literal[
        "replace_deduced_from_claim",
        "insert_have_before",
        "insert_specialize_before",
        "insert_lemma_before",
    ] = Field(
        description=(
            "`replace_deduced_from_claim` only rewrites or removes the dependency list. "
            "`insert_have_before` inserts a named `have`/assertion proved by a Lean term. "
            "`insert_specialize_before` is accepted as a backwards-compatible alias for "
            "`insert_have_before`; it must not mean Lean's destructive `specialize` tactic. "
            "`insert_lemma_before` inserts a named local theorem/lemma with its own proof."
        )
    )
    deduced_from_claim: list[str] = Field(
        default_factory=list,
        description="Replacement dependency claims that should remain on the original object.",
    )
    remove_claims: list[str] = Field(
        default_factory=list,
        description="Dependency claims to remove from the original object.",
    )
    name: str | None = Field(
        default=None,
        description="Name for the inserted specialized lemma or local lemma.",
    )
    lean_term: str | None = Field(
        default=None,
        description="Lean term for the inserted specialization.",
    )
    claim: str | None = Field(
        default=None,
        description="Claim proved by the inserted specialization or local lemma.",
    )
    source_claim: str | None = Field(
        default=None,
        description="General already-proved claim being instantiated.",
    )
    arguments: list[str] = Field(default_factory=list)
    proof_steps: list[LogicalProofStepData] = Field(
        default_factory=list,
        description="Proof steps for an inserted local theorem/lemma.",
    )
    notes: list[str] = Field(default_factory=list)


class DeducedFromClaimRewriteSpec(BaseModel):
    patches: list[DeducedFromClaimPatchSpec] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)


class ProofSanityPatchSpec(BaseModel):
    path: str = Field(
        description=(
            "JSON pointer path to the assert_statement or calculation assertion "
            "whose proof-step claim should be marked or repaired."
        )
    )
    action: Literal["mark_needs_review", "replace_claim", "replace_assertion_with_steps"] = Field(
        description=(
            "`mark_needs_review` records a counterexample/strength/unbound-variable "
            "risk without changing the claim. `replace_claim` rewrites only the "
            "claim string. `replace_assertion_with_steps` replaces an assertion "
            "with a smaller Proof object."
        )
    )
    reason: str = Field(
        description=(
            "Concrete reason the claim is risky, e.g. stronger than the source, "
            "has unbound variables, or has an obvious counterexample."
        )
    )
    claim: str | None = Field(
        default=None,
        description="Replacement claim when action is `replace_claim`.",
    )
    proof_steps: list[LogicalProofStepData] = Field(
        default_factory=list,
        description="Smaller proof steps when action is `replace_assertion_with_steps`.",
    )
    suggested_repair: str | None = Field(
        default=None,
        description="Short general repair suggestion.",
    )
    notes: list[str] = Field(default_factory=list)


class ProofSanityAuditSpec(BaseModel):
    patches: list[ProofSanityPatchSpec] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)
