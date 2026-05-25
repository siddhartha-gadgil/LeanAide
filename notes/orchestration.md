Below is a detailed Markdown implementation document suitable to give to a coding agent.

````markdown
# Implementation Specification: Agentic Mathematical Document and Proof Decomposition System

## 1. Goal

Build a Python system that takes mathematical documents as input and incrementally decomposes them into a structured intermediate representation.

The document may contain:

- sections;
- paragraphs;
- definitions;
- examples;
- lemmas;
- theorems;
- propositions;
- corollaries;
- proofs;
- remarks;
- nested results inside proofs;
- proof fragments;
- calculations;
- references to earlier or local results.

Proofs themselves should be document-like. A proof may contain local lemmas, claims, definitions, subproofs, calculations, case splits, induction proofs, and other structured components.

The system should be extensible: new proof types, calculation types, theorem-like environments, validation rules, and export targets should be addable without rewriting the orchestration loop.

The core design should use:

- Pydantic models for the intermediate representation;
- a generic document tree;
- a generic proof tree;
- typed payloads for specialized node kinds;
- registered refinement handlers with dynamic dispatch;
- deterministic Python orchestration;
- agent calls only for bounded local refinement tasks;
- validation and repair loops;
- provenance and run logs.

The implementation should not hardcode a complete list of proof or calculation types. Those will be maintained in separate documents. This system should load or register proof types modularly.

---

## 2. Design Principles

### 2.1 Python owns the global state

Do not let an LLM recursively rewrite an entire proof tree or document tree.

Instead:

1. Python maintains the document tree.
2. Python maintains node IDs, parent-child relations, statuses, references, and run logs.
3. Agents propose local refinements.
4. Python validates, repairs, accepts, rejects, or marks nodes opaque.

The orchestration pattern is:

```text
while unresolved nodes remain:
    choose one node
    build local context
    dispatch to the relevant handler
    call a specialist agent if needed
    build a typed replacement
    validate replacement
    repair if needed
    replace node if valid
    recompute statuses
````

### 2.2 Nodes are data; handlers provide behavior

Use a stable generic node model. Do not create many subclasses of recursive document/proof nodes at the top level.

Preferred:

```text
DocumentNode
  kind: "theorem" | "definition" | "proof" | "section" | ...
  data: dict

ProofNode
  kind: "induction" | "cases" | "calculation" | ...
  data: dict
```

Then use handler classes:

```python
handler = registry.get(node.kind)
replacement = await handler.refine(node, context)
```

Do not put behavior directly on node subclasses.

This gives a compiler-like architecture:

```text
AST nodes are data.
Handlers/passes implement behavior.
```

### 2.3 Local patches, not global rewrites

Agent outputs should usually be refinement specs or patches, not complete rewritten documents.

Example:

```text
Bad:
  "Here is the entire new document tree."

Good:
  "Replace node proof.3.case.2 with this decomposed cases node."
```

### 2.4 Proofs are document-like

A proof should be allowed to contain:

* text paragraphs;
* calculations;
* local claims;
* local lemmas;
* local definitions;
* nested theorem-like statements;
* subproofs;
* case blocks;
* induction blocks;
* opaque steps.

Therefore, do not model a proof as only a tree of proof tactics. Model it as a structured document region whose nodes may include proof-specific nodes.

---

## 3. Recommended Package Layout

```text
mathdoc_agent/
  __init__.py

  models/
    __init__.py
    base.py
    document.py
    proof.py
    payloads.py
    references.py
    runs.py
    validation.py

  registries/
    __init__.py
    document_registry.py
    proof_registry.py

  handlers/
    __init__.py
    base.py
    document_handlers.py
    proof_handlers.py
    simple_handler.py
    induction_handler.py
    cases_handler.py
    calculation_handler.py
    theorem_handler.py
    definition_handler.py
    opaque_handler.py

  agents/
    __init__.py
    definitions.py
    prompts.py
    runner.py

  orchestration/
    __init__.py
    document_orchestrator.py
    proof_orchestrator.py
    worklist.py
    context.py
    repair.py
    status.py

  validation/
    __init__.py
    deterministic.py
    llm_validation.py
    references.py

  builders/
    __init__.py
    document_builder.py
    proof_builder.py

  plugins/
    __init__.py
    proof_types.py
    calculation_types.py
    document_types.py

  export/
    __init__.py
    markdown.py
    json.py
    lean.py

  tests/
    test_models.py
    test_proof_handlers.py
    test_document_orchestrator.py
    test_nested_proofs.py
```

---

## 4. External Agent Framework

Use the OpenAI Agents SDK if available. It provides `Agent` and `Runner` abstractions for model calls, tools, handoffs, guardrails, sessions, and structured outputs. The SDK documentation says `Agent` plus `Runner` lets the SDK manage turns, tools, handoffs, guardrails, and sessions, while direct Responses API use is appropriate if the application wants to fully own the loop. In this project, Python should own the proof/document refinement loop, while the SDK can be used for bounded structured-output agent calls. The SDK also supports output schemas that validate/parse JSON produced by the model into a typed output object. Use that for refinement specs, validation reports, and repair proposals.

References: official Agents SDK docs on agents, running agents, handoffs, tools, results, and structured outputs.

Implementation note: handoffs are useful for conversational delegation, but this project should prefer code-level orchestration at first. The SDK documentation describes handoffs as a mechanism by which an agent delegates to another agent; for this system, explicit Python dispatch is more deterministic than LLM-chosen handoff routing.

---

## 5. Core Model Layer

### 5.1 Base enums

Create `models/base.py`.

```python
from __future__ import annotations

from enum import Enum


class NodeStatus(str, Enum):
    raw = "raw"
    classified = "classified"
    decomposed = "decomposed"
    locally_refined = "locally_refined"
    validated = "validated"
    resolved = "resolved"
    opaque = "opaque"


class DocumentKind(str, Enum):
    unknown = "unknown"
    document = "document"
    section = "section"
    subsection = "subsection"
    paragraph = "paragraph"
    definition = "definition"
    theorem = "theorem"
    lemma = "lemma"
    proposition = "proposition"
    corollary = "corollary"
    example = "example"
    remark = "remark"
    proof = "proof"
    local_claim = "local_claim"
    calculation_block = "calculation_block"
    opaque = "opaque"


class ProofKind(str, Enum):
    unknown = "unknown"
    simple = "simple"
    calculation = "calculation"
    cases = "cases"
    induction = "induction"
    contradiction = "contradiction"
    contrapositive = "contrapositive"
    extensionality = "extensionality"
    existence = "existence"
    uniqueness = "uniqueness"
    local_claim = "local_claim"
    theorem_application = "theorem_application"
    definition_unfolding = "definition_unfolding"
    opaque = "opaque"
```

The lists above are starting points only. The full taxonomy of proof types and calculation types should be loaded from separate plugin modules or documents.

---

## 6. References and IDs

Create `models/references.py`.

All document nodes and proof nodes must have stable IDs.

```python
from __future__ import annotations

from enum import Enum
from pydantic import BaseModel


class RefKind(str, Enum):
    document_node = "document_node"
    proof_node = "proof_node"
    named_result = "named_result"
    local_result = "local_result"
    external = "external"


class Reference(BaseModel):
    kind: RefKind
    target_id: str | None = None
    label: str | None = None
    text: str | None = None
```

Use references for:

* theorem uses;
* lemma uses;
* “by the induction hypothesis”;
* “by the previous claim”;
* local claim references inside a proof.

---

## 7. Document Model

Create `models/document.py`.

```python
from __future__ import annotations

from typing import Any
from pydantic import BaseModel, Field

from .base import DocumentKind, NodeStatus
from .references import Reference
from .proof import ProofTree


class DocumentNode(BaseModel):
    id: str
    kind: DocumentKind = DocumentKind.unknown
    status: NodeStatus = NodeStatus.raw

    title: str | None = None
    label: str | None = None
    text: str = ""

    children: list["DocumentNode"] = Field(default_factory=list)

    # The proof attached to a theorem/lemma/proposition/etc.
    proof: ProofTree | None = None

    # Kind-specific payload.
    data: dict[str, Any] = Field(default_factory=dict)

    references: list[Reference] = Field(default_factory=list)

    confidence: float = Field(default=0.5, ge=0.0, le=1.0)
    notes: list[str] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)


class MathDocument(BaseModel):
    id: str
    title: str | None = None
    root: DocumentNode
    run_log: list["AgentRunRecord"] = Field(default_factory=list)


DocumentNode.model_rebuild()
```

Important: a `DocumentNode` can itself contain a `ProofTree`. This allows theorem-like statements to have structured proofs.

---

## 8. Proof Model

Create `models/proof.py`.

```python
from __future__ import annotations

from typing import Any
from pydantic import BaseModel, Field

from .base import ProofKind, NodeStatus
from .references import Reference


class ProofNode(BaseModel):
    id: str
    kind: ProofKind = ProofKind.unknown
    status: NodeStatus = NodeStatus.raw

    text: str
    goal: str | None = None
    hypotheses: list[str] = Field(default_factory=list)

    children: list["ProofNode"] = Field(default_factory=list)

    # Proof-kind-specific payload.
    data: dict[str, Any] = Field(default_factory=dict)

    references: list[Reference] = Field(default_factory=list)

    confidence: float = Field(default=0.5, ge=0.0, le=1.0)
    notes: list[str] = Field(default_factory=list)
    unresolved_details: list[str] = Field(default_factory=list)


class ProofTree(BaseModel):
    id: str
    theorem_statement: str | None = None
    root: ProofNode


ProofNode.model_rebuild()
```

The proof tree can contain local claims. A local claim should be represented as a proof node with kind `local_claim`, whose payload includes its statement and whose children or attached proof encode its proof.

---

## 9. Payload Models

Create `models/payloads.py`.

Do not include a complete list of proof and calculation types here. Add the initial payloads needed for the orchestrator and load specialized ones through plugins.

```python
from __future__ import annotations

from enum import Enum
from pydantic import BaseModel, Field


class ProofKindData(BaseModel):
    pass


class DocumentKindData(BaseModel):
    pass


class StatementData(DocumentKindData):
    statement: str
    assumptions: list[str] = Field(default_factory=list)
    conclusion: str | None = None


class DefinitionData(DocumentKindData):
    term: str | None = None
    definitions: str | None = None
    notation: str | None = None


class SimpleProofData(ProofKindData):
    method: str | None = None
    hints: list[str] = Field(default_factory=list)
    referenced_lemmas: list[str] = Field(default_factory=list)
    referenced_hypotheses: list[str] = Field(default_factory=list)


class InductionData(ProofKindData):
    variable: str | None = None
    principle: str | None = None
    base_case_ids: list[str] = Field(default_factory=list)
    step_case_ids: list[str] = Field(default_factory=list)
    induction_hypotheses: list[str] = Field(default_factory=list)


class CasesData(ProofKindData):
    split_on: str | None = None
    exhaustive_reason: str | None = None
    case_ids: list[str] = Field(default_factory=list)


class CalcRelation(str, Enum):
    eq = "="
    le = "≤"
    lt = "<"
    ge = "≥"
    gt = ">"
    iff = "↔"
    implies = "→"
    equiv_mod = "≡"


class CalcStep(BaseModel):
    lhs: str
    relation: CalcRelation
    rhs: str
    justification: str | None = None
    side_conditions: list[str] = Field(default_factory=list)


class CalculationData(ProofKindData):
    calculation_kind: str | None = None
    start: str | None = None
    target: str | None = None
    steps: list[CalcStep] = Field(default_factory=list)


class LocalClaimData(ProofKindData):
    statement: str
    proof_node_id: str | None = None
    label: str | None = None
```

---

## 10. Payload Registry

Create `registries/proof_registry.py`.

```python
from __future__ import annotations

from typing import Type

from pydantic import BaseModel

from mathdoc_agent.models.base import ProofKind
from mathdoc_agent.models.payloads import (
    ProofKindData,
    SimpleProofData,
    InductionData,
    CasesData,
    CalculationData,
    LocalClaimData,
)


class ProofPayloadRegistry:
    def __init__(self) -> None:
        self._models: dict[str, type[ProofKindData]] = {}

    def register(self, kind: str | ProofKind, model: type[ProofKindData]) -> None:
        self._models[str(kind.value if isinstance(kind, ProofKind) else kind)] = model

    def get(self, kind: str | ProofKind) -> type[ProofKindData] | None:
        return self._models.get(str(kind.value if isinstance(kind, ProofKind) else kind))

    def validate_data(self, kind: str | ProofKind, data: dict) -> ProofKindData | None:
        model = self.get(kind)
        if model is None:
            return None
        return model.model_validate(data)


proof_payload_registry = ProofPayloadRegistry()

proof_payload_registry.register(ProofKind.simple, SimpleProofData)
proof_payload_registry.register(ProofKind.induction, InductionData)
proof_payload_registry.register(ProofKind.cases, CasesData)
proof_payload_registry.register(ProofKind.calculation, CalculationData)
proof_payload_registry.register(ProofKind.local_claim, LocalClaimData)
```

This registry allows adding new proof kinds without changing the core proof node.

Similarly create a `DocumentPayloadRegistry`.

---

## 11. Run Logs and Provenance

Create `models/runs.py`.

```python
from __future__ import annotations

from datetime import datetime
from pydantic import BaseModel, Field


class AgentRunRecord(BaseModel):
    run_id: str
    timestamp: datetime = Field(default_factory=datetime.utcnow)

    agent_name: str
    target_node_id: str
    target_node_kind: str

    input_summary: str
    output_summary: str

    validation_ok: bool
    issues: list[str] = Field(default_factory=list)

    old_status: str | None = None
    new_status: str | None = None
```

Every accepted or rejected refinement should add a run log entry.

---

## 12. Validation Models

Create `models/validation.py`.

```python
from __future__ import annotations

from typing import Literal
from pydantic import BaseModel, Field


class ValidationIssue(BaseModel):
    severity: Literal["error", "warning", "info"]
    path: str
    message: str


class ValidationReport(BaseModel):
    ok: bool
    issues: list[ValidationIssue] = Field(default_factory=list)

    @classmethod
    def ok_report(cls) -> "ValidationReport":
        return cls(ok=True, issues=[])

    def has_errors(self) -> bool:
        return any(issue.severity == "error" for issue in self.issues)
```

---

## 13. Builders

Builders should deterministically construct well-formed nodes from agent-produced specs.

Create `builders/proof_builder.py`.

```python
from __future__ import annotations

from mathdoc_agent.models.base import ProofKind, NodeStatus
from mathdoc_agent.models.proof import ProofNode
from mathdoc_agent.models.payloads import (
    SimpleProofData,
    InductionData,
    CasesData,
    CalculationData,
    CalcStep,
    LocalClaimData,
)


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
    ) -> ProofNode:
        data = SimpleProofData(
            method=method,
            hints=hints or [],
        )

        return ProofNode(
            id=id,
            kind=ProofKind.simple,
            status=NodeStatus.resolved if hints else NodeStatus.classified,
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
```

---

## 14. Refinement Specs

Agents should generally return specs, not arbitrary replacement nodes.

Create `models/refinement_specs.py`.

```python
from __future__ import annotations

from pydantic import BaseModel, Field

from mathdoc_agent.models.base import ProofKind, DocumentKind
from mathdoc_agent.models.payloads import CalcStep


class ChildProofSpec(BaseModel):
    id_suffix: str
    kind: ProofKind = ProofKind.unknown
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


class DocumentChildSpec(BaseModel):
    id_suffix: str
    kind: DocumentKind = DocumentKind.unknown
    title: str | None = None
    label: str | None = None
    text: str
    notes: list[str] = Field(default_factory=list)


class DocumentRefinementSpec(BaseModel):
    children: list[DocumentChildSpec]
    notes: list[str] = Field(default_factory=list)
```

---

## 15. Context Objects

Create `orchestration/context.py`.

```python
from __future__ import annotations

from pydantic import BaseModel, Field


class DocumentContext(BaseModel):
    document_title: str | None = None
    ancestor_titles: list[str] = Field(default_factory=list)
    available_labels: list[str] = Field(default_factory=list)
    nearby_statements: list[str] = Field(default_factory=list)


class ProofContext(BaseModel):
    theorem_statement: str | None = None

    ancestor_goals: list[str] = Field(default_factory=list)
    inherited_hypotheses: list[str] = Field(default_factory=list)

    active_inductions: list[str] = Field(default_factory=list)
    active_cases: list[str] = Field(default_factory=list)

    local_claims: list[str] = Field(default_factory=list)
    available_document_results: list[str] = Field(default_factory=list)
```

The proof context must distinguish:

* outer induction hypotheses;
* nested induction hypotheses;
* active case assumptions;
* local lemmas/claims inside the proof;
* global lemmas/theorems available from the document.

---

## 16. Handler Interfaces

Create `handlers/base.py`.

```python
from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Generic, TypeVar

from mathdoc_agent.models.document import DocumentNode
from mathdoc_agent.models.proof import ProofNode
from mathdoc_agent.models.validation import ValidationReport
from mathdoc_agent.orchestration.context import DocumentContext, ProofContext


SpecT = TypeVar("SpecT")


class ProofRefinementHandler(ABC, Generic[SpecT]):
    kind: str
    output_model: type[SpecT] | None = None

    @abstractmethod
    async def refine(
        self,
        node: ProofNode,
        context: ProofContext,
    ) -> ProofNode:
        ...

    def validate(
        self,
        node: ProofNode,
        context: ProofContext,
    ) -> ValidationReport:
        return ValidationReport.ok_report()

    def is_resolved(
        self,
        node: ProofNode,
        context: ProofContext,
    ) -> bool:
        return False

    def child_context(
        self,
        parent: ProofNode,
        child: ProofNode,
        context: ProofContext,
    ) -> ProofContext:
        return context


class DocumentRefinementHandler(ABC, Generic[SpecT]):
    kind: str
    output_model: type[SpecT] | None = None

    @abstractmethod
    async def refine(
        self,
        node: DocumentNode,
        context: DocumentContext,
    ) -> DocumentNode:
        ...

    def validate(
        self,
        node: DocumentNode,
        context: DocumentContext,
    ) -> ValidationReport:
        return ValidationReport.ok_report()

    def is_resolved(
        self,
        node: DocumentNode,
        context: DocumentContext,
    ) -> bool:
        return False

    def child_context(
        self,
        parent: DocumentNode,
        child: DocumentNode,
        context: DocumentContext,
    ) -> DocumentContext:
        return context
```

---

## 17. Handler Registries

Create `registries/proof_handlers.py`.

```python
from __future__ import annotations

from mathdoc_agent.handlers.base import ProofRefinementHandler


class ProofHandlerRegistry:
    def __init__(self) -> None:
        self._handlers: dict[str, ProofRefinementHandler] = {}

    def register(self, kind: str, handler: ProofRefinementHandler) -> None:
        self._handlers[kind] = handler

    def get(self, kind: str) -> ProofRefinementHandler:
        if kind in self._handlers:
            return self._handlers[kind]
        return self._handlers["unknown"]

    def kinds(self) -> list[str]:
        return sorted(self._handlers.keys())


proof_handler_registry = ProofHandlerRegistry()
```

Do the same for document handlers.

---

## 18. Agent Runner Wrapper

Create `agents/runner.py`.

This wrapper isolates the Agents SDK dependency.

```python
from __future__ import annotations

from typing import Any, TypeVar

from pydantic import BaseModel

# If using the OpenAI Agents SDK:
from agents import Agent, Runner


T = TypeVar("T", bound=BaseModel)


async def run_agent_typed(
    agent: Agent,
    payload: BaseModel | dict[str, Any],
    output_type: type[T],
) -> T:
    if isinstance(payload, BaseModel):
        input_payload = payload.model_dump_json()
    else:
        input_payload = payload

    result = await Runner.run(agent, input_payload)
    output = result.final_output

    if isinstance(output, output_type):
        return output

    if isinstance(output, dict):
        return output_type.model_validate(output)

    if isinstance(output, str):
        return output_type.model_validate_json(output)

    return output_type.model_validate(output)
```

The SDK `Runner.run` returns a result object exposing `final_output`, among other result surfaces. Use `final_output` for typed structured outputs.

---

## 19. Agent Definitions

Create `agents/definitions.py`.

The actual model name should be configured externally.

```python
from __future__ import annotations

from agents import Agent

from mathdoc_agent.models.refinement_specs import (
    InductionRefinementSpec,
    CasesRefinementSpec,
    SimpleProofRefinementSpec,
    CalculationRefinementSpec,
    DocumentRefinementSpec,
)


MODEL = "gpt-5.5-thinking"


document_parser_agent = Agent(
    name="Document parser",
    model=MODEL,
    instructions="""
You decompose mathematical document text into a structured document tree.

Preserve the author's structure.
Do not invent mathematical content.
Classify sections, definitions, theorems, lemmas, proofs, remarks, examples, and paragraphs.
If unsure, use kind='unknown' and add a note.
""",
    output_type=DocumentRefinementSpec,
)


proof_classifier_agent = Agent(
    name="Proof classifier",
    model=MODEL,
    instructions="""
Classify one proof fragment into the most appropriate proof kind.

Do not deeply refine the proof.
If the fragment contains multiple proof structures, choose the outermost structure.
If unsure, use kind='unknown' and explain the uncertainty.
""",
)


induction_agent = Agent(
    name="Induction proof refiner",
    model=MODEL,
    instructions="""
Refine one proof fragment that is an induction proof.

Extract:
- induction variable;
- induction principle, if stated;
- induction hypotheses;
- base cases;
- step cases;
- child proof fragments.

Do not deeply refine child proofs. Assign each child a likely kind if obvious.
Preserve the original proof text.
Do not invent missing arguments.
""",
    output_type=InductionRefinementSpec,
)


cases_agent = Agent(
    name="Cases proof refiner",
    model=MODEL,
    instructions="""
Refine one proof fragment that is a case split.

Extract:
- the expression/proposition/condition split on;
- the cases;
- the case assumptions;
- an exhaustiveness reason, if stated;
- child proof fragments.

Do not deeply refine child proofs.
Do not invent missing cases.
""",
    output_type=CasesRefinementSpec,
)


simple_proof_agent = Agent(
    name="Simple proof refiner",
    model=MODEL,
    instructions="""
Refine a simple proof fragment.

Extract:
- method;
- hints;
- referenced lemmas;
- referenced hypotheses;
- unresolved details.

A simple proof may include phrases such as "by the previous lemma",
"by simplification", "by the induction hypothesis", or "immediate".
Do not expand omitted arguments unless they are explicitly present.
""",
    output_type=SimpleProofRefinementSpec,
)


calculation_agent = Agent(
    name="Calculation proof refiner",
    model=MODEL,
    instructions="""
Refine a calculational proof fragment.

Extract calculation steps:
- lhs;
- relation;
- rhs;
- justification;
- side conditions.

Do not invent omitted calculation steps.
If a calculation is only mentioned but not written, return no steps and record it as unresolved.
""",
    output_type=CalculationRefinementSpec,
)
```

---

## 20. Proof Handlers

### 20.1 Unknown handler

Create `handlers/proof_handlers.py`.

```python
from __future__ import annotations

from pydantic import BaseModel

from mathdoc_agent.handlers.base import ProofRefinementHandler
from mathdoc_agent.models.base import ProofKind, NodeStatus
from mathdoc_agent.models.proof import ProofNode
from mathdoc_agent.models.validation import ValidationReport
from mathdoc_agent.orchestration.context import ProofContext


class ClassificationSpec(BaseModel):
    kind: ProofKind
    confidence: float = 0.5
    notes: list[str] = []


class UnknownProofHandler(ProofRefinementHandler[ClassificationSpec]):
    kind = ProofKind.unknown.value
    output_model = ClassificationSpec

    def __init__(self, agent):
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        from mathdoc_agent.agents.runner import run_agent_typed

        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
                "task": "Classify this proof node by outermost proof structure.",
            },
            ClassificationSpec,
        )

        return node.model_copy(
            update={
                "kind": spec.kind,
                "status": NodeStatus.classified,
                "confidence": spec.confidence,
                "notes": node.notes + spec.notes,
            }
        )

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        return False
```

### 20.2 Induction handler

```python
from mathdoc_agent.builders.proof_builder import ProofBuilder
from mathdoc_agent.models.refinement_specs import InductionRefinementSpec


class InductionHandler(ProofRefinementHandler[InductionRefinementSpec]):
    kind = ProofKind.induction.value
    output_model = InductionRefinementSpec

    def __init__(self, agent):
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        from mathdoc_agent.agents.runner import run_agent_typed

        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
            },
            InductionRefinementSpec,
        )

        base_nodes = [
            ProofNode(
                id=f"{node.id}.{child.id_suffix}",
                kind=child.kind,
                status=NodeStatus.raw,
                text=child.text,
                goal=child.goal,
                hypotheses=child.hypotheses,
                notes=child.notes,
            )
            for child in spec.base_cases
        ]

        step_nodes = [
            ProofNode(
                id=f"{node.id}.{child.id_suffix}",
                kind=child.kind,
                status=NodeStatus.raw,
                text=child.text,
                goal=child.goal,
                hypotheses=child.hypotheses,
                notes=child.notes,
            )
            for child in spec.step_cases
        ]

        replacement = ProofBuilder.induction(
            id=node.id,
            text=node.text,
            variable=spec.variable,
            principle=spec.principle,
            induction_hypotheses=spec.induction_hypotheses,
            base_cases=base_nodes,
            step_cases=step_nodes,
            goal=node.goal,
            hypotheses=node.hypotheses,
        )

        return replacement.model_copy(
            update={"notes": node.notes + spec.notes}
        )

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        from mathdoc_agent.models.payloads import InductionData
        from mathdoc_agent.models.validation import ValidationIssue

        issues = []
        data = InductionData.model_validate(node.data)

        if not data.variable:
            issues.append(ValidationIssue(
                severity="error",
                path="data.variable",
                message="Induction node has no induction variable.",
            ))

        if not data.base_case_ids:
            issues.append(ValidationIssue(
                severity="error",
                path="data.base_case_ids",
                message="Induction node has no base cases.",
            ))

        if not data.step_case_ids:
            issues.append(ValidationIssue(
                severity="error",
                path="data.step_case_ids",
                message="Induction node has no step cases.",
            ))

        child_ids = {child.id for child in node.children}
        for cid in data.base_case_ids + data.step_case_ids:
            if cid not in child_ids:
                issues.append(ValidationIssue(
                    severity="error",
                    path="data",
                    message=f"Referenced child id {cid!r} is missing.",
                ))

        return ValidationReport(
            ok=not any(i.severity == "error" for i in issues),
            issues=issues,
        )

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        return bool(node.children) and all(
            child.status in {NodeStatus.resolved, NodeStatus.opaque}
            for child in node.children
        )

    def child_context(
        self,
        parent: ProofNode,
        child: ProofNode,
        context: ProofContext,
    ) -> ProofContext:
        from mathdoc_agent.models.payloads import InductionData

        data = InductionData.model_validate(parent.data)

        active_inductions = list(context.active_inductions)
        active_inductions.append(
            f"Induction on {data.variable}; IHs: {data.induction_hypotheses}"
        )

        inherited_hypotheses = list(context.inherited_hypotheses)
        inherited_hypotheses.extend(parent.hypotheses)

        return context.model_copy(
            update={
                "active_inductions": active_inductions,
                "inherited_hypotheses": inherited_hypotheses,
            }
        )
```

### 20.3 Cases handler

Implement analogously to the induction handler.

```python
class CasesHandler(ProofRefinementHandler[CasesRefinementSpec]):
    kind = ProofKind.cases.value
    output_model = CasesRefinementSpec

    def __init__(self, agent):
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        from mathdoc_agent.agents.runner import run_agent_typed

        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
            },
            CasesRefinementSpec,
        )

        case_nodes = [
            ProofNode(
                id=f"{node.id}.{child.id_suffix}",
                kind=child.kind,
                status=NodeStatus.raw,
                text=child.text,
                goal=child.goal,
                hypotheses=child.hypotheses,
                notes=child.notes,
            )
            for child in spec.cases
        ]

        replacement = ProofBuilder.cases(
            id=node.id,
            text=node.text,
            split_on=spec.split_on,
            exhaustive_reason=spec.exhaustive_reason,
            cases=case_nodes,
            goal=node.goal,
            hypotheses=node.hypotheses,
        )

        return replacement.model_copy(
            update={"notes": node.notes + spec.notes}
        )
```

### 20.4 Simple proof handler

```python
class SimpleProofHandler(ProofRefinementHandler[SimpleProofRefinementSpec]):
    kind = ProofKind.simple.value
    output_model = SimpleProofRefinementSpec

    def __init__(self, agent):
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        from mathdoc_agent.agents.runner import run_agent_typed
        from mathdoc_agent.models.payloads import SimpleProofData

        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
            },
            SimpleProofRefinementSpec,
        )

        data = SimpleProofData(
            method=spec.method,
            hints=spec.hints,
            referenced_lemmas=spec.referenced_lemmas,
            referenced_hypotheses=spec.referenced_hypotheses,
        )

        status = NodeStatus.resolved
        if spec.unresolved_details and not spec.hints:
            status = NodeStatus.locally_refined

        return node.model_copy(
            update={
                "kind": ProofKind.simple,
                "status": status,
                "data": data.model_dump(),
                "unresolved_details": node.unresolved_details + spec.unresolved_details,
            }
        )

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        from mathdoc_agent.models.payloads import SimpleProofData

        data = SimpleProofData.model_validate(node.data)
        return bool(data.hints or data.referenced_lemmas or data.referenced_hypotheses)
```

### 20.5 Calculation handler

```python
class CalculationHandler(ProofRefinementHandler[CalculationRefinementSpec]):
    kind = ProofKind.calculation.value
    output_model = CalculationRefinementSpec

    def __init__(self, agent):
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        from mathdoc_agent.agents.runner import run_agent_typed

        spec = await run_agent_typed(
            self.agent,
            {
                "node": node.model_dump(),
                "context": context.model_dump(),
            },
            CalculationRefinementSpec,
        )

        replacement = ProofBuilder.calculation(
            id=node.id,
            text=node.text,
            steps=spec.steps,
            goal=node.goal,
            hypotheses=node.hypotheses,
            calculation_kind=spec.calculation_kind,
        )

        return replacement.model_copy(
            update={
                "unresolved_details": node.unresolved_details + spec.unresolved_details
            }
        )

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        from mathdoc_agent.models.payloads import CalculationData
        from mathdoc_agent.models.validation import ValidationIssue

        issues = []
        data = CalculationData.model_validate(node.data)

        for i in range(1, len(data.steps)):
            prev_rhs = data.steps[i - 1].rhs.strip()
            curr_lhs = data.steps[i].lhs.strip()
            if curr_lhs != "_" and curr_lhs != prev_rhs:
                issues.append(ValidationIssue(
                    severity="warning",
                    path=f"data.steps[{i}].lhs",
                    message=(
                        f"Calculation step lhs {curr_lhs!r} does not match "
                        f"previous rhs {prev_rhs!r}."
                    ),
                ))

        return ValidationReport(
            ok=not any(issue.severity == "error" for issue in issues),
            issues=issues,
        )

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        from mathdoc_agent.models.payloads import CalculationData

        data = CalculationData.model_validate(node.data)
        return bool(data.steps) or bool(node.unresolved_details)
```

---

## 21. Document Handlers

Document handlers should decompose mathematical text into document nodes.

### 21.1 Theorem-like handler

A theorem-like document node may contain:

* a statement;
* assumptions;
* conclusion;
* optional label;
* proof.

If the proof text is present but unstructured, create a `ProofTree` with a raw root.

```python
from mathdoc_agent.models.document import DocumentNode
from mathdoc_agent.models.proof import ProofTree, ProofNode
from mathdoc_agent.models.base import DocumentKind, ProofKind, NodeStatus
from mathdoc_agent.models.payloads import StatementData


def make_theorem_node(
    *,
    id: str,
    kind: DocumentKind,
    text: str,
    statement: str,
    proof_text: str | None = None,
    label: str | None = None,
) -> DocumentNode:
    proof = None
    if proof_text:
        proof = ProofTree(
            id=f"{id}.proof",
            theorem_statement=statement,
            root=ProofNode(
                id=f"{id}.proof.root",
                kind=ProofKind.unknown,
                status=NodeStatus.raw,
                text=proof_text,
                goal=statement,
            ),
        )

    return DocumentNode(
        id=id,
        kind=kind,
        status=NodeStatus.decomposed if proof else NodeStatus.classified,
        label=label,
        text=text,
        data=StatementData(statement=statement).model_dump(),
        proof=proof,
    )
```

### 21.2 Proofs inside proofs

A proof may contain local claims or lemmas.

Represent a local claim as a `ProofNode`, not necessarily a `DocumentNode`, unless you want every local claim to share the full document model.

Example:

```text
We first prove the following claim.
Claim. For every x, Q(x).
Proof. ...
Now using the claim, ...
```

Represent as:

```text
ProofNode(kind="local_claim")
  data.statement = "For every x, Q(x)"
  children = [
    ProofNode(kind="unknown", text="Proof of the claim...")
  ]
```

This keeps local proof structure inside the proof tree.

---

## 22. Orchestration

### 22.1 Tree traversal helpers

Create `orchestration/worklist.py`.

```python
from __future__ import annotations

from collections.abc import Iterator

from mathdoc_agent.models.proof import ProofNode
from mathdoc_agent.models.document import DocumentNode
from mathdoc_agent.models.base import NodeStatus


def walk_proof_nodes(root: ProofNode) -> Iterator[ProofNode]:
    yield root
    for child in root.children:
        yield from walk_proof_nodes(child)


def walk_document_nodes(root: DocumentNode) -> Iterator[DocumentNode]:
    yield root
    for child in root.children:
        yield from walk_document_nodes(child)
    if root.proof is not None:
        # Document traversal may choose to expose proof roots separately.
        pass


def find_proof_node(root: ProofNode, node_id: str) -> ProofNode | None:
    for node in walk_proof_nodes(root):
        if node.id == node_id:
            return node
    return None


def replace_proof_node(root: ProofNode, node_id: str, replacement: ProofNode) -> ProofNode:
    if root.id == node_id:
        return replacement

    return root.model_copy(
        update={
            "children": [
                replace_proof_node(child, node_id, replacement)
                for child in root.children
            ]
        }
    )


def unresolved_proof_nodes(root: ProofNode) -> list[ProofNode]:
    return [
        node for node in walk_proof_nodes(root)
        if node.status not in {NodeStatus.resolved, NodeStatus.opaque}
    ]
```

### 22.2 Choosing the next proof node

```python
from mathdoc_agent.models.base import ProofKind, NodeStatus


def proof_node_priority(node: ProofNode) -> tuple[int, int, int]:
    status_rank = {
        NodeStatus.raw: 0,
        NodeStatus.classified: 1,
        NodeStatus.decomposed: 2,
        NodeStatus.locally_refined: 3,
        NodeStatus.validated: 4,
    }.get(node.status, 9)

    kind_rank = {
        ProofKind.unknown: 0,
        ProofKind.induction: 1,
        ProofKind.cases: 1,
        ProofKind.local_claim: 2,
        ProofKind.extensionality: 2,
        ProofKind.existence: 2,
        ProofKind.uniqueness: 2,
        ProofKind.calculation: 3,
        ProofKind.simple: 4,
    }.get(node.kind, 9)

    return (status_rank, kind_rank, -len(node.text))


def choose_next_proof_node(root: ProofNode) -> ProofNode | None:
    candidates = unresolved_proof_nodes(root)
    if not candidates:
        return None
    return sorted(candidates, key=proof_node_priority)[0]
```

---

## 23. Context Building

Create `orchestration/context.py`.

Add path computation.

```python
def path_to_proof_node(root: ProofNode, node_id: str) -> list[ProofNode] | None:
    if root.id == node_id:
        return [root]

    for child in root.children:
        subpath = path_to_proof_node(child, node_id)
        if subpath is not None:
            return [root] + subpath

    return None
```

Build proof context by walking ancestors.

```python
from mathdoc_agent.models.payloads import InductionData, CasesData, LocalClaimData


def build_proof_context(
    proof_tree: ProofTree,
    node_id: str,
    available_document_results: list[str] | None = None,
) -> ProofContext:
    path = path_to_proof_node(proof_tree.root, node_id)
    if path is None:
        return ProofContext(theorem_statement=proof_tree.theorem_statement)

    ancestor_goals = []
    inherited_hypotheses = []
    active_inductions = []
    active_cases = []
    local_claims = []

    for ancestor in path[:-1]:
        if ancestor.goal:
            ancestor_goals.append(ancestor.goal)

        inherited_hypotheses.extend(ancestor.hypotheses)

        if ancestor.kind == ProofKind.induction:
            try:
                data = InductionData.model_validate(ancestor.data)
                active_inductions.append(
                    f"Induction on {data.variable}; IHs: {data.induction_hypotheses}"
                )
            except Exception:
                pass

        if ancestor.kind == ProofKind.cases:
            try:
                data = CasesData.model_validate(ancestor.data)
                active_cases.append(f"Case split on {data.split_on}")
            except Exception:
                pass

        if ancestor.kind == ProofKind.local_claim:
            try:
                data = LocalClaimData.model_validate(ancestor.data)
                local_claims.append(data.statement)
            except Exception:
                pass

    return ProofContext(
        theorem_statement=proof_tree.theorem_statement,
        ancestor_goals=ancestor_goals,
        inherited_hypotheses=inherited_hypotheses,
        active_inductions=active_inductions,
        active_cases=active_cases,
        local_claims=local_claims,
        available_document_results=available_document_results or [],
    )
```

---

## 24. Proof Orchestrator

Create `orchestration/proof_orchestrator.py`.

```python
from __future__ import annotations

from mathdoc_agent.models.proof import ProofTree, ProofNode
from mathdoc_agent.models.base import NodeStatus, ProofKind
from mathdoc_agent.models.validation import ValidationReport
from mathdoc_agent.registries.proof_handlers import ProofHandlerRegistry
from mathdoc_agent.orchestration.worklist import (
    choose_next_proof_node,
    replace_proof_node,
)
from mathdoc_agent.orchestration.context import build_proof_context


def mark_opaque(node: ProofNode, reason: str) -> ProofNode:
    return node.model_copy(
        update={
            "kind": ProofKind.opaque,
            "status": NodeStatus.opaque,
            "notes": node.notes + [reason],
        }
    )


async def refine_one_proof_node(
    proof_tree: ProofTree,
    node: ProofNode,
    registry: ProofHandlerRegistry,
    available_document_results: list[str] | None = None,
) -> ProofTree:
    context = build_proof_context(
        proof_tree,
        node.id,
        available_document_results=available_document_results,
    )

    handler = registry.get(node.kind.value if hasattr(node.kind, "value") else str(node.kind))

    candidate = await handler.refine(node, context)
    report = handler.validate(candidate, context)

    if not report.ok:
        # Initial implementation: mark opaque.
        # Later implementation: call repair handler.
        candidate = mark_opaque(
            node,
            "Marked opaque after failed validation: "
            + "; ".join(issue.message for issue in report.issues),
        )

    new_root = replace_proof_node(proof_tree.root, node.id, candidate)
    new_tree = proof_tree.model_copy(update={"root": new_root})
    return recompute_proof_statuses(new_tree, registry)


async def refine_proof_tree(
    proof_tree: ProofTree,
    registry: ProofHandlerRegistry,
    available_document_results: list[str] | None = None,
    max_iterations: int = 100,
) -> ProofTree:
    tree = recompute_proof_statuses(proof_tree, registry)

    for _ in range(max_iterations):
        node = choose_next_proof_node(tree.root)
        if node is None:
            break

        tree = await refine_one_proof_node(
            tree,
            node,
            registry,
            available_document_results=available_document_results,
        )

    return recompute_proof_statuses(tree, registry)
```

Status recomputation:

```python
def recompute_proof_node_status(
    node: ProofNode,
    proof_tree: ProofTree,
    registry: ProofHandlerRegistry,
) -> ProofNode:
    children = [
        recompute_proof_node_status(child, proof_tree, registry)
        for child in node.children
    ]

    node = node.model_copy(update={"children": children})

    if node.kind == ProofKind.opaque:
        return node.model_copy(update={"status": NodeStatus.opaque})

    context = build_proof_context(proof_tree, node.id)
    handler = registry.get(node.kind.value if hasattr(node.kind, "value") else str(node.kind))

    if handler.is_resolved(node, context):
        return node.model_copy(update={"status": NodeStatus.resolved})

    if node.children:
        return node.model_copy(update={"status": NodeStatus.decomposed})

    if node.kind != ProofKind.unknown:
        return node.model_copy(update={"status": NodeStatus.classified})

    return node.model_copy(update={"status": NodeStatus.raw})


def recompute_proof_statuses(
    proof_tree: ProofTree,
    registry: ProofHandlerRegistry,
) -> ProofTree:
    root = recompute_proof_node_status(proof_tree.root, proof_tree, registry)
    return proof_tree.model_copy(update={"root": root})
```

---

## 25. Document Orchestration

The document orchestrator should refine document structure first, then refine proofs attached to theorem-like nodes.

Recommended high-level flow:

```text
1. Parse whole document into top-level document tree.
2. Refine each document node until definitions/theorems/proofs are identified.
3. For each theorem-like node with proof text:
   a. initialize ProofTree;
   b. run proof orchestrator;
   c. attach refined ProofTree back to document node.
4. If a proof contains local lemmas/claims:
   refine them inside the proof tree.
5. Recompute document statuses.
```

Document nodes may be resolved when:

* their children are resolved;
* their attached proof tree, if any, is resolved;
* their payload validates.

---

## 26. Nested Lemmas Inside Proofs

A local lemma inside a proof should be represented as a `ProofNode(kind="local_claim")`.

Example input:

```text
We first prove a claim.

Claim. For every m, Q(m).
Proof. By induction on m...

Using the claim, the theorem follows.
```

Expected proof tree:

```text
root: proof
  child 1: local_claim
    data.statement = "For every m, Q(m)"
    child: induction proof of Q(m)
  child 2: simple
    references: local claim
```

Implementation behavior:

1. A proof handler or classifier detects “Claim.”
2. It creates a `local_claim` node.
3. The local claim node has a child proof node.
4. The context builder makes the local claim available to later sibling nodes.

This requires sibling-aware context. Initial implementation can collect local claims from ancestor nodes only. Improved implementation should collect earlier sibling local claims.

Add this function later:

```python
def earlier_sibling_local_claims(
    proof_tree: ProofTree,
    node_id: str,
) -> list[str]:
    # Find parent and siblings before node.
    # Return statements of local_claim siblings that occur earlier.
    ...
```

Then include these in `ProofContext.local_claims`.

---

## 27. Extension Mechanism for New Proof Types

Each new proof type should provide:

1. a proof kind name;
2. a payload model;
3. an optional refinement spec model;
4. a builder function;
5. a handler;
6. validation rules;
7. status-resolution logic;
8. optional context propagation logic.

Example skeleton:

```python
from pydantic import BaseModel, Field

from mathdoc_agent.handlers.base import ProofRefinementHandler
from mathdoc_agent.models.proof import ProofNode
from mathdoc_agent.models.validation import ValidationReport
from mathdoc_agent.orchestration.context import ProofContext


class NewProofTypeData(BaseModel):
    important_field: str | None = None
    child_ids: list[str] = Field(default_factory=list)


class NewProofTypeSpec(BaseModel):
    important_field: str | None = None
    children: list[ChildProofSpec] = Field(default_factory=list)


class NewProofTypeHandler(ProofRefinementHandler[NewProofTypeSpec]):
    kind = "new_proof_type"
    output_model = NewProofTypeSpec

    def __init__(self, agent):
        self.agent = agent

    async def refine(self, node: ProofNode, context: ProofContext) -> ProofNode:
        ...

    def validate(self, node: ProofNode, context: ProofContext) -> ValidationReport:
        ...

    def is_resolved(self, node: ProofNode, context: ProofContext) -> bool:
        ...
```

Register it:

```python
proof_payload_registry.register("new_proof_type", NewProofTypeData)
proof_handler_registry.register("new_proof_type", NewProofTypeHandler(agent))
```

The orchestration loop must not change.

---

## 28. Extension Mechanism for New Calculation Types

Calculation types should not usually be new `ProofKind`s. Prefer:

```python
ProofKind.calculation
data.calculation_kind = "telescoping_sum"
```

The detailed taxonomy of calculation kinds is external.

Register calculation validators separately:

```python
class CalculationKindValidator:
    calculation_kind: str

    def validate(self, data: CalculationData) -> ValidationReport:
        ...


class CalculationKindRegistry:
    def __init__(self):
        self._validators = {}

    def register(self, kind: str, validator: CalculationKindValidator):
        self._validators[kind] = validator

    def validate(self, data: CalculationData) -> ValidationReport:
        if data.calculation_kind in self._validators:
            return self._validators[data.calculation_kind].validate(data)
        return ValidationReport.ok_report()
```

The generic `CalculationHandler` should call this registry after generic chain validation.

---

## 29. Repair Loop

Initial implementation may mark invalid nodes opaque. The next stage should add repair.

Repair request:

```python
from pydantic import BaseModel

class RepairRequest(BaseModel):
    old_node: ProofNode
    candidate: ProofNode
    context: ProofContext
    issues: list[ValidationIssue]


class RepairSpec(BaseModel):
    replacement: ProofNode
    explanation: str
```

Repair flow:

```text
candidate = handler.refine(node, context)
report = handler.validate(candidate, context)

if not report.ok:
    repaired = repair_agent(candidate, issues)
    report2 = handler.validate(repaired, context)

if report2.ok:
    accept repaired
else:
    mark opaque
```

Do not allow unlimited repair loops. Use at most one or two repair attempts.

---

## 30. Deterministic Validators

Implement deterministic validators before relying on LLM validators.

Examples:

### 30.1 Unique IDs

```python
def validate_unique_proof_ids(root: ProofNode) -> ValidationReport:
    seen = set()
    issues = []

    for node in walk_proof_nodes(root):
        if node.id in seen:
            issues.append(ValidationIssue(
                severity="error",
                path=node.id,
                message=f"Duplicate proof node id {node.id!r}.",
            ))
        seen.add(node.id)

    return ValidationReport(
        ok=not any(issue.severity == "error" for issue in issues),
        issues=issues,
    )
```

### 30.2 Referenced child IDs exist

Each handler should validate its own child ID references.

### 30.3 Calculation adjacency

```python
def validate_calculation_adjacency(data: CalculationData) -> ValidationReport:
    issues = []

    for i in range(1, len(data.steps)):
        prev_rhs = data.steps[i - 1].rhs.strip()
        curr_lhs = data.steps[i].lhs.strip()

        if curr_lhs != "_" and curr_lhs != prev_rhs:
            issues.append(ValidationIssue(
                severity="warning",
                path=f"steps[{i}].lhs",
                message=f"Expected lhs to be {prev_rhs!r}, got {curr_lhs!r}.",
            ))

    return ValidationReport(
        ok=True,
        issues=issues,
    )
```

---

## 31. Export

### 31.1 JSON export

All models should serialize through Pydantic:

```python
json_text = document.model_dump_json(indent=2)
```

### 31.2 Markdown export

Implement a readable Markdown renderer that preserves structure.

Example:

```python
def render_proof_node_md(node: ProofNode, indent: int = 0) -> str:
    pad = "  " * indent
    lines = [
        f"{pad}- **{node.kind}** `{node.id}` [{node.status}]",
    ]

    if node.goal:
        lines.append(f"{pad}  - Goal: `{node.goal}`")

    if node.hypotheses:
        lines.append(f"{pad}  - Hypotheses: {', '.join(node.hypotheses)}")

    if node.notes:
        lines.append(f"{pad}  - Notes: {'; '.join(node.notes)}")

    for child in node.children:
        lines.append(render_proof_node_md(child, indent + 1))

    return "\n".join(lines)
```

### 31.3 Lean export

Do not attempt full Lean generation initially. Instead export a skeleton:

```text
theorem ... := by
  -- proof kind: induction
  induction n with
  | zero =>
      -- base case hints
  | succ n ih =>
      -- step case hints
```

Lean export should be a separate pass over the refined tree.

---

## 32. Minimal End-to-End Example

Input:

```text
Theorem. For all n, P(n).
Proof. We prove this by induction on n. The base case follows from L0.
For the step, assume P(n). We split into cases according to Q(n).
In the first case, we prove a claim by induction on m. The base case is H1,
and the step follows by the induction hypothesis.
In the second case, split further on R. If R, use L2. If not R, the result
follows by calculation.
The remaining case follows from the induction hypothesis and L3.
```

Expected refinement sequence:

```text
1. Document parser:
   theorem node with attached raw proof tree.

2. Proof classifier:
   proof root classified as induction.

3. Induction handler:
   root decomposed into base case and step case.

4. Simple handler:
   base case resolved with hint L0.

5. Cases handler:
   step case decomposed into cases on Q(n).

6. Induction handler:
   first case decomposed as nested induction on m.

7. Cases handler:
   second case decomposed as nested case split on R.

8. Simple/calculation handlers:
   leaves refined as simple hints or calculation blocks.

9. Status recomputation:
   all leaves resolved;
   nested structures resolved bottom-up;
   proof tree resolved;
   theorem node resolved.
```

Expected tree shape:

```text
Document theorem
└── ProofTree
    └── induction on n
        ├── base case: simple, use L0
        └── step case: cases on Q(n)
            ├── case 1: induction on m
            │   ├── base: simple, use H1
            │   └── step: simple, use nested IH
            ├── case 2: cases on R
            │   ├── R: simple, use L2
            │   └── not R: calculation
            └── case 3: simple, use outer IH and L3
```

---

## 33. Tests to Implement

### 33.1 Model tests

* `ProofNode` round-trips through JSON.
* `DocumentNode` with attached `ProofTree` round-trips through JSON.
* payload registries validate known payloads.
* unknown payloads do not crash the system.

### 33.2 Builder tests

* induction builder creates valid child ID references.
* cases builder creates valid case references.
* calculation builder sets start and target.

### 33.3 Handler tests

Use fake agents returning fixed specs.

* unknown handler classifies a raw node.
* induction handler decomposes a node.
* cases handler decomposes a node.
* simple handler marks hint-based proof resolved.
* calculation handler extracts steps.

### 33.4 Orchestrator tests

Use fake handlers.

Test nested proof:

```text
induction
  step
    cases
      case
        induction
      case
        cases
      case
        simple
```

Assert that:

* worklist terminates;
* root becomes resolved;
* all IDs are unique;
* local contexts include active inductions and cases.

### 33.5 Local lemma tests

Input proof with local claim.

Assert:

* local claim is represented as a `ProofNode(kind="local_claim")`;
* its child proof is refined;
* later proof nodes can see the local claim in context.

---

## 34. Implementation Order

Implement in this order:

1. Core models.
2. Payload registries.
3. Builders.
4. Deterministic tree utilities.
5. Handler interfaces and registries.
6. Fake handlers for tests.
7. Proof orchestrator.
8. Document orchestrator.
9. Agent wrapper.
10. Real agents for:

    * document parsing;
    * unknown proof classification;
    * induction;
    * cases;
    * simple proofs;
    * calculations.
11. Validation and repair.
12. Local claim support.
13. Plugin loading.
14. Exporters.

---

## 35. Non-Goals for the First Version

Do not implement full formal proof checking initially.

Do not attempt complete Lean proof generation initially.

Do not include a full taxonomy of proof types or calculation types in the core code.

Do not let agents rewrite the whole document tree repeatedly.

Do not require all proof leaves to be fully formal. It is acceptable to have:

```text
simple proof with hints
opaque proof fragment
calculation mentioned but not expanded
standard argument, unresolved
```

The first target is a faithful, inspectable, structured decomposition.

---

## 36. Key Architectural Invariant

The central invariant is:

```text
Every refinement step replaces exactly one node with a more structured node,
or marks it opaque.
```

All global behavior follows from that:

```text
document tree remains stable;
proof tree remains inspectable;
agent failures are local;
new proof types are plugins;
validation is modular;
orchestration is generic.
```

This invariant should be maintained throughout the implementation.

```

A small note: if you use the OpenAI Agents SDK, use structured outputs for the refinement specs and keep Python in control of the iteration loop. The official SDK docs describe Agents as model configurations with instructions/tools/handoffs, Runner results exposing `final_output`, and output schemas that validate/parse JSON into output types; those are the relevant pieces for this design. :contentReference[oaicite:0]{index=0}
::contentReference[oaicite:1]{index=1}
```
