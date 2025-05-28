import LeanAide.Codegen
import LeanAide.StructToLean
/-!
# Code generation for LeanAide "PaperStructure" schema

To Do:

* For existential types in `have` statements, use `rcases` to separate the variable and its properties.
* Have a clear way to specify used results, and use them in the proof.
* Handle theorems with deferred proofs, i.e., where the proof is not immediately after the theorem.
* Refine `cases` to separate `if`, multiple `if`s and patterns.
-/
open Lean Meta Qq Elab Term

namespace LeanAide

open Codegen Translate

@[codegen "assumption_statement"]
def assumptionCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let .ok assumption :=
    js.getObjValAs? String "assumption" | throwError
    s!"codegen: no assumption found in {js}"
  addPrelude assumption
  return none

open Lean.Parser.Tactic

@[codegen "document"]
def documentCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getArr? | throwError "document must be a JSON array"
  getCodeCommands translator none  content.toList
| _, kind, _ => throwError
    s!"codegen: documentCode does not work for kind {kind}"

@[codegen "title","abstract", "remark", "metadata", "author", "bibliography", "citation", "internalreference"]
def noGenCode := noCode

/- Section
{
  "type": "object",
  "description": "A section of the document.",
  "properties": {
    "type": {
      "type": "string",
      "const": "Section",
      "description": "The type of this document element."
    },
    "content": {
      "type": "array",
      "description": "The content of the section.",
      "items": {
        "anyOf": [
          {
            "$ref": "#/$defs/Section"
          },
          {
            "$ref": "#/$defs/Theorem"
          },
          {
            "$ref": "#/$defs/Definition"
          },
          {
            "$ref": "#/$defs/Remark"
          },
          {
            "$ref": "#/$defs/LogicalStepSequence"
          },
          {
            "$ref": "#/$defs/Paragraph"
          },
          {
            "$ref": "#/$defs/Proof"
          },
          {
            "$ref": "#/$defs/Figure"
          },
          {
            "$ref": "#/$defs/Table"
          }
        ]
      }
    },
    "label": {
      "type": "string",
      "description": "Section identifier."
    },
    "level": {
      "type": "integer",
      "description": "The section level such as `1` for a section, `2` for a subsection."
    },
    "header": {
      "type": "string",
      "description": "The section header."
    }
  },
  "required": [
    "type",
    "label",
    "header",
    "content"
  ],
  "additionalProperties": false
}
-/
@[codegen "section"]
def sectionCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getObjValAs? (List Json) "content" | throwError "section must have content"
  getCodeCommands translator none  content
| _, kind, _ => throwError
    s!"codegen: sectionCode does not work for kind {kind}"


/- Theorem
{
  "type": "object",
  "description": "A mathematical theorem, lemma, proposition, corollary, or claim.",
  "properties": {
    "type": {
      "type": "string",
      "const": "Theorem",
      "description": "The type of this document element."
    },
    "hypothesis": {
      "type": "array",
      "description": "(OPTIONAL) The hypothesis or assumptions of the theorem, consisting of statements like 'let', 'assume', etc.",
      "items": {
        "anyOf": [
          {
            "$ref": "#/$defs/let_statement"
          },
          {
            "$ref": "#/$defs/assume_statement"
          },
          {
            "$ref": "#/$defs/some_statement"
          }
        ]
      }
    },
    "claim": {
      "type": "string",
      "description": "The statement."
    },
    "label": {
      "type": "string",
      "description": "Unique identifier/label for referencing (e.g., 'thm:main', 'lem:pumping')."
    },
    "proof_steps": {
          "type": "array",
          "description": "Steps in the proof, if the proof is present soon after the theorem.",
          "items": {
            "anyOf": [
              { "$ref": "#/$defs/Remark" },
              { "$ref": "#/$defs/LogicalStepSequence" },
              { "$ref": "#/$defs/Paragraph" },
              { "$ref": "#/$defs/Figure" },
              { "$ref": "#/$defs/Table" }
            ]
          }
        },
    "header": {
      "type": "string",
      "description": "The type of theorem-like environment. Must be one of the predefined values.",
      "enum": [
        "Theorem",
        "Lemma",
        "Proposition",
        "Corollary",
        "Claim"
      ]
    },
    "citations": {
      "type": "array",
      "description": "(OPTIONAL) Explicit list of citations relevant to this statement.",
      "items": {
        "$ref": "#/$defs/Citation"
      }
    },
    "internal_references": {
      "type": "array",
      "description": "(OPTIONAL) Explicit list of internal references mentioned in the statement.",
      "items": {
        "$ref": "#/$defs/InternalReference"
      }
    }
  },
  "required": [
    "type",
    "label",
    "header",
    "claim"
  ],
  "additionalProperties": false
}
-/

#eval "Hello".toName ++ ("World".toName)

@[codegen "theorem"]
def theoremCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, `command, js => do
  let (stx, name, pf?) ← thmStxParts js goal
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(command| theorem $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propIdent := mkIdent `Prop
    `(command| abbrev $n : $propIdent := $stx)
| some goal, `commandSeq, js => do
  let (stx, name, pf?) ← thmStxParts js goal
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(commandSeq| theorem $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propIdent := mkIdent `Prop
    `(commandSeq| abbrev $n : $propIdent := $stx)

| some goal, ``tacticSeq, js => do
  let (stx, name, pf?) ← thmStxParts js goal
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(tacticSeq| have $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propIdent := mkIdent `Prop
    `(tacticSeq| let $n : $propIdent := $stx)
| some goal, `tactic, js => do
  let (stx, name, pf?) ← thmStxParts js goal
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(tactic| have $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propIdent := mkIdent `Prop
    `(tactic| let $n : $propIdent := $stx)
| _, _, _ => throwError
    s!"codegen: theorem does not work"
where
  thmStxParts (js: Json) (goal: MVarId) :
    TranslateM <| Syntax.Term × Name × Option (TSyntax ``tacticSeq)  := withoutModifyingState do
    match js.getObjVal?  "hypothesis" with
      | Except.ok h => contextRun translator none ``tacticSeq h
      | Except.error _ => pure ()
    let .ok  claim := js.getObjValAs? String "claim" | throwError
      s!"codegen: no claim found in {js}"
    let proofSteps? :=
      js.getObjValAs? (List Json) "proof_steps" |>.toOption
    let proofStx? ← proofSteps?.mapM fun
      proofSteps => getCodeTactics translator goal proofSteps
    let thm ← withPreludes claim
    let .ok type ← translator.translateToProp? thm | throwError
        s!"codegen: no translation found for {thm}"
    let type ← instantiateMVars type
    Term.synthesizeSyntheticMVarsNoPostponing
    if type.hasSorry || type.hasExprMVar then
      throwError s!"Failed to infer type {type} has sorry or mvar"
    let univ ← try
      withoutErrToSorry do
      if type.hasSorry then
        throwError "Type has sorry"
      inferType type
    catch e =>
      throwError s!"Failed to infer type {type}, error {← e.toMessageData.format}"
    if univ.isSort then
      let type ←  dropLocalContext type
      -- IO.eprintln s!"Type: {← PrettyPrinter.ppExpr type}"
      let name ← translator.server.theoremName thm
      let typeStx ← PrettyPrinter.delab type
      let label := js.getObjString? "label" |>.getD name.toString
      Translate.addTheorem <| {name := name, type := type, label := label, isProved := true}
      return (typeStx, name, proofStx?)
    else
      IO.eprintln s!"Not a type: {type}"
      throwError s!"codegen: no translation found for {js}"

#check commandToTactic

/- Definition
{
  "type": "object",
  "description": "A mathematical definition.",
  "properties": {
    "type": {
      "type": "string",
      "const": "Definition",
      "description": "The type of this document element."
    },
    "definition": {
      "type": "string",
      "description": "Definition content."
    },
    "label": {
      "type": "string",
      "description": "Definition identifier."
    },
    "header": {
      "type": "string",
      "description": "The definition type.",
      "enum": [
        "Definition",
        "Notation",
        "Terminology",
        "Convention"
      ]
    },
    "citations": {
      "type": "array",
      "description": "(OPTIONAL) Explicit list of citations relevant to this theorem statement.",
      "items": {
        "$ref": "#/$defs/Citation"
      }
    },
    "internal_references": {
      "type": "array",
      "description": "(OPTIONAL) Explicit list of internal references mentioned in the theorem statement.",
      "items": {
        "$ref": "#/$defs/InternalReference"
      }
    }
  },
  "required": [
    "type",
    "label",
    "header",
    "definition"
  ],
  "additionalProperties": false
}
-/
@[codegen "definition"]
def defCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let stx ← defCmdStx js
  `(command| $stx)
| _, `commandSeq, js => do
  let stx ← defCmdStx js
  let stxs := #[stx]
  `(commandSeq | $stxs*)
| _, ``tacticSeq, js => do
  let stx ← defCmdStx js
  let tac ← commandToTactic stx
  let tacs := #[tac]
  `(tacticSeq| $tacs*)
| _, `tactic, js => do
  let stx ← defCmdStx js
  let tac ← commandToTactic stx
  `(tactic| $tac)
| _, _, _ => throwError
    s!"codegen: theorem does not work"
where
  defCmdStx (js: Json) :
    TranslateM <| Syntax.Command :=
    withoutModifyingState do
    let .ok statement :=
      js.getObjValAs? String "definition" | throwError
        s!"codegen: no definition found in {js}"
    let .ok cmd ←
      translator.translateDefCmdM? statement | throwError
        s!"codegen: no translation found for {statement}"
    return cmd


/- LogicalStepSequence
{
  "type": "array",
  "description": "A sequence of structured logical steps, typically used within a proof or derivation, consisting of statements like 'let', 'assert', 'assume', etc.",
  "items": {
    "anyOf": [
      {
        "$ref": "#/$defs/let_statement"
      },
      {
        "$ref": "#/$defs/assert_statement"
      },
      {
        "$ref": "#/$defs/assume_statement"
      },
      {
        "$ref": "#/$defs/some_statement"
      },
      {
        "$ref": "#/$defs/cases_statement"
      },
      {
        "$ref": "#/$defs/induction_statement"
      },
      {
        "$ref": "#/$defs/calculate_statement"
      },
      {
        "$ref": "#/$defs/contradiction_statement"
      },
      {
        "$ref": "#/$defs/conclude_statement"
      }
    ]
  }
}
-/
@[codegen "section"]
def logicalStepCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getArr? | throwError "logicalStepCode must be a JSON array"
  getCodeCommands translator none  content.toList
| some goal, ``tacticSeq, js => do
  let .ok content := js.getArr? | throwError "logicalStepCode must be a JSON array"
  getCodeTactics translator goal  content.toList
| goal?, kind, _ => throwError
    s!"codegen: logicalStepCode does not work for kind {kind}where goal present: {goal?.isSome}"

/- Proof
{
  "type": "object",
  "description": "A proof environment.",
  "properties": {
    "type": {
      "type": "string",
      "const": "Proof",
      "description": "The type of this document element."
    },
    "claim_label": {
      "type": "string",
      "description": "Theorem label being proved."
    },
    "proof_steps": {
      "type": "array",
      "description": "Steps in the proof.",
      "items": {
        "anyOf": [
          {
            "$ref": "#/$defs/Remark"
          },
          {
            "$ref": "#/$defs/LogicalStepSequence"
          },
          {
            "$ref": "#/$defs/Paragraph"
          },
          {
            "$ref": "#/$defs/Figure"
          },
          {
            "$ref": "#/$defs/Table"
          }
        ]
      }
    }
  },
  "required": [
    "type",
    "claim_label",
    "proof_steps"
  ],
  "additionalProperties": false
}
-/
@[codegen "proof"]
def proofCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getObjValAs? (List Json) "proof_steps" | throwError "missing or invalid proof_steps"
  let .ok claimLabel := js.getObjValAs? String "claim_label" | throwError
    s!"codegen: no claim_label found in {js}"
  let some labelledTheorem ← findTheorem? claimLabel | throwError
    s!"codegen: no theorem found with label {claimLabel}"
  let goalType := labelledTheorem.type

  let goalExpr ← mkFreshExprMVar goalType
  let goal := goalExpr.mvarId!
  let pfStx ← getCodeTactics translator goal content
  let n := mkIdent labelledTheorem.name
  let typeStx ← PrettyPrinter.delab goalType
  `(commandSeq| theorem $n : $typeStx := by $pfStx)
| some goal, ``tacticSeq, js => do
  let .ok content := js.getObjValAs? (List Json) "proof_steps" | throwError "missing or invalid proof_steps"
  getCodeTactics translator goal  content
| goal?, kind, _ => throwError
    s!"codegen: proofCode does not (yet) work for kind {kind}where goal present: {goal?.isSome}"


/- let_statement
{
  "type": "object",
  "description": "A statement introducing a new variable with given value, type and/or property.",
  "properties": {
    "type": {
      "type": "string",
      "const": "let_statement",
      "description": "The type of this logical step."
    },
    "variable": {
      "type": "string",
      "description": "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"
    },
    "value": {
      "type": "string",
      "description": "(OPTIONAL) The value of the variable being defined"
    },
    "kind": {
      "type": "string",
      "description": "(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc."
    },
    "properties": {
      "type": "string",
      "description": "(OPTIONAL) Specific properties of the variable beyond the type"
    }
  },
  "required": [
    "type",
    "variable"
  ],
  "additionalProperties": false
}
-/
@[codegen "let_statement"]
def letCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let statement :=
    match js.getObjValAs? String "statement" with
    | Except.ok s => s
    | Except.error _ =>
      let varSegment := match js.getObjString? "variable_name" with
      | some "<anonymous>" => "We have "
      | some v => s!"Let {v} be"
      | _ => "We have "
    let kindSegment := match js.getObjValAs? String "variable_type" with
      | Except.ok k => s!"a {k}"
      | Except.error _ => s!""
    let valueSegment := match js.getObjString? "value" with
      | some v => s!"{v}"
      | _ => ""
    let propertySegment := match js.getObjString? "properties" with
      | some p => s!"(such that) {p}"
      | _ => ""
    s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}".trim ++ "."
  addPrelude statement
  return none


/- some_statement
{
  "type": "object",
  "description": "A statement introducing a new variable and saying that **some** value of this variable is as required (i.e., an existence statement). This is possibly with given type and/or property. This corresponds to statements like 'for some integer `n` ...' or 'There exists an integer `n` ....'",
  "properties": {
    "type": {
      "type": "string",
      "const": "some_statement",
      "description": "The type of this logical step."
    },
    "variable": {
      "type": "string",
      "description": "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"
    },
    "kind": {
      "type": "string",
      "description": "(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc."
    },
    "properties": {
      "type": "string",
      "description": "(OPTIONAL) Specific properties of the variable beyond the type"
    }
  },
  "required": [
    "type",
    "variable"
  ],
  "additionalProperties": false
}
-/
@[codegen "some_statement"]
def someCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let statement :=
    match js.getObjValAs? String "statement" with
    | Except.ok s => s
    | Except.error _ =>
      let varSegment := match js.getObjString? "variable_name" with
      | some "<anonymous>" => "We have "
      | some v => s!"Let {v} be"
      | _ => "We have "
    let kindSegment := match js.getObjValAs? String "variable_kind" with
      | Except.ok k => s!"a {k}"
      | Except.error _ => s!""
    let propertySegment := match js.getObjString? "properties" with
      | some p => s!"(such that) {p}"
      | _ => ""
    s!"{varSegment} {kindSegment} {propertySegment}".trim ++ "."
  addPrelude statement
  return none


/- assume_statement
{
  "type": "object",
  "description": "A mathematical assumption being made. Use 'let_statement' or 'some_statement' if introducing variables.",
  "properties": {
    "type": {
      "type": "string",
      "const": "assume_statement",
      "description": "The type of this logical step."
    },
    "assumption": {
      "type": "string",
      "description": "The assumption text."
    },
    "label": {
      "type": "string",
      "description": "(OPTIONAL) The label of the assumption, if any."
    },
    "citations": {
      "type": "array",
      "description": "(OPTIONAL) Citations supporting or related to the assumption.",
      "items": {
        "$ref": "#/$defs/Citation"
      }
    },
    "internal_references": {
      "type": "array",
      "description": "(OPTIONAL) Internal references related to the assumption.",
      "items": {
        "$ref": "#/$defs/InternalReference"
      }
    }
  },
  "required": [
    "type",
    "assumption"
  ],
  "additionalProperties": false
}
-/
@[codegen "assume_statement"]
def assumeCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let .ok statement :=
      js.getObjValAs? String "assumption" | throwError ""
  addPrelude statement
  return none


/- assert_statement
{
  "type": "object",
  "description": "A mathematical statement whose proof is a straightforward consequence of given and known results following some method.",
  "properties": {
    "type": {
      "type": "string",
      "const": "assert_statement",
      "description": "The type of this logical step."
    },
    "claim": {
      "type": "string",
      "description": "The mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained."
    },
    "proof_method": {
      "type": "string",
      "description": "(OPTIONAL) The method used to prove the claim. This could be a direct proof, proof by contradiction, proof by induction, etc. this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use `citations`or `internal_references`."
    },
    "label": {
      "type": "string",
      "description": "The label of the statement, if any. If this statement is used in a proof or as justification for an assertion, it should be labeled so that it can be referenced later."
    },
    "citations": {
      "type": "array",
      "description": "(OPTIONAL) Explicit list of citations relevant to this theorem statement.",
      "items": {
        "$ref": "#/$defs/Citation"
      }
    },
    "results_used": {
      "type": "array",
      "description": "(OPTIONAL) Explicit list of internal references used in the proof, for example where the assertion says \"using ...\".",
      "items": {
        "$ref": "#/$defs/InternalReference"
      }
    },
    "internal_references": {
      "type": "array",
      "description": "(OPTIONAL) Explicit list of internal references mentioned in the theorem statement.",
      "items": {
        "$ref": "#/$defs/InternalReference"
      }
    },
    "calculate": {
      "$ref": "#/$defs/calculate_choice",
      "description": "(OPTIONAL) An equation, inequality, short calculation etc."
    }
  },
  "required": [
    "type",
    "claim"
  ],
  "additionalProperties": false
}
-/
-- Very basic version; should add references to `auto?` as well as other modifications as in `StructToLean`
@[codegen "assertion_statement"]
def assertionCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let stx ← typeStx js
  `(command| example : $stx := by sorry)
| _, `commandSeq, js => do
  let stx ← typeStx js
  `(commandSeq| example : $stx := by sorry)
| _, ``tacticSeq, js => do
  let stx ← typeStx js
  `(tacticSeq| have : $stx := bysorry)
| _, `tactic, js => do
  let stx ← typeStx js
  `(tactic| have : $stx := bysorry)
| _, _, _ => throwError
    s!"codegen: test does not work"
where typeStx (js: Json) : TranslateM Syntax.Term := do
  let .ok  claim := js.getObjValAs? String "claim" | throwError
    s!"codegen: no claim found in {js}"
  let .ok type ← translator.translateToProp? claim | throwError
      s!"codegen: no translation found for {claim}"
  let type ← instantiateMVars type
  Term.synthesizeSyntheticMVarsNoPostponing
  if type.hasSorry || type.hasExprMVar then
    throwError s!"Failed to infer type {type} has sorry or mvar"
  let univ ← try
    withoutErrToSorry do
    if type.hasSorry then
      throwError "Type has sorry"
    inferType type
  catch e =>
    throwError s!"Failed to infer type {type}, error {← e.toMessageData.format}"
  if univ.isSort then
    let type ←  dropLocalContext type
    -- IO.eprintln s!"Type: {← PrettyPrinter.ppExpr type}"
    PrettyPrinter.delab type
  else
    IO.eprintln s!"Not a type: {type}"
    throwError s!"codegen: no translation found for {js}"

/- calculate_choice
{
  "type": "object",
  "description": "An equation, inequality, short calculation etc.",
  "minProperties": 1,
  "maxProperties": 1,
  "properties": {
    "inline_calculation": {
      "type": "string",
      "description": "A simple calculation or computation written as a single line."
    },
    "calculation_sequence": {
      "type": "array",
      "description": "A list of elements of type `calculation_step`.",
      "items": {
        "$ref": "#/$defs/calculation_step"
      }
    }
  }
}
-/

/- calculation_step
{
  "type": "string",
  "description": "A step, typically an equality or inequality, in a calculation or computation."
}
-/

/- cases_statement
{
  "type": "object",
  "description": "A proof by cases or proof by induction, with a list of cases.",
  "properties": {
    "type": {
      "type": "string",
      "const": "cases_statement",
      "description": "The type of this logical step."
    },
    "split_kind": {
      "type": "string",
      "description": "one of 'implication_direction' (for two sides of an 'iff' implication), 'match' (for pattern matching), 'condition' (if based on a condition being true or false) and 'groups' (for more complex cases).",
      "enum": [
        "implication_direction",
        "match",
        "condition",
        "groups"
      ]
    },
    "on": {
      "type": "string",
      "description": "The variable or expression on which the cases are being done. Write 'implication direction' for an 'iff' statement."
    },
    "proof_cases": {
      "type": "array",
      "description": "A list of elements of type `case`.",
      "items": {
        "$ref": "#/$defs/case"
      }
    },
    "exhaustiveness": {
      "$ref": "#/$defs/Proof",
      "description": "(OPTIONAL) Proof that the cases are exhaustive."
    }
  },
  "required": [
    "type",
    "split_kind",
    "on",
    "proof_cases"
  ],
  "additionalProperties": false
}
-/

/- case
{
  "type": "object",
  "description": "A case in a proof by cases or proof by induction.",
  "properties": {
    "type": {
      "type": "string",
      "const": "case",
      "description": "The type of this logical step."
    },
    "condition": {
      "type": "string",
      "description": "The case condition or pattern; for induction one of 'base' or 'induction-step'; for a side of an 'iff' statement write the claim being proved (i.e., the statement `P => Q` or `Q => P`)."
    },
    "proof": {
      "type": "array",
      "description": "Steps proving this case.",
      "items": {
        "anyOf": [
          {
            "$ref": "#/$defs/LogicalStepSequence"
          },
          {
            "$ref": "#/$defs/Paragraph"
          },
          {
            "$ref": "#/$defs/Proof"
          },
          {
            "$ref": "#/$defs/Figure"
          },
          {
            "$ref": "#/$defs/Table"
          },
          {
            "$ref": "#/$defs/Remark"
          }
        ]
      }
    }
  },
  "required": [
    "type",
    "condition",
    "proof"
  ],
  "additionalProperties": false
}
-/

/- induction_statement
{
  "type": "object",
  "description": "A proof by induction, with a base case and an induction step.",
  "properties": {
    "type": {
      "type": "string",
      "const": "induction_statement",
      "description": "The type of this logical step."
    },
    "on": {
      "type": "string",
      "description": "The variable or expression on which induction is being done."
    },
    "proof_cases": {
      "type": "array",
      "description": "A list of elements of type `case`.",
      "items": {
        "$ref": "#/$defs/case"
      }
    }
  },
  "required": [
    "type",
    "on",
    "proof_cases"
  ],
  "additionalProperties": false
}
-/

/- contradiction_statement
{
  "type": "object",
  "description": "A proof by contradiction, with an assumption and a proof of the contradiction.",
  "properties": {
    "type": {
      "type": "string",
      "const": "contradiction_statement",
      "description": "The type of this logical step."
    },
    "assumption": {
      "type": "string",
      "description": "The assumption being made to be contradicted."
    },
    "proof": {
      "$ref": "#/$defs/Proof",
      "description": "The proof of the contradiction given the assumption."
    }
  },
  "required": [
    "type",
    "assumption",
    "proof"
  ],
  "additionalProperties": false
}
-/

/- calculate_statement
{
  "type": "object",
  "properties": {
    "type": {
      "type": "string",
      "const": "calculate_statement",
      "description": "The type of this logical step."
    },
    "calculation": {
      "$ref": "#/$defs/calculate_choice",
      "description": "An equation, inequality, short calculation etc."
    }
  },
  "required": [
    "type",
    "calculation"
  ],
  "additionalProperties": false
}
-/

/- conclude_statement
{
  "type": "object",
  "description": "Conclude a claim obtained from the steps so far. This is typically the final statement of a proof giving the conclusion of the theorem.",
  "properties": {
    "type": {
      "type": "string",
      "const": "conclude_statement",
      "description": "The type of this logical step."
    },
    "claim": {
      "type": "string",
      "description": "The conclusion of the proof."
    }
  },
  "required": [
    "type",
    "claim"
  ],
  "additionalProperties": false
}
-/


/- Figure
{
  "type": "object",
  "description": "A figure or image.",
  "properties": {
    "type": {
      "type": "string",
      "const": "Figure",
      "description": "The type of this document element."
    },
    "label": {
      "type": "string",
      "description": "Unique identifier/label for referencing (e.g., 'fig:flowchart')."
    },
    "source": {
      "type": "string",
      "description": "URL or path to the image file."
    },
    "caption": {
      "type": "string",
      "description": "(OPTIONAL) Caption describing the figure."
    },
    "alt_text": {
      "type": "string",
      "description": "(OPTIONAL) Alternative text for accessibility."
    }
  },
  "required": [
    "type",
    "label",
    "source"
  ],
  "additionalProperties": false
}
-/

/- Table
{
  "type": "object",
  "description": "A data table.",
  "properties": {
    "type": {
      "type": "string",
      "const": "Table",
      "description": "The type of this document element."
    },
    "label": {
      "type": "string",
      "description": "Unique identifier/label for referencing (e.g., 'tab:results')."
    },
    "caption": {
      "type": "string",
      "description": "(OPTIONAL) Caption describing the table."
    },
    "content": {
      "type": "array",
      "description": "Table data, represented as an array of rows, where each row is an array of cell strings.",
      "items": {
        "type": "array",
        "items": {
          "type": "string"
        }
      }
    },
    "header_row": {
      "type": "boolean",
      "description": "(OPTIONAL) Indicates if the first row in 'content' is a header row. Default: false",
      "default": false
    }
  },
  "required": [
    "type",
    "label",
    "content"
  ],
  "additionalProperties": false
}
-/


-- -- older code, should not be used
-- def metaDataFields := ["author", "date", "title", "abstract", "keywords", "authors", "affiliations", "acknowledgements", "msc_codes", "publication_date", "doi", "arxiv_id", "url", "source", "header", "entries"]

-- @[codegen]
-- def metaNoCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
-- | _, js => do
--   match js.getObj? with
--   | .ok obj =>
--     let keys := obj.toArray.map (fun ⟨ k, _⟩  => k)
--     let nonMetaKeys := keys.filter (fun k => !metaDataFields.contains k)
--     if nonMetaKeys.isEmpty then
--       return none
--     else
--       throwError s!"codegen: no metadata found in {js}, extra keys: {nonMetaKeys}"
--   | .error _ => do
--   throwError s!"codegen: no metadata found in {js}"
