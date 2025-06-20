import LeanAide.Codegen
import LeanAide.StructToLean
import Hammer
/-!
# Code generation for LeanAide "PaperStructure" schema

This module provides code generation for the LeanAide "PaperStructure" schema, which includes sections, theorems, definitions, logical steps, proofs, and other elements of a mathematical document.

Each function corresponds to a specific JSON schema element and generates the appropriate Lean code. The tag `codegen` is used to mark these functions for code generation with argument the key.
-/
open Lean Meta Qq Elab Term

namespace LeanAide

open Codegen Translate

/--
Translating to a proposition in Lean, using the `translateToProp?` method of the `Translator`. Various checks are performed to ensure the type is valid and does not contain `sorry` or metavariables. An error is thrown if the translation fails or if the type is not valid.
-/
def Translator.translateToPropStrictAux
    (claim: String)(translator : Translator)
    : TranslateM Expr := do
  let thm ← withPreludes claim
  IO.eprintln s!"Translating to proposition: {claim}, full statement: {thm}"
  let (js, _, _) ← translator.getLeanCodeJson  thm
  let output ← getMessageContents js
  for out in output do
    let el? ← elabThm4 out
    match el? with
    | Except.error _ =>
      continue
    | Except.ok type =>
      let type ← instantiateMVars type
      Term.synthesizeSyntheticMVarsNoPostponing
      if type.hasSorry || (← type.hasUnassignedExprMVar) then
        throwError s!"Failed to infer type {type} has sorry or mvar when translating assertion '{claim}', full statement {thm}"
      let univ ← try
        Term.withoutErrToSorry do
        if type.hasSorry then
          throwError "Type {type} has sorry when translating assertion '{claim}', full statement {thm}"
        inferType type
      catch e =>
        throwError s!"Failed to infer type {type}, error {← e.toMessageData.format} when translating assertion '{claim}', full statement {thm}"
      if univ.isSort then
        IO.eprintln s!"Obtained type: {← ppExpr type}"
        let type ← dropLocalContext type
        IO.eprintln s!"Obtained type in local context: {← ppExpr type}"
        return type
      else
        throwError s!"codegen: not a type {type} when translating assertion '{claim}', full statement {thm}"
  throwError s!"codegen: no valid type found for assertion '{claim}', full statement {thm}; all translations: {output}"

def Translator.translateToPropStrict
    (claim: String)(translator : Translator)
    : TranslateM Expr := do
    try
      Translator.translateToPropStrictAux claim translator
    catch e =>
      let fullClaim ← translator.server.fullStatement claim
      try
        Translator.translateToPropStrictAux fullClaim translator
      catch e' =>
        -- If the translation fails, we throw an error with the original claim and the error message.
        -- This is useful for debugging and understanding what went wrong.
        throwError s!"codegen: failed to translate '{claim}' to a proposition even with 'full statement', error: {← e.toMessageData.format}; full claim: {fullClaim}, error: {← e'.toMessageData.format}"


def consumeIntros (goal: MVarId) (maxDepth : Nat)
    (accum: List Name) : TranslateM <| MVarId × List Name := do
  match maxDepth, ← goal.getType with
  | 0, _ =>
    return (goal, accum)
  | k + 1, Expr.forallE n type _ _ => do
    let n := if n.isInternal then n.components[0]! else n
    addPrelude s!"Fix {n} : {← ppExpr type}"
    let (_, goal') ← goal.intro n
    consumeIntros goal' k (accum ++ [n])
  | k + 1, Expr.letE n type value _ _ => do
    let n := if n.isInternal then n.components[0]! else n
    addPrelude s!"Fix {n} : {← ppExpr type} := {← ppExpr value}"
    let (_, goal') ← goal.intro n
    consumeIntros goal' k (accum ++ [n])
  | _, _ => do
    return (goal, accum)
open Lean.Parser.Tactic


/-
"ResultUsed": {
  "type": "object",
  "properties": {
    "statement": {
      "type": "string",
      "description": "The statement of the result used."
    },
    "target_identifier": {
      "type": "string",
      "description": "(OPTIONAL) The unique 'label' of the document element being referenced (e.g., 'sec:intro', 'thm:main', 'fig:,diagram')."
    },
    "mathlib_identifier": {
      "type": "string",
      "description": "(OPTIONAL) The name of the result being used in Lean Prover or its library Mathlib)."
    }
  },
  "required": [
    "statement"
  ],
  "additionalProperties": false
},
-/
def getResultUsed? (translator: Translator) (js: Json) : TranslateM (Option Syntax.Term) := do
  let targetIdentifier? := js.getObjValAs? String "target_identifier"
  let mathlibIdentifier? := js.getObjValAs? String "mathlib_identifier"
  match targetIdentifier?, mathlibIdentifier? with
  | .error _, .error _ =>
    let .ok statement := js.getObjValAs? String "statement" | throwError "'ResultUsed' must have 'statement'"
    let type ← translator.translateToPropStrict statement
    getExactTerm? type
  | _, .ok mathlibIdentifier =>
    return mkIdent mathlibIdentifier.toName
  | .ok targetIdentifier, _ =>
    let l? ← findTheorem? targetIdentifier
    return l?.map fun l =>
      mkIdent l.name

def getResultsUsed (translator: Translator) (js: Json) : TranslateM (Array Syntax.Term) := do
  match js.getObjValAs? (Array Json) "results_used" with
  | .error _ => return #[]
  | .ok resultsUsed =>
    resultsUsed.filterMapM fun js =>
      getResultUsed? translator js

@[codegen "document"]
def documentCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getArr? | throwError "'document' must be a JSON array"
  getCodeCommands translator none  content.toList
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok content := js.getArr? | throwError "'document' must be a JSON array"
  getCodeTactics translator goal  content.toList
| _, kind, _ => throwError
    s!"codegen: 'document' does not work for kind {kind}"

@[codegen "title","abstract", "remark", "metadata", "author", "bibliography", "citation", "internalreference", "paragraph", "figure", "table", "image"]
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
def sectionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getObjValAs? (List Json) "content" | throwError "'section' must have 'content'"
  getCodeCommands translator none  content
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok content := js.getObjValAs? (List Json) "content" | throwError "'section' must have 'content'"
  getCodeTactics translator goal  content
| _, kind, _ => throwError
    s!"codegen: 'section' does not work for kind {kind}"


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
    "proof" : {
          "$ref": "#/$defs/Proof",
          "description": "Proof of the theorems, if it is present soon after the statement."
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

@[codegen "theorem"]
def theoremCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let (stx, name, pf?) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(command| theorem $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(command| abbrev $n : $propIdent:term := $stx)
| _, `commandSeq, js => do
  let (stx, name, pf?) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(commandSeq| theorem $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(commandSeq| abbrev $n : $propIdent:term := $stx)

| some _, ``tacticSeq, js => do
  let (stx, name, pf?) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(tacticSeq| have $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(tacticSeq| let $n : $propIdent := $stx)
| some _, `tactic, js => do
  let (stx, name, pf?) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(tactic| have $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(tactic| let $n : $propIdent := $stx)
| goal?, kind, _ => throwError
    s!"codegen: 'theorem' does not work for kind {kind}where goal present: {goal?.isSome}"
where
  thmStxParts (js: Json)  :
    TranslateM <| Syntax.Term × Name × Option (TSyntax ``tacticSeq)  := withoutModifyingState do
    match js.getObjVal?  "hypothesis" with
      | Except.ok h => contextRun translator none ``tacticSeq h
      | Except.error _ => pure ()
    let .ok  claim := js.getObjValAs? String "claim" | throwError
      s!"codegen: no 'claim' found in 'theorem'"
    let thm ← withPreludes claim
    let type ← translator.translateToPropStrict claim
    let proof? :=
      js.getObjVal? "proof" |>.toOption
    let pfGoal ← mkFreshExprMVar type
    let hypSize ←
      match js.getObjValAs? (Array Json)  "hypothesis" with
      | Except.ok h =>
        IO.eprintln s!"hypothesis: {h} in proof"
        contextRun translator none ``tacticSeq (.arr h)
        -- IO.eprintln "Preludes added:"
        -- IO.eprintln <| ← withPreludes ""
        pure h.size
      | Except.error _ => pure 0
    IO.eprintln s!"hypothesis size: {hypSize} in proof"
    let (pfGoal', names') ← extractIntros pfGoal.mvarId! hypSize
    let (pfGoal, names) ← consumeIntros pfGoal' 10 names'
    let proofStx? ← proof?.mapM fun
      pf => withoutModifyingState do
      let pfStx ←  match ←
        getCode translator pfGoal ``tacticSeq (Json.mkObj [("proof", pf)]) with
      | some pfStx =>
        let pfStx ←  if names.isEmpty then
            pure pfStx
          else
            let namesStx : List <| TSyntax `term ←
              names.mapM fun n =>
                if n.isInaccessibleUserName || n.isInternal then
                  `(_)
                else do
                  IO.eprintln s!"Adding intro for {n}, not inaccessible"
                  let n' := mkIdent n
                  `($n':ident)
            let namesStx := namesStx.toArray
            let introTac ←
              `(tacticSeq| intro $namesStx*)
            appendTactics introTac pfStx
        pure pfStx
      | none => throwError
        s!"codegen: no proof translation found for {pf}"
      pure pfStx
    let name ← translator.server.theoremName thm
    let name :=
      if name.toString = "[anonymous]" then
        let hash := thm.hash
        let name := s!"thm_{hash}"
        name.toName
      else
        name
    IO.eprintln s!"codegen: Theorem name: {name} for {thm}"
    let typeStx ← delabDetailed type
    let label := js.getObjString? "label" |>.getD name.toString
    Translate.addTheorem <| {name := name, type := type, label := label, isProved := true, source:= js}
    logInfo m!"All theorems : {← allLabels}"
    return (typeStx, name, proofStx?)

-- #check commandToTactic

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
def defCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
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
| _, kind, _ => throwError
    s!"codegen: 'definition' does not work for kind {kind}"
where
  defCmdStx (js: Json) :
    TranslateM <| Syntax.Command :=
    withoutModifyingState do
    let .ok statement :=
      js.getObjValAs? String "definition" | throwError
        s!"codegen: no 'definition' found in 'definition'"
    let cmd ← match
      ← translator.translateDefCmdM? statement with
      | .ok cmd => pure cmd
      | .error errs => throwError
        let outputs := errs.map (·.text)
        s!"codegen: no definition translation found for {statement}; outputs: {outputs}"
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
@[codegen "logicalstepsequence"]
def logicalStepCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getObjValAs? (Array Json) "items" | throwError "logicalStepSequence must have an `items` field that is a JSON array"
  getCodeCommands translator none  content.toList
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok content := js.getObjValAs? (Array Json) "items" | throwError "logicalStepSequence must have an `items` field that is a JSON array"
  getCodeTactics translator goal  content.toList
| goal?, kind, _ => throwError
    s!"codegen: logicalStepSequence does not work for kind {kind}where goal present: {goal?.isSome}"

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
def proofCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getObjValAs? (List Json) "proof_steps" | throwError "missing or invalid 'proof_steps' in 'proof'"
  let .ok claimLabel := js.getObjValAs? String "claim_label" | throwError
    s!"codegen: no 'claim_label' found in standalone 'proof'"
  let some labelledTheorem ← findTheorem? claimLabel | throwError
    s!"codegen: no theorem found with label {claimLabel}; all labels {← allLabels}"
  let goalType := labelledTheorem.type
  let goalExpr ← mkFreshExprMVar goalType
  let goal := goalExpr.mvarId!
  -- IO.eprintln s!"number of proof steps: {content.length}"
  let hypSize ←
    match labelledTheorem.source.getObjValAs? (Array Json)  "hypothesis" with
      | Except.ok h =>
        IO.eprintln s!"hypothesis: {h} in proof"
        contextRun translator none ``tacticSeq (.arr h)
        -- IO.eprintln "Preludes added:"
        -- IO.eprintln <| ← withPreludes ""
        pure h.size
      | Except.error _ => pure 0
  IO.eprintln s!"hypothesis size: {hypSize} in proof"
  let (goal, names) ← extractIntros goal hypSize
  let pfStx ←
    withoutModifyingState do
    getCodeTactics translator goal content
  let pfStx ←  if names.isEmpty then
      pure pfStx
    else
      let namesStx : List <| TSyntax `term ←
        names.mapM fun n =>
          if n.isInaccessibleUserName || n.isInternal then
            `(_)
          else do
            IO.eprintln s!"Adding intro for {n}, not inaccessible"
            let n' := mkIdent n
            `($n':ident)
      let namesStx := namesStx.toArray
      let introTac ←
        `(tacticSeq| intro $namesStx*)
      appendTactics introTac pfStx
  IO.eprintln s!"Proof steps: {← PrettyPrinter.ppCategory ``tacticSeq pfStx}"
  let n := mkIdent labelledTheorem.name
  let typeStx ← delabDetailed goalType
  `(commandSeq| theorem $n : $typeStx := by $pfStx)
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok content := js.getObjValAs? (List Json) "proof_steps" | throwError "missing or invalid 'proof_steps' in 'proof'"
  withoutModifyingState do
  getCodeTactics translator goal  content
| goal?, kind, _ => throwError
    s!"codegen: proof does not work for kind {kind}where goal present: {goal?.isSome}"

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
    "variable_name": {
      "type": "string",
      "description": "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"
    },
    "value": {
      "type": "string",
      "description": "(OPTIONAL) The value of the variable being defined"
    },
    "variable_type": {
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
def letCode (translator : CodeGenerator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)) := fun s js => do
  match s, js with
  | ``tacticSeq, js => do
    let statement := statement js
    match js.getObjString? "value" with
    | none =>
      -- If there is no value, we do not need to return a value
      IO.eprintln s!"codegen: No value in 'let_statement' for {js.getObjString? "variable_name" |>.getD ""}"
      addPrelude statement
      return none
    | some value =>
      let letStx ←
        commandToTactic
          (← defStx translator js statement value)
      let stxs := #[letStx]
      addPrelude statement
      return some <| ← `(tacticSeq| $stxs*)
  | ``commandSeq, js => do
    let statement := statement js
    match js.getObjString? "value" with
    | none =>
      -- If there is no value, we do not need to return a value
      IO.eprintln s!"codegen: No value in 'let_statement' for {js.getObjString? "variable_name" |>.getD ""}"
      addPrelude statement
      return none
    | some value =>
      let defStx ←
          defStx translator js statement value
      let stxs := #[defStx]
      match ← DefData.ofSyntax? defStx with
      | some data =>
        -- If we have a definition, we add it to the definitions
        -- and return the command
        addDefn data
      | none =>
        IO.eprintln s!"codegen: No definition found for 'let_statement' {statement} with value {value}"
      addPrelude statement
      return some <| ← `(commandSeq| $stxs*)

  | _, js =>
      addPrelude <| statement js
      return none
  where
    statement (js: Json) : String :=
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
        let propertySegment := match js.getObjString? "properties", js.getObjString? "variable_name" with
          | some p, some v =>
            if v != "<anonymous>"
              then s!"(such that) ({v} is) {p}"
              else s!"(such that) {p}"
          | _, _ => ""
        s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}".trim ++ "."
    defStx (translator: CodeGenerator) (js: Json) (statement: String)  (value: String) : TranslateM Syntax.Command :=
      withoutModifyingState do
        let statement' ← withPreludes statement
        let varName ← match js.getObjString? "variable_name" with
        | some "<anonymous>" => pure "_"
        | some v => pure v
        | _ => throwError s!"codegen: no 'variable_name' found in 'let_statement' for {js}"
        let statement' := statement'.trim ++ "\n" ++ s!"Define ONLY the term {varName} with value {value}. Other terms have been defined already."

        let stx? ← translator.translateDefCmdM? statement'
        match stx? with
        | .ok stx =>
          IO.eprintln s!"codegen: 'let_statement' {statement'} translated to command:\n{← PrettyPrinter.ppCommand stx}"
          return stx
        | .error es =>
          let fallback ← try
            CmdElabError.fallback es
          catch _ =>
            IO.eprintln s!"codegen: 'let_statement' {statement'} fallback failed"
            let output := es.map fun e => e.text
            throwError
              s!"codegen: no fallback for 'let_statement' {statement'}; output: {output} "
          match Parser.runParserCategory (← getEnv) `command fallback with
          | .ok stx =>
            let stx: Syntax.Command := ⟨stx⟩
            return stx
          |.error er =>
            IO.eprintln s!"codegen: 'let_statement' {statement'} translation failed with error:\n{er} and fallback:\n{fallback}"
            IO.eprintln s!"codegen: 'let_statement' {statement'} translation attempts:\n"
            for e in es do
              IO.eprintln s!"codegen: not a command:\n{e.text}"
            throwError
              s!"codegen: no definition translation found for {statement'}"

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
    "variable_name": {
      "type": "string",
      "description": "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"
    },
    "variable_kind": {
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
def someCode (translator : CodeGenerator := {})(goal : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| kind, js => do
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
  let assJs := Json.mkObj [
    ("type", "assert_statement"),
    ("claim", .str statement)
  ]
  addPrelude statement
  getCode translator goal kind assJs


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
def assumeCode (_ : CodeGenerator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let .ok statement :=
      js.getObjValAs? String "assumption" | throwError "No 'assumption' found in 'assume_statement'"
  addPrelude <| "Assume that: " ++ statement
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
      "$ref": "#/$defs/calculate",
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

@[codegen "assert_statement"]
def assertionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let (stx, tac) ← typeStx js
  `(command| example : $stx := by $tac)
| _, `commandSeq, js => do
  let (stx, tac) ← typeStx js
  let hash₀ := hash stx.raw.reprint
  let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let head ← `(command| theorem $name : $stx := by $tac)
  let dfn: DefData :=
    { name := "assert_{hash₀}".toName, type := stx, value := stx, isProp := true, isNoncomputable := false, doc? := none}
  addDefn dfn
  let resolvedCmds ←
    CodeGenerator.cmdResolveExistsHave stx
  toCommandSeq <| #[head] ++ resolvedCmds
| _, ``tacticSeq, js => do
  let (stx, tac) ← typeStx js
  let hash₀ := hash stx.raw.reprint
  let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let headTac ← `(tactic| have $name : $stx := by $tac)
  let resTacs ← CodeGenerator.resolveExistsHave stx
  let tacSeq := #[headTac] ++ resTacs
  `(tacticSeq| $tacSeq*)
| _, `tactic, js => do
  let (stx, tac) ← typeStx js
  `(tactic| have : $stx := by $tac)
| _, kind, _ => throwError
    s!"codegen: test does not work for kind {kind}"
where typeStx (js: Json) :
    TranslateM <| Syntax.Term × (TSyntax ``tacticSeq) :=
      withoutModifyingState do
  let .ok  claim := js.getObjValAs? String "claim" | throwError
    s!"codegen: no claim found in 'assertion_statement'"
  let type ← translator.translateToPropStrict claim
  let resultsUsed ←
    getResultsUsed translator.toTranslator js
  let tac ← `(tactic| hammer [ $resultsUsed,* ])
  let tacs ← runTacticsAndGetTryThisI (type) #[tac]
  return (← delabDetailed type, ← `(tacticSeq| $tacs*))

/- calculation
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
@[codegen "calculation"]
def calculationCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``tacticSeq, js => do
  let tac ← `(tacticSeq | first | linarith | ring | norm_num | simp | omega | rfl)
  match js.getObjVal? "inline_calculation" with
  | Except.ok <| .str inline =>
    -- let .ok inline := inlineJs.getObjValAs? String "inline_calculation" | throwError
    --   s!"codegen: no 'inline_calculation' string found in 'calculation'"
    let stx ← typeStx inline
    let hash₀ := hash stx.raw.reprint
    let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
    let headTac ← `(tactic| have $name : $stx := by $tac)
    let tacSeq := #[headTac]
    `(tacticSeq| $tacSeq*)
  | Except.ok js =>
    throwError
      s!"codegen: 'calculation' must have 'inline_calculation' as a string, got {js}"
  | Except.error _ =>
    let .ok steps := js.getObjValAs? (Array String) "calculation_sequence" | throwError
      s!"codegen: no 'calculation_sequence' found in 'calculation'"
    let mut tacs : Array <| Syntax.Tactic := #[]
    for step in steps do
      let stx ← typeStx step
      let hash₀ := hash stx.raw.reprint
      let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
      let headTac ← `(tactic| have $name : $stx := by $tac)
      tacs := tacs.push headTac
    `(tacticSeq| $tacs*)
| _, kind, _ => throwError
    s!"codegen: test does not work for kind {kind}"
where typeStx (eqn: String) :
    TranslateM <| Syntax.Term  := do
  let claim := "Have " ++ eqn ++ "."
  let type ← translator.translateToPropStrict claim
  delabDetailed type


/-     "pattern_cases_statement": {
      "type": "object",
      "description": "A proof by cases, with cases determined by matching a pattern.",
      "properties": {
        "type": {
          "type": "string",
          "const": "pattern_cases_statement",
          "description": "The type of this logical step."
        },
        "on": {
          "type": "string",
          "description": "The variable or expression which is being matched against patterns."
        },
        "proof_cases": {
          "type": "array",
          "description": "A list of elements of type `case`.",
          "items": {
            "$ref": "#/$defs/pattern_case"
          }
        },
      "required": [
        "type",
        "on",
        "proof_cases"
      ],
      "additionalProperties": false
    },
-/
open Lean.Parser.Term CodeGenerator Parser
@[codegen "pattern_cases_statement"]
def patternCasesCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok discr := js.getObjValAs? String "on" | throwError
    s!"codegen: no 'on' found in 'pattern_cases_statement'"
  let .ok patternCases := js.getObjValAs? (Array Json) "proof_cases" | throwError
    s!"codegen: no 'proof_cases' found in 'pattern_cases_statement'"
  let pats := patternCases.filterMap fun
    case =>
      case.getObjValAs? String "pattern" |>.toOption
  let proofData := patternCases.filterMap fun
    case =>
      case.getObjValAs? Json "proof" |>.toOption
  let mut alts : Array <| TSyntax ``matchAltTac := #[]
  let mut patTerms : Array Syntax.Term := #[]
  for pat in pats do
    let patTerm :=
      runParserCategory (← getEnv) `term pat |>.toOption.getD (← `(_))
    let patTerm' : Syntax.Term := ⟨patTerm⟩
    patTerms := patTerms.push patTerm'
    let m ← `(matchAltTac| | $patTerm' => _)
    alts := alts.push m
  let alts' : Array <| TSyntax ``matchAlt := alts.map fun alt => ⟨alt⟩
  let discrTerm :=
    runParserCategory (← getEnv) `term discr |>.toOption.getD (← `(_))
  let discrTerm' : Syntax.Term := ⟨discrTerm⟩
  let hash := hash discrTerm.reprint
  let c := mkIdent <| ("c" ++ s!"_{hash}").toName
  let tac ← `(tactic| match $c:ident : $discrTerm':term with $alts':matchAlt*)
  let newGoals ←
    runAndGetMVars goal #[tac] proofData.size
  let proofStxs ← proofData.zip newGoals.toArray |>.mapM fun (proof, newGoal) => do
    let some proofStx ← getCode translator (some newGoal) ``tacticSeq proof |
      throwError s!"codegen: no translation found for {proof}"
    return proofStx
  let mut provedAlts : Array <| TSyntax ``matchAltTac := #[]
  for (patTerm, pf) in patTerms.zip proofStxs do
    let m ← `(matchAltTac| | $patTerm => $pf)
    provedAlts := provedAlts.push m
  let alts' : Array <| TSyntax ``matchAlt := provedAlts.map fun alt => ⟨alt⟩
  let c := mkIdent <| ("c" ++ s!"_{hash}").toName
  `(tacticSeq| match $c:ident : $discrTerm':term with $alts':matchAlt*)

| goal?, kind ,_ => throwError
    s!"codegen: biequivalenceCode does not work for kind {kind} with goal present: {goal?.isSome}"


/- bi-implication_cases_statement
    "bi-implication_cases_statement": {
      "type": "object",
      "description": "Proof of a statement `P ↔ Q`.",
      "properties": {
        "type": {
          "type": "string",
          "const": "bi-implication_cases_statement",
          "description": "The type of this logical step."
        },
        "if_proof": {
          "$ref": "#/$defs/Proof",
          "description": "Proof that `P` implies `Q`."
        },
        "only_if_proof": {
          "$ref": "#/$defs/Proof",
          "description": "Proof that `Q` implies `P`."
        },
      "required": [
        "type",
        "antecedent",
        "consequent",
        "if_proof",
        "only_if_proof"
      ],
      "additionalProperties": false
    }
  },
-/
@[codegen "bi-implication_cases_statement"]
def biequivalenceCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok ifProof := js.getObjValAs? Json "if_proof" | throwError
    s!"codegen: no 'if_proof' found in 'bi-implication_cases_statement'"
  let .ok onlyIfProof := js.getObjValAs? Json "only_if_proof" | throwError
    s!"codegen: no 'only_if_proof' found in 'bi-implication_cases_statement'"
  let tac ← `(tactic|constructor)
  let [ifGoal, onlyIfGoal] ←
    runAndGetMVars goal #[tac] 2 | throwError "codegen: in 'biequivalenceCode' `constructor` failed to get two goals; goal: {← ppExpr <| ← goal.getType}"
  let some ifProofStx ← getCode translator (some ifGoal) ``tacticSeq ifProof | throwError
    s!"codegen: no translation found for if_proof {ifProof}"
  let some onlyIfProofStx ← getCode translator (some onlyIfGoal) ``tacticSeq onlyIfProof | throwError
    s!"codegen: no translation found for only_if_proof {onlyIfProof}"
  let tacs := #[tac, ← `(tactic| · $ifProofStx), ← `(tactic| · $onlyIfProofStx)]
  `(tacticSeq| $tacs*)
| goal?, kind ,_ => throwError
    s!"codegen: biequivalenceCode does not work for kind {kind} with goal present: {goal?.isSome}"

/- condition_cases_statement
    "condition_cases_statement": {
      "type": "object",
      "description": "Proof of a statement based on splitting into cases where a condition is true and false, i.e., an if-then-else proof.",
      "properties": {
        "type": {
          "type": "string",
          "const": "condition_cases_statement",
          "description": "The type of this logical step."
        },
        "condition": {
          "type": "string",
          "description": "The condition based on which the proof is split."
        },
        "true_case_proof": {
          "$ref": "#/$defs/Proof",
          "description": "Proof of the case where the condition is true."
        },
        "false_case_proof": {
          "$ref": "#/$defs/Proof",
          "description": "Proof of the case where the condition is false."
        },
      "required": [
        "type",
        "condition",
        "true_case_proof",
        "false_case_proof"
      ],
      "additionalProperties": false
    }
  },
-/
@[codegen "condition_cases_statement"]
def conditionCasesCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok condition := js.getObjValAs? String "condition" | throwError
    s!"codegen: no 'condition' found in 'condition_cases_statement'"
  let conditionType ← translator.translateToPropStrict condition
  let conditionStx ← delabDetailed conditionType
  let tac ← `(tactic|if $conditionStx then ?_ else ?_)
  let [thenGoal, elseGoal] ←
    runAndGetMVars goal #[tac] 2 | throwError "codegen:  `if _ then _ else _` failed to get two goals, goal: {← ppExpr <| ← goal.getType}"
  let .ok trueCaseProof := js.getObjValAs? Json "true_case_proof" | throwError
    s!"codegen: no 'true_case_proof' found in 'condition_cases_statement'"
  let .ok falseCaseProof := js.getObjValAs? Json "false_case_proof" | throwError
    s!"codegen: no 'false_case_proof' found in 'condition_cases_statement'"
  let some trueCaseProofStx ← getCode translator (some thenGoal) ``tacticSeq trueCaseProof | throwError
    s!"codegen: no translation found for true_case_proof {trueCaseProof}"
  let some falseCaseProofStx ← getCode translator (some elseGoal) ``tacticSeq falseCaseProof | throwError
    s!"codegen: no translation found for false_case_proof {falseCaseProof}"
  let hash := hash conditionStx.raw.reprint
  let conditionId := mkIdent <| ("condition" ++ s!"_{hash}").toName
  let conditionBinder ←
    `(Lean.binderIdent| $conditionId:ident)
  let tacs := #[← `(tactic| if $conditionBinder :  $conditionStx then $trueCaseProofStx else $falseCaseProofStx), ← `(tactic| done)]
  `(tacticSeq| $tacs*)
| goal?, kind ,_ => throwError
    s!"codegen: conditionCasesCode does not work for kind {kind} with goal present: {goal?.isSome}"

def multiConditionCasesAux (translator : CodeGenerator := {}) (goal: MVarId) (cases : List (Expr ×Json)) (exhaustiveness: Option <| Syntax.Tactic) : TranslateM (TSyntax ``tacticSeq) := match cases with
  | [] => goal.withContext do
    let pf ← runTacticsAndGetTryThisI (← goal.getType) #[← `(tactic| hammer)]
    let pf := match exhaustiveness with
      | some e => #[e] ++ pf
      | none => pf
    `(tacticSeq| $pf*)
  | (conditionType, trueCaseProof) :: tail => goal.withContext do
    IO.eprintln s!"number of cases (remaining): {tail.length + 1}"
    let conditionStx ← delabDetailed conditionType
    let tac ← `(tactic|if $conditionStx then ?_ else ?_)
    let [thenGoal, elseGoal] ←
      runAndGetMVars goal #[tac] 2 | throwError "codegen:  `if _ then _ else _` failed to get two goals, goal: {← ppExpr <| ← goal.getType}"
    let some trueCaseProofStx ← getCode translator (some thenGoal) ``tacticSeq trueCaseProof | throwError
      s!"codegen: no translation found for true_case_proof {trueCaseProof}"
    let falseCaseProofStx ←
      multiConditionCasesAux translator elseGoal tail exhaustiveness
    let hash := hash conditionStx.raw.reprint
    let conditionId := mkIdent <| ("condition" ++ s!"_{hash}").toName
    let conditionBinder ←
      `(Lean.binderIdent| $conditionId:ident)
    let tacs := #[← `(tactic| if $conditionBinder :  $conditionStx then $trueCaseProofStx else $falseCaseProofStx)]
    `(tacticSeq| $tacs*)

/-
    "multi-condition_cases_statement": {
      "type": "object",
      "description": "A proof by cases given by three or more conditions.",
      "properties": {
        "type": {
          "type": "string",
          "const": "multi-condtion_cases_statement",
          "description": "The type of this logical step."
        },
        "proof_cases": {
          "type": "array",
          "description": "The conditions and proofs in the different cases.",
          "items": {
            "$ref": "#/$defs/condition_case"
          }
        },
        "exhaustiveness": {
          "$ref": "#/$defs/Proof",
          "description": "(OPTIONAL) Proof that the cases are exhaustive."
        }
      },
      "required": [
        "type",
        "proof_cases"
      ],
      "additionalProperties": false
    },
-/
@[codegen "multi-condition_cases_statement"]
def multiConditionCasesCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok proofCases := js.getObjValAs? (List Json) "proof_cases" | throwError
    s!"codegen: no 'proof_cases' found in 'multi-condition_cases_statement'"
  let exhaustiveness? := js.getObjValAs? Json "exhaustiveness" |>.toOption
  let cases ←  proofCases.mapM fun
    c => do
      let .ok condition := c.getObjValAs? String "condition" | throwError
        s!"codegen: no 'condition' found in 'condition_case'"
      let conditionType ← translator.translateToPropStrict condition
      let .ok proof := c.getObjValAs? Json "proof" | throwError
        s!"codegen: no 'proof' found in 'condition_case'"
      pure (conditionType, proof)
  let exhaustiveTac : Option <| Syntax.Tactic ←
    exhaustiveness?.mapM fun
      e => do
        let conds := cases.map (·.1)
        let exhaustGoalType ←
          orAllWithGoal conds (← goal.getType)
        let exhaustGoalStx ← delabDetailed exhaustGoalType
        let hash := hash exhaustGoalStx.raw.reprint
        let exhaustId := mkIdent <| ("exhaust" ++ s!"_{hash}").toName
        let exhaustGoalExpr ← mkFreshExprMVar
          exhaustGoalType
        let exhaustGoal := exhaustGoalExpr.mvarId!
        let some pfStx ← getCode translator (some exhaustGoal) ``tacticSeq e | throwError
          s!"codegen: no translation found for exhaustiveness {e}"
        `(tactic| have $exhaustId : $exhaustGoalStx := by $pfStx)
  IO.eprintln s!"number of cases (after exhaustiveness): {cases.length}"
  let tacs ← multiConditionCasesAux translator goal cases exhaustiveTac
  appendTactics tacs <| ← `(tacticSeq| done)
| goal?, kind ,_ => throwError
    s!"codegen: conditionCasesCode does not work for kind {kind} with goal present: {goal?.isSome}"

/- induction_statement
    "induction_statement": {
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
        "base_case_proof": {
          "$ref": "#/$defs/Proof",
          "description": "Proof of the base case."
        },
        "induction_step_proof": {
          "$ref": "#/$defs/Proof",
          "description": "Proof of the induction step, which typically shows that if the statement holds for `n`, it holds for `n+1`."
        }},
      "required": [
        "type",
        "on",
        "base_case_proof",
        "induction_step_proof"
      ],
      "additionalProperties": false
    },
-/
@[codegen "induction_statement"]
def inductionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok discr := js.getObjValAs? String "on" | throwError
    s!"codegen: no 'on' found in 'induction_statement'"
  let discrTerm' :=
    runParserCategory (← getEnv) `term discr |>.toOption.getD (← `(sorry))
        let succId := mkIdent ``Nat.succ
  let ihId := mkIdent `ih
  let discrTerm : Syntax.Term := ⟨discrTerm'⟩
  let dicrTerm' ← `(elimTarget| $discrTerm:term)
  let discrTerm'' : TSyntax ``elimTarget := ⟨dicrTerm'⟩
  let zeroId := mkIdent ``Nat.zero
  let tac ← `(tactic|
    induction $discrTerm'' with
    | $zeroId => _
    | $succId:ident $ihId:ident => _)

  let [baseGoal, stepGoal] ←
    runAndGetMVars goal #[tac] 2 | throwError s!"codegen: induction failed to get two goals, goal: {← ppExpr <| ← goal.getType}"
  let .ok baseCaseProof := js.getObjValAs? Json "base_case_proof" | throwError
    s!"codegen: no true_case_proof found in {js}"
  let .ok inductionStepProof := js.getObjValAs? Json "induction_step_proof" | throwError
    s!"codegen: no false_case_proof found in {js}"
  let some baseCaseProofStx ← getCode translator (some baseGoal) ``tacticSeq baseCaseProof | throwError
    s!"codegen: no translation found for base_case_proof {baseCaseProof}"
  let some inductionStepProofStx ← getCode translator (some stepGoal) ``tacticSeq inductionStepProof | throwError
    s!"codegen: no translation found for induction_step_proof {inductionStepProof}"
  let tacs := #[← `(tactic|
    induction $discrTerm'' with
    | $zeroId => $baseCaseProofStx
    | $succId:ident $ihId:ident => $inductionStepProofStx), ← `(tactic| done)]
  `(tacticSeq| $tacs*)
| goal?, kind ,_ => throwError
    s!"codegen: induction does not work for kind {kind} with goal present: {goal?.isSome}"

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
@[codegen "contradiction_statement"]
def contradictCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``tacticSeq, js => do
  let .ok assumptionText := js.getObjValAs? String "assumption" | throwError
    s!"codegen: no 'assumption' found in 'contradiction_statement'"
  let assumptionType ← translator.translateToPropStrict assumptionText
  let goalType ← mkArrow assumptionType (mkConst ``False)
  let goalExpr ←  mkFreshExprMVar goalType
  let fullGoal := goalExpr.mvarId!
  let contraId := mkIdent `contraHyp
  let [goal] ← runAndGetMVars fullGoal #[← `(tactic| intro $contraId:term)] 1 | throwError
    s!"codegen: contradiction_statement failed to get goal, goalType: {← ppExpr <| goalType}"
  let .ok proof := js.getObjValAs? Json "proof" | throwError
    s!"codegen: no 'proof' found in 'contradiction_statement'"
  let some tacs ← getCode translator (some goal) ``tacticSeq proof | throwError
    s!"codegen: no tactics found for proof {proof}"
  let fullTacs ←  appendTactics (← `(tacticSeq| intro $contraId:term)) tacs
  let stx ← delabDetailed assumptionType
  `(tacticSeq| have : $stx := by $fullTacs)
| _, kind, _ => throwError
    s!"codegen: conclude_statement does not work for kind {kind}"


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
@[codegen "conclude_statement"]
def concludeCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => do
  let type ←
    match js.getObjValAs? String "claim" with
    | .ok claim =>
      let claim := "We have: " ++ claim
      translator.translateToPropStrict claim
    | .error _ =>
      goal.getType
  let stx ← delabDetailed type
  let resultsUsed ←
    getResultsUsed translator.toTranslator js
  let tac ← `(tactic| hammer [ $resultsUsed,* ])
  let pf ← runTacticsAndGetTryThisI type #[tac]
  `(tacticSeq| have : $stx := by $pf*)
| none, ``tacticSeq, _ => do return none
| _, kind, _ => throwError
    s!"codegen: conclude_statement does not work for kind {kind}"
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
#notImplementedCode "Figure"

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
#notImplementedCode "Table"

-- Test

def egTheorem : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "There are infinitely many odd numbers.",
    "proof": {
      "proof_steps": []
    }
  }

def egTheorem' : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "label": "egTheorem",
    "claim": "There are infinitely many odd numbers."
  }


def egTheorem'' : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "There are infinitely many odd numbers.",
    "proof": {
      "proof_steps": []
    }
  }

def egLet : Json :=
  json% {
    "type" : "let_statement",
    "variable_name": "n",
    "variable_type": "natural number",
    "value": "n is odd",
    "properties": "n > 0"
  }

open Codegen
-- #eval showStx egTheorem

-- #eval showStx egTheorem''


-- #eval egTheorem


-- #eval showStx egLet

def egView : MetaM Format := do
  let .ok js := runParserCategory (← getEnv) `json egTheorem.pretty | throwError
    "Failed to parse egLet as JSON"
  PrettyPrinter.ppCategory `json js

-- #eval egView

-- def egTacs : TermElabM <|  Format := do
--   let goal := q(∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N)
--   let autoTac ← `(tactic| aesop?)
--   let tacs ← runTacticsAndGetTryThisI goal #[autoTac]
--   PrettyPrinter.ppCategory ``tacticSeq <| ← `(tacticSeq|$tacs*)


-- #eval egTacs

-- example: ∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N := by
--   intro
--   aesop?
--   · sorry
--   · sorry

-- #eval (ChatServer.default).fullStatement "p ∤ m!"

-- #eval Translator.translateToPropStrict "p ∤ m!" {}

def thr : MetaM Unit := do
  throwError "This is a test error"

def ctch : MetaM Unit := do
  try
    thr
  catch e =>
    throwError s!"Caught error: {← e.toMessageData.toString}"

-- #eval ctch
-- #premises (∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N)
