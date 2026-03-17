import LeanAide.Codegen
import LeanAideCore.PaperCodes
-- import LeanAide.StructToLean
import Hammer
/-!
# Code generation for LeanAide "PaperStructure" schema

This module provides code generation for the LeanAide "PaperStructure" schema, which includes sections, theorems, definitions, logical steps, proofs, and other elements of a mathematical document.

Each function corresponds to a specific JSON schema element and generates the appropriate Lean code. The tag `codegen` is used to mark these functions for code generation with argument the key.
-/
open Lean Meta Qq Elab Term

namespace LeanAide

open Codegen Translate

#logIO leanaide.papercodes.info

open Lean.Parser.Tactic

open Lean.Parser.Term CodeGenerator Parser
/--
Generate code for a theorem, lemma, proposition, corollary, or claim. It processes the `hypothesis`, `claim`, and `proof` fields to generate the appropriate Lean code. If the proof is absent a definition is generated instead, which is the statement of the theorem and with name `{name}.prop`.

Should perhaps try to use automation if there is no proof.
-/
@[codegen "theorem"]
def theoremCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let (stx, name, pf?, isProp) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    if isProp then
      `(command| theorem $n : $stx := by $pf)
    else
      `(command| noncomputable def $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(command| abbrev $n : $propIdent:term := $stx)
| _, `commandSeq, js => do
  let (stx, name, pf?, isProp) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    let defn : DefData := {
      name := n.getId,
      type := stx,
      value := ← `(by $pf),
      isProp := isProp,
      isNoncomputable := true,
      doc? := none
    }
    addDefn defn
    traceAide `leanaide.papercodes.info s!"Added theorem definition: {defn.name}"
    if isProp then
      `(commandSeq| theorem $n : $stx := by $pf)
    else
      `(commandSeq| noncomputable def $n : $stx := by $pf)
  | none =>
    let propName := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    let head ← `(command| def $propName : $propIdent:term := $stx)
    let fctIdent := mkIdent ``Fact
    let instName := "assume_" ++ name.toString |>.toName
    let instIdent := mkIdent instName
    let witIdent := mkIdent <| "deferred".toName ++ name
    let elimIdent := mkIdent <| instName ++ "elim".toName
    let _ ← `(command| def $witIdent [$instIdent : $fctIdent $propName] : $propName := $elimIdent)
    let cmds := #[head] -- assumeDef removed for now
    for cmd in cmds do
      runCommand cmd
    `(commandSeq| $cmds*)
| some goal, ``tacticSeq, js => goal.withContext do
  let (stx, name, pf?, _) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(tacticSeq| have $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(tacticSeq| have $n : $propIdent := $stx)
| some _, `tactic, js => do
  let (stx, name, pf?, _) ← thmStxParts js
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
    TranslateM <| Syntax.Term × Name × Option (TSyntax ``tacticSeq) × Bool  := withoutModifyingState do
    match js.getObjVal?  "hypothesis" with
      | Except.ok h => contextRun translator none ``tacticSeq h
      | Except.error _ => pure ()
    let .ok  claim := js.getObjValAs? String "claim" | throwError
      s!"codegen: no 'claim' found in 'theorem'"
    traceAide `leanaide.papercodes.info s!"Translating claim: {claim}"
    let type ← translator.translateToPropStrict claim
    traceAide `leanaide.papercodes.info s!"Obtained type from translation: {← ppExpr type}"
    let proof? :=
      js.getObjVal? "proof" |>.toOption
    let hypSize ←
      match js.getObjValAs? (Array Json)  "hypothesis" with
      | Except.ok h =>
        traceAide `leanaide.papercodes.info s!"hypothesis: {h} in proof"
        contextRun translator none ``tacticSeq (.arr h)
        -- logToStdErr `leanaide.translate.info "Preludes added:"
        -- logToStdErr `leanaide.translate.info <| ← withPreludes ""
        traceAide `leanaide.papercodes.info s!"Preludes added:\n {(← withPreludes "")}"
        pure h.size
      | Except.error _ => pure 0
    traceAide `leanaide.papercodes.info s!"hypothesis size: {hypSize} in proof"
    let proofStx? ← proof?.mapM fun
      pf => withoutModifyingState do
      let pfGoal ← mkFreshExprMVar type
      let (pfGoal', names') ← extractIntros pfGoal.mvarId! hypSize
      traceAide `leanaide.papercodes.debug s!"Extracted intros, names: {names'}"
      let (pfGoal'', names) ← consumeIntros pfGoal' 10 names'
      traceAide `leanaide.papercodes.debug s!"Consumed intros, names: {names}"
      let (pfGoal, resTacs) ← resolveIntros pfGoal'' names
      let pfStx ←
        withoutModifyingState do
        pfGoal.withContext do
        match ←
        getCode translator pfGoal ``tacticSeq pf with
      | some pfStx =>
        let pfStx ←  if names.isEmpty then
            pure pfStx
          else
            let namesStx : List <| TSyntax `term ←
              names.mapM fun n =>
                if n.isInaccessibleUserName || n.isInternal then
                  `(_)
                else do
                  traceAide `leanaide.papercodes.info s!"Adding intro for {n}, not inaccessible"
                  let n' := Lean.mkIdent n
                  `($n':ident)
            let namesStx := namesStx.toArray
            let introTac ←
              `(tacticSeq| intro $namesStx*; $resTacs*)
            appendTacticSeqSeq introTac pfStx
        pure pfStx
      | none => throwError
        s!"codegen: no proof translation found for {pf}"
      pure pfStx
    traceAide `leanaide.papercodes.info s!"Obtained or skipped proof; obtained: {proofStx?.isSome}"
    let thm ← withPreludes claim
    let name := (js.getObjValAs? Name "name").toOption.getD <| ← translator.server.theoremName thm
    let name ← newName name
    let name :=
      if name.toString = "[anonymous]" then

        let hash := thm.hash
        let name := s!"thm_{hash}"
        name.toName
      else
        name
    traceAide `leanaide.papercodes.info s!"codegen: Theorem name: {name} for {thm}"
    let typeStx ← delabDetailed type
    let label := js.getObjValAs? String "label" |>.toOption.getD name.toString
    Translate.addTheorem <| {name := name, type := type, label := label, isProved := proof?.isSome, source:= js}
    logInfo m!"All theorems : {← allLabels}"
    return (typeStx, name, proofStx?, ← isProp type)

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


/--
Generate code for a `let_statement`. If the let statement has a value, it generates a command or tactic that defines the variable with the given value. If there is no value, it simply adds a prelude statement.
If goal is a `there exists` statement and binderName matches variable_name, it returns `use` tactic.
-/
@[codegen "let_statement"]
def letCode (translator : CodeGenerator := {})(goal? : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)) := fun s js => do
  match s, js with
  | ``tacticSeq, js => do
    let statement := statement js
    match js.getObjValAs? String "value" with
    | .error _ =>
      -- If there is no value, we do not need to return a value
      traceAide `leanaide.papercodes.info s!"codegen: No value in 'let_statement' for {js.getObjValAs? String "variable_name" |>.toOption.getD ""}"
      addPrelude statement
      return none
    | .ok value =>
      match goal? with
      | some goal =>
        match (← goal.getType).app2? ``Exists with
        | some (_, .lam name _ _ _) =>
            traceAide `leanaide.papercodes.info s!"goal is a there exists statement"
            if name.toString == (js.getObjValAs? String "variable_name" |>.toOption.getD "") then
              traceAide `leanaide.papercodes.info s!"binderName {name.toString} same as variable_name"
              let useStx ← commandToUseTactic (← defStx translator js statement value)
              let usestxs := #[useStx]
              return some <| ← `(tacticSeq| $usestxs*)
        | _ => pure ()
      | none => pure ()
      let letStx ←
        commandToTactic
          (← defStx translator js statement value)
      let stxs := #[letStx]
      addPrelude statement
      return some <| ← `(tacticSeq| $stxs*)
  | ``commandSeq, js => do
    let statement := statement js
    match js.getObjValAs? String "value" with
    | .error _ =>
      -- If there is no value, we do not need to return a value
      traceAide `leanaide.papercodes.info s!"codegen: No value in 'let_statement' for {js.getObjValAs? String "variable_name" |>.toOption.getD ""}"
      addPrelude statement
      return none
    | .ok value =>
      let defStx ←
          defStx translator js statement value
      let stxs := #[defStx]
      match ← DefData.ofSyntax? defStx with
      | some data =>
        -- If we have a definition, we add it to the definitions
        -- and return the command
        addDefn data
        -- data.addDeclaration
      | none =>
        traceAide `leanaide.papercodes.info s!"codegen: No definition found for 'let_statement' {statement} with value {value}"
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
        let varSegment := match js.getObjValAs? String "variable_name" with
        | .ok "<anonymous>" => "We have "
        | .ok v => s!"Let {v} be"
        | .error _ => "We have "
        let kindSegment := match js.getObjValAs? String "variable_type" with
          | .ok k => s!"a {k}"
          | .error _ => s!""
        let valueSegment := match js.getObjValAs? String "value" with
          | .ok v => s!"{v}"
          | .error _ => ""
        let propertySegment := match js.getObjValAs? String "properties", js.getObjValAs? String "variable_name" with
          | .ok p, .ok v =>
            if v != "<anonymous>"
              then s!"(such that) ({v} is) {p}"
              else s!"(such that) {p}"
          | _, _ => ""
        s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}".trimAscii.toString ++ "."
    defStx (translator: CodeGenerator) (js: Json) (statement: String)  (value: String) : TranslateM Syntax.Command :=
      withoutModifyingState do
        let statement' ← withPreludes statement
        let varName ← match js.getObjValAs? String "variable_name" with
        | .ok "<anonymous>" => pure "_"
        | .ok v => pure v
        | .error _ => throwError s!"codegen: no 'variable_name' found in 'let_statement' for {js}"
        let statement' := statement'.trimAscii.toString ++ "\n" ++ s!"Define ONLY the term {varName} with value {value}. Other terms have been defined already."

        let stx? ← translator.translateDefCmdM? statement'
        match stx? with
        | .ok stx =>
          traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} translated to command:\n{← PrettyPrinter.ppCommand stx}"
          return stx
        | .error es =>
          let fallback ← try
            CmdElabError.fallback es
          catch _ =>
            traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} fallback failed"
            let output := es.map fun e => e.text
            throwError
              s!"codegen: no fallback for 'let_statement' {statement'}; output: {output} "
          match Parser.runParserCategory (← getEnv) `command fallback with
          | .ok stx =>
            let stx: Syntax.Command := ⟨stx⟩
            return stx
          |.error er =>
            traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} translation failed with error:\n{er} and fallback:\n{fallback}"
            traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} translation attempts:\n"
            for e in es do
              traceAide `leanaide.papercodes.info s!"codegen: not a command:\n{e.text}"
            throwError
              s!"codegen: no definition translation found for {statement'}"

/- some_statement
{
  "type": "object",
  "description": "A statement introducing a new variable and saying that **some** value of this variable is as required (i.e., an existence statement). This is possibly with given type and/or property. This corresponds to statements like 'for some integer `n` ...' or 'There exists an integer `n` ....'. **NOTE:** It is better to use `assert_statement` instead if the variable is not being defined but rather asserted to exist.",
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
    },
    "statement": {
      "type": "string",
      "description": "The full statement made."
    }
  },
  "required": [
    "type",
    "variable_name"
  ],
  "additionalProperties": false
}
-/


/-
    "general_induction_proof": {
      "type": "object",
      "description": "A proof by cases given by three or more conditions.",
      "properties": {
        "type": {
          "type": "string",
          "const": "multi-condtion_cases_proof",
          "description": "The type of this logical step."
        },
        "induction_principle": {
          "type": "string",
          "description": "The induction principle being used, such as 'strong induction for natural numbers' or 'structural induction for binary trees'."
        },
        "proof_cases": {
          "type": "array",
          "description": "The conditions and proofs in the different cases.",
          "items": {
            "$ref": "#/$defs/induction_case"
          }
        }
      },
      "required": [
        "type",
        "induction_principle",
        "proof_cases"
      ],
      "additionalProperties": false
    },
-/
