import LeanAide.Codegen
import LeanAideCore.PaperCodes
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
| _, `commandSeq, js => do
  if js.getObjVal? "proof" |>.toOption.isSome then
    throwError s!"codegen: 'theorem' with proof is not supported by the deferred theorem handler"
  let (stx, name) ← thmStxParts js
    -- TODO-Partial(mathlib-deferred-theorem): This should become the entire body of the
    -- renamed Mathlib fallback. Build and elaborate a real deferred theorem
    -- interface: emit the proposition definition and a checked theorem/witness
    -- whose proof is obtained from `[Fact proposition]`. The current code merely
    -- constructs the intended `Fact` command and discards it, so no deferred
    -- proof can actually be used. Commit both commands and theorem metadata only
    -- after the complete sequence elaborates successfully; do not expose a
    -- partially registered deferred theorem on failure.
    -- Update: runs only for deferred proofs, but does not check or output here.
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
| goal?, kind, _ => throwError
    s!"codegen: 'theorem' does not work for kind {kind}where goal present: {goal?.isSome}"
where
  thmStxParts (js: Json)  :
    TranslateM <| Syntax.Term × Name  :=
    withoutModifyingTranslateAndTermState do
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
        traceAide `leanaide.papercodes.info s!"Preludes added:\n {(← withPreludes "")}"
        pure h.size
      | Except.error _ => pure 0
    traceAide `leanaide.papercodes.info s!"hypothesis size: {hypSize} in proof"
    let thm ← withPreludes claim
    let name := (js.getObjValAs? Name "name").toOption.getD <| ← translator.server.theoremName thm
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
    -- `IsProved
    Translate.addTheorem <| {name := name, type := type, label := label, isProved := proof?.isSome, source:= js}
    logInfo m!"All theorems : {← allLabels}"
    return (typeStx, name)

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
      throwError s!"codegen: 'let_statement' with no value is not supported in tacticSeq"
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
      addPromptContext statement
      return some <| ← `(tacticSeq| $stxs*)
  | ``commandSeq, js => do
    let statement := statement js
    match js.getObjValAs? String "value" with
    | .error _ =>
      -- If there is no value, we do not need to return a value
      traceAide `leanaide.papercodes.info s!"codegen: No value in 'let_statement' for {js.getObjValAs? String "variable_name" |>.toOption.getD ""}"
      addPromptContext statement
      return none
    | .ok value =>
      let defStx ←
          defStx translator js statement value
      let stxs := #[defStx]
      match ← DefData.ofSyntax? defStx with
      | some data =>
        -- If we have a definition, we add it to the definitions
        -- and return the command
        registerDefnEnv data
      | none =>
        traceAide `leanaide.papercodes.info s!"codegen: No definition found for 'let_statement' {statement} with value {value}"
      addPromptContext statement
      return some <| ← `(commandSeq| $stxs*)

  | _, js =>
      addPromptContext <| statement js
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
      withoutModifyingTranslateAndTermState do
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

partial def dropFuncs : Syntax.Term → Syntax.Term
  | `(fun $_* => $body) => dropFuncs body
  | stx => stx

partial def dropForallsExpr : Expr → TermElabM Expr := fun expr => do
  match expr with
  | Expr.forallE _ _ body _ => do
    dropForallsExpr body
  | _ => pure expr


partial def simpleLet : Syntax.Tactic → TermElabM Syntax.Tactic := fun tac => do
  match tac with
  | `(tactic| let $n := fun $x:ident => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n := $val)
    else
      return tac
  | `(tactic| let $n := fun $x:ident $ys* => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n := fun $ys* => $val)
    else
      return tac
  | `(tactic| let $n : ∀ $_, $t := fun $x:ident => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $t := $val)
    else
      return tac
  | `(tactic| let $n : ∀ $_ $ys*, $t := fun $x:ident $zs* => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : ∀ $ys*, $t := fun $zs* => $val)
    else
      return tac
  | `(tactic| let $n : ∀ ($_ : $_), $t := fun $x:ident => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $t := $val)
    else
      return tac
  | `(tactic| let $n : ∀ {$_ : $_}, $t := fun $x:ident => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $t := $val)
    else
      return tac
  | `(tactic| let $n : ∀ ⦃$_ : $_⦄, $t := fun $x:ident => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $t := $val)
    else
      return tac
  | `(tactic| let $n : ∀ [$_ : $_], $t := fun $_ => $val) => do
      simpleLet <| ←  `(tactic| let $n : $t := $val)
  | `(tactic| let $n : ∀ [$_], $t := fun $_ => $val) => do
      simpleLet <| ←  `(tactic| let $n : $t := $val)
  | `(tactic| let $n : [$_ : $_] → $ty := fun $_ => $val) => do
      simpleLet <| ←  `(tactic| let $n : $ty := $val)
  | `(tactic| let $n : [$_] → $ty := fun $_  => $val) => do
      simpleLet <| ←  `(tactic| let $n : $ty := $val)
  | `(tactic| let $n : [$_ : $_] → $ty := fun $_ $ys* => $val) => do
      simpleLet <| ←  `(tactic| let $n : $ty := fun $ys* => $val)
  | `(tactic| let $n : [$_] → $ty := fun $_ $ys* => $val) => do
      simpleLet <| ←  `(tactic| let $n : $ty := fun $ys* => $val)
  | `(tactic| let $n : ($_ : $_) → $ty := fun $x:ident => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $ty := $val)
    else
      traceAide `leanaide.papercodes.info s!"simpleLet: cannot simplify let statement with binder {x}, which is used in the value as this is not a user variable"
      return tac
  | `(tactic| let $n : ($_ : $_) → $ty := fun $x:ident $ys* => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $ty := fun $ys* => $val)
    else
      return tac
  | `(tactic| let $n : $_ → $ty := fun $x:ident $ys* => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $ty := fun $ys* => $val)
    else
      return tac
  | `(tactic| let $n : $_ → $ty := fun $x:ident => $val) => do
    if ← check x then
      simpleLet <| ←  `(tactic| let $n : $ty := $val)
    else
      return tac
  | tac => do
    traceAide `leanaide.papercodes.info
      s!"simpleLet: simplified tactic to {← PrettyPrinter.ppCategory `term <| ← `(by $tac:tactic)}"
    return tac
  where check (x: Syntax.Ident) : MetaM Bool := do
          try
           let _ ← getFVarFromUserName x.getId
           return true
          catch _ =>
           return false

def simpEg : TermElabM Syntax.Tactic := do
  let stx ← `(tactic| let e : (G : Type u) → [inst : AddGroup G] → G := fun G [AddGroup G] => 0)
  simpleLet stx


def existenceProof (translator : CodeGenerator) (variableName construction : String) (proof: Json) (goal : MVarId) :
    TranslateM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let varId := mkIdent variableName.toName
  let statement := s!"Let {variableName} be {construction}."
  let defStx ← translator.translateDefCmdM? statement
  match defStx with
  | .ok defStx =>
    traceAide `leanaide.papercodes.info s!"Existence proof: translated statement to definition command:\n{← PrettyPrinter.ppCommand defStx}"
    let letTactic ← commandToTactic defStx
    let letTactic ← simpleLet letTactic
    let useTacticSeq ← `(tacticSeq| $letTactic; use $varId:ident)
    traceAide `leanaide.papercodes.info s!"Existence proof: created tactic sequence for definition and use:\n{useTacticSeq}"
    -- TODO(assigned-goal-invariant): Update this caller when
    -- `runForSingleGoal` gains a structured result. A tactic failure must not be
    -- interpreted as closure (`none`) or one remaining goal (`some`). Validate
    -- that `newGoal` is unassigned; `runForSingleGoal` should commit its state on
    -- this successful live-goal path. The following tactic-mode `getCode`, by
    -- contrast, returns replayable syntax and must always restore Term/Meta state
    -- so it cannot leave `newGoal` assigned.
    let newGoal? ← runForSingleGoal goal useTacticSeq
    match newGoal? with
    | some newGoal =>
      traceAide `leanaide.papercodes.info s!"Existence proof: after applying 'use', new goal is {← Term.ppGoal newGoal}"
      let proofTactics ← getCode translator newGoal ``tacticSeq proof
      traceAide `leanaide.papercodes.info s!"Existence proof: obtained tactics for proof: {proofTactics.isSome}"
      match proofTactics with
      | some proofTactics =>
        let fullTactics ← appendTacticSeqSeq useTacticSeq proofTactics
        return fullTactics
      | none =>
        traceAide `leanaide.papercodes.info s!"Existence proof: no tactics obtained for proof, returning just 'use' tactic"
        return useTacticSeq
    | none =>
      traceAide `leanaide.papercodes.info s!"Existence proof: 'use' tactic did not create a new goal, returning just 'use' tactic"
      return useTacticSeq
  | .error _ =>
    traceAide `leanaide.papercodes.info s!"Existence proof: failed to translate statement to definition command"
    traceAide `leanaide.papercodes.info s!"Existence proof: attempted statement was:\n{statement}"
    throwError s!"Existence proof: failed to create definition for witness {construction} with variable name {variableName} and statement {statement}"

/-!
### `existence_proof`

JSON type to match: `existence_proof`.

Fields:

- `full_claim`: required existential claim being proved.
- `variable_name`: name of the bound object in the existential claim.
- `claim`: required property of `variable_name`, after the object is fixed.
- `witness`: constructed witness.
- `proof`: verification that the witness satisfies the predicate.

Expected Lean behavior: treat `full_claim` as the ambient existential goal, use
`witness` for the variable named by `variable_name`, then generate tactics for
the verification proof of `claim`.

Use this type when the main mathematical act is proving an already stated
existential proposition, usually by providing a witness for `∃ x, P x`. The
field `claim` is not the existential proposition; it is the proposition to prove
after the witness has been introduced.

-/
@[codegen "existence_proof"]
def existenceProofCode (translator : CodeGenerator := {}) (goal? : Option MVarId) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)) := fun s js => do
  match goal?, s, js with
  | some goal, ``tacticSeq, js => goal.withContext do
    let .ok variableName := js.getObjValAs? String "variable_name" | throwError
      s!"codegen: no 'variable_name' found in 'existence_proof'"
    let .ok witness := js.getObjValAs? String "witness" | throwError
      s!"codegen: no 'witness' found in 'existence_proof'"
    let .ok proof := js.getObjVal? "proof" | throwError s!"codegen: no 'proof' found in 'existence_proof'"
    existenceProof translator variableName witness proof goal
  | _, _,_ => throwError s!"codegen: 'existence_proof' only works for tactic sequences with a goal, got kind {s} and goal? {goal?.isSome}"

/-!
### `construction_proof`

JSON type to match: `construction_proof`.

Fields:

- `full_claim`: required existential claim supplied by the construction.
- `variable_name`: name of the object being constructed.
- `claim`: required target property of `variable_name` supplied by the
  construction.
- `construction`: constructed object or definition.
- `verification`: proof that the construction has the required property.

Expected Lean behavior: treat `full_claim` as the ambient existential goal,
define or refine the constructed object named by `variable_name` using
`construction`, then discharge the verification goals for `claim`.

Use this type when the proof must build a mathematical object, map, structure,
definition, or auxiliary datum that will be used as an object in the surrounding
argument. Unlike `existence_proof`, the construction itself is first-class data;
`full_claim` records the surrounding existential statement, while `claim`
records what property the named constructed object is meant to certify. Both
`existence_proof` and `construction_proof` use the same `full_claim` /
`variable_name` / `claim` split; the difference is that `existence_proof`
supplies an already available `witness`, while `construction_proof` supplies a
first-class `construction` or definition for the object.
-/

@[codegen "construction_proof"]
def constructionProofCode (translator : CodeGenerator := {}) (goal? : Option MVarId) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
  | ``tacticSeq, js => do
    let some goal := goal? | throwError s!"codegen: 'construction_proof' requires a goal, but none found"
    goal.withContext do
    let .ok variableName := js.getObjValAs? String "variable_name" | throwError
      s!"codegen: no 'variable_name' found in 'construction_proof'"
    let .ok construction := js.getObjValAs? String "construction" | throwError
      s!"codegen: no 'construction' found in 'construction_proof'"
    let .ok verification := js.getObjVal? "verification" | throwError s!"codegen: no 'verification' found in 'construction_proof'"
    let .ok fullClaim := js.getObjValAs? String "full_claim" | throwError
      s!"codegen: no 'full_claim' found in 'construction_proof'"
    let .ok claim := js.getObjValAs? String "claim" | throwError
      s!"codegen: no 'claim' found in 'construction_proof'"
    -- TODO(generation-check-homogeneous): Operate on `goal` and its actual
    -- existential binders instead of retranslating/proving `full_claim` and
    -- `claim` independently. Refine the witness once and discharge only the
    -- resulting verification goal; complex constructions should invoke a
    -- reusable library theorem rather than recursively replaying the proof tree.
    let existenceType ← translator.translateToPropStrict fullClaim
    let existenceGoal ← mkFreshExprMVar existenceType
    let existenceProofTacs ←
        existenceProof translator variableName construction verification existenceGoal.mvarId!
    -- TODO(generation-check-homogeneous): Never delaborate the mvar expression.
    -- Read its assignment with `getExprMVarAssignment?`, recursively resolve it
    -- using `instantiateMVars`, infer/instantiate the assigned value's type, and
    -- delaborate that type (or the assigned value when a value is required).
    let existenceSyntax ← delabDetailed existenceGoal
    let hash := fullClaim.hash
    let existsId := mkIdent (s!"assert_exists_{hash}").toName
    let haveStx ←
      `(tacticSeq| have $existsId : $existenceSyntax := by $existenceProofTacs)
    let varId := mkIdent variableName.toName
    let propId := mkIdent (s!"assert_prop_{hash}").toName
    let splitStx ←
        `(tacticSeq| let ⟨$varId:ident, $propId:ident⟩ := $existsId)
    let verificationId := mkIdent (s!"verification_{hash}").toName
    let verificationType ← translator.translateToPropStrict claim
    let verificationGoal ← mkFreshExprMVar verificationType
    let .some verificationTacs ←
      getProof translator verificationGoal.mvarId! verification | throwError s!"codegen: no proof translation found for verification part of 'construction_proof'"
    let claimStx ← delabDetailed verificationType
    let verificationStx ← `(tacticSeq| have $verificationId : $claimStx := by $verificationTacs)
    appendTacticSeqSeq haveStx <| ← appendTacticSeqSeq splitStx verificationStx
  | s, _ => throwError s!"codegen: 'construction_proof' only works for tactic sequences with goal, got kind {s}"

def existenceProofForUniqueness (translator : CodeGenerator) (js : Json) :
    TranslateM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let .ok fullClaim := js.getObjValAs? String "full_claim" | throwError
      s!"codegen: no 'full_claim' found in 'existence_proof'"
  let .ok variableName := js.getObjValAs? String "variable_name" | throwError
      s!"codegen: no 'variable_name' found in 'existence_proof'"
  let .ok witness := js.getObjValAs? String "witness" | throwError
      s!"codegen: no 'witness' found in 'existence_proof'"
  let .ok proof := js.getObjVal? "proof" | throwError
      s!"codegen: no 'proof' found in 'existence_proof'"
  let goalType ← translator.translateToPropStrict fullClaim
  let existenceGoalExpr ← mkFreshExprMVar goalType
  let existenceGoal := existenceGoalExpr.mvarId!
  let proofStx ← existenceProof translator variableName witness proof existenceGoal
  let stx ← delabDetailed goalType
  let hash₀ := hash ((← ppTerm {env := ← getEnv} stx).pretty)
  let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  `(tacticSeq| have $name : $stx := by $proofStx)

def uniquenessProofCore (translator : CodeGenerator) (existence_js : Json) (proof : Json) :
    TranslateM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let .ok fullClaim := existence_js.getObjValAs? String "full_claim" | throwError
      s!"codegen: no 'full_claim' found in 'existence_proof'"
  let uniquenessClaim := s!"If x and y both satisfy {fullClaim}, then x = y"
  let goalType ← translator.translateToPropStrict uniquenessClaim
  let uniquenessGoalExpr ← mkFreshExprMVar goalType
  let uniquenessGoal := uniquenessGoalExpr.mvarId!
  let some proofStx ← withoutModifyingTranslateAndTermState do
    getProof translator uniquenessGoal proof | throwError
    s!"codegen: no tactics found for contrapositive proof {proof}"
  let stx ← delabDetailed goalType
  let hash₀ := hash ((← ppTerm {env := ← getEnv} stx).pretty)
  let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  `(tacticSeq| have $name : $stx := by $proofStx)

/-!
### `uniqueness_proof`

JSON type to match: `uniqueness_proof`.

Fields:

- `existence_proof`: proof that at least one object exists.
- `uniqueness_proof`: proof that any two candidates are equal.
- `candidate_variables`: optional names for arbitrary candidates.
- `claim`: optional uniqueness or `exists unique` statement.

Expected Lean behavior: split existence and uniqueness goals, then prove the
equality of arbitrary candidates.
-/
@[codegen "uniqueness_proof"]
def uniquenessProofCode (translator : CodeGenerator := {}) (goal? : Option MVarId) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)) := fun s js => do
  match goal?, s, js with
  | some goal, ``tacticSeq, js => goal.withContext do
    let .ok existenceProof := js.getObjVal? "existence_proof" | throwError
      s!"codegen: no 'existence_proof' found in 'uniqueness_proof'"
    let .ok uniquenessProof := js.getObjVal? "uniqueness_proof" | throwError
      s!"codegen: no 'uniqueness_proof' found in 'uniqueness_proof'"
    let existenceTacs ← existenceProofForUniqueness translator existenceProof
    let uniquenessTacs ← uniquenessProofCore translator existenceProof uniquenessProof
    let bothTacs ← appendTacticSeqSeq existenceTacs uniquenessTacs
    let exId := mkIdent `existsUnique_of_exists_of_unique
    let grindTac ← `(tacticSeq| first | apply $exId; repeat (assumption) | grind)
    appendTacticSeqSeq bothTacs grindTac
  | _, _,_ => throwError s!"codegen: 'uniqueness_proof' only works for tactic sequences with a goal, got kind {s} and goal? {goal?.isSome}"

/-!
## Adding handlers for different schema elements

The following functions are helpers that one can use.
-/

/--
info: LeanAide.runForSingleGoal (mvarId : MVarId) (tacticCode : TSyntax `Lean.Parser.Tactic.tacticSeq) :
  TermElabM (Option MVarId)
-/
#guard_msgs in
#check runForSingleGoal


/--
info: LeanAide.Translator.translateToPropStrict (claim : String) (translator : Translator) : TranslateM Expr
-/
#guard_msgs in
#check Translator.translateToPropStrict

/--
info: LeanAide.Translator.translateDefCmdM? (s : String) (translator : Translator) (isProp : Bool := false) :
  TranslateM (Except (Array CmdElabError) Command)
-/
#guard_msgs in
#check Translator.translateDefCmdM?

/--
info: LeanAide.getProof (translator : CodeGenerator) (goal : MVarId) (js : Json) :
  TranslateM (Option (TSyntax `Lean.Parser.Tactic.tacticSeq))
-/
#guard_msgs in
#check getProof

/--
info: LeanAide.Codegen.getCode (translator : CodeGenerator) (goal? : Option MVarId) (kind : SyntaxNodeKinds) (source : Json) :
  TranslateM (Option (TSyntax kind))
-/
#guard_msgs in
#check getCode

/--
info: LeanAide.Codegen.getCodeTactics (translator : CodeGenerator) (goal : MVarId) (sources : List Json) :
  TranslateM (TSyntax `Lean.Parser.Tactic.tacticSeq)
-/
#guard_msgs in
#check getCodeTactics

/--
info: LeanAide.Codegen.commandSeqToTacticSeq (cmdSeq : TSyntax `commandSeq) :
  TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)
-/
#guard_msgs in
#check commandSeqToTacticSeq

/-- info: LeanAide.Codegen.commandToTactic (cmd : Command) : TermElabM Syntax.Tactic -/
#guard_msgs in
#check commandToTactic
