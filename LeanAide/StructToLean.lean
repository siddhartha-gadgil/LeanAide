import Lean
import Mathlib
import LeanCodePrompts.Translate
import LeanAide.AesopSyntax
import LeanAide.CheckedSorry
open LeanAide.Meta Lean Meta

/-!
# Lean code from `ProofJSON`

This file contains code to generate Lean code from a JSON structured proof. The plan is to incrementally improve this code to handle more and more complex proofs.

Some of the ingredients are:

* Extracting text from `let`, `assume` for context.
* Extracting text for a theorem statement.
* Translating a theorem object to a theorem and proof.
* Translating a sequence of statements to tactic proofs.
* Rules for `aesop` to complete proofs.

The cases to cover: "define", "assert", "theorem", "problem", "assume", "let", "proof", "cases", "induction", "case", "conclude", "remark". We can have different modes, at least "tactic" and "command".

* **remark**: This is a comment. We can ignore it.
* **define**: This is a definition. We can translate it to a `def` in command mode and `let` in tactic mode.
* **theorem**: This is a lemma. We can translate it to a `theorem` in command mode and `have` in tactic mode. We then pass to the proof in tactic mode. We begin the proof with `intro` statements for the hypotheses. We conclude the theorem with an `aesop` based tactic with fallback.
* **assert**: This is a lemma. We can translate it to a `theorem` in command mode and `have` in tactic mode. We then pass to the proof in tactic mode. We may (or may not) begin the proof with `intro` statements for the hypotheses not already introduced. We build an `aesop` based tactic with fallback and have this as the proof. This includes a search for relevant lemmas.
* **let** and **assume**: These are context statements. We simply add them to the context, so they get used in assertion.
* **induction**: We first look ahead to the proof cases to write this as `induction ...` in tactic mode, with the `case` heads also determined. We then use recursively the proofs in the cases.
* **cases**: We first look ahead to the proof cases to write this as `cases ...`, `by_cases` or `match ...` in tactic mode, with the `case` heads also determined. We then use recursively the proofs in the cases. In the multiple options case, we make claims `p₁ ∨ p₂ ∨ p₃` and `pᵢ → q` and then use `aesop` to complete. Here `q` is the goal.
* **conclude**: We make an assertion and prove it by default `aesop`.
* **contradiction**: Translate the statement to be contradicted to a statement `P`, then prove `P → False` using the given proof (with aesop having contradiction as a tactic). Finally follow the claim with `contradiction` (or `aesop` with contradiction).
-/

elab "#note" "[" term,* "]" : command => do
  return ()

elab "#note" "[" term,* "]" : tactic => do
  return ()

def mkNoteCmd (s: String) : MetaM Syntax.Command :=
  let sLit := Lean.Syntax.mkStrLit  s
  `(command | #note [$sLit])

def mkNoteTactic (s: String) : MetaM Syntax.Tactic :=
  let sLit := Lean.Syntax.mkStrLit  s
  `(tactic | #note [$sLit])

def Lean.Json.getObjString? (js: Json) (key: String) : Option String :=
  match js.getObjValAs? String key with
  | Except.ok s => some s
  | _ => none

/--
Get a key-value pair from a JSON object which is a single key-value pair.
-/
def Lean.Json.getKV? (js : Json) : Option (String × Json) :=
  match js with
  | Json.obj m =>
    match m.toArray with
    | #[⟨k, v⟩] => some (k, v)
    | _ => none
  | _ => none

def addFullStop (s: String) : String :=
  if s.endsWith "." then s else s ++ "."

open Lean Meta Elab Term PrettyPrinter Tactic Parser
def contextStatementOfJson (js: Json) : Option String :=
  match js.getKV?  with
  | some ("assume", v) =>
    match v with
    | .str s => some <| "Assume that " ++ s
    | _ => none
  | some ("let", v) =>
    let varSegment := match v.getObjString? "variable" with
      | some "<anonymous>" => "We have "
      | some v => s!"Let {v} be"
      | _ => "We have "
    let kindSegment := match v.getObjValAs? String "kind" with
      | Except.ok k => s!"a {k}"
      | Except.error e => s!"kind error: {e}; {v.getObjVal? "kind"}; {v}"
    let valueSegment := match js.getObjString? "value" with
      | some v => s!"{v}"
      | _ => ""
    let propertySegment := match v.getObjString? "properties" with
      | some p => s!"(such that) {p}"
      | _ => ""
    return s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}".trim ++ "."
  | some ("cases", v) =>
    match v.getObjValAs? String "on" with
    | Except.ok s => some <| "We consider cases based on " ++ (addFullStop s)
    | _ => none
  | some ("induction", v) =>
    match v.getObjValAs? String "on" with
    | Except.ok s => some <| "We induct on " ++ (addFullStop s)
    | _ => none
  | some ("case", v) =>
    match v.getObjValAs? String "condition" with
    | Except.ok p =>
      /- one of "induction", "property" and "pattern" -/
      "Consider the case " ++ (addFullStop p)
    | _ => none
  | _ => none

def localDeclExists (name: Name) (type : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  match lctx.findFromUserName? name with
  | some (.cdecl _ _ _ dtype ..) => isDefEq dtype type
  | _ => return false

partial def dropLocalContext (type: Expr) : MetaM Expr := do
  match type with
  | .forallE name binderType body _ => do
    if ← localDeclExists name binderType then
        dropLocalContext body
    else
      return type
  | _ => return type


open Lean Meta Tactic

def powerTactics : CoreM <| List <| TSyntax ``tacticSeq := do
  return [← `(tacticSeq| omega), ← `(tacticSeq| ring), ← `(tacticSeq| linarith), ← `(tacticSeq| norm_num), ← `(tacticSeq| positivity), ← `(tacticSeq| gcongr), ←`(tacticSeq| contradiction)]

def powerRules (weight sorryWeight strongSorryWeight: Nat) : MetaM <| List <| TSyntax `Aesop.rule_expr := do
  let tacs ← powerTactics
  let rules ← tacs.mapM fun tac => AesopSyntax.RuleExpr.ofTactic tac (some weight)
  return rules ++ [← AesopSyntax.RuleExpr.sorryRule sorryWeight, ← AesopSyntax.RuleExpr.strongSorryRule strongSorryWeight]

def suggestionRules (names: List Name) (weight: Nat := 90)
    (rwWeight: Nat := 50) : MetaM <| List <| TSyntax `Aesop.rule_expr := do
  let tacs ← names.mapM fun n => AesopSyntax.RuleExpr.ofName n (some weight)
  let rws ← names.mapM fun n => AesopSyntax.RuleExpr.rewriteName n (some rwWeight)
  let rwsFlip ← names.mapM fun n => AesopSyntax.RuleExpr.rewriteName n (some rwWeight) true
  return tacs ++ rws ++ rwsFlip

def aesopTactic (weight sorryWeight strongSorryWeight: Nat) (names: List Name := []) :
    MetaM <| Syntax.Tactic := do
  let rules ← powerRules weight sorryWeight strongSorryWeight
  let sugRules ← suggestionRules names
  AesopSyntax.fold (rules ++ sugRules).toArray

syntax (name := auto_aesop) "auto?" ("[" ident,* "]")? : tactic

-- should configure 90, 50, 10
@[tactic auto_aesop] def autoAesopImpl : Tactic := fun stx => do
match stx with
| `(tactic| auto?) => do
  let tac ← aesopTactic 90 50 10
  evalTactic tac
| `(tactic| auto? [$names,*]) => do
  let names := names.getElems.map fun n => n.getId
  let tac ← aesopTactic 90 50 10 names.toList
  evalTactic tac
| _ => throwUnsupportedSyntax

def theoremExprInContext? (ctx: Array Json)(statement: String) (qp: CodeGenParams): TranslateM (Except (Array ElabError) Expr) := do
  let mut context := #[]
  for js in ctx do
    match contextStatementOfJson js with
    | some s => context := context.push s
    | none => pure ()
  let fullStatement := context.foldr (· ++ " " ++ ·) s!"Then, {statement}"
  -- IO.eprintln s!"Full statement: {fullStatement}"
  let type? ← translateToProp?
    fullStatement.trim qp.server {qp.params with n := 5} qp.pb .simple
  -- IO.eprintln s!"Type: {← type?.mapM fun e => PrettyPrinter.ppExpr e}"
  type?.mapM <| fun e => dropLocalContext e

def purgeLocalContext: Syntax.Command →  TranslateM Syntax.Command
| `(command|def $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delab type
  `(command|def $name : $type := $value)
| `(command|theorem $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delab type
  `(command|theorem $name : $type := $value)
| stx => return stx

def defnInContext? (ctx: Array Json)(statement: String) (qp: CodeGenParams) : TranslateM (Option Syntax.Command) := do
  let mut context := #[]
  for js in ctx do
    match contextStatementOfJson js with
    | some s => context := context.push s
    | none => pure ()
  let fullStatement := context.foldr (· ++ " " ++ ·) statement
  let cmd? ←
    translateDefCmdM? fullStatement qp.server qp.params qp.pb .doc
  let cmd? ← cmd?.mapM purgeLocalContext
  match cmd? with
  | Except.error e => do
    mkNoteCmd s!"Failed to parse definition {fullStatement}: {repr e}"
  | Except.ok cmd => return cmd

open Lean.Parser.Term
/--
Convert theorem or definition to `have` or `let`
-/
def commandToTactic (cmd: Syntax.Command) : TermElabM Syntax.Tactic := do
  match cmd with
  | `(command| theorem $name:ident $args:bracketedBinder* : $type := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| have $name $letArgs* : $type := $value)
  | `(command| def $name:ident $args:bracketedBinder* : $type := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs* : $type := $value)
  | `(command| def $name:ident $args:bracketedBinder* := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs*  := $value)
  | `(command| #note [$s,*]) => `(tactic| #note [$s,*])
  | _ => `(tactic| sorry)


def inductionCase (name: String)(condition: String)
    (pf: Array Syntax.Tactic) : TermElabM Syntax.Tactic := do
  match condition with
  | "base" =>
      let zeroId := mkIdent `zero
      let zeroArg ← `(caseArg| $zeroId:ident)
      `(tactic| case $zeroArg => $pf*)
  | _ =>
      let nId := mkIdent name.toName
      let succId := mkIdent `succ
      let succId' ← `(Lean.binderIdent| $succId:ident)
      let ihId := mkIdent `ih
      let ihId' ← `(Lean.binderIdent| $ihId:ident)
      `(tactic| case $succId' $nId:ident $ihId' => $pf*)

def inductionCases (name: String)
    (condPfs : Array (String × Array Syntax.Tactic))
    : TermElabM <| Array Syntax.Tactic := do
  let nId := mkIdent name.toName
  let mut cases := #[← `(tactic| induction $nId:ident)]
  for (cond, pf) in condPfs do
    let caseTac ← inductionCase name cond pf
    cases := cases.push caseTac
  return cases

def conditionCases (cond₁ cond₂ : String)
    (pf₁ pf₂ : Array Syntax.Tactic) (context: Array Json) (qp: CodeGenParams)  : TranslateM <| Array Syntax.Tactic := do
  let condProp₁? ← theoremExprInContext?  context cond₁ qp
  let condProp₂? ← theoremExprInContext?  context cond₂ qp
  match condProp₁?, condProp₂? with
  | Except.error _, _ => do
    return #[← mkNoteTactic s!"Failed to translate condition {cond₁}"]
  | _, Except.error _ => do
    return #[← mkNoteTactic s!"Failed to translate condition {cond₂}"]
  | Except.ok condProp₁, Except.ok condProp₂ => do
  let condTerm₁ ← delab condProp₁
  let condTerm₂ ← delab condProp₂
  let condTerm₁' : Syntax.Term := ⟨condTerm₁⟩
  let condTerm₂' : Syntax.Term := ⟨condTerm₂⟩
  let tac ← `(tactic| auto?)
  let ass₂ ← `(tactic| have : $condTerm₂' := by $tac:tactic)
  let pf₂' := #[ass₂] ++ pf₂
  let posId := mkIdent `pos
  let negId := mkIdent `neg
  let posId' ← `(caseArg| $posId:ident)
  let negId' ← `(caseArg| $negId:ident)
  return #[← `(tactic| by_cases $condTerm₁'), ← `(tactic| case $posId' => $pf₁*), ← `(tactic| case $negId' => $pf₂'*)]

def matchAltTac := Term.matchAlt (rhsParser := matchRhs)

def matchCases (discr: String)
    (pat_pfs: Array <| String × Array Syntax.Tactic) : TermElabM Syntax.Tactic := do
  let mut alts : Array <| TSyntax ``matchAltTac := #[]
  for (pat, pf) in pat_pfs do
    let patTerm :=
      runParserCategory (← getEnv) `term pat |>.toOption.get!
    let patTerm' : Syntax.Term := ⟨patTerm⟩
    let m ← `(matchAltTac| | $patTerm' => $pf*)
    alts := alts.push m
  let alts' : Array <| TSyntax ``matchAlt := alts.map fun alt => ⟨alt⟩
  let discrTerm :=
    runParserCategory (← getEnv) `term discr |>.toOption.get!
  let discrTerm' : Syntax.Term := ⟨discrTerm⟩
  `(tactic| match $discrTerm':term with $alts':matchAlt*)

def groupCasesAux (context: Array Json) (cond_pfs: List <| String × Array Syntax.Tactic)(qp: CodeGenParams)
    : TranslateM <| Array Syntax.Tactic := do
    match cond_pfs with
    | [] => return #[← `(tactic| auto?)]
    | (cond, pf) :: tail => do
      let condProp? ← theoremExprInContext? context cond qp
      match condProp? with
      | Except.error _ =>
        return #[← mkNoteTactic s!"Failed to translate condition {cond}"]
      | Except.ok condProp => do
      let condTerm ← delab condProp
      let condTerm' : Syntax.Term := ⟨condTerm⟩
      let tailTacs ← groupCasesAux context tail qp
      let posId := mkIdent `pos
      let negId := mkIdent `neg
      let posId' ← `(caseArg| $posId:ident)
      let negId' ← `(caseArg| $negId:ident)
      return #[← `(tactic| by_cases $condTerm':term), ← `(tactic| case $posId' => $pf*), ← `(tactic| case $negId' => $tailTacs*)]

def groupCases (context : Array Json) (cond_pfs: List <| String × Array Syntax.Tactic)
    (union_pfs: Array Syntax.Tactic) (qp: CodeGenParams) :
    TranslateM <| Array Syntax.Tactic := do
  let conds := cond_pfs.map (·.1)
  let env ← getEnv
  let condTerms := conds.map fun cond =>
    runParserCategory env `term cond |>.toOption.get!
  let orAll : Syntax.Term ←  match condTerms with
    | [] => do
      let falseId := mkIdent `False
      `($falseId:ident)
    | [h] => pure ⟨h⟩
    | h :: t =>
      let t' : List Syntax.Term := t.map fun term => ⟨term⟩
      t'.foldlM (fun acc cond => `($acc ∨ $cond)) ⟨h⟩
  let casesTacs ← groupCasesAux context cond_pfs qp
  let head ← `(tactic| have : $orAll := by $union_pfs*)
  return #[head] ++ casesTacs

def conclusionTactic (conclusion: String)
     : TermElabM Syntax.Tactic := do
  let conclusionTerm :=
    runParserCategory (← getEnv) `term conclusion |>.toOption.get!
  let conclusionTerm' : Syntax.Term := ⟨conclusionTerm⟩
  let tac ← `(tactic| auto?)
  `(tactic| have : $conclusionTerm':term := by $tac:tactic)

def contradictionTactics (statement: String)
    (pf: Array Syntax.Tactic) : TermElabM <| Array Syntax.Tactic := do
  let statementTerm :=
    runParserCategory (← getEnv) `term statement |>.toOption.get!
  let statementTerm' : Syntax.Term := ⟨statementTerm⟩
  let falseId := mkIdent `False
  let assId := mkIdent `assumption
  let assumeTactic ← `(tactic| intro $assId:ident)
  let fullPf := #[assumeTactic] ++ pf
  return #[←
    `(tactic| have : $statementTerm':term → $falseId := by $fullPf*), ← `(tactic| auto?)]


def haveForAssertion  (type: Syntax.Term)
  (premises: List Name) :
    MetaM <| Syntax.Tactic := do
  let ids := premises.toArray.map fun n => Lean.mkIdent n
  let tac ← `(tactic| auto? [$ids,*])
  `(tactic| have : $type := by $tac:tactic)

mutual
  partial def structToCommand? (context: Array Json)
      (input: Json) (qp: CodeGenParams) : TranslateM <| Option Syntax.Command := do
      match input.getKV? with
      | some ("theorem", v) =>
        -- logInfo s!"Found theorem"
        let name? := v.getObjString? "name" |>.map String.toName
        let name? := name?.filter (· ≠ Name.anonymous)
        let hypothesis :=
          v.getObjValAs? (Array Json) "hypothesis"
            |>.toOption.getD #[]
        match v.getObjValAs? String "conclusion", v.getObjValAs? Json "proof" with
        | Except.ok claim, Except.ok (.arr steps) =>
            let thm? ← theoremExprInContext?  (context ++ hypothesis) claim qp
            match thm? with
            | Except.error _ =>
              mkNoteCmd s!"Failed to translate theorem {claim}"
            | Except.ok thm => do
              let pf ← structToTactics #[] (context ++ hypothesis) steps.toList qp
              let pf := pf.push <| ← `(tactic| auto?)
              let pfTerm ← `(by $pf*)
              -- IO.eprintln s!"Proof term: {← ppTerm {env := ← getEnv} pfTerm}"
              mkStatementStx name? (← delab thm) pfTerm true
        | _, _ =>
          -- logInfo s!"failed to get theorem conclusion or proof"
          mkNoteCmd "No theorem conclusion or proof found"
      | some ("define", v) =>
        match v.getObjValAs? String "statement", v.getObjValAs? String "term" with
        | Except.ok s, Except.ok t =>
          let statement := s!"We define {t} as follows:\n{s}."
          defnInContext? context statement qp
        | _ , _ => none
      | _ => mkNoteCmd s!"Json not a KV pair {input.compress}"

  partial def structToTactics  (accum: Array Syntax.Tactic)
    (context: Array Json)(input: List Json)
    (qp: CodeGenParams): TranslateM <| Array Syntax.Tactic := do
      match input with
      | [] => return accum.push <| ← `(tactic| auto?)
      | head :: tail =>
        -- IO.eprintln s!"Processing {head}"
        let headTactics: Array Syntax.Tactic ←
          match head.getKV? with
          | some ("assert", head) =>
            match head.getObjValAs? String "claim" with
            | Except.ok claim =>
              let useResults: List String :=
                match head.getObjValAs? Json "deduced_from_results"  with
                | Except.ok known =>
                  match known.getKV? with
                  | some ("deduced_from", .arr results) =>
                    results.toList.filterMap fun js =>
                      match js.getObjString? "result_used", js.getObjValAs? Bool "proved_earlier" with
                      | some s, Except.ok false => some s
                      | _, _ => none
                  | _ => []
                | _ => []
              let type? ← theoremExprInContext? context claim qp
              match type? with
              | Except.error _ =>
                pure #[← mkNoteTactic s!"Failed to translate assertion {claim}"]
              | Except.ok type =>
                let names' ← useResults.mapM fun s =>
                  matchingTheoremsAI   (s := s) (qp:= qp)
                let premises := names'.join
                let tac ← haveForAssertion  (← delab type) premises
                pure #[tac]
            | _ => pure #[]
          | some ("define", head) =>
            match ← structToCommand? context head qp with
            | some cmd =>
              let tac ← commandToTactic  <| ←  purgeLocalContext cmd
              pure #[tac]
            | none => pure #[]
          | some ("theorem", head) =>
            match ← structToCommand? context head qp with
            | some cmd =>
              let tac ← commandToTactic  <| ←  purgeLocalContext cmd
              pure #[tac]
            | none => pure #[]
          | some ("cases", head) =>
            match head.getObjValAs? (Array Json) "proof_cases" with
            | Except.ok cs =>
              let conditionProofs ← cs.filterMapM fun js =>
                match js.getKV? with
                | some ("case", js) =>
                  match js.getObjString? "condition",
                    js.getObjValAs? (List Json) "proof" with
                  | some cond, Except.ok pfSource => do
                    let pf ← structToTactics #[] context pfSource qp
                    pure <| some (cond, pf)
                  | _, _ => pure none
                | _ => pure none
              match head.getObjString? "split_kind" with
              | some "match" =>
                match head.getObjString? "on" with
                | some discr =>
                  let casesTac ← matchCases discr conditionProofs
                  return #[casesTac]
                | _ => pure #[]
              | some "group" =>
                let union_pf : Array Syntax.Tactic ←
                  match head.getObjValAs? (List Json) "exhaustiveness" with
                  | Except.ok pfSource => structToTactics #[] context pfSource qp
                  | _ => pure #[← `(tactic| auto?)]
                groupCases context conditionProofs.toList union_pf qp
              | some "condition" =>
                match conditionProofs with
                | #[(cond₁, pf₁), (cond₂, pf₂)] =>
                  conditionCases cond₁ cond₂ pf₁ pf₂ context qp
                | _ => pure #[]
              | _ => /- treat like a group but with conditions as claims;
                      works for `iff` -/
                let union_pf : Array Syntax.Tactic ←
                  pure #[← `(tactic| auto?)]
                groupCases context conditionProofs.toList union_pf qp
            | _ =>
              pure #[]
          | some ("induction", head) =>
            match head.getObjValAs? String "on",
              head.getObjValAs? (Array Json) "proof_cases" with
            | Except.ok name, Except.ok cs =>
              let conditionProofs ← cs.filterMapM fun js =>
                match js.getKV? with
                | some ("case", js) =>
                  match js.getObjString? "condition",
                    js.getObjValAs? (List Json) "proof" with
                  | some cond, Except.ok pfSource => do
                    let pf ← structToTactics #[] context pfSource qp
                    return some (cond, pf)
                  | _, _ => return none
                | _ => return none
              inductionCases name conditionProofs
            | _, _ => pure #[]
          | some ("contradiction", head) =>
            match head.getObjValAs? String "assumption",
              head.getObjValAs? (List Json) "proof" with
            | Except.ok s, Except.ok pf =>
              let proof ← structToTactics #[] context pf qp
              contradictionTactics s proof
            | _, _ => pure #[]
          | some ("conclude", head) =>
            match head.getObjValAs? String "claim" with
            | Except.ok s => pure #[← conclusionTactic s]
            | _ => pure #[]
          | _ => pure #[]
        -- IO.eprintln s!"Head tactics"
        -- for tac in headTactics do
        --   IO.eprintln s!"{← ppTactic tac}"
        structToTactics (accum ++ headTactics) (context.push head) tail qp

end

syntax commandSeq := sepBy1IndentSemicolon(command)

def commands : TSyntax `commandSeq → Array (TSyntax `command)
  | `(commandSeq| $cs*) => cs
  | _ => #[]

def toCommandSeq : Array (TSyntax `command) → CoreM (TSyntax `commandSeq)
  | cs => `(commandSeq| $cs*)


def structToCommandSeq? (context: Array Json)
    (input: Json) (qp: CodeGenParams) : TranslateM <| Option <| Array Syntax.Command := do
  match input with
  | Json.arr js =>
    let mut cmds := #[]
    let mut ctx := context
    for j in js do
      match ← structToCommand?  ctx j qp with
      | some cmd => cmds := cmds.push cmd
      | none =>
        unless contextStatementOfJson j |>.isSome do
          let s := s!"JSON object not command or context: {j.compress}"
          let cmd ←
            mkNoteCmd s
          cmds := cmds.push cmd
        pure ()
      ctx := ctx.push j
    match cmds with
    | #[] => none
    | _ => pure <| some  cmds
  | _ => none

def mathDocumentCommands (doc: Json) (qp: CodeGenParams) :
  TranslateM <| Array Syntax.Command := do
    match doc.getKV? with
    | some  ("math_document", proof) =>
      let cmds? ←
        structToCommandSeq? #[] proof qp
      return cmds?.getD #[← mkNoteCmd "No commands found"]
    | _ => return #[← mkNoteCmd "No math document found"]

def mathDocumentCode (doc: Json) (qp: CodeGenParams) :
  TranslateM Format := do
    let cmds ←
       mathDocumentCommands doc qp
    let cmds' ← cmds.mapM fun cmd => do
      let cmd' ← PrettyPrinter.ppCommand cmd
      return cmd'
    return cmds'.foldl (· ++ "\n" ++ ·) ""

elab "dl!" t: term : term => do
let t ← elabType t
  let t' ← dropLocalContext t
  return t'

set_option linter.unusedVariables false in
def eg_drop (n m: Nat)  := dl! (∀ n m: Nat, n = n + 1 → False)

def topCode := "import Mathlib
import LeanAide.CheckedSorry
universe u v u_1
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

"
