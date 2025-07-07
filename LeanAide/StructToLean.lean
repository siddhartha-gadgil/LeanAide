import Lean
import Mathlib
import LeanCodePrompts.Translate
import LeanAide.AesopSyntax
import LeanAide.CheckedSorry
import LeanAide.AutoTactic
import LeanAide.RunTactics
open LeanAide.Meta Lean Meta PrettyPrinter

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

## TODO

* In the case of an **exists** `have`, follow this by introducing the variable and witness.
* For generating tactics, possibly have an MVarId for the goal as an argument (but this could lead to repeatedly running automation).
* Alternatively, we add appropriate declarations to the context whenever a new variable is introduced by an assertion or a pattern matching.
* Start the code with `mvarId.withContext do`.
* Use helpers `MVarId.cases` etc to generate the inner `mvarId`s.
* If there are no sorries except in `have` statements that are unused, then we can remove them.
* Split `by auto?` into two lines to take care of the aesop bug (the naive way did not work).
-/

def Lean.Json.getObjString? (js: Json) (key: String) : Option String :=
  match js.getObjValAs? String key with
  | Except.ok s => some s
  | _ => none


namespace LeanAide

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
  | some ("some", v) =>
    let varSegment := "There exists some " ++
      match v.getObjString? "variable" with
      | some "<anonymous>" => ""
      | some v => s!"{v} "
      | _ => ""
    let kindSegment := match v.getObjValAs? String "kind" with
      | Except.ok k => s!"a {k}"
      | Except.error e => s!"kind error: {e}; {v.getObjVal? "kind"}; {v}"
    let propertySegment := match v.getObjString? "properties" with
      | some p => s!"(such that) {p}"
      | _ => ""
    return s!"{varSegment} {kindSegment} {propertySegment}".trim ++ "."
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

partial def getVars (type: Expr) : MetaM <| List Name := do
  match type with
  | .forallE n type body bi => do
    withLocalDecl n  bi type fun x => do
      let type' := body.instantiate1 x
      let names ← getVars type'
      return n::names
  | _ => return []


def findLocalDecl? (name: Name) (type : Expr) : MetaM <| Option FVarId := do
  let lctx ← getLCtx
  match lctx.findFromUserName? name with
  | some (.cdecl _ fVarId _ dtype ..) =>
    let check ← isDefEq dtype type
    logInfo m!"Checking {dtype} and {type} gives {check}"
    if check
      then return fVarId
      else return none
  | _ => return none


partial def dropLocalContext (type: Expr) : MetaM Expr := do
  match type with
  | .forallE name binderType body _ => do
    let lctx ← getLCtx
    match lctx.findFromUserName? name with
    | some (.cdecl _ fVarId _ dtype ..) =>
      let check ← isDefEq dtype binderType
      -- logInfo m!"Checking {dtype} and {type} gives {check}"
      if check then
        let body' := body.instantiate1 (mkFVar fVarId)
        dropLocalContext body'
      else
        IO.eprintln s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr binderType}"
        return type
    | some (.ldecl _ _ _ dtype value ..) =>
      let check ← isDefEq dtype binderType
      -- logInfo m!"Checking {dtype} and {type} gives {check}"
      if check then
        let body' := body.instantiate1 value
        dropLocalContext body'
      else
        IO.eprintln s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr binderType}"
        return type
    | _ => return type
  | _ => return type


open Lean Meta Tactic

def purgeLocalContext: Syntax.Command →  TranslateM Syntax.Command
| `(command|def $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delabDetailed type
  `(command|def $name : $type := $value)
| `(command|theorem $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delabDetailed type
  `(command|theorem $name : $type := $value)
| stx => return stx

example (p: ∃ n m : Nat, n + m = 3): True := by
  let ⟨n, m, h⟩ := p
  exact trivial

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

def commandSeqToTacticSeq (cmdSeq: TSyntax ``commandSeq) : TermElabM <| TSyntax ``tacticSeq := do
  let cmds := commands cmdSeq
  let tactics ← cmds.mapM commandToTactic
  `(tacticSeq| $tactics:tactic*)

/--
Converts definition to `use`
-/
def commandToUseTactic (cmd: Syntax.Command) : TermElabM Syntax.Tactic := do
  match cmd with
  | `(command| def $_:ident $_:bracketedBinder* : $_ := $value) =>
      `(tactic| use $value:term)
  | `(command| def $_:ident $_:bracketedBinder* := $value) =>
      `(tactic| use $value:term)
  | `(command| #note [$s,*]) => `(tactic| #note [$s,*])
  | _ => throwError s!"could not parse the definition {← PrettyPrinter.ppCommand cmd} in commandToUseTactic"


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

def inductionCaseSkeleton (name: String)(condition: String)
     : TermElabM (TSyntax ``Tactic.inductionAlt) := do
  match condition with
  | "base" =>
      let zeroId := mkIdent ``Nat.zero
      `(inductionAlt| | $zeroId => _)
  | _ =>
      let nId := mkIdent name.toName
      let succId := mkIdent ``Nat.succ
      let ihId := mkIdent `ih
      `(inductionAlt| | $succId $nId $ihId => _)


def inductionCases (name: String)
    (condPfs : Array (String × Array Syntax.Tactic))
    : TermElabM <| Array Syntax.Tactic := do
  let nId := mkIdent name.toName
  let mut cases := #[← `(tactic| induction $nId:ident)]
  for (cond, pf) in condPfs do
    let caseTac ← inductionCase name cond pf
    cases := cases.push caseTac
  return cases

def inductionCasesSkeleton (name: String)
    (conds : Array (String))
    : TermElabM <| Syntax.Tactic := do
  let nId := mkIdent name.toName
  let mut cases := #[]
  for cond in conds do
    let caseTac ← inductionCaseSkeleton name cond
    cases := cases.push caseTac
  let alts ← `(inductionAlts| with $cases:inductionAlt*)
  `(tactic| induction $nId:ident $alts:inductionAlts)


namespace CodeGenerator

def topCode := "import Mathlib
universe u v w u_1 u_2 u_3 u₁ u₂ u₃
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
open Nat
"

def theoremExprInContext? (ctx: Array Json)(statement: String) (qp: CodeGenerator): TranslateM (Except (Array ElabError) Expr) := do
  let mut context := #[]
  for js in ctx do
    match contextStatementOfJson js with
    | some s => context := context.push s
    | none => pure ()
  let mut decls : Array String := #[]
  for decl in ← getLCtx do
    let s := s!"{decl.userName} : {← PrettyPrinter.ppExpr decl.type};"
    unless decl.userName.toString.contains '_' do
      decls := decls.push s
  -- IO.eprintln s!"Context: {context}"
  -- IO.eprintln s!"Declarations: {decls}"
  unless decls.isEmpty do
    context := context ++ #["We have the following variables with types in context: "] ++ decls ++ #["."]
  let fullStatement := context.foldr (· ++ " " ++ ·) s!"Then, {statement}"
  -- IO.eprintln s!"Full statement: {fullStatement}"
  let translator := qp.toTranslator
  let type? ← Translator.translateToProp?
    fullStatement.trim {translator with params:={translator.params with n := 5}}
  -- IO.eprintln s!"Type: {← type?.mapM fun e => PrettyPrinter.ppExpr e}"
  match type? with
  | Except.error e => do
    return Except.error e
  | Except.ok type => do
    let type ← instantiateMVars type
    Term.synthesizeSyntheticMVarsNoPostponing
    if type.hasSorry || (← type.hasUnassignedExprMVar) then
      return Except.error #[ElabError.parsed statement s!"Failed to infer type {type} has sorry or mvar" [] none]
    let univ ← try
      withoutErrToSorry do
      if type.hasSorry then
        throwError "Type has sorry"
      inferType type
    catch e =>
      return Except.error #[ElabError.parsed statement s!"Failed to infer type {type}, error {← e.toMessageData.format}" [] none]
    if univ.isSort then
      let type ←  dropLocalContext type
      -- IO.eprintln s!"Type: {← PrettyPrinter.ppExpr type}"
      return Except.ok type
    else
      IO.eprintln s!"Not a type: {type}"
      return Except.error #[ElabError.parsed statement s!"Not a type {type}" [] none]

def defnInContext? (ctx: Array Json)(statement: String) (qp: CodeGenerator) : TranslateM (Option Syntax.Command) := do
  let mut context := #[]
  for js in ctx do
    match contextStatementOfJson js with
    | some s => context := context.push s
    | none => pure ()
  let fullStatement := context.foldr (· ++ " " ++ ·) statement
  let translator := qp.toTranslator
  let cmd? ←
    Translator.translateDefCmdM? fullStatement {translator with toChat := .doc}
  let cmd? ← cmd?.mapM purgeLocalContext
  match cmd? with
  | Except.error e => do
    mkNoteCmd s!"Failed to parse definition {fullStatement}: {repr e}"
  | Except.ok cmd => return cmd



def matchAltTac := Term.matchAlt (rhsParser := matchRhs)

def matchCasesSkeleton (discr: String)
    (pats: Array <| String) : TermElabM Syntax.Tactic := do
  let mut alts : Array <| TSyntax ``matchAltTac := #[]
  for pat in pats do
    let patTerm :=
      runParserCategory (← getEnv) `term pat |>.toOption.getD (← `(_))
    let patTerm' : Syntax.Term := ⟨patTerm⟩
    let m ← `(matchAltTac| | $patTerm' => _)
    alts := alts.push m
  let alts' : Array <| TSyntax ``matchAlt := alts.map fun alt => ⟨alt⟩
  let discrTerm :=
    runParserCategory (← getEnv) `term discr |>.toOption.getD (← `(_))
  let discrTerm' : Syntax.Term := ⟨discrTerm⟩
  let hash := hash discrTerm.reprint
  let c := mkIdent <| ("c" ++ s!"_{hash}").toName
  `(tactic| match $c:ident : $discrTerm':term with $alts':matchAlt*)

def ifSkeleton (context: Array Json) (discr: String) (qp: CodeGenerator) : TranslateM Syntax.Tactic := do
  let discrTerm? ←
    theoremExprInContext? context discr qp
  match discrTerm? with
  | Except.error _ =>
    mkNoteTactic s!"Failed to translate condition {discr}"
  | Except.ok discrTerm => do
    let discrTerm' : Syntax.Term ← delabDetailed discrTerm
    let hash := hash discrTerm'.raw.reprint
    let c := mkIdent <| ("c" ++ s!"_{hash}").toName
    `(tactic| if $c:ident : $discrTerm':term then _ else _)


example (n: Nat) : n = n := by
  induction n with
  | zero  => _
  | succ n ih => _
  rfl
  rfl

example (n: Nat) : n = n := by
  match n with
  | Nat.zero  => _
  | Nat.succ n  => _
  rfl
  rfl

example (n: Nat) : n = n := by
  if n = 0 then _ else _
  rfl
  rfl



def matchCases (discr: String)
    (pat_pfs: Array <| String × Array Syntax.Tactic) : TermElabM Syntax.Tactic := do
  let mut alts : Array <| TSyntax ``matchAltTac := #[]
  for (pat, pf) in pat_pfs do
    let patTerm :=
      runParserCategory (← getEnv) `term pat |>.toOption.getD (← `(_))
    let patTerm' : Syntax.Term := ⟨patTerm⟩
    let m ← `(matchAltTac| | $patTerm' => $pf*)
    alts := alts.push m
  let alts' : Array <| TSyntax ``matchAlt := alts.map fun alt => ⟨alt⟩
  let discrTerm :=
    runParserCategory (← getEnv) `term discr |>.toOption.getD (← `(_))
  let discrTerm' : Syntax.Term := ⟨discrTerm⟩
  `(tactic| match $discrTerm':term with $alts':matchAlt*)


def orAllSimple (terms: List Syntax.Term) : Syntax.Term :=
  match terms with
  | [] => mkIdent `False
  | [h] => h
  | h :: t =>
      let t' : List Syntax.Term := t.map fun term => ⟨term⟩
    t'.foldl (fun acc cond => Syntax.mkApp (mkIdent `or) #[acc, cond]) h

def orAllSimpleExpr (terms: List Expr) : MetaM Expr := do
  match terms with
  | [] => return mkConst ``False
  | [h] => return h
  | h :: t =>
    let mut result := h
    for term in t do
      result ← mkAppM ``Or #[result, term]
    return result


partial def orAllWithGoal (terms: List Expr) (goal: Expr) : MetaM Expr := do
  match goal with
  | .forallE name type _ bi =>
    withLocalDecl name bi type fun x => do
      let inner ← orAllWithGoal terms type
      mkForallFVars #[x] inner
  | _ =>
    let terms ← terms.mapM dropLocalContext
    orAllSimpleExpr terms

def exhaustiveType (goal: MVarId)(context : Array Json) (conds: List <| String)
    (qp: CodeGenerator)  : TranslateM Expr := goal.withContext do
  let condExprs ←  conds.filterMapM fun cond => do
      let e? ← qp.theoremExprInContext? context cond
      pure e?.toOption
  orAllWithGoal condExprs (← goal.getType)

def groupCasesAux (context: Array Json) (cond_pfs: List <| Expr × Array Syntax.Tactic)(qp: CodeGenerator)
    : TranslateM <| Array Syntax.Tactic := do
    match cond_pfs with
    | [] => return #[]
    | (condProp, pf) :: tail => do
      let condTerm ← delabDetailed condProp
      let condTerm' : Syntax.Term := ⟨condTerm⟩
      let tailTacs ← groupCasesAux context tail qp
      let hash := hash condTerm'.raw.reprint
      let c := mkIdent <| ("c" ++ s!"_{hash}").toName
      return #[← `(tactic| if $c:ident : $condTerm':term then $pf* else  $tailTacs*)]

def groupCases (context : Array Json) (cond_pfs: List <| String × Array Syntax.Tactic)
    (union_pfs: Array Syntax.Tactic) (qp: CodeGenerator) (goal?: Option Expr) :
    TranslateM <| Array Syntax.Tactic := do
  let conds := cond_pfs.map (·.1)
  let condExprs ←  conds.filterMapM fun cond => do
    let e? ← qp.theoremExprInContext? context cond
    pure e?.toOption
  let condPfExprs ←  cond_pfs.filterMapM fun (cond, pf) => do
    let e? ← qp.theoremExprInContext? context cond
    pure <| e?.toOption.map (·, pf)
  let orAllExpr ←  match goal? with
    | some goal => orAllWithGoal condExprs goal
    | none => orAllSimpleExpr condExprs
  let orAll ← delabDetailed orAllExpr
  let hash := hash orAll.raw.reprint
  let orAllId := mkIdent <| Name.mkSimple s!"orAll_{hash}"
  let casesTacs ← groupCasesAux context condPfExprs qp
  let head ← `(tactic| have $orAllId : $orAll := by $union_pfs*)
  return #[head] ++ casesTacs


-- Does not work for multiple variables together
partial def existsVars (type: Syntax.Term) : MetaM <| Option (Array Syntax.Term) := do
  match type with
  | `(∃ $n:ident, $t) => do
    return some <| #[n] ++ ((← existsVars t).getD #[])
  | `(∃ ($n:ident: $_), $t) => do
    return some <| #[n] ++ ((← existsVars t).getD #[])
  | `(∃ $n:ident: $_, $t) => do
    return some <| #[n] ++ ((← existsVars t).getD #[])
  | `(∃ $n:ident $ms*, $t) => do
    let ms' := ms.toList.toArray
    let t' ← `(∃ $ms':binderIdent*, $t)
    return some <| #[n] ++ ((← existsVars t').getD #[])
  | `(∃ ($n:ident $ms* : $type), $t) => do
    let t' ← `(∃ ($ms* : $type), $t)
    return some <| #[n] ++ ((← existsVars t').getD #[])
  | `(∃ ($n:ident $ms* : $type), $t) => do
    let t' ← `(∃ ($ms* : $type), $t)
    return some <| #[n] ++ ((← existsVars t').getD #[])
  | `(∃ $n:ident $ms* : $type, $t) => do
    let t' ← `(∃ ($ms* : $type), $t)
    return some <| #[n] ++ ((← existsVars t').getD #[])
  | _ =>
    logInfo s!"No vars in {type}, i.e., {← ppTerm {env := ← getEnv} type}"
    return none

partial def existsVarTypesStx (type: Syntax.Term) : MetaM <| Option (Array <| Syntax.Ident × Syntax.Term) := do
  match type with
  | `(∃ $n:ident, $t) => do
    return some <| #[(n, t)] ++ ((← existsVarTypesStx t).getD #[])
  | `(∃ ($n:ident: $_), $t) => do
    return some <| #[(n, t)] ++ ((← existsVarTypesStx t).getD #[])
  | `(∃ $n:ident: $_, $t) => do
    return some <| #[(n, t)] ++ ((← existsVarTypesStx t).getD #[])
  | `(∃ $n:ident $ms*, $t) => do
    let ms' := ms.toList.toArray
    let t' ← `(∃ $ms':binderIdent*, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | `(∃ ($n:ident :  $_) $ms*, $t) => do
    let t' ← `(∃ $ms*, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | `(∃ ($n:ident $ms* : $type), $t) => do
    let ms' := ms.toList.toArray
    let t' ← `(∃ $ms':binderIdent* : $type, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | `(∃ $n:ident $ms* : $type, $t) => do
    let ms' := ms.toList.toArray
    let t' ← `(∃ $ms':binderIdent* : $type, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | _ =>
    -- logInfo s!"No vars in {type}, i.e., {← ppTerm {env := ← getEnv} type}"
    return none

partial def existsVarTypes (type: Expr) : MetaM <| Option (Array <| Name × Expr) := do
  match type.app2? ``Exists with
  | some (_, .lam name type body binderInfo) =>
      sorry
  | _ => return none



open LeanAide.CodeGenerator
example (h : ∃ n m : Nat, ∃ _k: Nat, n + m  = 3) : True := by
  rcases h with ⟨n, m, k, h⟩
  trivial

elab "#exists_varTypes" type:term : command => do
  Command.liftTermElabM do
  match ← existsVarTypesStx type with
  | some varTypes =>
    logInfo s!"Var types: {varTypes.size}"
    for (var, type) in varTypes do
      logInfo s!"Var: {var}; type: {← ppTerm type}"
    return
  | none =>
      logInfo s!"No vars"
      return

-- #exists_varTypes ∃ n m : Nat, ∃ k: Nat, n + m  = 3

example (h : ∃ l n m : Nat, l + n + m = 3) : True := by
  let ⟨l, ⟨n, ⟨m, h⟩⟩⟩  := h
  trivial

def calculateStatement (js: Json) : IO <| Array String := do
  match js.getKV? with
  | some ("inline_calculation", .str s) => return #["We have: " ++ s]
  | some ("calculation_sequence", .arr seq) =>
    -- IO.eprintln s!"Calculating sequence: {seq}"
    let steps := seq.filterMap fun js =>
      js.getStr? |>.toOption |>.orElse fun _ =>
      match js.getKV? with
      | some ("calculation_step", .str s) => some s
      | _ => none
    return steps.map fun s => "We have: " ++ s
  | _ => do
    IO.eprintln s!"No calculation found in {js.compress}"
    return #[]


def conclusionTactic (conclusion: String)(context: Array Json) (qp: CodeGenerator)
     : TranslateM Syntax.Tactic := do
  let conclusionTerm? ← qp.theoremExprInContext? context conclusion
  let conclusionTerm :=
    conclusionTerm? |>.toOption.getD (mkConst ``True)
  let conclusionTerm' : Syntax.Term ← delabDetailed conclusionTerm
  let hash := hash conclusion
  let conclusionId := mkIdent <| Name.mkSimple s!"conclusion_{hash}"
  let tacs ←
    runTacticsAndGetTryThisI conclusionTerm #[← `(tactic| auto?)]
  `(tactic| first | done |have $conclusionId : $conclusionTerm':term := by $tacs*)

def contradictionTactics (statement: String)
    (pf: Array Syntax.Tactic)(context: Array Json) (qp: CodeGenerator) : TranslateM <| Array Syntax.Tactic := do
  let statementTerm? ← qp.theoremExprInContext? context statement
  let statementTerm :=
    statementTerm? |>.toOption.getD (mkConst ``True)
  let statementTerm' : Syntax.Term ← delabDetailed statementTerm
  let falseId := mkIdent `False
  let assId := mkIdent `assumption
  let assumeTactic ← `(tactic| intro $assId:ident)
  let fullPf := #[assumeTactic] ++ pf
  let hash := hash statement
  let statementId := mkIdent <| Name.mkSimple s!"statement_{hash}"
  return #[←
    `(tactic| have $statementId : $statementTerm':term → $falseId := by $fullPf*), ← `(tactic| auto?)]


elab "#tactic_trythis" goal:term "by" tacticCode:tactic "log" : command =>
  Command.liftTermElabM do
  let goal ← elabType goal
  let tacs? ← runTacticsAndGetTryThis? goal #[tacticCode]
  match tacs? with
    | some tacs => do
      logInfo "Tactics found:"
      for tac in tacs do
        logInfo m!"Tactic: {← ppTactic tac}"
    | none => do
      logInfo "No tactics found"
      return ()

def resolveExistsHave (type : Syntax.Term) (typeTerm? : Option Syntax.Term :=none) : TermElabM <| Array Syntax.Tactic := do
  let existsVarTypes? ← existsVarTypesStx type
  let existsVarTypes := existsVarTypes?.getD #[]
  let existsVarTypeIdents := existsVarTypes.map fun (n, t) =>
    let hsh := hash t.raw.reprint
    let tId := mkIdent <| Name.mkSimple s!"assert_{hsh}"
    (n, tId)
  let hash₀ := hash type.raw.reprint
  let typeIdent : Syntax.Term := typeTerm?.getD <| mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let rhsIdents :=
    #[typeIdent] ++ existsVarTypeIdents.map fun (_, tId) => tId
  (existsVarTypeIdents.zip rhsIdents).mapM
    fun ((name, tId), rhs) =>
      `(tactic| let ⟨$name, $tId⟩  := $rhs:term)

def cmdResolveExistsHave (type : Syntax.Term) : TermElabM <| Array Syntax.Command := do
  let existsVarTypes? ← existsVarTypesStx type
  let existsVarTypes := existsVarTypes?.getD #[]
  let mut cmds : Array Syntax.Command := #[]
  let existsFst := mkIdent ``Exists.fst
  let existsSnd := mkIdent ``Exists.snd
  let existsVarTypeIdents : Array (Ident ×  Ident × Term) := existsVarTypes.map fun (n, t) =>
    let hsh := hash t.raw.reprint
    let tId := mkIdent <| Name.mkSimple s!"assert_{hsh}"
    (n, tId, type)
  let hash₀ := hash type.raw.reprint
  let typeIdent : Syntax.Term := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let mut prevTypeIdent := typeIdent
  for (name, tId, type) in existsVarTypeIdents do
    let defCmd ←
      `(command| def $name  := $existsFst $prevTypeIdent:term)
    cmds := cmds.push defCmd
    let thmCmd ← `(command| theorem $tId : $type  := $existsSnd $prevTypeIdent:term)
    cmds := cmds.push thmCmd
    prevTypeIdent := tId
  return cmds


def haveForAssertion (goal: Expr)
  (premises: List Name) :
    TermElabM <| Array Syntax.Tactic := do
  let type ← delabDetailed goal
  let hash₀ := hash type.raw.reprint
  let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let ids := premises.toArray.map fun n => Lean.mkIdent n
  let existsTacs ←
    resolveExistsHave type
  let headTacs? ←
    runTacticsAndGetTryThis? goal #[← `(tactic| auto? [$ids,*])]
  if headTacs?.isNone then
    IO.eprintln s!"No tactics found for {← PrettyPrinter.ppExpr goal} while running "
  let headTacs := headTacs?.getD #[← `(tactic| sorry)]
  let head ← `(tactic| have $name : $type := by $headTacs*)
  return #[head] ++ existsTacs


def calculateTactics (js: Json) (context: Array Json) (qp: CodeGenerator) :
    TranslateM <| Array Syntax.Tactic := do
  let statements ←  calculateStatement js
  statements.mapM fun statement => do
    let type? ← theoremExprInContext? context statement qp
    match type? with
      | Except.error e =>
        IO.eprintln s!"Failed to translate calculation: {repr e}"
        mkNoteTactic s!"Failed to translate calculation {js.compress}"
      | Except.ok type =>
        let typeStx ← delabDetailed type
        let hash := hash statement
        let name := mkIdent <| Name.mkSimple s!"calculation_{hash}"
        let headTacs? ←
          runTacticsAndGetTryThis? type #[← `(tactic| auto?)]
        if headTacs?.isNone then
          IO.eprintln s!"No tactics found for {← PrettyPrinter.ppExpr type} while running "
        let headTacs := headTacs?.getD #[← `(tactic| sorry)]
        `(tactic| have $name : $typeStx := by
            $headTacs*)

def conditionCases (cond₁ cond₂ : String)
    (pf₁ pf₂ : Array Syntax.Tactic) (context: Array Json) (qp: CodeGenerator)  : TranslateM <| Array Syntax.Tactic := do
  let condProp₁? ← theoremExprInContext?  context cond₁ qp
  let condProp₂? ← theoremExprInContext?  context cond₂ qp
  match condProp₁?, condProp₂? with
  | Except.error _, _ => do
    return #[← mkNoteTactic s!"Failed to translate condition {cond₁}"]
  | _, Except.error _ => do
    return #[← mkNoteTactic s!"Failed to translate condition {cond₂}"]
  | Except.ok condProp₁, Except.ok condProp₂ => do
  let condTerm₁ ← delabDetailed condProp₁
  let condTerm₂ ← delabDetailed condProp₂
  let condTerm₁' : Syntax.Term := ⟨condTerm₁⟩
  let condTerm₂' : Syntax.Term := ⟨condTerm₂⟩
  let hash := hash cond₂
  let condId₂ := mkIdent <| Name.mkSimple s!"cond_{hash}"
  let headTacs? ←
    runTacticsAndGetTryThis? condProp₂ #[← `(tactic| auto?)]
  if headTacs?.isNone then
    IO.eprintln s!"No tactics found for {← PrettyPrinter.ppExpr condProp₂} while running "
  let headTacs := headTacs?.getD #[← `(tactic| sorry)]
  let ass₂ ← `(tactic| have $condId₂ : $condTerm₂' := by
    $headTacs*)
  let pf₂' := #[ass₂] ++ pf₂
  return #[← `(tactic| if $condTerm₁' then $pf₁* else $pf₂'*)]


-- #tactic_trythis (∀ _n: Nat,(1 : Nat) ≤  7) by auto? log

def groupCasesGoals (goal: MVarId) (context : Array Json) (conds: List String)
    (qp: CodeGenerator) : TranslateM <| List MVarId := goal.withContext do
    match conds with
    | [] => return [goal]
    | [_] => return [goal]
    | h :: t => do
      let tacs ← ifSkeleton context h qp
      let splitGoals ← runAndGetMVars goal #[tacs] 2
      let tailGoals ← groupCasesGoals (splitGoals[1]!) context t qp
      return splitGoals[0]! :: tailGoals

def _root_.Lean.Json.getJsonList? (js: Json) (key: String) :
  Except String (List Json) :=
  match js.getObjValAs? (List Json) key with
  | Except.ok arr => Except.ok arr
  | Except.error e =>
    match js.getKV? with
    | some (k, v) =>
      if k.containsSubstr "doc" then
        v.getObjValAs? (List Json) key
      else
        Except.error s!"Expected key `doc` in {js.compress}, found {k} instead"
    | none => Except.error e


-- #check String.containsSubstr "hello" "hel"

-- #check Json.getObj?

namespace expr

-- TODO: Correct the `goal` passed in various cases.
mutual
  partial def structToCommand? (context: Array Json)
      (input: Json) (qp: CodeGenerator) : TranslateM <| Option Syntax.Command :=
      do
      match input.getKV? with
      | some ("theorem", v) =>
        -- logInfo s!"Found theorem"
        let name? := v.getObjString? "name" |>.map String.toName
        let name? := name?.filter (· ≠ Name.anonymous)
        let hypothesis :=
          v.getObjValAs? (Array Json) "hypothesis"
            |>.toOption.getD #[]
        match v.getObjValAs? String "conclusion", v.getObjVal? "proof" with
        | Except.ok claim, Except.ok (.arr steps) =>
            let thm? ← theoremExprInContext?  (context ++ hypothesis) claim qp
            match thm? with
            | Except.error _ =>
              mkNoteCmd s!"Failed to translate theorem {claim}"
            | Except.ok thm => do
              -- IO.eprintln s!"Theorem: {← PrettyPrinter.ppExpr thm}"
              let mvar ← mkFreshExprMVar thm
              let mvarId := mvar.mvarId!
              let vars ← getVars thm
              let varIds := vars.toArray.map fun n => Lean.mkIdent n
              let introTacs ← `(tactic| intro $varIds*)
              let (_, mvarId) ← mvarId.introN vars.length vars
              mvarId.withContext do
                let pf ←
                  structToTactics mvarId #[] (context ++ hypothesis) steps.toList qp
                let pf := #[introTacs] ++  pf
                let pfTerm ← `(by $pf*)
                -- IO.eprintln s!"Proof term: {← ppTerm {env := ← getEnv} pfTerm}"
                let name ← match name? with
                  | some n => pure n
                  | none => qp.server.theoremName (← PrettyPrinter.ppExpr thm).pretty
                mkStatementStx name (← delabDetailed thm) pfTerm true
        | _, _ =>
          -- logInfo s!"failed to get theorem conclusion or proof"
          mkNoteCmd "No theorem conclusion or proof found"
      | some ("def", v) =>
        match v.getObjValAs? String "statement", v.getObjValAs? String "term" with
        | Except.ok s, Except.ok t =>
          let statement := s!"We define {t} as follows:\n{s}."
          defnInContext? context statement qp
        | _ , _ => return none
      | _ => mkNoteCmd s!"Json not a KV pair {input.compress}"


  partial def structToTactics (goal: MVarId) (accum: Array Syntax.Tactic)
    (context: Array Json)(input: List Json)
    (qp: CodeGenerator) : TranslateM <| Array Syntax.Tactic := goal.withContext do
      match input with
      | [] => do
        let headTacs? ←
          runTacticsAndGetTryThis? (← goal.getType) #[← `(tactic| auto?)]
        if headTacs?.isNone then
          IO.eprintln s!"No tactics found for {← PrettyPrinter.ppExpr <| ← goal.getType} while running "
        let headTacs := headTacs?.getD #[← `(tactic| sorry)]
        return accum ++ headTacs
      | head :: tail => do
        let headTactics: Array Syntax.Tactic ←
          match head.getKV? with
          | some ("assert", head) =>
            match head.getObjValAs? String "claim" with
            | Except.ok claim =>
              let mut useResults: Array String := #[]
              let mut prevTacs : Array Syntax.Tactic := #[]
              match head.getObjVal? "deduced_from_results"  with
              | Except.ok known =>
                match known.getKV? with
                | some ("deduced_from", .arr results) =>
                  for js in results do
                    match js.getObjString? "result_used", js.getObjValAs? Bool "proved_earlier" with
                    | some s, Except.ok false => useResults := useResults.push s
                    | some s, Except.ok true =>
                      let type? ← theoremExprInContext? context s qp
                      match type? with
                      | Except.ok e =>
                        let stx ← delabDetailed e
                        let name := mkIdent <| Name.mkSimple s
                        let tacs ← runTacticsAndGetTryThisI e #[← `(tactic| auto?)]
                        prevTacs := prevTacs.push <| ← `(tactic| have $name : $stx := by
                          $tacs*)
                      | _ => pure ()
                    | _, _ => pure ()
                | _ => pure ()
              | _ => pure ()
              match head.getObjVal? "calculate" with
              | Except.ok js =>
                let tac ← calculateTactics js context qp
                prevTacs := prevTacs ++ tac
              | _ => pure ()
              let type? ← theoremExprInContext? context claim qp
              match type? with
              | Except.error _ =>
                IO.eprintln s!"Failed to translate assertion {claim}"
                pure #[← mkNoteTactic s!"Failed to translate assertion {claim}"]
              | Except.ok type =>
                let names' ← useResults.toList.mapM fun s =>
                  Translator.matchingTheoremsAI   (s := s) (qp:= qp)
                let premises := names'.flatten
                let tacs ←
                  goal.withContext do
                  haveForAssertion type  premises
                pure <| prevTacs ++ tacs
            | _ => pure #[]
          | some ("define", head) =>
            match ← goal.withContext do structToCommand? context head qp with
            | some cmd =>
              let tac ← commandToTactic  <| ←  purgeLocalContext cmd
              pure #[tac]
            | none => pure #[]
          | some ("theorem", head) =>
            match (← goal.withContext do structToCommand? context head qp) with
            | some cmd =>
              let tac ← commandToTactic  <| ←  purgeLocalContext cmd
              pure #[tac]
            | none => pure #[]
          | some ("cases", head) =>
            match head.getObjValAs? (Array Json) "proof_cases" with
            | Except.ok cs =>
              let conds := cs.filterMap fun js =>
                match js.getKV? with
                | some ("case", js) => js.getObjString? "condition"
                | _ => none
              let newGoals : List MVarId ←
                match head.getObjString? "split_kind" with
                | "group" =>
                  groupCasesGoals goal context conds.toList qp
                | "condition" =>
                  match conds.toList with
                  | [cond₁, _] =>
                    let tac ← ifSkeleton context cond₁ qp
                    runAndGetMVars goal #[tac] 2
                  | _ =>
                    pure [goal, goal]
                | "match" =>
                  match head.getObjString? "on" with
                  | some discr =>
                    let casesTac ← matchCasesSkeleton discr conds
                    runAndGetMVars goal #[casesTac] 2
                  | _ => pure <| List.replicate conds.size goal
                | _ =>
                  groupCasesGoals goal context conds.toList qp
              let conditionProofs ←
                (cs.zip newGoals.toArray).filterMapM fun (js, newGoal) =>
                match js.getKV? with
                | some ("case", js) =>
                  match js.getObjString? "condition",
                    js.getJsonList? "proof" with
                  | some cond, Except.ok pfSource => do
                    let pf ← structToTactics newGoal #[] context pfSource qp
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
                let exType ← exhaustiveType goal context conds.toList qp
                let union_pf : Array Syntax.Tactic ←
                  match head.getJsonList? "exhaustiveness" with
                  | Except.ok pfSource =>
                    let mvar ← mkFreshExprMVar exType
                    structToTactics mvar.mvarId! #[] context pfSource qp
                  | _ => runTacticsAndGetTryThisI exType #[← `(tactic| auto?)]
                groupCases context conditionProofs.toList union_pf qp none
              | some "condition" =>
                match conditionProofs with
                | #[(cond₁, pf₁), (cond₂, pf₂)] =>
                  conditionCases cond₁ cond₂ pf₁ pf₂ context qp
                | _ => pure #[]
              | _ => /- treat like a group but with conditions as claims;
                      works for `iff` -/
                let exType ← exhaustiveType goal context conds.toList qp
                let union_pf : Array Syntax.Tactic ←
                  runTacticsAndGetTryThisI exType #[← `(tactic| auto?)]
                groupCases context conditionProofs.toList union_pf qp none
            | _ =>
              pure #[]
          | some ("induction", head) =>
            match head.getObjValAs? String "on",
              head.getObjValAs? (Array Json) "proof_cases" with
            | Except.ok name, Except.ok cs =>
              let skeletonTac ←
                inductionCasesSkeleton name <|
                  cs.filterMap fun js => js.getObjString? "condition"
              let newGoals ← runAndGetMVars goal #[skeletonTac] cs.size
              let cs' := cs.zip newGoals.toArray
              let conditionProofs ← cs'.filterMapM fun (js, newGoal) =>
                match js.getKV? with
                | some ("case", js) =>
                  match js.getObjString? "condition",
                    js.getJsonList? "proof" with
                  | some cond, Except.ok pfSource => do
                    let pf ← structToTactics newGoal #[] context pfSource qp
                    return some (cond, pf)
                  | _, _ => return none
                | _ => return none
              inductionCases name conditionProofs
            | _, _ => pure #[]
          | some ("contradiction", head) =>
            match head.getObjValAs? String "assumption",
              head.getJsonList? "proof" with
            | Except.ok s, Except.ok pf => do
              let fe := mkIdent ``False.elim
              let newGoals ← runAndGetMVars goal #[← `(tactic|apply $fe)] 1
              let proof? ← newGoals.head?.mapM fun goal =>
                structToTactics goal #[] context pf qp
              let proof := proof?.getD #[]
              let tacs ← contradictionTactics s proof context qp
              runTacticsAndGetTryThisI (← goal.getType) tacs
            | _, _ => pure #[]
          | some ("conclude", head) =>
            match head.getObjValAs? String "claim" with
            | Except.ok s => pure #[← conclusionTactic s context qp]
            | _ =>
              IO.eprintln s!"Failed to translate conclusion {head}"
              pure #[]
          | some ("calculate", js) =>
            calculateTactics js context qp
          | _ =>
            pure #[]
        -- IO.eprintln s!"Head tactics : {headTactics.size}"
        let newGoals ← runAndGetMVars goal  headTactics 1 true
        match newGoals.head? with
        | none =>
          IO.eprintln s!"Failed to get new goal"
          return accum
        | some newGoal =>
          structToTactics newGoal (accum ++ headTactics) (context.push head) tail qp

end
end expr


namespace stx
mutual
  partial def structToCommand? (context: Array Json)
      (input: Json) (qp: CodeGenerator) : TranslateM <| Option Syntax.Command := do
      match input.getKV? with
      | some ("theorem", v) =>
        -- logInfo s!"Found theorem"
        let name? := v.getObjString? "name" |>.map String.toName
        let name? := name?.filter (· ≠ Name.anonymous)
        let hypothesis :=
          v.getObjValAs? (Array Json) "hypothesis"
            |>.toOption.getD #[]
        match v.getObjValAs? String "conclusion", v.getObjVal? "proof" with
        | Except.ok claim, Except.ok (.arr steps) =>
            let thm? ← theoremExprInContext?  (context ++ hypothesis) claim qp
            match thm? with
            | Except.error _ =>
              mkNoteCmd s!"Failed to translate theorem {claim}"
            | Except.ok thm => do
              let mvar ← mkFreshExprMVar thm
              let mvarId := mvar.mvarId!
              let vars ← getVars thm
              let varIds := vars.toArray.map fun n => Lean.mkIdent n
              let introTacs ← `(tactic| intro $varIds*)
              let (_, mvarId) ← mvarId.introN vars.length vars
              mvarId.withContext do
                let pf ←
                  structToTactics #[] (context ++ hypothesis) steps.toList qp (some thm)
                let pf := #[introTacs] ++  pf
                let pfTerm ← `(by $pf*)
                -- IO.eprintln s!"Proof term: {← ppTerm {env := ← getEnv} pfTerm}"
                mkStatementStx name? (← delabDetailed thm) pfTerm true
        | _, _ =>
          -- logInfo s!"failed to get theorem conclusion or proof"
          mkNoteCmd "No theorem conclusion or proof found"
      | some ("def", v) =>
        match v.getObjValAs? String "statement", v.getObjValAs? String "term" with
        | Except.ok s, Except.ok t =>
          let statement := s!"We define {t} as follows:\n{s}."
          defnInContext? context statement qp
        | _ , _ => return none
      | _ => mkNoteCmd s!"Json not a KV pair {input.compress}"

  partial def structToTactics  (accum: Array Syntax.Tactic)
    (context: Array Json)(input: List Json)
    (qp: CodeGenerator) (goal?: Option Expr): TranslateM <| Array Syntax.Tactic := do
      match input with
      | [] => return accum.push <| ← `(tactic| auto?)
      | head :: tail =>
        -- IO.eprintln s!"Processing {head}"
        let headTactics: Array Syntax.Tactic ←
          match head.getKV? with
          | some ("assert", head) =>
            match head.getObjValAs? String "claim" with
            | Except.ok claim =>
              let mut useResults: Array String := #[]
              let mut prevTacs : Array Syntax.Tactic := #[]
              match head.getObjVal? "deduced_from_results"  with
              | Except.ok known =>
                match known.getKV? with
                | some ("deduced_from", .arr results) =>
                  for js in results do
                    match js.getObjString? "result_used", js.getObjValAs? Bool "proved_earlier" with
                    | some s, Except.ok false => useResults := useResults.push s
                    | some s, Except.ok true =>
                      let type? ← theoremExprInContext? context s qp
                      match type? with
                      | Except.ok e =>
                        let stx ← delabDetailed e
                        let name := mkIdent <| Name.mkSimple s
                        prevTacs := prevTacs.push <| ← `(tactic| have $name : $stx := by
                          auto?)
                      | _ => pure ()
                    | _, _ => pure ()
                | _ => pure ()
              | _ => pure ()
              match head.getObjVal? "calculate" with
              | Except.ok js =>
                let tac ← calculateTactics js context qp
                prevTacs := prevTacs ++ tac
              | _ => pure ()
              let type? ← theoremExprInContext? context claim qp
              match type? with
              | Except.error _ =>
                IO.eprintln s!"Failed to translate assertion {claim}"
                pure #[← mkNoteTactic s!"Failed to translate assertion {claim}"]
              | Except.ok type =>
                let names' ← useResults.toList.mapM fun s =>
                  Translator.matchingTheoremsAI   (s := s) (qp:= qp)
                let premises := names'.flatten
                let tacs ← haveForAssertion type  premises
                pure <| prevTacs ++ tacs
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
                    js.getJsonList? "proof" with
                  | some cond, Except.ok pfSource => do
                    let pf ← structToTactics #[] context pfSource qp goal?
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
                  match head.getJsonList? "exhaustiveness" with
                  | Except.ok pfSource =>
                    structToTactics #[] context pfSource qp goal?
                  | _ => pure #[← `(tactic| auto?)]
                groupCases context conditionProofs.toList union_pf qp goal?
              | some "condition" =>
                match conditionProofs with
                | #[(cond₁, pf₁), (cond₂, pf₂)] =>
                  conditionCases cond₁ cond₂ pf₁ pf₂ context qp
                | _ => pure #[]
              | _ => /- treat like a group but with conditions as claims;
                      works for `iff` -/
                let union_pf : Array Syntax.Tactic ←
                  pure #[← `(tactic| auto?)]
                groupCases context conditionProofs.toList union_pf qp goal?
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
                    js.getJsonList? "proof" with
                  | some cond, Except.ok pfSource => do
                    let pf ← structToTactics #[] context pfSource qp goal?
                    return some (cond, pf)
                  | _, _ => return none
                | _ => return none
              inductionCases name conditionProofs
            | _, _ => pure #[]
          | some ("contradiction", head) =>
            match head.getObjValAs? String "assumption",
              head.getJsonList? "proof" with
            | Except.ok s, Except.ok pf =>
              let proof ← structToTactics #[] context pf qp goal?
              contradictionTactics s proof context qp
            | _, _ => pure #[]
          | some ("conclude", head) =>
            match head.getObjValAs? String "claim" with
            | Except.ok s => pure #[← conclusionTactic s context qp]
            | _ =>
              IO.eprintln s!"Failed to translate conclusion {head}"
              pure #[]
          | some ("calculate", js) =>
            calculateTactics js context qp
          | _ =>
            pure #[]
        -- IO.eprintln s!"Head tactics"
        -- for tac in headTactics do
        --   IO.eprintln s!"{← ppTactic tac}"
        structToTactics (accum ++ headTactics) (context.push head) tail qp goal?

end
end stx

open expr

def structToCommandSeq? (context: Array Json)
    (input: Json) (qp: CodeGenerator) : TranslateM <| Option <| Array Syntax.Command := do
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
          IO.eprintln s
          let cmd ←
            mkNoteCmd s
          cmds := cmds.push cmd
        pure ()
      ctx := ctx.push j
    match cmds with
    | #[] => return none
    | _ => pure <| some  cmds
  | _ => return none

def mathDocumentCommands (doc: Json) (qp: CodeGenerator) :
  TranslateM <| Array Syntax.Command := do
    match doc.getKV? with
    | some  ("math_document", proof) =>
      let cmds? ←
        structToCommandSeq? #[] proof qp
      return cmds?.getD #[← mkNoteCmd "No commands found"]
    | _ => return #[← mkNoteCmd "No math document found"]

def namesFromCommands (cmds: Array Syntax.Command) : Array Name :=
  cmds.foldl (fun acc cmd =>
    match cmd with
    | `(command| theorem $name:ident $_:bracketedBinder* : $_ := $_) => acc.push name.getId
    | `(command| def $name:ident $_:bracketedBinder* : $_ := $_) => acc.push name.getId
    | _ => acc) #[]

def mathDocumentCode (doc: Json) (qp: CodeGenerator) :
  TranslateM <| Format × Array Name := do
    let cmds ←
       mathDocumentCommands doc qp
    let cmds' ← cmds.mapM fun cmd => do
      let cmd' ← PrettyPrinter.ppCommand cmd
      return cmd'
    let view : Format := cmds'.foldl (· ++ "\n" ++ ·) ""
    return (view, namesFromCommands cmds)


elab "dl!" t: term : term => do
let t ← elabType t
  let t' ← dropLocalContext t
  return t'

set_option linter.unusedVariables false in
def eg_drop (n m: Nat)  := dl! (∀ n m: Nat, n = n + 1 → False)

def thmProofStrucToCode (thm pf: String) (js: Json) (qp: CodeGenerator):
    TranslateM <| Format × Name := do
    let mut fmt : Format := s!"/-!\n## Theorem\n{thm}"
    fmt := fmt ++ "\n## Proof\n" ++ pf ++ "\n"
    fmt := fmt ++ "\n## JSON structured proof\n" ++ js.pretty ++ "-/\n"
    IO.println fmt
    let (code, names) ← mathDocumentCode js qp
    fmt := fmt ++ code
    -- IO.println fmt
    let (exprs, msgLogs) ←
      elabFrontDefsExprM code.pretty names.toList
    fmt := fmt ++ "\n\n/-!\n## Elaboration logs\n"
    for msg in msgLogs.toList do
      fmt := fmt ++ (← msg.data.format) ++ "\n"
    fmt := fmt ++ "\n"
    for (n, e) in exprs do
      fmt := fmt ++ s!"* Sorries in {n}:\n"
      let sorries ← getSorryTypes e
      for s in sorries do
        fmt := fmt ++ "\n "++ s!"* `{← PrettyPrinter.ppExpr s}`".replace "\n" " "
    fmt := fmt ++ "\n-/\n"
    return (topCode ++ fmt, names[0]!)

def statementToCode (s: String) (qp: CodeGenerator) :
  TranslateM <| Format × Name := do
    let xs ← qp.server.structuredProofFromStatement s
    match xs[0]? with
    | some (pf, #[js]) =>
      thmProofStrucToCode s pf js qp
    | _ =>
      let fmt := s!"/-!\n## Theorem\n{s}" ++ "No structured proof found"
      IO.println fmt
      return (fmt, s!"failure_{hash s}".toName)

-- #check MVarId.introN

elab "intro_experiment%" t:term : term => do
  let t ← elabType t
  let mvar ← mkFreshExprMVar t
  let mvarId := mvar.mvarId!
  let vars ← getVars t
  let (xs, mvarId) ← mvarId.introN vars.length vars
  mvarId.withContext do
    for x in xs do
      let fvar ←  x.getUserName
      logInfo m!"Intro: {fvar}"
    logInfo m!"MVar type: {← mvarId.getType}"
    let type' ← dropLocalContext t
    logInfo m!"Inner type: {← PrettyPrinter.ppExpr type'}"
  return t

-- #check intro_experiment% ∀(n m : Nat), ∀ (fin: Fin n), n = m

-- #check intro_experiment% ∀(n m : Nat), ∀ (fin: Fin n), n = m → (m = n)

elab "intro_experiment%%" t:term "vs" s:term : term => do
  let t ← elabType t
  let mvar ← mkFreshExprMVar t
  let mvarId := mvar.mvarId!
  let vars ← getVars t
  let (xs, mvarId) ← mvarId.introN vars.length vars
  mvarId.withContext do
    for x in xs do
      let fvar ←  x.getUserName
      logInfo m!"Intro: {fvar}"
    logInfo m!"MVar type: {← mvarId.getType}"
    let s ← elabType s
    let type' ← dropLocalContext s
    logInfo m!"Inner type: {← PrettyPrinter.ppExpr type'}"
  return t

-- #check intro_experiment%% (∀(n  : Nat), n = 1) vs
--     (∀(n m : Nat), ∀ (fin: Fin n), n = m → (m = n))
