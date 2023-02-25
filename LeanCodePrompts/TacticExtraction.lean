import Lean
import Mathlib.Tactic.Simps.Basic
import LeanInk.Analysis.Basic

open Lean Elab Parser Term Meta Tactic Meta

def inputFile : System.FilePath := 
"LeanCodePrompts"/"TacticExtractionTest.lean"
-- "LeanCodePrompts"/"PowTest.lean"
-- "lake-packages"/"mathlib"/"Mathlib"/"Data"/"Int"/"Dvd"/"Pow.lean"

#eval inputFile.pathExists

-- Leonardo de Moura's code for generating trace data
def getTactics : TSyntax ``tacticSeq → TSyntaxArray `tactic
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]

#check TraceElem
#check MessageData
#check Tactic.evalTraceMessage
#check getTraceState
#check TraceState
#check setOptionFromString
#check KVMap.setBool
#check elabTerm
#check PrettyPrinter.ppExpr
#check Format
#check TacticM
#check TermElabM

-- modified from `Lean.Elab.Tactic.Simp`
def traceSimpCall' (stx : Syntax) (usedSimps : Simp.UsedSimps) : MetaM Syntax := do
  let mut stx := stx
  if stx[3].isNone then
    stx := stx.setArg 3 (mkNullNode #[mkAtom "only"])
  let mut args := #[]
  let mut localsOrStar := some #[]
  let lctx ← getLCtx
  let env ← getEnv
  for (thm, _) in usedSimps.toArray.qsort (·.2 < ·.2) do
    match thm with
    | .decl declName => -- global definitions in the environment
      if env.contains declName && !simpOnlyBuiltins.contains declName then
        args := args.push (← `(Parser.Tactic.simpLemma| $(mkIdent (← unresolveNameGlobal declName)):ident))
    | .fvar fvarId => -- local hypotheses in the context
      if let some ldecl := lctx.find? fvarId then
        localsOrStar := localsOrStar.bind fun locals =>
          if !ldecl.userName.isInaccessibleUserName &&
              (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
            some (locals.push ldecl.userName)
          else
            none
      -- Note: the `if let` can fail for `simp (config := {contextual := true})` when
      -- rewriting with a variable that was introduced in a scope. In that case we just ignore.
    | .stx _ thmStx => -- simp theorems provided in the local invocation
      args := args.push ⟨thmStx⟩ 
    | .other _ => -- Ignore "special" simp lemmas such as constructed by `simp_all`.
      pure ()     -- We can't display them anyway.
  if let some locals := localsOrStar then
    args := args ++ (← locals.mapM fun id => `(Parser.Tactic.simpLemma| $(mkIdent id):ident))
  else
    args := args.push ⟨(← `(Parser.Tactic.simpStar| *))⟩ 
  let argsStx := if args.isEmpty then #[] else #[mkAtom "[", (mkAtom ",").mkSep args, mkAtom "]"]
  stx := stx.setArg 4 (mkNullNode argsStx)
  return stx

def expandTacStx : TSyntax `tactic → TacticM (TSyntax `tactic)
  | stx@`(tactic| simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
      let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
      let usedSimps ← dischargeWrapper.with fun discharge? =>
        simpLocation ctx discharge? (expandOptLocation stx.raw[5])
      return ⟨← traceSimpCall' stx usedSimps⟩
      -- `(tactic| simp) 
  | `(tactic| $tac) => do
    evalTactic tac
    return tac

elab "seq" s:tacticSeq : tactic => do
  let tacs := getTactics s
  for tac in tacs do
    let gs ← getUnsolvedGoals
    -- withRef tac <| addRawTrace (goalsToMessageData gs)
    -- withOptions (·.setBool `tactic.simp.trace true) do
    let tac' ← expandTacStx tac
    -- evalTactic tac
    withRef tac <| addRawTrace m!"[TACTIC] {tac'}"

def addSeq : TSyntax ``tacticSeq → TermElabM (TSyntax ``tacticSeq)
  | `(tacticSeq| { $[$t]* }) => `(tacticSeq| { seq $[$t]* })
  | `(tacticSeq| $[$t]*) => `(tacticSeq| seq $[$t]*)
  | _ => `(tacticSeq| seq done)

example (h : x = y) : 0 + x = y := by
  seq 
    rw [Nat.zero_add]
    rw [h]
  done


-- /-- `by tac` constructs a term of the expected type by running the tactic(s) `tac`. -/
-- def byTactic' := leading_parser:leadPrec
--   ppAllowUngrouped >> "by' " >> Tactic.tacticSeqIndentGt

-- a deep copy of Lean's `by` tactic, called `by'`
syntax (name := byTactic') "by' " tacticSeq : term

@[term_elab byTactic'] def elabByTactic' : TermElab := fun stx expectedType? => do
  match expectedType? with
  | some expectedType =>
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    let mvarId := mvar.mvarId!
    let ref ← getRef
    registerSyntheticMVar ref mvarId <| SyntheticMVarKind.tactic stx (← saveContext)
    return mvar
  | none =>
    tryPostpone
    throwError ("invalid 'by\'' tactic, expected type has not been provided")

example : 1 + 1 = 2 := by' -- the new `by'` syntax can be used to replace `by`
  rfl

-- intercepting the `by` tactic to output intermediate trace data
-- the `by'` clone is needed here to avoid infinite recursion
macro_rules
  | `(by $ts) => `(by' seq $ts) 

-- the `by` tactic now generates trace data by default
example (h : x = y) : 0 + x = y := by
  rw [h]
  simp
  done