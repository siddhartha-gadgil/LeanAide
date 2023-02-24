import Lean
import Mathlib.Tactic.Simps.Basic
import LeanInk.Analysis.Basic

open Lean Elab

def inputFile : System.FilePath := 
"LeanCodePrompts"/"TacticExtractionTest.lean"
-- "LeanCodePrompts"/"PowTest.lean"
-- "lake-packages"/"mathlib"/"Mathlib"/"Data"/"Int"/"Dvd"/"Pow.lean"

#eval inputFile.pathExists

open Lean Parser Term Meta Tactic

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

elab "seq" s:tacticSeq : tactic => do
  let tacs := getTactics s
  for tac in tacs do
    let gs ← getUnsolvedGoals
    let toStxLog := withRef tac
    toStxLog <| addRawTrace (goalsToMessageData gs)
    withOptions (·.setBool `tactic.simp.trace true) do

    -- match tac with
    --   | `(tactic| simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    --     toStxLog <| addRawTrace (m!"simp")
    --   | tac@_ => withRef tac <| addRawTrace (m!"other") 
      evalTactic tac
      toStxLog <| addRawTrace m!"[TACTIC] {tac}"

example (h : x = y) : 0 + x = y := by
  seq rw [Nat.zero_add]; rw [h]
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
  simp [Nat.zero_add]
  done