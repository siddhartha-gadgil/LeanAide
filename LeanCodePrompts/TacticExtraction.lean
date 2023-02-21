import Lean
import LeanInk.Analysis.Basic

open Lean Elab

def inputFile : System.FilePath := 
"LeanCodePrompts"/"TacticExtractionTest.lean"
-- "LeanCodePrompts"/"PowTest.lean"
-- "lake-packages"/"mathlib"/"Mathlib"/"Data"/"Int"/"Dvd"/"Pow.lean"

#eval inputFile.pathExists

namespace LeanInk

/-! This code will likely be abandoned. -/

def tacticExtractionConfig : IO LeanInk.Configuration := return {
  inputFilePath := inputFile
  inputFileContents := ← IO.FS.readFile inputFile
  lakeFile := some $ "lake-packages"/"leanInk"/"lakefile.lean"
  verbose := true
  prettifyOutput := true
  experimentalTypeInfo := true
  experimentalDocString := false
  experimentalSemanticType := false
}

def options : Options :=
  Options.empty 
    |>.set `trace.Elab.info true
    |>.set `tactic.simp.trace true

-- modified from `LeanInk` source
open LeanInk in
def analyzeInput' : AnalysisM Analysis.AnalysisResult := do
  let config ← tacticExtractionConfig 
  let context := Parser.mkInputContext config.inputFileContents config.inputFileName
  let (header, state, messages) ← Parser.parseHeader context
  -- doc-gen: Lake already configures us via LEAN_PATH
  -- initializeSearchPaths header config
  let (environment, messages) ← processHeader header options messages context 0
  logInfo s!"Header: {environment.header.mainModule}"
  logInfo s!"Header: {environment.header.moduleNames}"
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        let _ ← logError (← msg.toString)
    throw <| IO.userError "Errors during import; aborting"
  let commandState := Analysis.configureCommandState environment messages
  let s ← IO.processCommands context state commandState
  let result ← Analysis.resolveTacticList s.commandState.infoState.trees.toList
  let messages := s.commandState.messages.msgs.toList --.filter (·.endPos.isSome)
  return ← result.insertMessages messages context.fileMap

#check MessageLog

def tacticData : IO <| List LeanInk.Analysis.Sentence := do
  let config ← tacticExtractionConfig
  let result ← analyzeInput'.run config 
  return result.sentences

instance : ToString LeanInk.Analysis.Goal where
  toString goal := toString goal.conclusion

instance : ToString LeanInk.Analysis.Tactic where
  toString t := toString t.goalsAfter

instance (priority := high) : ToString LeanInk.Analysis.Sentence where
  toString
    | .tactic t => s!"[TACTIC:{t.headPos}-{t.tailPos}]" ++ toString t
    | .message m => "[MESSAGE]" ++ m.msg

def tacticDataStrings : IO <| List String := do
  let tacs ← tacticData
  return tacs.map toString 
  -- TODO replace the default `toString` instance with a more descriptive one

-- #eval tacticDataStrings

end LeanInk

open Lean Parser Term Meta Tactic

-- Leonardo de Moura's code for generating trace data
def getTactics (s : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match s with
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]

elab "seq" s:tacticSeq : tactic => do
  let tacs := getTactics  s
  for tac in tacs do
    let gs ← getUnsolvedGoals
    withRef tac <| addRawTrace (goalsToMessageData gs)
    evalTactic tac

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
  rw [h]; rw [Nat.zero_add]
  done