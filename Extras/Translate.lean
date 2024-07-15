import Lean
import Lean.Meta
import Lean.Parser
import LeanAide.TheoremElab
import LeanAide.Lean4Names
import LeanAide.TheoremEquality
import LeanAide.IP
import LeanCodePrompts.SpawnNearestEmbeddings
import Lean.Meta.Tactic.TryThis
import Std.Util.Pickle
import LeanCodePrompts.Translate

open Lean Meta Elab Parser Command
open Lean.Meta.Tactic

def fileName := "resources/mathlib4-prompts.json"

def lean4mode := decide (fileName ∈ ["resources/mathlib4-prompts.json",
        "resources/mathlib4-thms.json"])

def docField :=
        if lean4mode then "docString" else "doc_string"

def theoremField :=
        if lean4mode then "type" else "theorem"

/-- extract prompt pairs from JSON response to local server -/
def sentenceSimPairs
  (s: String)
  (theoremField : String := theoremField)
   : IO  <| Except String (Array (String × String)) := do
  let json := Lean.Json.parse  s |>.toOption.get!
  return do
    (← json.getArr?).mapM <| fun j => do
      let lean4mode := fileName ∈ ["resources/mathlib4-prompts.json",
        "resources/mathlib4-thms.json"]
      let docstring ← j.getObjValAs? String docField
      let typeField :=
        if lean4mode then "type"
        else theoremField
      let thm ← j.getObjValAs? String typeField
      pure (docstring, thm)

-- #eval sentenceSimPairs egSen


def getPromptPairsBert(s: String)(numSim : Nat)
   : IO <| Except String (Array (String × String)) := do
      let jsData := Json.mkObj [
        ("filename", fileName),
        ("field", docField),
        (docField, s),
        ("n", numSim),
        ("model_name", "all-mpnet-base-v2")
      ]
      let simJsonOut ←
        IO.Process.output {cmd:= "curl", args:=
          #["-X", "POST", "-H", "Content-type: application/json", "-d", jsData.pretty, s!"{← leanAideIP}/nearest_prompts"]}
      unless simJsonOut.exitCode == 0 do
        return Except.error s!"curl failed with exit code {simJsonOut.exitCode}¬{simJsonOut.stderr}"
      let pairs? ← sentenceSimPairs simJsonOut.stdout theoremField
      -- IO.println s!"obtained sentence similarity; time : {← IO.monoMsNow}"
      let allPairs : Array (String × String) ←
        match pairs? with
        | Except.error e =>
            return Except.error e
        | Except.ok pairs => pure pairs
      -- logInfo m!"all pairs: {allPairs}"
      let allPairs := allPairs.toList.eraseDups.toArray
      return Except.ok allPairs.toList.eraseDups.toArray

/-- choosing example theorems to build a prompt -/
def getPromptPairsGeneral(s: String)(numSim : Nat)(field: String := docField)
    (theoremField : String := theoremField)
   : TermElabM (Array (String × String) × IO.Process.Output) := do
      let jsData := Json.mkObj [
        ("filename", fileName),
        ("field", field),
        (field, s),
        ("n", numSim),
        ("model_name", "all-mpnet-base-v2")
      ]
      let simJsonOut ←
        IO.Process.output {cmd:= "curl", args:=
          #["-X", "POST", "-H", "Content-type: application/json", "-d", jsData.pretty, s!"{← leanAideIP}/nearest_prompts"]}
      let pairs? ← sentenceSimPairs simJsonOut.stdout theoremField
      -- IO.println s!"obtained sentence similarity; time : {← IO.monoMsNow}"
      let allPairs : Array (String × String) ←
        match pairs? with
        | Except.error e =>
            throwError e

        | Except.ok pairs => pure pairs
      -- logInfo m!"all pairs: {allPairs}"
      return (
          allPairs.toList.eraseDups.toArray, simJsonOut)


/-- make prompt for reverse translation from prompt pairs -/
@[deprecated makeFlipPrompt]
def makeFlipPrompt'(statement : String)(pairs: Array (String × String)) : String :=
      pairs.foldr (fun  (ds, thm) acc =>
s!"theorem {thm} :=
/- {ds} -/

{acc}"
          ) s!"theorem {statement} :=
/- "


/-- make prompt from prompt pairs -/
@[deprecated mkMessages']
def makePrompt(prompt : String)(pairs: Array (String × String)) : String :=
      pairs.foldr (fun  (ds, thm) acc =>
        -- acc ++ "/-- " ++ ds ++" -/\ntheorem" ++ thm ++ "\n" ++ "\n"
s!"/-- {ds} -/
theorem {thm} :=

{acc}"
          ) s!"/-- {prompt} -/
theorem "



def egPairs := getPromptPairsGeneral egThm 5 "statement" "statement"

def egPrompt := do
  let (pairs, _) ← egPairs
  return makeFlipStatementsPrompt egThm pairs
