import LeanAideCore.Aides
import LeanAideCore.ChatClient
import LeanAideCore.Translator
import LeanAideCore.RunTactics
import LeanAideCore.PaperCodes

open Lean Meta Elab Tactic LeanAide ChatServer Nat
syntax (name:=llmSyntax) "llm?" : tactic
syntax (name:=llmSorrySyntax) "llm_with_sorries?" : tactic

def extractProof? (s : String) : Option String :=
  match s.splitOn "by" with
  -- If the list is empty or has only one element, "by" was not found.
  | [] => none
  | [_] => none
  -- If "by" is found, `rest` contains everything after the first "by".
  -- We intercalate it back with "by" just in case there were multiple "by"s.
  | _ :: rest => some (String.intercalate "by" rest)


def prompt : Json := json%
  {
    "role": "system",
    "content": "You are an expert mathematician and Lean 4 theorem proving assistant. Your task is to replace the `sorry` placeholders in the provided Lean 4 code with valid, compiling proof terms or tactic scripts.\n\nStrict Guidelines:\n1. Lean 4 & Mathlib4 Only: Write idiomatic Lean 4 code. Do not use Lean 3 syntax or deprecated tactics (e.g., use `by` with indentation, no commas between tactics). Rely heavily on standard Mathlib4 tactics like `intro`, `apply`, `rw`, `exact`, `simp`, `linarith`, `ring`, `omega`, and `aesop` where appropriate.\n2. Preserve Signatures: Do not modify the theorem statement, its name, the hypotheses, or any preceding imports and definitions. Your only job is to replace `sorry`.\n3. Complete the Proof: Ensure the proof is complete and leaves no remaining `sorry` or open goals.\n4. Minimal Output: Output ONLY the completed Lean 4 code block. Do not include conversational filler, explanations, or introductory text outside of the code block unless explicitly asked.\n\nOutput Format:\nWrap your completed Lean code in a standard markdown code block starting with ```lean."
  }

@[tactic llmSyntax]
def llmTactic : Tactic
  | stx@`(tactic| llm?) =>
      withMainContext do
      let goalmVar ← getMainGoal
      let goalExpr ← ppGoal goalmVar
      -- let dir ← getBaseDir
      --logInfo m!"Goal expression: {goalExpr}"
      let newThmStatement ← ("import Mathlib\n example :"++ m!"{goalExpr} := by sorry").toString
      --let mathPrompt ← mathPrompt
      let messages := Json.arr #[prompt,Json.mkObj [("role","user"),("content", "In the following Lean code, replace the sorry by valid proof:\n ```lean \n"++ newThmStatement ++"\n ``` \n Give only the LEAN code")]]
      let response ← query (← chatServer) (messages) {}
      let choices ← match response.getObjVal? "choices" with
        | Except.ok c => pure c
        | Except.error e => throwError e
      let content ← getMessageContents choices
      let code := extractLean content[0]!
      let proof? := extractProof? code
      match proof? with
      | some proof? =>
          let leanproof? ← getTacticsFromText? proof?
          match leanproof? with
          | some (leanproof, hasSorry) =>
              if hasSorry then
                throwError "The extracted proof still contains sorry."
              else
                TryThis.addSuggestion stx leanproof
          | none => throwError "Could not extract tactics from the LLM response."
      | none => throwError "Could not extract proof from the LLM response."
      --logInfo m!"{goalExpr}"
  | _ => throwError "Unexpected syntax"

def prompt_sorry : Json := json%
 {
 "role": "system",
 "content": "You are an expert mathematician and Lean 4 theorem proving assistant. Your task is to replace the `sorry` placeholders in the provided Lean 4 code with valid, compiling proof terms or tactic scripts.\n\nStrict Guidelines:\n1. Lean 4 & Mathlib4 Only: Write idiomatic Lean 4 code. Do not use Lean 3 syntax or deprecated tactics (e.g., use `by` with indentation, no commas between tactics). Rely heavily on standard Mathlib4 tactics like `intro`, `apply`, `rw`, `exact`, `simp`, `linarith`, `ring`, `omega`, and `aesop` where appropriate.\n2. Maximize Automation: Use automation, especially the `grind` tactic, wherever possible to close goals efficiently.\n3. Tactic Preferences: *Rely more heavily on `simp` rather than `simpa` for simplification tasks*.\n4. Leverage Context: Carefully check the given variables and hypotheses in the local context. Make sure to use them whenever possible to drive the proof forward.*Take care not to add any variable which is not defined in the context or explicitly by you*.\n5. Preserve Signatures: Do not modify the theorem statement, its name, the hypotheses, or any preceding imports and definitions.\n6. Strategic Use of Sorry: You do not need to complete the proof at all costs. If you are unsure about a specific theorem name, a definition, or how to close a goal/subgoal made by a hypothesis, *you can use `sorry` to close it*.You must not give wrong definitions or theorems at any cost. However, you MUST move forward with the proof at all costs, outlining the rest of the logical steps and structure even if intermediate steps rely on `sorry`.\n7. Minimal Output: Output ONLY the completed Lean 4 code block. Do not include conversational filler, explanations, or introductory text outside of the code block unless explicitly asked.\n\nOutput Format:\nWrap your completed Lean code in a standard markdown code block starting with ```lean."
 }

@[tactic llmSorrySyntax]
def llmSorryTactic : Tactic
  | stx@`(tactic| llm_with_sorries?) =>
      withMainContext do
      let goalmVar ← getMainGoal
      let goalExpr ← ppGoal goalmVar
      -- let dir ← getBaseDir
      --logInfo m!"Goal expression: {goalExpr}"
      let newThmStatement ← ("import Mathlib\n example :"++ m!"{goalExpr} := by sorry").toString
      --let mathPrompt ← mathPrompt
      let messages := Json.arr #[prompt_sorry,Json.mkObj [("role","user"),("content", "In the following Lean code, replace the sorry by valid proof:\n ```lean \n"++ newThmStatement ++"\n ``` \n Give only the LEAN code")]]
      let response ← query (← chatServer) (messages) {}
      let choices ← match response.getObjVal? "choices" with
        | Except.ok c => pure c
        | Except.error e => throwError e
      let content ← getMessageContents choices
      let code := extractLean content[0]!
      let proof? := extractProof? code
      match proof? with
      | some proof? =>
          let leanproof? ← getTacticsFromText? proof?
          match leanproof? with
          | some (leanproof, _) =>
                TryThis.addSuggestion stx leanproof
          | none => throwError "Could not extract tactics from the LLM response."
      | none => throwError "Could not extract proof from the LLM response."
  | _ => throwError "Unexpected syntax"

/-example : 4+1 =5 := by
  llm?
  sorry
-/
