import LeanAideCore.Aides
import LeanAideCore.ChatClient
import LeanAideCore.Translator

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
    "content": "You are an expert mathematician and Lean 4 theorem proving assistant. Your job is to turn a Lean Infoview goal state into a proof term that Lean can elaborate immediately.\n\nHard requirements:\n1. Return a complete tactic proof beginning with `by`. The proof must close all goals.\n2. Use Lean 4 and Mathlib4 syntax only. Do not use Lean 3 syntax, comma-separated tactic scripts, `begin`/`end`, or deprecated tactic forms.\n3. Do not use `sorry`, `admit`, `by_contra!`, `exact?`, `apply?`, `rw?`, `simp?`, placeholders such as `_`, or any tactic that intentionally leaves obligations unsolved.\n4. Treat everything before `⊢` as the local context and everything after `⊢` as the target. Use the displayed local names exactly as written, and introduce new names only with tactics such as `intro`, `rintro`, `constructor`, or `cases`.\n5. Do not restate, rename, generalize, or modify the goal. Do not add imports, declarations, examples, comments, explanations, or natural language.\n6. Prefer short, robust tactic scripts. Useful tactics include `intro`, `intros`, `rintro`, `constructor`, `cases`, `rcases`, `apply`, `exact`, `refine`, `rw`, `simp`, `simpa`, `norm_num`, `omega`, `linarith`, `nlinarith`, `ring`, `aesop`, and `grind`.\n7. When using a theorem or definition name, be conservative: use names that are in the local context, clearly standard Mathlib names, or obvious from the goal. Do not invent lemma names.\n\nOutput format:\nReturn exactly one markdown Lean code block and no other text. The block must contain only the proof, for example:\n```lean\nby\n  simp\n```"
  }

@[tactic llmSyntax]
def llmTactic : Tactic
  | stx@`(tactic| llm?) =>
      withMainContext do
      let goalmVar ← getMainGoal
      let goalExpr ← ppGoal goalmVar
      -- let dir ← getBaseDir
      -- logInfo m!"Goal expression: {goalExpr}"
      let newThmStatement ← (m!"{goalExpr}").toString
      --let mathPrompt ← mathPrompt
      let messages := Json.arr #[prompt,Json.mkObj [("role","user"),("content", "Solve this Lean 4 Infoview goal state.\n\nUse the hypotheses and variables before `⊢` as the local context, and prove the target after `⊢`. Produce a complete tactic proof starting with `by`. The proof must elaborate without leaving any goals, and it must not contain `sorry`, `admit`, generated placeholders, or explanatory text.\n\nGoal state:\n```lean\n"++ newThmStatement ++"\n```")]]
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
                evalTactic leanproof
                TryThis.addSuggestion stx leanproof
          | none => throwError "Could not extract tactics from the LLM response."
      | none => throwError "Could not extract proof from the LLM response."
      --logInfo m!"{goalExpr}"
  | _ => throwError "Unexpected syntax"

def prompt_sorry : Json := json%
 {
 "role": "system",
 "content": "You are an expert mathematician and Lean 4 theorem proving assistant. Your job is to turn a Lean Infoview goal state into a tactic proof that Lean can elaborate, possibly with `sorry` for unresolved subgoals.\n\nHard requirements:\n1. Return a tactic proof beginning with `by`. Close as many goals as possible with valid Lean proof steps.\n2. Use Lean 4 and Mathlib4 syntax only. Do not use Lean 3 syntax, comma-separated tactic scripts, `begin`/`end`, or deprecated tactic forms.\n3. `sorry` is allowed when a goal cannot be closed confidently. Use `sorry` rather than inventing theorem names, definitions, or fragile proof steps. Do not use `admit`, `by_contra!` with unresolved goals, `exact?`, `apply?`, `rw?`, `simp?`, placeholders such as `_`, or any non-sorry placeholder/search tactic in the final answer.\n4. Treat everything before `⊢` as the local context and everything after `⊢` as the target. Use the displayed local names exactly as written, and introduce new names only with tactics such as `intro`, `rintro`, `constructor`, or `cases`.\n5. Do not restate, rename, generalize, or modify the goal. Do not add imports, declarations, examples, comments, explanations, or natural language.\n6. Prefer short, robust tactic scripts. Useful tactics include `intro`, `intros`, `rintro`, `constructor`, `cases`, `rcases`, `apply`, `exact`, `refine`, `rw`, `simp`, `simpa`, `norm_num`, `omega`, `linarith`, `nlinarith`, `ring`, `aesop`, and `grind`.\n7. When using a theorem or definition name, be conservative: use names that are in the local context, clearly standard Mathlib names, or obvious from the goal. Do not invent lemma names.\n\nOutput format:\nReturn exactly one markdown Lean code block and no other text. The block must contain only the proof, for example:\n```lean\nby\n  simp\n```"
 }

@[tactic llmSorrySyntax]
def llmSorryTactic : Tactic
  | stx@`(tactic| llm_with_sorries?) =>
      withMainContext do
      let goalmVar ← getMainGoal
      let goalExpr ← ppGoal goalmVar
      -- let dir ← getBaseDir
      --logInfo m!"Goal expression: {goalExpr}"
      let newThmStatement ← (m!"{goalExpr}").toString
      --let mathPrompt ← mathPrompt
      let messages := Json.arr #[prompt_sorry,Json.mkObj [("role","user"),("content", "Solve this Lean 4 Infoview goal state.\n\nUse the hypotheses and variables before `⊢` as the local context, and prove the target after `⊢`. Produce a tactic proof starting with `by`. Close the goal completely if possible; otherwise, make as much valid progress as possible and use `sorry` for the remaining subgoals. Do not use `admit`, generated placeholders, or explanatory text.\n\nGoal state:\n```lean\n"++ newThmStatement ++"\n```")]]
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
                evalTactic leanproof
                TryThis.addSuggestion stx leanproof
          | none => throwError "Could not extract tactics from the LLM response."
      | none => throwError "Could not extract proof from the LLM response."
  | _ => throwError "Unexpected syntax"
