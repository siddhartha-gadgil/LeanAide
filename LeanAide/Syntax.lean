import LeanCodePrompts.Translate
import Lean
import LeanAideCore.Syntax
import LeanAideCore.Kernel
import LeanAide.Responses

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide.Meta



open Tactic Translator
elab "what" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← relLCtx goal
  logInfo m!"goal : {type}"
  -- let defs ← defsInExpr type
  -- logInfo m!"defs : {defs}"
  let some (transl, _, _) ← getTypeDescriptionM type {} | throwError "No description from LLM"
  logInfo transl


@[tactic whyTac] def whyTacImpl : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let type ← relLCtx goal
  logInfo m!"goal : {type}"
  let some (transl, _, _) ← getTypeProofM type {} |
            throwError "No description from LLM"
  logInfo m!"Theorem and proof: {transl}"
  -- let pfStx := Syntax.mkStrLit proof[0]!
  -- let proofTac ← `(tactic| #proof $pfStx)
  let proofTac : Syntax.Tactic := ⟨mkProofStx transl⟩
  TryThis.addSuggestion stx proofTac




-- #check TryThis.Suggestion

open Lean.Parser.Command


end LeanAide.Meta
