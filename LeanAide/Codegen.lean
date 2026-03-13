import Lean
import Qq
import LeanAide.Aides
import LeanAideCore.Translate
import LeanAide.RunTactics
import Mathlib
import LeanAideCore.Syntax
import LeanAideCore.CodegenCore
import Hammer
/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `CodeGenerator`, an optional goal, a syntax category, and a JSON object, and returns the corresponding syntax or throws an error.
-/


open Lean Meta Qq Elab LeanAide

namespace LeanAide
namespace Codegen

def exType : Q(Type) :=
    q(CodeGenerator → Option MVarId  → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)))

-- #eval exType


#logIO leanaide.codegen.info
#logFile leanaide.codegen.info


open Lean.Parser.Tactic


end Codegen

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
#add_auto_tactics [hammer {aesopPremises := 5, autoPremises := 0}, try_this (constructor) then (grind?)]

-- #eval getAutoTactics


open Command Elab Term Tactic Codegen
-- @[command_elab codegenCmd]
def elabCodegenCmdImpl' : CommandElab
| stx@`(command| #codegen $s:term) =>
  Command.liftTermElabM do
  withoutModifyingEnv do
    let source : Q(Json) ← elabTerm s q(Json)
    let e := q(getCode CodeGenerator.default none ``commandSeq $source)
    let codeM? ←
      unsafe evalExpr (TranslateM (Option (TSyntax ``commandSeq))) q((TranslateM (Option (TSyntax ``commandSeq)))) e
    let code? ←  codeM?.run' {}
    let code := code?.getD (← `(commandSeq|#check "No code generated"))
    TryThis.addSuggestion stx code
| _ => throwUnsupportedSyntax


/--
Converts definition to `use`
-/
def commandToUseTactic (cmd: Syntax.Command) : TermElabM Syntax.Tactic := do
  match cmd with
  | `(command| def $_:ident $_:bracketedBinder* : $_ := $value) =>
      `(tactic| use $value:term)
  | `(command| def $_:ident $_:bracketedBinder* := $value) =>
      `(tactic| use $value:term)
  | _ => throwError s!"could not parse the definition {← PrettyPrinter.ppCommand cmd} in commandToUseTactic"

/-!
Resolving existential theorems:
* We have a series of let statements, each of which introduces a variable and a proof that it exists.
* The proof is passed recursively to the next let statement.
* We start with a type and a witness for it.
* If the type is existential, we resolve the witness.
* The resolved proof and term used will depend on variables, so we will have to export these.
* **Alternative:** We only resolve other existential theorems if they are used, and we fill in the arguments with the local context.
* Seems like a good approach to include used theorems in the local context, filling in the arguments with the local context.
-/
example : True := by
  have egExists : ∃ n: Nat, n = 3 := by
    use 3
  let ⟨n, h⟩ := egExists
  simp




end LeanAide
