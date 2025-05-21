import LeanAide.Codegen

open Lean Meta Qq Elab

namespace LeanAide.Codegen

@[codegen "test"]
def test (_translator : Translator := {}) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| `term, js =>
  match js.getStr? with
  | .ok str => do
    let name := Syntax.mkStrLit str
    `($name)
  | .error _ => do
    `(sorry)
| `tactic, _ => `(tactic|sorry)
| _, _ => throwError
    s!"codegen: test does not work"

#eval test {} `term (Json.str "Nat.succ")

#eval codeFromFunc {} ``test `term (Json.null)

#eval codeFromFunc {} ``test `term (Json.str "Hello")

def testJson : Json :=
  Json.mkObj [ ("test" , Json.str "Hello") ]

#eval getCode {} `term testJson
#eval getCode {} `tactic testJson

@[codegen "thm_test"]
def thmTest (translator : Translator := {}) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| `command, js =>
  match js.getStr? with
  | .ok str => do
    let .ok t ← translator.translateToProp? str | throwError
      s!"codegen: no translation found for {str}"
      let stx ← PrettyPrinter.delab t
      `(command| example : $stx := sorry)
  | .error _ => do
    `(command| example: False := sorry)
| `tactic, _ => `(tactic|sorry)
| _, _ => throwError
    s!"codegen: test does not work"

def thmJson : Json :=
  Json.mkObj [ ("thm_test" , Json.str "There are infinitely many odd numbers.") ]

open PrettyPrinter in
def showCommand (translator: Translator)
  (source: Json) :
    TranslateM (Format) := do
    let some cmd ← getCode translator `command source | throwError
      s!"codegen: no command"
    ppCommand cmd

#eval showCommand {} thmJson
