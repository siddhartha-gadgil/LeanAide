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

/-!
## Micro schema
This is a micro schema for testing and illustrating the code generation. This includes recursive calls to `getCode`.
-/

open Lean.Parser.Tactic
@[codegen "thm_test"]
def thmTest (translator : Translator := {}) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| `command, js => do
  let stx ← typeStx js
  `(command| example : $stx := by sorry)
| `commandSeq, js => do
  let stx ← typeStx js
  `(commandSeq| example : $stx := by sorry)
| ``tacticSeq, js => do
  let stx ← typeStx js
  `(tacticSeq| have : $stx := bysorry)
| `tactic, js => do
  let stx ← typeStx js
  `(tactic| have : $stx := bysorry)
| _, _ => throwError
    s!"codegen: test does not work"
where typeStx (js: Json) : TranslateM Syntax.Term :=
  match js.getStr? with
  | .ok str => do
    let .ok t ← translator.translateToProp? str | throwError
      s!"codegen: no translation found for {str}"
    PrettyPrinter.delab t
  | .error _ => do
    throwError
      s!"codegen: no translation found for {js}"

@[codegen "doc_test"]
def docTest (translator : Translator := {}) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| `commandSeq, js => withoutModifyingState do
  let .ok statements := js.getArr? | throwError "document must be an array"
  let mut stxs : Array (TSyntax `commandSeq) := #[]
  for statement in statements do
    let stx ← getCode translator `commandSeq statement
    match stx with
    | some stx => stxs := stxs.push stx
    | none => pure ()
  flattenCommands stxs
| ``tacticSeq, js => withoutModifyingState do
  let .ok statements := js.getArr? | throwError "document must be an array"
  let mut stxs : Array (TSyntax `tactic) := #[]
  for statement in statements do
    let stx ← getCode translator `tactic statement
    match stx with
    | some stx => stxs := stxs.push stx
    | none => pure ()
  `(tacticSeq| $stxs*)


| _, _ => throwError
    s!"codegen: test does not work"

def thmJson : Json :=
  Json.mkObj [ ("thm_test" , Json.str "There are infinitely many odd numbers.") ]

def thmJson' : Json :=
  Json.mkObj [ ("thm_test" , Json.str "There are infinitely many prime numbers.") ]

def docJson : Json :=
  Json.mkObj [ ("doc_test" , Json.arr #[thmJson, thmJson'])]

open PrettyPrinter
def showCommand (translator: Translator)
  (source: Json) :
    TranslateM (Format) := do
    let some cmd ← getCode translator `command source | throwError
      s!"codegen: no command"
    ppCommand cmd

def showStx  (translator: Translator)
  (source: Json) (cat: Name) :
    TranslateM (Format) := do
    let some stx ← getCode translator cat source | throwError
      s!"codegen: no command"
    ppCategory cat stx


#eval showCommand {} thmJson -- example : {n | Odd n}.Infinite := by sorry

/-
  example : {n | Odd n}.Infinite := by sorry
  example : {p | Nat.Prime p}.Infinite := by sorry
-/
#eval showStx {} docJson `commandSeq
