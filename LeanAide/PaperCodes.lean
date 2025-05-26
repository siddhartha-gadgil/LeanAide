import LeanAide.Codegen

open Lean Meta Qq Elab

namespace LeanAide

open Codegen Translate

@[codegen "assumption_statement"]
def assumptionCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let .ok assumption :=
    js.getObjValAs? String "assumption" | throwError
    s!"codegen: no assumption found in {js}"
  addPrelude assumption
  return none

open Lean.Parser.Tactic
-- Very basic version; should add references to `auto?` as well as other modifications as in `StructToLean`
@[codegen "assertion_statement"]
def assertionCode (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let stx ← typeStx js
  `(command| example : $stx := by sorry)
| _, `commandSeq, js => do
  let stx ← typeStx js
  `(commandSeq| example : $stx := by sorry)
| _, ``tacticSeq, js => do
  let stx ← typeStx js
  `(tacticSeq| have : $stx := bysorry)
| _, `tactic, js => do
  let stx ← typeStx js
  `(tactic| have : $stx := bysorry)
| _, _, _ => throwError
    s!"codegen: test does not work"
where typeStx (js: Json) : TranslateM Syntax.Term := do
  let .ok  claim := js.getObjValAs? String "claim" | throwError
    s!"codegen: no claim found in {js}"
  let .ok t ← translator.translateToProp? claim | throwError
      s!"codegen: no translation found for {claim}"
    PrettyPrinter.delab t


-- Copied code

open Lean.Parser.Tactic
@[codegen "thm_test"]
def thmTest (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let stx ← typeStx js
  `(command| example : $stx := by sorry)
| _, `commandSeq, js => do
  let stx ← typeStx js
  `(commandSeq| example : $stx := by sorry)
| _, ``tacticSeq, js => do
  let stx ← typeStx js
  `(tacticSeq| have : $stx := bysorry)
| _, `tactic, js => do
  let stx ← typeStx js
  `(tactic| have : $stx := bysorry)
| _, _, _ => throwError
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

@[codegen]
def thmStringTest (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let stx ← typeStx js
  `(command| example : $stx := by sorry)
| _, `commandSeq, js => do
  let stx ← typeStx js
  `(commandSeq| example : $stx := by sorry)
| _, ``tacticSeq, js => do
  let stx ← typeStx js
  `(tacticSeq| have : $stx := bysorry)
| _, `tactic, js => do
  let stx ← typeStx js
  `(tactic| have : $stx := bysorry)
| _, _, _ => throwError
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
def docTest  (translator : Translator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| goal?, `commandSeq, js => withoutModifyingState do
  let .ok statements := js.getArr? | throwError "document must be an array"
  let mut stxs : Array (TSyntax `commandSeq) := #[]
  for statement in statements do
    let stx ← getCode translator goal? `commandSeq statement
    match stx with
    | some stx => stxs := stxs.push stx
    | none => pure ()
  flattenCommands stxs
| goal?, ``tacticSeq, js => withoutModifyingState do
  let .ok statements := js.getArr? | throwError "document must be an array"
  let mut stxs : Array (TSyntax `tactic) := #[]
  for statement in statements do
    let stx ← getCode translator goal? `tactic statement
    match stx with
    | some stx => stxs := stxs.push stx
    | none => pure ()
  `(tacticSeq| $stxs*)


| _, _, _ => throwError
    s!"codegen: test does not work"

def thmJson : Json :=
  Json.mkObj [ ("thm_test" , Json.str "There are infinitely many odd numbers.") ]

def thmJson' : Json :=
  Json.mkObj [ ("thm_test" , Json.str "There are infinitely many prime numbers.") ]

def docJson : Json :=
  Json.mkObj [ ("doc_test" , Json.arr #[thmJson, thmJson', Json.str "There are infinitely many odd numbers."])]

open PrettyPrinter
def showCommand (translator: Translator)
  (source: Json) :
    TranslateM (Format) := do
    let some cmd ← getCode translator none `command source | throwError
      s!"codegen: no command"
    ppCommand cmd

def showStx  (translator: Translator)(goal? : Option (MVarId))
  (source: Json) (cat: Name) :
    TranslateM (Format) := do
    let some stx ← getCode translator  goal? cat source | throwError
      s!"codegen: no command"
    ppCategory cat stx


#eval showCommand {} thmJson -- example : {n | Odd n}.Infinite := by sorry

/-
  example : {n | Odd n}.Infinite := by sorry
  example : {p | Nat.Prime p}.Infinite := by sorry
-/
#eval showStx {} none docJson `commandSeq
