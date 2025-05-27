import LeanAide.Codegen
import LeanAide.StructToLean
/-!
##Code generation for LeanAide "PaperStructure" schema

Need at top level generators for:

* Section
* Theorem
* Definition
* LogicalStepSequence
* Proof
* let_statement
* some_statement
* assume_statement
* assert_statement
* calculate_statement
* calculation_step
* cases_statement
* case
* induction_statement
* contradiction_statement
* conclude_statement
* Paragraph

We may need some more specific generators for:
* Figure
* Table


-/
open Lean Meta Qq Elab Term

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

@[codegen "let_statement"]
def letCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let statement :=
    match js.getObjValAs? String "statement" with
    | Except.ok s => s
    | Except.error _ =>
      let varSegment := match js.getObjString? "variable_name" with
      | some "<anonymous>" => "We have "
      | some v => s!"Let {v} be"
      | _ => "We have "
    let kindSegment := match js.getObjValAs? String "variable_type" with
      | Except.ok k => s!"a {k}"
      | Except.error _ => s!""
    let valueSegment := match js.getObjString? "value" with
      | some v => s!"{v}"
      | _ => ""
    let propertySegment := match js.getObjString? "properties" with
      | some p => s!"(such that) {p}"
      | _ => ""
    s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}".trim ++ "."
  addPrelude statement
  return none

@[codegen "some_statement"]
def someCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let statement :=
    match js.getObjValAs? String "statement" with
    | Except.ok s => s
    | Except.error _ =>
      let varSegment := match js.getObjString? "variable_name" with
      | some "<anonymous>" => "We have "
      | some v => s!"Let {v} be"
      | _ => "We have "
    let kindSegment := match js.getObjValAs? String "variable_kind" with
      | Except.ok k => s!"a {k}"
      | Except.error _ => s!""
    let propertySegment := match js.getObjString? "properties" with
      | some p => s!"(such that) {p}"
      | _ => ""
    s!"{varSegment} {kindSegment} {propertySegment}".trim ++ "."
  addPrelude statement
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
  let .ok type ← translator.translateToProp? claim | throwError
      s!"codegen: no translation found for {claim}"
  let type ← instantiateMVars type
  Term.synthesizeSyntheticMVarsNoPostponing
  if type.hasSorry || type.hasExprMVar then
    throwError s!"Failed to infer type {type} has sorry or mvar"
  let univ ← try
    withoutErrToSorry do
    if type.hasSorry then
      throwError "Type has sorry"
    inferType type
  catch e =>
    throwError s!"Failed to infer type {type}, error {← e.toMessageData.format}"
  if univ.isSort then
    let type ←  dropLocalContext type
    -- IO.eprintln s!"Type: {← PrettyPrinter.ppExpr type}"
    PrettyPrinter.delab type
  else
    IO.eprintln s!"Not a type: {type}"
    throwError s!"codegen: no translation found for {js}"

@[codegen "title","abstract", "remark", "metadata", "author", "bibliography", "citation", "internalreference"]
def noGenCode := noCode

-- older code, should not be used
def metaDataFields := ["author", "date", "title", "abstract", "keywords", "authors", "affiliations", "acknowledgements", "msc_codes", "publication_date", "doi", "arxiv_id", "url", "source", "header", "entries"]

@[codegen]
def metaNoCode (_ : Translator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  match js.getObj? with
  | .ok obj =>
    let keys := obj.toArray.map (fun ⟨ k, _⟩  => k)
    let nonMetaKeys := keys.filter (fun k => !metaDataFields.contains k)
    if nonMetaKeys.isEmpty then
      return none
    else
      throwError s!"codegen: no metadata found in {js}, extra keys: {nonMetaKeys}"
  | .error _ => do
  throwError s!"codegen: no metadata found in {js}"



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
