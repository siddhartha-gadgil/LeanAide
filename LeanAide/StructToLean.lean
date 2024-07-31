import Lean
import Mathlib
import LeanCodePrompts.Translate
import LeanAide.AesopSyntax
import LeanAide.CheckedSorry

/-!
# Lean code from `ProofJSON`

This file contains code to generate Lean code from a JSON structured proof. The plan is to incrementally improve this code to handle more and more complex proofs.

Some of the ingredients are:

* Extracting text from `let`, `assume` for context.
* Extracting text for a theorem statement.
* Translating a theorem object to a theorem and proof.
* Translating a sequence of statements to tactic proofs.
* Rules for `aesop` to complete proofs.
-/

def Lean.Json.getObjString? (js: Json) (key: String) : Option String :=
  match js.getObjValAs? String key with
  | Except.ok s => some s
  | _ => none

open Lean Meta Elab Term PrettyPrinter Tactic Parser
def contextJSON (js: Json) : Option String :=
  match js.getObjString? "type" with
  | some "assume" =>
    match js.getObjValAs? String "statement" with
    | Except.ok s => some <| "Assume that " ++ s ++ "."
    | _ => none
  | some "let" =>
    let varSegment := match js.getObjString? "var" with
      | some "<anonymous>" => "We have "
      | some v => s!"Let {v} be"
      | _ => "We have "
    let kindSegment := match js.getObjString? "kind" with
      | some k => s!"a {k}"
      | _ => ""
    let valueSegment := match js.getObjString? "value" with
      | some v => s!"{v}"
      | _ => ""
    let propertySegment := match js.getObjString? "property" with
      | some p => s!"such that {p}"
      | _ => ""
    return s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}."
  | _ => none

def localDeclExists (name: Name) (type : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  match lctx.findFromUserName? name with
  | some (.cdecl _ _ _ dtype ..) => isDefEq dtype type
  | _ => return false

partial def dropLocalContext (type: Expr) : MetaM Expr := do
  match type with
  | .forallE name binderType body _ => do
    if ← localDeclExists name binderType then
        dropLocalContext body
    else
      return type
  | _ => return type

def theoremInContext? (ctx: Array Json)(statement: String)(server: ChatServer := ChatServer.openAI)(params : ChatParams := {}) (numSim: Nat := 8)(numConcise numDesc : ℕ := 0)(toChat : ToChatExample := simpleChatExample)
  (dataMap : HashMap String (Array ((String × String × Bool × String) × FloatArray)) := HashMap.empty ) : TermElabM (Option Expr) := do
  let mut context := #[]
  for js in ctx do
    match contextJSON js with
    | some s => context := context.push s
    | none => pure ()
  let fullStatement := context.foldr (· ++ " " ++ ·) statement
  let type? ← translateToProp?
    fullStatement.trim server params numSim numConcise numDesc toChat dataMap
  type?.mapM <| fun e => dropLocalContext e

def purgeLocalContext: Syntax.Command →  TermElabM Syntax.Command
| `(command|def $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delab type
  `(command|def $name : $type := $value)
| `(command|theorem $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delab type
  `(command|theorem $name : $type := $value)
| stx => return stx

def defnInContext? (ctx: Array Json)(statement: String)(server: ChatServer := ChatServer.openAI)(params : ChatParams := {}) (numSim: Nat := 8)(numConcise numDesc : ℕ := 0)(toChat : ToChatExample := simpleChatExample)
  (dataMap : HashMap String (Array ((String × String × Bool × String) × FloatArray)) := HashMap.empty ) : TermElabM (Option Syntax.Command) := do
  let mut context := #[]
  for js in ctx do
    match contextJSON js with
    | some s => context := context.push s
    | none => pure ()
  let fullStatement := context.foldr (· ++ " " ++ ·) statement
  let cmd? ←
    translateDefCmdM? fullStatement server params numSim numConcise numDesc toChat dataMap
  let cmd? ← cmd?.mapM purgeLocalContext
  return cmd?


elab "dl!" t: term : term => do
let t ← elabType t
  let t' ← dropLocalContext t
  return t'

set_option linter.unusedVariables false in
def eg_drop (n m: Nat)  := dl! (∀ n m: Nat, n = n + 1 → False)

#print eg_drop


variable (dataMap :
  HashMap String (Array ((String × String × Bool × String) × FloatArray)))
