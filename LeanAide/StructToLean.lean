import Lean
import Mathlib

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
    | Except.ok s => some <| "Assume:" ++ s
    | _ => none
  | some "let" =>
    let varSegment := match js.getObjString? "var" with
      | some "<anonymous>" => "We have"
      | some v => s!"Let {v} be"
      | _ => "Consider"
    let kindSegment := match js.getObjString? "kind" with
      | some k => s!"s {k}"
      | _ => ""
    let valueSegment := match js.getObjString? "value" with
      | some v => s!"{v}"
      | _ => ""
    let propertSegment := match js.getObjString? "property" with
      | some p => s!"such that {p}"
      | _ => ""
    return s!"{varSegment} {kindSegment} {valueSegment} {propertSegment}"
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

elab "dl!" t: term : term => do
let t ← elabType t
  let t' ← dropLocalContext t
  logInfo m!"{t} -> {t'}"
  return t'

def eg_drop (n: Nat)  := dl! (∀ n : Nat, n = n + 1 → False)

#print eg_drop


variable (dataMap :
  HashMap String (Array ((String × String × Bool × String) × FloatArray)))
