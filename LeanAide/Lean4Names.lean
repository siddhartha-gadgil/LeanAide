import Lean
import Mathlib
import LeanAide.TheoremElab
import LeanAide.SimpleFrontend
import LeanAide.TranslateM
open Lean Meta Elab Term LeanAide.Meta

-- As Mathlib support for port is dropped, this is also dropped


-- def lean4Name? (name: Name) : MetaM (Option Name) := do
--   let m := renameExtension.getState (← getEnv) |>.get
--   let name? :=
--     (m.find? name).map (·.2)
--   match name? with
--   | none => pure none
--   | some name =>
--     pure name

-- #eval lean4Name? `nat.prime -- some (`Nat.Prime, true)
-- #eval lean4Name? `nat -- some (`Nat, true)

partial def lean4NamesSyntax : Syntax → MetaM Syntax := fun stx => pure stx
-- do
-- match stx with
-- | Syntax.ident _ _ name .. =>
--     match ← lean4Name? name with
--     | some name' => do
--         return mkIdent name'
--     | none => return stx
-- | Syntax.node _ k args  => do
--   let args ← args.mapM lean4NamesSyntax
--   return mkNode k args
-- | stx => pure stx

def parseThm4 (s : String) : TermElabM <| Except String Syntax := do
  let env ← getEnv
  let stx? := Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.error err => return Except.error err
  | Except.ok stx => return Except.ok <| ← lean4NamesSyntax stx

def elabThm4Aux (s : String)
  (levelNames : List Lean.Name := levelNames)
  : TranslateM <| Except String Expr := do
  let env ← getEnv
  let ctx? ← getContext
  let stx? :=
    Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.error err =>
      let jsError :=
        Json.mkObj [
        ("input", s),
        ("parsed", false),
        ("parse-error", err),
        ("context", ctx?.getD "")
        ]
      appendLog "elab_errors" jsError
      return Except.error s!"{err} for:\n {s}"
  | Except.ok stx =>
    elaborate stx
  where elaborate (stx) := do
    let ctx? ← getContext
    match ← elabThmFromStx stx levelNames with
    | Except.error err₁ =>
      let frontEndErrs ← checkTypeElabFrontM s
      let jsError := Json.mkObj [
        ("input", s),
        ("parsed", true),
        ("elab-error", err₁),
        ("frontend-errors", toJson frontEndErrs),
        ("context", ctx?.getD "")
        ]
      appendLog "elab_errors" jsError
      return Except.error s!"{err₁}"
    | Except.ok e => return  Except.ok e

-- for testing

def elabThm4 (s : String)
  (levelNames : List Lean.Name := levelNames)
  : TranslateM <| Except String Expr := do
  match ← elabThm4Aux s levelNames with
  | Except.error err =>
      let groups := lineBlocks s
      let elabs? ←  groups.findSomeM? (fun s => do
        pure (← elabThm4Aux s levelNames).toOption)
      match elabs? with
      | none => return Except.error err
      | some e => return Except.ok e
  | Except.ok e => return Except.ok e

elab "lean3named" t:term : term => do
  let t' ← lean4NamesSyntax t
  elabTerm t' none

-- #check lean3named nat.prime
-- #check lean3named (fun (n: Nat) ↦ nat.prime n) -- handles a mix fine

def egLines := "Yes, a vector space with dimension `2` is indeed finite dimensional. In the language of Lean theorem prover, you don't need to write an explicit proof for this, because the fact that the space has dimension `2` already implies that it is finite dimensional. However, if you want to insist on having an explicit statement, it could be something like:

     ∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V],
       (Module.rank K V = 2) → FiniteDimensional K V

     Please note that `Module.rank K V = 2` is the way to express that the vector space `V` over the field `K` has dimension `2` in Lean. The `→` is logical implication."

-- #eval elabThm4 egLines
-- #eval lineBlocks egLines
