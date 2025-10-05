import Mathlib
import LeanAide.TheoremElab
import LeanAide.SimpleFrontend
import LeanAide.TranslateM
open Lean Meta Elab Term

namespace LeanAide
open Translate

open Lean.Parser.Category

def parseThm4 (s : String) : TermElabM <| Except String Syntax := do
  let env ← getEnv
  let s := s.replace "\\n" " "
  let s := s.replace "\n" " "
  let stx? := Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.error err => return Except.error err
  | Except.ok stx => return Except.ok stx

def elabThm4Aux (s : String)
  (_levelNames : List Lean.Name := levelNames)
  : TranslateM <| Except ElabError Expr := do
  let s := s.replace "\n" " "
  let env ← getEnv
  let stx ←
    try
      typeFromThm s
    catch e =>
      let error ← e.toMessageData.toString
      return Except.error <| .unparsed s error (← getContext)
  elaborate (← ppTerm {env:= env} stx).pretty
  where elaborate (s: String) := do
    let ctx? ← getContext
    -- match ← elabThmFromStx stx levelNames with
    -- | Except.error err₁ =>
      let frontEndErrs ← do
        try
          checkTypeElabFrontM s
        catch e =>
          let error ← e.toMessageData.toString
          pure [error]
      if frontEndErrs.isEmpty then
        match ← elabFrontTheoremExprM s with
        | Except.error err₂ =>
          let res := .parsed s "" err₂ ctx?
          appendLog "elab_errors" <| toJson res
          return Except.error res
        | Except.ok e => return Except.ok e
      else
        let res := .parsed s "" frontEndErrs ctx?
        appendLog "elab_errors" <| toJson res
        return Except.error res
    -- | Except.ok e => return  Except.ok e

-- for testing

def elabThm4 (s : String)
  (levelNames : List Lean.Name := levelNames)
  : TranslateM <| Except ElabError Expr := do
  match ← elabThm4Aux s levelNames with
  | Except.error err =>
      let groups := lineBlocks s
      let elabs? ←  groups.findSomeM? (fun s => do
        pure (← elabThm4Aux s levelNames).toOption)
      match elabs? with
      | none => return Except.error err
      | some e => return Except.ok e
  | Except.ok e => return Except.ok e

def egLines := "Yes, a vector space with dimension `2` is indeed finite dimensional. In the language of Lean theorem prover, you don't need to write an explicit proof for this, because the fact that the space has dimension `2` already implies that it is finite dimensional. However, if you want to insist on having an explicit statement, it could be something like:

     ∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V],
       (Module.rank K V = 2) → FiniteDimensional K V

     Please note that `Module.rank K V = 2` is the way to express that the vector space `V` over the field `K` has dimension `2` in Lean. The `→` is logical implication."

-- #eval elabThm4 "theorem : (0: Nat) =1"
-- #eval elabThm4 "theorem hello : (0: Nat) =1"
-- #eval elabThm4 "(0: Nat) = 1"
-- #eval elabThm4 "theorem (x: Nat) : x =1"
-- #eval elabThm4 "theorem hi (x: Nat) : x =1"

-- #eval lineBlocks egLines
