import Lean
import Mathlib

open Lean Meta Elab Term

def existsUniqueSeqTerm (xs : List (TSyntax `Lean.binderIdent)) (type prop : Syntax.Term) : MetaM Syntax.Term := do
  match xs with
  | [] => return prop
  | h :: t =>
    let tailTerm ← existsUniqueSeqTerm t type prop
    `(∃! ($h : $type), $tailTerm)


mutual

partial def expandExistsUnique? (stx: Syntax.Term) :
  MetaM <| Option Syntax.Term := do
  match stx with
  | `(∃! ($xs* : $type), $value) =>
    let value ← expandExistsUnique value
    existsUniqueSeqTerm xs.toList type ⟨value⟩
  | _  => return none

partial def expandExistsUnique (stx: Syntax.Term) : MetaM Syntax.Term := do
  match ← expandExistsUnique? stx with
  | some newStx => some newStx
  | none =>
    match stx.raw with
    | .node info kind args =>
      let newArgs ← args.mapM fun arg => do
         pure (← expandExistsUnique ⟨arg⟩).raw
      return {raw := Syntax.node info kind newArgs}
    | s => return ⟨s⟩
end
