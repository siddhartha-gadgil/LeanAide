import Lean
import Aesop
import LeanAide.CheckedSorry
open Lean Meta Elab Tactic Parser
open Lean.Parser.Tactic

namespace LeanAide.Meta
namespace AesopSyntax

namespace RuleExpr

open Aesop

def ofTerm (t: Syntax.Term)(wt?: Option Nat := none) : MetaM <| TSyntax `Aesop.rule_expr := do
  match wt? with
  | none => `(rule_expr| unsafe ($t))
  | some wt =>
    let n := Syntax.mkNumLit <| toString wt
    `(rule_expr| unsafe $n:num% ($t))

def ofName (n: Name)(wt?: Option Nat := none) : MetaM <| TSyntax `Aesop.rule_expr := do
  let t := mkIdent n
  ofTerm t wt?

def ofTactic (t: TSyntax ``tacticSeq)(wt?: Option Nat := none) : MetaM <| TSyntax `Aesop.rule_expr := do
  match wt? with
  | none => `(rule_expr| unsafe (by $t))
  | some wt =>
    let n := Syntax.mkNumLit <| toString wt
    `(rule_expr| unsafe $n:num% (by $t))

def sorryRule (wt: Nat := 10) :
  MetaM <| TSyntax `Aesop.rule_expr := do
  let stx ← `(tacticSeq| checked_sorry)
  ofTactic stx (some wt)

def strongSorryRule (wt: Nat := 10) :
  MetaM <| TSyntax `Aesop.rule_expr := do
  let stx ← `(tacticSeq| unchecked_sorry)
  ofTactic stx (some wt)

def rewrite (e: Syntax.Term)(wt? : Option Nat := none)
  (flip: Bool := false) : MetaM <| TSyntax `Aesop.rule_expr := do
  let tacM :=
      if flip then
      `(tacticSeq| rw [ ← ($e) ])
      else
      `(tacticSeq| rw [ ($e) ])
  let tac ← tacM
  ofTactic tac wt?

def rewriteName (n: Name)(wt? : Option Nat := none)
  (flip: Bool := false) : MetaM <| TSyntax `Aesop.rule_expr := do
  let t := mkIdent n
  rewrite t wt? flip

end RuleExpr

def fold (rules : Array <| TSyntax `Aesop.rule_expr) :
  MetaM <| Syntax.Tactic  := do
  let clauses ← rules.mapM fun r => `(tactic_clause| (add $r))
  `(tactic| aesop? $clauses*)

def runFold (rules : Array <| TSyntax `Aesop.rule_expr) :
    TacticM Unit := do
  let stx ← fold rules
  evalTactic stx
  return ()

elab "aesop_fold" "["ts:term ,*"]"* ";" "["tacs:tacticSeq ,*"]"*  : tactic => do
  let terms :=  ts.getElems
  let termRules ← terms.mapM fun t => RuleExpr.ofTerm t
  let tacs := tacs.getElems
  let tacticRules ← tacs.mapM fun t => RuleExpr.ofTactic t
  let rwTactics ←  terms.mapM fun t => RuleExpr.rewrite t (some 10)
  let rwFlipTactics ←
    terms.mapM fun t => RuleExpr.rewrite t (some 10) true
  let stx ← fold <| termRules ++ tacticRules ++ rwTactics ++ rwFlipTactics
  evalTactic stx
  return ()

example (n m : Nat) : n + m = m + n := by
  aesop_fold []; [simp [Nat.add_comm]]

example (n m : Nat) : n + m = m + n := by
  aesop_fold [Nat.add_comm]; []

opaque p : Nat
opaque q : Nat
axiom p_eq_q : p = q

example : p = q := by
  aesop_fold [p_eq_q]; []

example : False := by
  aesop_fold []; [sorry]

end AesopSyntax
end LeanAide.Meta
