import Lean
import Aesop
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

def ofTactic (t: TSyntax ``tacticSeq)(wt?: Option Nat := none) : MetaM <| TSyntax `Aesop.rule_expr := do
  match wt? with
  | none => `(rule_expr| unsafe (by $t))
  | some wt =>
    let n := Syntax.mkNumLit <| toString wt
    `(rule_expr| unsafe $n:num% (by $t))

def rewrite (e: Syntax.Term)(wt? : Option Nat := none)
  (flip: Bool := false) : MetaM <| TSyntax `Aesop.rule_expr := do
  let tacM :=
      if flip then
      `(tacticSeq| rw [ ← ($e) ])
      else
      `(tacticSeq| rw [ ($e) ])
  let tac ← tacM
  ofTactic tac wt?

end RuleExpr

def fold (rules : Array <| TSyntax `Aesop.rule_expr) :
  MetaM <| Syntax.Tactic  := do
  let clauses ← rules.mapM fun r => `(tactic_clause| (add $r))
  `(tactic| aesop $clauses*)

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

end AesopSyntax
end LeanAide.Meta
