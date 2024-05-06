import Lean
import Aesop
open Lean Meta Tactic Parser
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
    `(rule_expr| unsafe $n:num ($t))

def ofTactic (t: TSyntax ``tacticSeq)(wt?: Option Nat := none) : MetaM <| TSyntax `Aesop.rule_expr := do
  match wt? with
  | none => `(rule_expr| unsafe (by $t))
  | some wt =>
    let n := Syntax.mkNumLit <| toString wt
    `(rule_expr| unsafe $n:num (by $t))

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

end AesopSyntax
end LeanAide.Meta
