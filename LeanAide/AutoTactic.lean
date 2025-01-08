import Lean
import Mathlib
import LeanAide.AesopSyntax
import LeanAide.CheckedSorry
import LeanAide.Aides
open LeanAide.Meta Lean Meta Elab

open Lean Meta Tactic Parser.Tactic

namespace LeanAide

def powerTactics : CoreM <| List <| TSyntax ``tacticSeq := do
  return [← `(tacticSeq| ring),← `(tacticSeq| omega),  ← `(tacticSeq| linarith)
  -- , ← `(tacticSeq| norm_num), ← `(tacticSeq| positivity), ← `(tacticSeq| gcongr), ←`(tacticSeq| contradiction)
  ]

def powerRules (weight sorryWeight strongSorryWeight: Nat) : MetaM <| List <| TSyntax `Aesop.rule_expr := do
  let tacs ← powerTactics
  let rules ← tacs.mapM fun tac => AesopSyntax.RuleExpr.ofTactic tac (some weight)
  if sorryWeight == 0 then
    return rules
  else
    return rules ++ [← AesopSyntax.RuleExpr.sorryRule sorryWeight, ← AesopSyntax.RuleExpr.strongSorryRule strongSorryWeight]

def suggestionRules (names: List Name) (weight: Nat := 90)
    (rwWeight: Nat := 50) : MetaM <| List <| TSyntax `Aesop.rule_expr := do
  let tacs ← names.mapM fun n => AesopSyntax.RuleExpr.ofName n (some weight)
  let rws ← names.mapM fun n => AesopSyntax.RuleExpr.rewriteName n (some rwWeight)
  let rwsFlip ← names.mapM fun n => AesopSyntax.RuleExpr.rewriteName n (some rwWeight) true
  return tacs ++ rws ++ rwsFlip

def aesopTactic (weight sorryWeight strongSorryWeight: Nat) (names: List Name := []) :
    MetaM <| Syntax.Tactic := do
  let rules ← powerRules weight sorryWeight strongSorryWeight
  let sugRules ← suggestionRules names
  AesopSyntax.fold (rules ++ sugRules).toArray

syntax (name := auto_aesop) "auto?" (ppSpace "[" ident,* "]")? : tactic

-- should configure 90, 50, 10
@[tactic auto_aesop] def autoAesopImpl : Tactic := fun stx => do
unless (← getGoals).isEmpty do
  match stx with
  | `(tactic| auto?) => do
    let tac ← aesopTactic 90 0 0
    -- logInfo m!"auto tactic: {← PrettyPrinter.ppTactic tac}"
    let (_, goals) ← evalTacticSafe tac
    if goals == 0 then
      return ()
    let tac ← aesopTactic 90 20 10
    let (check, _) ← evalTacticSafe tac
    unless check do
      let tac ← `(tactic|sorry)
      evalTactic tac
  | `(tactic| auto? [$names,*]) => do
    let names := names.getElems.map fun n => n.getId
    let tac ← aesopTactic 90 0 0 names.toList
    trace[leanaide.codegen.info] s!"auto tactic: {← PrettyPrinter.ppTactic tac}"
    -- logInfo m!"auto tactic: {← PrettyPrinter.ppTactic tac}"
    let (_, goals) ← evalTacticSafe tac
    if goals == 0 then
      return ()
    let tac ← aesopTactic 90 20 10 names.toList
    trace[leanaide.codegen.info] s!"auto tactic: {← PrettyPrinter.ppTactic tac}"
    let (check, _) ← evalTacticSafe tac
    unless check do
      let tac ← `(tactic|sorry)
      evalTactic tac
  | _ => throwUnsupportedSyntax

elab "#note" "[" term,* "]" : command => do
  return ()

elab "#note" "[" term,* "]" : tactic => do
  return ()

def mkNoteCmd (s: String) : MetaM Syntax.Command :=
  let sLit := Lean.Syntax.mkStrLit  s
  `(command | #note [$sLit])

def mkNoteTactic (s: String) : MetaM Syntax.Tactic :=
  let sLit := Lean.Syntax.mkStrLit  s
  `(tactic | #note [$sLit])
