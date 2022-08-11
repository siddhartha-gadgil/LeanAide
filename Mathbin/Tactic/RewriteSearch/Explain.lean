/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import Mathbin.Tactic.RewriteSearch.Types
import Mathbin.Tactic.Converter.Interactive

/-!
# Tools to extract valid Lean code from a path found by rewrite search.
-/


-- Required for us to emit more compact `conv` invocations
-- Required for us to emit more compact `conv` invocations
open Interactive Interactive.Types Expr Tactic

namespace Tactic.RewriteSearch

universe u

/-- A `dir_pair` is a pair of items designed to be accessed according to
`dir`, a "direction" defined in the `expr_lens` library.
-/
structure DirPair (α : Type u) where
  (l R : α)
  deriving Inhabited

namespace DirPair

open ExprLens

variable {α β : Type} (p : DirPair α)

/-- Get one side of the pair, picking the side according to the direction. -/
def get : Dir → α
  | dir.F => p.l
  | dir.A => p.R

/-- Set one side of the pair, picking the side according to the direction. -/
def set : Dir → α → DirPair α
  | dir.F, v => ⟨v, p.R⟩
  | dir.A, v => ⟨p.l, v⟩

/-- Convert the pair to a list of its elements. -/
def toList : List α :=
  [p.l, p.R]

/-- Convert the pair to a readable string format. -/
def toString [HasToString α] (p : DirPair α) : Stringₓ :=
  toString p.l ++ "-" ++ toString p.R

instance hasToString [HasToString α] : HasToString (DirPair α) :=
  ⟨toString⟩

end DirPair

/-- Helper for getting the nth item in a list of rules -/
private unsafe def nth_rule (rs : List (expr × Bool)) (i : ℕ) : expr × Bool :=
  (rs.nth i).iget

/-- Convert a rule into the string of Lean code used to refer to this rule. -/
private unsafe def pp_rule (r : expr × Bool) : tactic Stringₓ := do
  let pp ← pp r.1
  return <| (if r.2 then "←" else "") ++ toString pp

private unsafe def how.to_rewrite (rs : List (expr × Bool)) : how → Option (expr × Bool)
  | h => nth_rule rs h.rule_index

/-- Explain a single rewrite using `nth_rewrite`. -/
private unsafe def explain_using_location (rs : List (expr × Bool)) (s : Side) : how → tactic (Option Stringₓ)
  | h => do
    let rule ← pp_rule <| nth_rule rs h.rule_index
    return <| some ("nth_rewrite_" ++ s ++ " " ++ toString h ++ " " ++ rule)

/-- Explain a list of rewrites using `nth_rewrite`. -/
private unsafe def using_location.explain_rewrites (rs : List (expr × Bool)) (s : Side) (steps : List how) :
    tactic Stringₓ := do
  let rules ← steps.mmap fun h : how => Option.toList <$> explain_using_location rs s h
  return <| Stringₓ.intercalate ",\n  " rules

namespace UsingConv

/-- `app_addr` represents a tree structure that `conv` tactics use for a rewrite. -/
inductive AppAddr
  | node (children : DirPair (Option app_addr)) : app_addr
  | rw : List ℕ → app_addr

open AppAddr

private unsafe def app_addr.to_string : AppAddr → Stringₓ
  | node c => "(node " ++ ((c.toList.filterMap id).map app_addr.to_string).toString ++ ")"
  | rw rws => "(rw " ++ rws.toString ++ ")"

/-- A data structure for the result of a splice operation.
obstructed:  There was more of the addr to be added left, but we hit a rw
contained:   The added addr was already contained, and did not terminate at an existing rw
new:         The added addr terminated at an existing rw or we could create a new one for it
-/
inductive SpliceResult
  | obstructed
  | contained
  | new (addr : AppAddr)
  deriving Inhabited

open SpliceResult

private unsafe def pack_splice_result (s : ExprLens.Dir) : SpliceResult → DirPair (Option AppAddr) → SpliceResult
  | new addr, c => new <| app_addr.node <| c.Set s (some addr)
  | sr, _ => sr

private unsafe def splice_in_aux (new_rws : List ℕ) : Option AppAddr → List ExprLens.Dir → SpliceResult
  | some <| node _, [] => contained
  | some <| node c, s :: rest => pack_splice_result s (splice_in_aux (c.get s) rest) c
  | some <| rw _, _ :: _ => obstructed
  | some <| rw rws, [] => new <| rw (rws ++ new_rws)
  | none, [] => new <| rw new_rws
  | none, l => splice_in_aux (some <| node ⟨none, none⟩) l

open ExprLens

private unsafe def to_congr_form : List ExprLens.Dir → tactic (List ExprLens.Dir)
  | [] => return []
  | dir.F :: dir.A :: rest => do
    let r ← to_congr_form rest
    return (dir.F :: r)
  | dir.A :: rest => do
    let r ← to_congr_form rest
    return (dir.A :: r)
  | [dir.F] => fail "app list ends in side.L!"
  | dir.F :: dir.F :: _ => fail "app list has repeated side.L!"

/-- Attempt to add new rewrites into the `app_addr` tree. -/
private unsafe def splice_in (a : Option AppAddr) (rws : List ℕ) (s : List ExprLens.Dir) : tactic SpliceResult :=
  splice_in_aux rws a <$> to_congr_form s

/-- Construct a single `erw` tactic for the given rules. -/
private unsafe def build_rw_tactic (rs : List (expr × Bool)) (hs : List ℕ) : tactic Stringₓ := do
  let rws ← (hs.map <| nth_rule rs).mmap pp_rule
  return <| "erw [" ++ Stringₓ.intercalate ", " rws ++ "]"

private unsafe def explain_tree_aux (rs : List (expr × Bool)) : AppAddr → tactic (Option (List Stringₓ))
  | app_addr.rw rws => (fun a => some [a]) <$> build_rw_tactic rs rws
  | app_addr.node ⟨func, arg⟩ => do
    let sf ←
      match func with
        | none => pure none
        | some func => explain_tree_aux func
    let sa ←
      match arg with
        | none => pure none
        | some arg => explain_tree_aux arg
    return <|
        match (sf, sa) with
        | (none, none) => none
        | (some sf, none) => ["congr"].append sf
        | (none, some sa) => ["congr", "skip"].append sa
        | (some sf, some sa) => (["congr"].append sf).append (["skip"].append sf)

/-- Construct a string of Lean code that does a rewrite for the provided tree. -/
private unsafe def explain_tree (rs : List (expr × Bool)) (tree : AppAddr) : tactic (List Stringₓ) :=
  List.join <$> Option.toList <$> explain_tree_aux rs tree

/-- Gather all rewrites into trees, then generate a line of code for each tree.
The return value has one `conv_x` tactic on each line.
-/
private unsafe def explanation_lines (rs : List (expr × Bool)) (s : Side) :
    Option AppAddr → List how → tactic (List Stringₓ)
  | none, [] => return []
  | some tree, [] => do
    let tacs ← explain_tree rs tree
    return <| if tacs = 0 then [] else ["conv_" ++ s ++ " { " ++ Stringₓ.intercalate ", " tacs ++ " }"]
  | tree, h :: rest => do
    let (new_tree, rest_if_fail) ←
      match h.addr with
        | some addr => do
          let new_tree ← splice_in tree [h.rule_index] addr
          return (some new_tree, List.cons h rest)
        | none => do
          return (none, rest)
    match new_tree with
      | some (new new_tree) => explanation_lines new_tree rest
      | _ => do
        let line ← explanation_lines tree []
        let lines ← explanation_lines none rest_if_fail
        return <| line ++ lines

/-- Explain a list of rewrites using `conv_x` tactics. -/
unsafe def explain_rewrites (rs : List (expr × Bool)) (s : Side) (hows : List how) : tactic Stringₓ :=
  Stringₓ.intercalate ",\n  " <$> explanation_lines rs s none hows

end UsingConv

private unsafe def explain_rewrites_concisely (steps : List (expr × Bool)) (needs_refl : Bool) : tactic Stringₓ := do
  let rules ← Stringₓ.intercalate ", " <$> steps.mmap pp_rule
  return <| "erw [" ++ rules ++ "]" ++ if needs_refl then ", refl" else ""

/-- Fails if we can't just use rewrite.
Otherwise, returns 'tt' if we need a `refl` at the end.
-/
private unsafe def check_if_simple_rewrite_succeeds (rewrites : List (expr × Bool)) (goal : expr) : tactic Bool :=
  lock_tactic_state <| do
    let m ← mk_meta_var goal
    set_goals [m]
    rewrites fun q => rewrite_target q.1 { symm := q.2, md := semireducible }
    reflexivity reducible >> return ff <|> reflexivity >> return tt

/-- Construct a list of rewrites from a proof unit. -/
unsafe def proof_unit.rewrites (u : proof_unit) (rs : List (expr × Bool)) : List (expr × Bool) :=
  u.steps.filterMap <| how.to_rewrite rs

/-- Construct an explanation string from a proof unit. -/
unsafe def proof_unit.explain (u : proof_unit) (rs : List (expr × Bool)) (explain_using_conv : Bool) : tactic Stringₓ :=
  if explain_using_conv then using_conv.explain_rewrites rs u.Side u.steps
  else using_location.explain_rewrites rs u.Side u.steps

private unsafe def explain_proof_full (rs : List (expr × Bool)) (explain_using_conv : Bool) :
    List proof_unit → tactic Stringₓ
  | [] => return ""
  | u :: rest => do
    let head
      ←-- Don't use transitivity for the last unit, since it must be redundant.
          if rest.length = 0 ∨ u.Side = side.L then pure []
        else do
          let n ← (infer_type u.proof >>= fun e => Prod.snd <$> (match_eq e <|> match_iff e)) >>= pp
          pure <| ["transitivity " ++ toString n]
    let unit_expl ← u.explain rs explain_using_conv
    let rest_expl ← explain_proof_full rest
    let expls := (head ++ [unit_expl, rest_expl]).filter fun t => ¬t.length = 0
    return <| Stringₓ.intercalate ",\n  " expls

private unsafe def explain_proof_concisely (rules : List (expr × Bool)) (proof : expr) (l : List proof_unit) :
    tactic Stringₓ := do
  let rws : List (expr × Bool) :=
    List.join <|
      l.map fun u => do
        let (r, s) ← u.rewrites rules
        return (r, if u = side.L then s else ¬s)
  let goal ← infer_type proof
  let needs_refl ← check_if_simple_rewrite_succeeds rws goal
  explain_rewrites_concisely rws needs_refl

/-- Trace a human-readable explanation in Lean code of a proof generated by rewrite search.
Emit it as `"Try this: <code>"` with each successive line of code indented.
-/
unsafe def explain_search_result (cfg : config) (rules : List (expr × Bool)) (proof : expr) (units : List proof_unit) :
    tactic Unit :=
  if units.Empty then trace "Try this: exact rfl"
  else do
    let explanation ←
      explain_proof_concisely rules proof units <|> explain_proof_full rules cfg.explain_using_conv units
    trace <| "Try this: " ++ explanation

end Tactic.RewriteSearch

