/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Tactic.DocCommands

/-!
# `generalize_proofs`

A simple tactic to find and replace all occurrences of proof terms in the
context and goal with new variables.
-/


open Interactive Interactive.Types Lean.Parser

namespace Tactic

private unsafe def collect_proofs_in : expr → List expr → List Name × List expr → tactic (List Name × List expr)
  | e, ctx, (ns, hs) =>
    let go (tac : List Name × List expr → tactic (List Name × List expr)) : tactic (List Name × List expr) := do
      let t ← infer_type e
      mcond (is_prop t)
          (do
            first
                  (hs fun h => do
                    let t' ← infer_type h
                    is_def_eq t t'
                    let g ← target
                    change <| g fun a n => if a = e then some h else none
                    return (ns, hs)) <|>
                (let (n, ns) :=
                    (match ns with
                    | [] => (`_x, [])
                    | n :: ns => (n, ns) :
                      Name × List Name)
                  do
                  generalize e n
                  let h ← intro n
                  return (ns, h :: hs)) <|>
                  return (ns, hs))
          (tac (ns, hs))
    match e with
    | expr.const _ _ => go return
    | expr.local_const _ _ _ _ => do
      let t ← infer_type e
      collect_proofs_in t ctx (ns, hs)
    | expr.mvar _ _ _ => do
      let e ← instantiate_mvars e
      match e with
        | expr.mvar _ _ _ => do
          let t ← infer_type e
          collect_proofs_in t ctx (ns, hs)
        | _ => collect_proofs_in e ctx (ns, hs)
    | expr.app f x => go fun nh => collect_proofs_in f ctx nh >>= collect_proofs_in x ctx
    | expr.lam n b d e =>
      go fun nh => do
        let nh ← collect_proofs_in d ctx nh
        let var ← mk_local' n b d
        collect_proofs_in (expr.instantiate_var e var) (var :: ctx) nh
    | expr.pi n b d e => do
      let nh ← collect_proofs_in d ctx (ns, hs)
      let var ← mk_local' n b d
      collect_proofs_in (expr.instantiate_var e var) (var :: ctx) nh
    | expr.elet n t d e =>
      go fun nh => do
        let nh ← collect_proofs_in t ctx nh
        let nh ← collect_proofs_in d ctx nh
        collect_proofs_in (expr.instantiate_var e d) ctx nh
    | expr.macro m l => go fun nh => mfoldl (fun x e => collect_proofs_in e ctx x) nh l
    | _ => return (ns, hs)

/-- Generalize proofs in the goal, naming them with the provided list. -/
unsafe def generalize_proofs (ns : List Name) (loc : Interactive.Loc) : tactic Unit := do
  intros_dep
  let hs ← local_context >>= mfilter is_proof
  let n ← loc.get_locals >>= revert_lst
  let t ← target
  collect_proofs_in t [] (ns, hs)
  intron n <|> intros $> ()

-- mathport name: «expr *»
local postfix:1024 "*" => many

namespace Interactive

/-- Generalize proofs in the goal, naming them with the provided list.

For example:
```lean
example : list.nth_le [1, 2] 1 dec_trivial = 2 :=
begin
  -- ⊢ [1, 2].nth_le 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nth_le 1 h = 2
end
```
-/
unsafe def generalize_proofs : parse ident_* → parse location → tactic Unit :=
  tactic.generalize_proofs

end Interactive

add_tactic_doc
  { Name := "generalize_proofs", category := DocCategory.tactic, declNames := [`tactic.interactive.generalize_proofs],
    tags := ["context management"] }

end Tactic

