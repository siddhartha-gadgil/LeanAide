/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Tactic.NormNum

/-! ### `norm_num` plugin for big operators

This `norm_num` plugin provides support for computing sums and products of
lists, multisets and finsets.

Example goals this plugin can solve:

 * `∑ i in finset.range 10, (i^2 : ℕ) = 285`
 * `Π i in {1, 4, 9, 16}, nat.sqrt i = 24`
 * `([1, 2, 1, 3]).sum = 7`

## Implementation notes

The tactic works by first converting the expression denoting the collection
(list, multiset, finset) to a list of expressions denoting each element. For
finsets, this involves erasing duplicate elements (the tactic fails if equality
or disequality cannot be determined).

After rewriting the big operator to a product/sum of lists, we evaluate this
using `norm_num` itself to handle multiplication/addition.

Finally, we package up the result using some congruence lemmas.

-/


open Tactic

namespace Tactic.NormNum

/-- Use `norm_num` to decide equality between two expressions.

If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial: it will fail in cases where `norm_num` can't reduce either side
to a rational numeral.
-/
unsafe def decide_eq (l r : expr) : tactic (Bool × expr) := do
  let (l', l'_pf) ← or_refl_conv norm_num.derive l
  let (r', r'_pf) ← or_refl_conv norm_num.derive r
  let n₁ ← l'.to_rat
  let n₂ ← r'.to_rat
  let c ← infer_type l' >>= mk_instance_cache
  if n₁ = n₂ then do
      let pf ← i_to_expr (pquote.1 (Eq.trans (%%ₓl'_pf) <| Eq.symm (%%ₓr'_pf)))
      pure (tt, pf)
    else do
      let (_, p) ← norm_num.prove_ne c l' r' n₁ n₂
      pure (ff, p)

theorem List.not_mem_cons {α : Type _} {x y : α} {ys : List α} (h₁ : x ≠ y) (h₂ : x ∉ ys) : x ∉ y :: ys := fun h =>
  ((List.mem_cons_iff _ _ _).mp h).elim h₁ h₂

/-- Use a decision procedure for the equality of list elements to decide list membership.

If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial iff its parameter `decide_eq` is partial.
-/
unsafe def list.decide_mem (decide_eq : expr → expr → tactic (Bool × expr)) : expr → List expr → tactic (Bool × expr)
  | x, [] => do
    let pf ← i_to_expr (pquote.1 (List.not_mem_nilₓ (%%ₓx)))
    pure (ff, pf)
  | x, y :: ys => do
    let (is_head, head_pf) ← decide_eq x y
    if is_head then do
        let pf ← i_to_expr (pquote.1 ((List.mem_cons_iff (%%ₓx) (%%ₓy) _).mpr (Or.inl (%%ₓhead_pf))))
        pure (tt, pf)
      else do
        let (mem_tail, tail_pf) ← list.decide_mem x ys
        if mem_tail then do
            let pf ← i_to_expr (pquote.1 ((List.mem_cons_iff (%%ₓx) (%%ₓy) _).mpr (Or.inr (%%ₓtail_pf))))
            pure (tt, pf)
          else do
            let pf ← i_to_expr (pquote.1 (List.not_mem_cons (%%ₓhead_pf) (%%ₓtail_pf)))
            pure (ff, pf)

theorem Finset.insert_eq_coe_list_of_mem {α : Type _} [DecidableEq α] (x : α) (xs : Finset α) {xs' : List α}
    (h : x ∈ xs') (nd_xs : xs'.Nodup) (hxs' : xs = Finset.mk (↑xs') (Multiset.coe_nodup.mpr nd_xs)) :
    insert x xs = Finset.mk (↑xs') (Multiset.coe_nodup.mpr nd_xs) := by
  have h : x ∈ xs := by
    simpa [← hxs'] using h
  rw [Finset.insert_eq_of_mem h, hxs']

theorem Finset.insert_eq_coe_list_cons {α : Type _} [DecidableEq α] (x : α) (xs : Finset α) {xs' : List α} (h : x ∉ xs')
    (nd_xs : xs'.Nodup) (nd_xxs : (x :: xs').Nodup) (hxs' : xs = Finset.mk (↑xs') (Multiset.coe_nodup.mpr nd_xs)) :
    insert x xs = Finset.mk (↑(x :: xs')) (Multiset.coe_nodup.mpr nd_xxs) := by
  have h : x ∉ xs := by
    simpa [← hxs'] using h
  rw [← Finset.val_inj, Finset.insert_val_of_not_mem h, hxs']
  simp only [← Multiset.cons_coe]

/-- Convert an expression denoting a finset to a list of elements,
a proof that this list is equal to the original finset,
and a proof that the list contains no duplicates.

We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).

`decide_eq` is a (partial) decision procedure for determining whether two
elements of the finset are equal, for example to parse `{2, 1, 2}` into `[2, 1]`.
-/
unsafe def eval_finset (decide_eq : expr → expr → tactic (Bool × expr)) : expr → tactic (List expr × expr × expr)
  | e@(quote.1 HasEmptyc.emptyc) => do
    let eq ← mk_eq_refl e
    let nd ← i_to_expr (pquote.1 List.nodup_nil)
    pure ([], Eq, nd)
  | e@(quote.1 (HasSingleton.singleton (%%ₓx))) => do
    let eq ← mk_eq_refl e
    let nd ← i_to_expr (pquote.1 (List.nodup_singleton (%%ₓx)))
    pure ([x], Eq, nd)
  | quote.1 (@HasInsert.insert (@Finset.hasInsert (%%ₓdec)) (%%ₓx) (%%ₓxs)) => do
    let (exs, xs_eq, xs_nd) ← eval_finset xs
    let (is_mem, mem_pf) ← list.decide_mem decide_eq x exs
    if is_mem then do
        let pf ←
          i_to_expr (pquote.1 (Finset.insert_eq_coe_list_of_mem (%%ₓx) (%%ₓxs) (%%ₓmem_pf) (%%ₓxs_nd) (%%ₓxs_eq)))
        pure (exs, pf, xs_nd)
      else do
        let nd ← i_to_expr (pquote.1 (List.nodup_cons.mpr ⟨%%ₓmem_pf, %%ₓxs_nd⟩))
        let pf ←
          i_to_expr (pquote.1 (Finset.insert_eq_coe_list_cons (%%ₓx) (%%ₓxs) (%%ₓmem_pf) (%%ₓxs_nd) (%%ₓnd) (%%ₓxs_eq)))
        pure (x :: exs, pf, nd)
  | quote.1 (@Finset.univ (%%ₓft)) => do
    let-- Convert the fintype instance expression `ft` to a list of its elements.
      -- Unfold it to the `fintype.mk` constructor and a list of arguments.
      `fintype.mk
      ← get_app_fn_const_whnf ft | fail (to_fmt "Unknown fintype expression" ++ format.line ++ to_fmt ft)
    let [_, args, _] ← get_app_args_whnf ft | fail (to_fmt "Expected 3 arguments to `fintype.mk`")
    eval_finset args
  | e@(quote.1 (Finset.range (%%ₓen))) => do
    let n ← expr.to_nat en
    let eis ← (List.range n).mmap fun i => expr.of_nat (quote.1 ℕ) i
    let eq ← mk_eq_refl e
    let nd ← i_to_expr (pquote.1 (List.nodup_range (%%ₓen)))
    pure (eis, Eq, nd)
  | e@(quote.1 (Finset.finRange (%%ₓen))) => do
    let n ← expr.to_nat en
    let eis ← (List.finRange n).mmap fun i => expr.of_nat (quote.1 (Finₓ (%%ₓen))) i
    let eq ← mk_eq_refl e
    let nd ← i_to_expr (pquote.1 (List.nodup_fin_range (%%ₓen)))
    pure (eis, Eq, nd)
  | e => fail (to_fmt "Unknown finset expression" ++ format.line ++ to_fmt e)

theorem List.map_cons_congr {α β : Type _} (f : α → β) {x : α} {xs : List α} {fx : β} {fxs : List β} (h₁ : f x = fx)
    (h₂ : xs.map f = fxs) : (x :: xs).map f = fx :: fxs := by
  rw [List.map_cons, h₁, h₂]

/-- Apply `ef : α → β` to all elements of the list, constructing an equality proof. -/
unsafe def eval_list_map (ef : expr) : List expr → tactic (List expr × expr)
  | [] => do
    let eq ← i_to_expr (pquote.1 (List.map_nil (%%ₓef)))
    pure ([], Eq)
  | x :: xs => do
    let (fx, fx_eq) ← or_refl_conv norm_num.derive (expr.app ef x)
    let (fxs, fxs_eq) ← eval_list_map xs
    let eq ← i_to_expr (pquote.1 (List.map_cons_congr (%%ₓef) (%%ₓfx_eq) (%%ₓfxs_eq)))
    pure (fx :: fxs, Eq)

theorem Multiset.cons_congr {α : Type _} (x : α) {xs : Multiset α} {xs' : List α} (xs_eq : (xs' : Multiset α) = xs) :
    (List.cons x xs' : Multiset α) = x ::ₘ xs := by
  rw [← xs_eq] <;> rfl

theorem Multiset.map_congr {α β : Type _} (f : α → β) {xs : Multiset α} {xs' : List α} {ys : List β}
    (xs_eq : xs = (xs' : Multiset α)) (ys_eq : xs'.map f = ys) : xs.map f = (ys : Multiset β) := by
  rw [← ys_eq, ← Multiset.coe_map, xs_eq]

/-- Convert an expression denoting a multiset to a list of elements.

We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).
-/
unsafe def eval_multiset : expr → tactic (List expr × expr)
  | e@(quote.1 (@Zero.zero (Multiset _) _)) => do
    let eq ← mk_eq_refl e
    pure ([], Eq)
  | e@(quote.1 HasEmptyc.emptyc) => do
    let eq ← mk_eq_refl e
    pure ([], Eq)
  | e@(quote.1 (HasSingleton.singleton (%%ₓx))) => do
    let eq ← mk_eq_refl e
    pure ([x], Eq)
  | e@(quote.1 (Multiset.cons (%%ₓx) (%%ₓxs))) => do
    let (xs, xs_eq) ← eval_multiset xs
    let eq ← i_to_expr (pquote.1 (Multiset.cons_congr (%%ₓx) (%%ₓxs_eq)))
    pure (x :: xs, Eq)
  | e@(quote.1 (@HasInsert.insert Multiset.hasInsert (%%ₓx) (%%ₓxs))) => do
    let (xs, xs_eq) ← eval_multiset xs
    let eq ← i_to_expr (pquote.1 (Multiset.cons_congr (%%ₓx) (%%ₓxs_eq)))
    pure (x :: xs, Eq)
  | e@(quote.1 (Multiset.range (%%ₓen))) => do
    let n ← expr.to_nat en
    let eis ← (List.range n).mmap fun i => expr.of_nat (quote.1 ℕ) i
    let eq ← mk_eq_refl e
    pure (eis, Eq)
  | quote.1 (@Multiset.map (%%ₓα) (%%ₓβ) (%%ₓef) (%%ₓexs)) => do
    let (xs, xs_eq) ← eval_multiset exs
    let (ys, ys_eq) ← eval_list_map ef xs
    let eq ← i_to_expr (pquote.1 (Multiset.map_congr (%%ₓef) (%%ₓxs_eq) (%%ₓys_eq)))
    pure (ys, Eq)
  | e => fail (to_fmt "Unknown multiset expression" ++ format.line ++ to_fmt e)

theorem List.cons_congr {α : Type _} (x : α) {xs : List α} {xs' : List α} (xs_eq : xs' = xs) : x :: xs' = x :: xs := by
  rw [xs_eq]

theorem List.map_congr {α β : Type _} (f : α → β) {xs xs' : List α} {ys : List β} (xs_eq : xs = xs')
    (ys_eq : xs'.map f = ys) : xs.map f = ys := by
  rw [← ys_eq, xs_eq]

/-- Convert an expression denoting a list to a list of elements. -/
unsafe def eval_list : expr → tactic (List expr × expr)
  | e@(quote.1 List.nil) => do
    let eq ← mk_eq_refl e
    pure ([], Eq)
  | e@(quote.1 (List.cons (%%ₓx) (%%ₓxs))) => do
    let (xs, xs_eq) ← eval_list xs
    let eq ← i_to_expr (pquote.1 (List.cons_congr (%%ₓx) (%%ₓxs_eq)))
    pure (x :: xs, Eq)
  | e@(quote.1 (List.range (%%ₓen))) => do
    let n ← expr.to_nat en
    let eis ← (List.range n).mmap fun i => expr.of_nat (quote.1 ℕ) i
    let eq ← mk_eq_refl e
    pure (eis, Eq)
  | quote.1 (@List.map (%%ₓα) (%%ₓβ) (%%ₓef) (%%ₓexs)) => do
    let (xs, xs_eq) ← eval_list exs
    let (ys, ys_eq) ← eval_list_map ef xs
    let eq ← i_to_expr (pquote.1 (List.map_congr (%%ₓef) (%%ₓxs_eq) (%%ₓys_eq)))
    pure (ys, Eq)
  | e => fail (to_fmt "Unknown list expression" ++ format.line ++ to_fmt e)

@[to_additive]
theorem List.prod_cons_congr {α : Type _} [Monoidₓ α] (xs : List α) (x y z : α) (his : xs.Prod = y) (hi : x * y = z) :
    (x :: xs).Prod = z := by
  rw [List.prod_cons, his, hi]

/-- Evaluate `list.prod %%xs`,
producing the evaluated expression and an equality proof. -/
unsafe def list.prove_prod (α : expr) : List expr → tactic (expr × expr)
  | [] => do
    let result ← expr.of_nat α 1
    let proof ← i_to_expr (pquote.1 (@List.prod_nil (%%ₓα) _))
    pure (result, proof)
  | x :: xs => do
    let eval_xs ← list.prove_prod xs
    let xxs ← i_to_expr (pquote.1 ((%%ₓx) * %%ₓeval_xs.1))
    let eval_xxs ← or_refl_conv norm_num.derive xxs
    let exs ← expr.of_list α xs
    let proof ←
      i_to_expr
          (pquote.1
            (List.prod_cons_congr (%%ₓexs) (%%ₓx) (%%ₓeval_xs.1) (%%ₓeval_xxs.1) (%%ₓeval_xs.2) (%%ₓeval_xxs.2)))
    pure (eval_xxs.1, proof)

/-- Evaluate `list.sum %%xs`,
sumucing the evaluated expression and an equality proof. -/
unsafe def list.prove_sum (α : expr) : List expr → tactic (expr × expr)
  | [] => do
    let result ← expr.of_nat α 0
    let proof ← i_to_expr (pquote.1 (@List.sum_nil (%%ₓα) _))
    pure (result, proof)
  | x :: xs => do
    let eval_xs ← list.prove_sum xs
    let xxs ← i_to_expr (pquote.1 ((%%ₓx) + %%ₓeval_xs.1))
    let eval_xxs ← or_refl_conv norm_num.derive xxs
    let exs ← expr.of_list α xs
    let proof ←
      i_to_expr
          (pquote.1 (List.sum_cons_congr (%%ₓexs) (%%ₓx) (%%ₓeval_xs.1) (%%ₓeval_xxs.1) (%%ₓeval_xs.2) (%%ₓeval_xxs.2)))
    pure (eval_xxs.1, proof)

@[to_additive]
theorem List.prod_congr {α : Type _} [Monoidₓ α] {xs xs' : List α} {z : α} (h₁ : xs = xs') (h₂ : xs'.Prod = z) :
    xs.Prod = z := by
  cc

@[to_additive]
theorem Multiset.prod_congr {α : Type _} [CommMonoidₓ α] {xs : Multiset α} {xs' : List α} {z : α}
    (h₁ : xs = (xs' : Multiset α)) (h₂ : xs'.Prod = z) : xs.Prod = z := by
  rw [← h₂, ← Multiset.coe_prod, h₁]

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).prod`,
producing the evaluated expression and an equality proof. -/
unsafe def list.prove_prod_map (β ef : expr) (xs : List expr) : tactic (expr × expr) := do
  let (fxs, fxs_eq) ← eval_list_map ef xs
  let (Prod, prod_eq) ← list.prove_prod β fxs
  let eq ← i_to_expr (pquote.1 (List.prod_congr (%%ₓfxs_eq) (%%ₓprod_eq)))
  pure (Prod, Eq)

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).sum`,
producing the evaluated expression and an equality proof. -/
unsafe def list.prove_sum_map (β ef : expr) (xs : List expr) : tactic (expr × expr) := do
  let (fxs, fxs_eq) ← eval_list_map ef xs
  let (Sum, sum_eq) ← list.prove_sum β fxs
  let eq ← i_to_expr (pquote.1 (List.sum_congr (%%ₓfxs_eq) (%%ₓsum_eq)))
  pure (Sum, Eq)

@[to_additive]
theorem Finset.eval_prod_of_list {β α : Type _} [CommMonoidₓ β] (s : Finset α) (f : α → β) {is : List α}
    (his : is.Nodup) (hs : Finset.mk (↑is) (Multiset.coe_nodup.mpr his) = s) {x : β} (hx : (is.map f).Prod = x) :
    s.Prod f = x := by
  rw [← hs, Finset.prod_mk, Multiset.coe_map, Multiset.coe_prod, hx]

/-- `norm_num` plugin for evaluating big operators:
 * `list.prod`
 * `list.sum`
 * `multiset.prod`
 * `multiset.sum`
 * `finset.prod`
 * `finset.sum`
-/
@[norm_num]
unsafe def eval_big_operators : expr → tactic (expr × expr)
  | quote.1 (@List.prod (%%ₓα) (%%ₓinst1) (%%ₓinst2) (%%ₓexs)) =>
    tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" <| do
      let (xs, list_eq) ← eval_list exs
      let (result, sum_eq) ← list.prove_prod α xs
      let pf ← i_to_expr (pquote.1 (List.prod_congr (%%ₓlist_eq) (%%ₓsum_eq)))
      pure (result, pf)
  | quote.1 (@List.sum (%%ₓα) (%%ₓinst1) (%%ₓinst2) (%%ₓexs)) =>
    tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" <| do
      let (xs, list_eq) ← eval_list exs
      let (result, sum_eq) ← list.prove_sum α xs
      let pf ← i_to_expr (pquote.1 (List.sum_congr (%%ₓlist_eq) (%%ₓsum_eq)))
      pure (result, pf)
  | quote.1 (@Multiset.prod (%%ₓα) (%%ₓinst) (%%ₓexs)) =>
    tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" <| do
      let (xs, list_eq) ← eval_multiset exs
      let (result, sum_eq) ← list.prove_prod α xs
      let pf ← i_to_expr (pquote.1 (Multiset.prod_congr (%%ₓlist_eq) (%%ₓsum_eq)))
      pure (result, pf)
  | quote.1 (@Multiset.sum (%%ₓα) (%%ₓinst) (%%ₓexs)) =>
    tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" <| do
      let (xs, list_eq) ← eval_multiset exs
      let (result, sum_eq) ← list.prove_sum α xs
      let pf ← i_to_expr (pquote.1 (Multiset.sum_congr (%%ₓlist_eq) (%%ₓsum_eq)))
      pure (result, pf)
  | quote.1 (@Finset.prod (%%ₓβ) (%%ₓα) (%%ₓinst) (%%ₓes) (%%ₓef)) =>
    tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" <| do
      let (xs, list_eq, nodup) ← eval_finset decide_eq es
      let (result, sum_eq) ← list.prove_prod_map β ef xs
      let pf ← i_to_expr (pquote.1 (Finset.eval_prod_of_list (%%ₓes) (%%ₓef) (%%ₓnodup) (%%ₓlist_eq) (%%ₓsum_eq)))
      pure (result, pf)
  | quote.1 (@Finset.sum (%%ₓβ) (%%ₓα) (%%ₓinst) (%%ₓes) (%%ₓef)) =>
    tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" <| do
      let (xs, list_eq, nodup) ← eval_finset decide_eq es
      let (result, sum_eq) ← list.prove_sum_map β ef xs
      let pf ← i_to_expr (pquote.1 (Finset.eval_sum_of_list (%%ₓes) (%%ₓef) (%%ₓnodup) (%%ₓlist_eq) (%%ₓsum_eq)))
      pure (result, pf)
  | _ => failed

end Tactic.NormNum

