/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Binder elimination
-/
import Mathbin.Order.CompleteLattice

namespace OldConv

open Tactic Monadₓ

unsafe instance : MonadFail old_conv :=
  { old_conv.monad with fail := fun α s => (fun r e => tactic.fail (to_fmt s) : old_conv α) }

unsafe instance : HasMonadLift tactic old_conv :=
  ⟨fun α => lift_tactic⟩

unsafe instance (α : Type) : Coe (tactic α) (old_conv α) :=
  ⟨monadLift⟩

unsafe def current_relation : old_conv Name := fun r lhs => return ⟨r, lhs, none⟩

unsafe def head_beta : old_conv Unit := fun r e => do
  let n ← tactic.head_beta e
  return ⟨(), n, none⟩

-- congr should forward data!
unsafe def congr_arg : old_conv Unit → old_conv Unit :=
  congr_core (return ())

unsafe def congr_fun : old_conv Unit → old_conv Unit := fun c => congr_core c (return ())

unsafe def congr_rule (congr : expr) (cs : List (List expr → old_conv Unit)) : old_conv Unit := fun r lhs => do
  let meta_rhs ← infer_type lhs >>= mk_meta_var
  let t
    ←-- is maybe overly restricted for `heq`
        mk_app
        r [lhs, meta_rhs]
  let ((), meta_pr) ←
    solve_aux t do
        apply congr
        focus <|
            cs fun c => do
              let xs ← intros
              conversion (head_beta >> c xs)
        done
  let rhs ← instantiate_mvars meta_rhs
  let pr ← instantiate_mvars meta_pr
  return ⟨(), rhs, some pr⟩

unsafe def congr_binder (congr : Name) (cs : expr → old_conv Unit) : old_conv Unit := do
  let e ← mk_const congr
  congr_rule e
      [fun bs => do
        let [b] ← return bs
        cs b]

unsafe def funext' : (expr → old_conv Unit) → old_conv Unit :=
  congr_binder `` _root_.funext

unsafe def propext' {α : Type} (c : old_conv α) : old_conv α := fun r lhs =>
  (do
      guardₓ (r = `iff)
      c r lhs) <|>
    do
    guardₓ (r = `eq)
    let ⟨res, rhs, pr⟩ ← c `iff lhs
    match pr with
      | some pr => return ⟨res, rhs, (expr.const `propext [] : expr) lhs rhs pr⟩
      | none => return ⟨res, rhs, none⟩

unsafe def apply (pr : expr) : old_conv Unit := fun r e => do
  let sl ← simp_lemmas.mk.add pr
  apply_lemmas sl r e

unsafe def applyc (n : Name) : old_conv Unit := fun r e => do
  let sl ← simp_lemmas.mk.add_simp n
  apply_lemmas sl r e

unsafe def apply' (n : Name) : old_conv Unit := do
  let e ← mk_const n
  congr_rule e []

end OldConv

open Expr Tactic OldConv

/- Binder elimination:

We assume a binder `B : p → Π (α : Sort u), (α → t) → t`, where `t` is a type depending on `p`.
Examples:
  ∃: there is no `p` and `t` is `Prop`.
  ⨅, ⨆: here p is `β` and `[complete_lattice β]`, `p` is `β`

Problem: ∀x, _ should be a binder, but is not a constant!

Provide a mechanism to rewrite:

  B (x : α) ..x.. (h : x = t), p x  =  B ..x/t.., p t

Here ..x.. are binders, maybe also some constants which provide commutativity rules with `B`.

-/
unsafe structure binder_eq_elim where
  match_binder : expr → tactic (expr × expr)
  -- returns the bound type and body
  adapt_rel : old_conv Unit → old_conv Unit
  -- optionally adapt `eq` to `iff`
  apply_comm : old_conv Unit
  -- apply commutativity rule
  apply_congr : (expr → old_conv Unit) → old_conv Unit
  -- apply congruence rule
  apply_elim_eq : old_conv Unit

-- (B (x : β) (h : x = t), s x) = s t
unsafe def binder_eq_elim.check_eq (b : binder_eq_elim) (x : expr) : expr → tactic Unit
  | quote.1 (@Eq (%%ₓβ) (%%ₓl) (%%ₓr)) => guardₓ (l = x ∧ ¬x.occurs r ∨ r = x ∧ ¬x.occurs l)
  | _ => fail "no match"

unsafe def binder_eq_elim.pull (b : binder_eq_elim) (x : expr) : old_conv Unit := do
  let (β, f) ← lhs >>= lift_tactic ∘ b.match_binder
  guardₓ ¬x β <|>
      b x β <|> do
        b fun x => binder_eq_elim.pull
        b

unsafe def binder_eq_elim.push (b : binder_eq_elim) : old_conv Unit :=
  b.apply_elim_eq <|>
    (do
        b
        b fun x => binder_eq_elim.push) <|>
      do
      b <| b
      binder_eq_elim.push

unsafe def binder_eq_elim.check (b : binder_eq_elim) (x : expr) : expr → tactic Unit
  | e => do
    let (β, f) ← b.match_binder e
    b x β <|> do
        let lam n bi d bd ← return f
        let x ← mk_local' n bi d
        binder_eq_elim.check <| bd x

unsafe def binder_eq_elim.old_conv (b : binder_eq_elim) : old_conv Unit := do
  let (β, f) ← lhs >>= lift_tactic ∘ b.match_binder
  let lam n bi d bd ← return f
  let x ← mk_local' n bi d
  b x (bd x)
  b b

theorem exists_elim_eq_left.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a' = a → Prop) :
    (∃ (a' : α)(h : a' = a), p a' h) ↔ p a rfl :=
  ⟨fun ⟨a', ⟨h, p_h⟩⟩ =>
    match a', h, p_h with
    | _, rfl, h => h,
    fun h => ⟨a, rfl, h⟩⟩

theorem exists_elim_eq_right.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a = a' → Prop) :
    (∃ (a' : α)(h : a = a'), p a' h) ↔ p a rfl :=
  ⟨fun ⟨a', ⟨h, p_h⟩⟩ =>
    match a', h, p_h with
    | _, rfl, h => h,
    fun h => ⟨a, rfl, h⟩⟩

unsafe def exists_eq_elim : binder_eq_elim where
  match_binder := fun e => do
    let quote.1 (@Exists (%%ₓβ) (%%ₓf)) ← return e
    return (β, f)
  adapt_rel := propext'
  apply_comm := applyc `` exists_comm
  apply_congr := congr_binder `` exists_congr
  apply_elim_eq := apply' `` exists_elim_eq_left <|> apply' `` exists_elim_eq_right

theorem forall_comm.{u, v} {α : Sort u} {β : Sort v} (p : α → β → Prop) : (∀ a b, p a b) ↔ ∀ b a, p a b :=
  ⟨fun h b a => h a b, fun h b a => h a b⟩

theorem forall_elim_eq_left.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a' = a → Prop) :
    (∀ (a' : α) (h : a' = a), p a' h) ↔ p a rfl :=
  ⟨fun h => h a rfl, fun h a' h_eq =>
    match a', h_eq with
    | _, rfl => h⟩

theorem forall_elim_eq_right.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a = a' → Prop) :
    (∀ (a' : α) (h : a = a'), p a' h) ↔ p a rfl :=
  ⟨fun h => h a rfl, fun h a' h_eq =>
    match a', h_eq with
    | _, rfl => h⟩

unsafe def forall_eq_elim : binder_eq_elim where
  match_binder := fun e => do
    let expr.pi n bi d bd ← return e
    return (d, expr.lam n bi d bd)
  adapt_rel := propext'
  apply_comm := applyc `` forall_comm
  apply_congr := congr_binder `` forall_congrₓ
  apply_elim_eq := apply' `` forall_elim_eq_left <|> apply' `` forall_elim_eq_right

unsafe def supr_eq_elim : binder_eq_elim where
  match_binder := fun e => do
    let quote.1 (@supr (%%ₓα) (%%ₓcl) (%%ₓβ) (%%ₓf)) ← return e
    return (β, f)
  adapt_rel := fun c => do
    let r ← current_relation
    guardₓ (r = `eq)
    c
  apply_comm := applyc `` supr_comm
  apply_congr := congr_arg ∘ funext'
  apply_elim_eq := applyc `` supr_supr_eq_left <|> applyc `` supr_supr_eq_right

unsafe def infi_eq_elim : binder_eq_elim where
  match_binder := fun e => do
    let quote.1 (@infi (%%ₓα) (%%ₓcl) (%%ₓβ) (%%ₓf)) ← return e
    return (β, f)
  adapt_rel := fun c => do
    let r ← current_relation
    guardₓ (r = `eq)
    c
  apply_comm := applyc `` infi_comm
  apply_congr := congr_arg ∘ funext'
  apply_elim_eq := applyc `` infi_infi_eq_left <|> applyc `` infi_infi_eq_right

universe u v w w₂

variable {α : Type u} {β : Type v} {ι : Sort w} {ι₂ : Sort w₂} {s t : Set α} {a : α}

section

variable [CompleteLattice α]

example {s : Set β} {f : β → α} : inf (Set.Image f s) = ⨅ a ∈ s, f a := by
  simp [← Inf_eq_infi, ← infi_and]
  run_tac
    conversion infi_eq_elim.old_conv

example {s : Set β} {f : β → α} : sup (Set.Image f s) = ⨆ a ∈ s, f a := by
  simp [← Sup_eq_supr, ← supr_and]
  run_tac
    conversion supr_eq_elim.old_conv

end

