/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Tactic.Rcases

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/


/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. -/
class CanLift (α β : Sort _) where
  coe : β → α
  cond : α → Prop
  prf : ∀ x : α, cond x → ∃ y : β, coe y = x

instance : CanLift ℤ ℕ :=
  ⟨coe, fun n => 0 ≤ n, fun n hn => ⟨n.natAbs, Int.nat_abs_of_nonneg hn⟩⟩

/-- Enable automatic handling of pi types in `can_lift`. -/
instance Pi.canLift (ι : Sort _) (α β : ι → Sort _) [∀ i : ι, CanLift (α i) (β i)] :
    CanLift (∀ i : ι, α i) (∀ i : ι, β i) where
  coe := fun f i => CanLift.coe (f i)
  cond := fun f => ∀ i, CanLift.Cond (β i) (f i)
  prf := fun f hf =>
    ⟨fun i => Classical.some (CanLift.prf (f i) (hf i)), funext fun i => Classical.some_spec (CanLift.prf (f i) (hf i))⟩

theorem Subtype.exists_pi_extension {ι : Sort _} {α : ι → Sort _} [ne : ∀ i, Nonempty (α i)] {p : ι → Prop}
    (f : ∀ i : Subtype p, α i) : ∃ g : ∀ i : ι, α i, (fun i : Subtype p => g i) = f := by
  run_tac
    tactic.classical
  refine' ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (Ne i), funext _⟩
  rintro ⟨i, hi⟩
  exact dif_pos hi

instance PiSubtype.canLift (ι : Sort _) (α : ι → Sort _) [ne : ∀ i, Nonempty (α i)] (p : ι → Prop) :
    CanLift (∀ i : Subtype p, α i) (∀ i, α i) where
  coe := fun f i => f i
  cond := fun _ => True
  prf := fun f _ => Subtype.exists_pi_extension f

instance PiSubtype.canLift' (ι : Sort _) (α : Sort _) [ne : Nonempty α] (p : ι → Prop) :
    CanLift (Subtype p → α) (ι → α) :=
  PiSubtype.canLift ι (fun _ => α) p

instance Subtype.canLift {α : Sort _} (p : α → Prop) : CanLift α { x // p x } where
  coe := coe
  cond := p
  prf := fun a ha => ⟨⟨a, ha⟩, rfl⟩

open Tactic

/-- A user attribute used internally by the `lift` tactic.
This should not be applied by hand.
-/
@[user_attribute]
unsafe def can_lift_attr : user_attribute (List Name) where
  Name := "_can_lift"
  descr := "internal attribute used by the lift tactic"
  parser := failed
  cache_cfg :=
    { mk_cache := fun _ => do
        let ls ← attribute.get_instances `instance
        ls fun l => do
            let (_, t) ← mk_const l >>= infer_type >>= open_pis
            return <| t `can_lift,
      dependencies := [`instance] }

namespace Tactic

/-- Construct the proof of `cond x` in the lift tactic.
*  `e` is the expression being lifted and `h` is the specified proof of `can_lift.cond e`.
*  `old_tp` and `new_tp` are the arguments to `can_lift` and `inst` is the `can_lift`-instance.
*  `s` and `to_unfold` contain the information of the simp set used to simplify.

If the proof was specified, we check whether it has the correct type.
If it doesn't have the correct type, we display an error message
(but first call dsimp on the expression in the message).

If the proof was not specified, we create assert it as a local constant.
(The name of this local constant doesn't matter, since `lift` will remove it from the context.)
-/
unsafe def get_lift_prf (h : Option pexpr) (old_tp new_tp inst e : expr) (s : simp_lemmas) (to_unfold : List Name) :
    tactic expr := do
  let expected_prf_ty ← mk_app `can_lift.cond [old_tp, new_tp, inst, e]
  let expected_prf_ty ← s.dsimplify to_unfold expected_prf_ty
  if h_some : h then
      decorate_error "lift tactic failed." <| i_to_expr (pquote.1 (%%ₓOption.getₓ h_some : %%ₓexpected_prf_ty))
    else do
      let prf_nm ← get_unused_name
      let prf ← assert prf_nm expected_prf_ty
      swap
      return prf

/-- Lift the expression `p` to the type `t`, with proof obligation given by `h`.
  The list `n` is used for the two newly generated names, and to specify whether `h` should
  remain in the local context. See the doc string of `tactic.interactive.lift` for more information.
  -/
unsafe def lift (p : pexpr) (t : pexpr) (h : Option pexpr) (n : List Name) : tactic Unit := do
  propositional_goal <|> fail "lift tactic failed. Tactic is only applicable when the target is a proposition."
  let e ← i_to_expr p
  let old_tp ← infer_type e
  let new_tp ← i_to_expr (pquote.1 (%%ₓt : Sort _))
  let inst_type ← mk_app `` CanLift [old_tp, new_tp]
  let inst ←
    mk_instance inst_type <|>
        (f!"Failed to find a lift from {(← old_tp)} to {(← new_tp)}. Provide an instance of
              {← inst_type}") >>=
          fail
  let can_lift_instances
    ←-- make the simp set to get rid of `can_lift` projections
          can_lift_attr.get_cache >>=
        fun l => l.mmap resolve_name
  let (s, to_unfold) ← mk_simp_set true [] <| can_lift_instances.map simp_arg_type.expr
  let prf_cond ← get_lift_prf h old_tp new_tp inst e s to_unfold
  let prf_nm := if prf_cond.is_local_constant then some prf_cond.local_pp_name else none
  let prf_ex0
    ←/- We use mk_mapp to apply `can_lift.prf` to all but one argument, and then just use expr.app
          for the last argument. For some reason we get an error when applying mk_mapp it to all
          arguments. -/
        mk_mapp
        `can_lift.prf [old_tp, new_tp, inst, e]
  let prf_ex := prf_ex0 prf_cond
  let new_nm
    ←-- Find the name of the new variable
        if n ≠ [] then return n.head
      else if e.is_local_constant then return e.local_pp_name else get_unused_name
  let eq_nm
    ←-- Find the name of the proof of the equation
        if hn : 1 < n.length then return (n.nthLe 1 hn)
      else if e.is_local_constant then return `rfl else get_unused_name `h
  let temp_nm
    ←/- We add the proof of the existential statement to the context and then apply
        `dsimp` to it, unfolding all `can_lift` instances. -/
      get_unused_name
  let temp_e ← note temp_nm none prf_ex
  dsimp_hyp temp_e s to_unfold {  }
  -- We case on the existential. We use `rcases` because `eq_nm` could be `rfl`.
        rcases
        none (pexpr.of_expr temp_e) <|
      rcases_patt.tuple ([new_nm, eq_nm].map rcases_patt.one)
  /- If the lifted variable is not a local constant,
          try to rewrite it away using the new equality. -/
      when
      (¬e)
      (get_local eq_nm >>= fun e => interactive.rw ⟨[⟨⟨0, 0⟩, tt, pexpr.of_expr e⟩], none⟩ Interactive.Loc.wildcard)
  /- If the proof `prf_cond` is a local constant, remove it from the context,
          unless `n` specifies to keep it. -/
      if h_prf_nm : prf_nm ∧ n 2 ≠ prf_nm then get_local (Option.getₓ h_prf_nm.1) >>= clear
    else skip

setup_tactic_parser

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Parses an optional token "using" followed by a trailing `pexpr`. -/
unsafe def using_texpr :=
  «expr ?» (tk "using" *> texpr)

/-- Parses a token "to" followed by a trailing `pexpr`. -/
unsafe def to_texpr :=
  tk "to" *> texpr

namespace Interactive

/-- Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℕ, h : P ↑n ⊢ ↑n = 3` and `n : ℤ, h : P n ⊢ n ≥ 0`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `can_lift α β`. In this case the proof obligation is specified by `can_lift.cond`.
* Given an instance `can_lift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, can_lift (β a) (γ a)]`, it
  automatically generates an instance `can_lift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
unsafe def lift (p : parse texpr) (t : parse to_texpr) (h : parse using_texpr) (n : parse with_ident_list) :
    tactic Unit :=
  tactic.lift p t h n

add_tactic_doc
  { Name := "lift", category := DocCategory.tactic, declNames := [`tactic.interactive.lift], tags := ["coercions"] }

end Interactive

end Tactic

