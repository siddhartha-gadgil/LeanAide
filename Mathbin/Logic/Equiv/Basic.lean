/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Data.FunLike.Equiv
import Mathbin.Data.Option.Basic
import Mathbin.Data.Prod.Basic
import Mathbin.Data.Quot
import Mathbin.Data.Sigma.Basic
import Mathbin.Data.Subtype
import Mathbin.Data.Sum.Basic
import Mathbin.Logic.Function.Conjugate
import Mathbin.Logic.Unique
import Mathbin.Tactic.NormCast
import Mathbin.Tactic.Simps

/-!
# Equivalence between types

In this file we define two types:

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `equiv.perm α`: the group of permutations `α ≃ α`. More lemmas about `equiv.perm` can be found in
  `group_theory/perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `equiv.refl α` is the identity map interpreted as `α ≃ α`;

  - `equiv.sum_equiv_sigma_bool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : bool, cond b α β`;

  - `equiv.prod_sum_distrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

  - `equiv.prod_congr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `prod.map`.

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `equiv.inhabited` takes `e : α ≃ β` and `[inhabited β]` and returns `inhabited α`;
  - `equiv.unique` takes `e : α ≃ β` and `[unique β]` and returns `unique α`;
  - `equiv.decidable_eq` takes `e : α ≃ β` and `[decidable_eq β]` and returns `decidable_eq α`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

## Tags

equivalence, congruence, bijective map
-/


open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equivₓ (α : Sort _) (β : Sort _) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse inv_fun to_fun
  right_inv : RightInverse inv_fun to_fun

-- mathport name: «expr ≃ »
infixl:25 " ≃ " => Equivₓ

instance {F} [EquivLike F α β] : CoeTₓ F (α ≃ β) :=
  ⟨fun f =>
    { toFun := f, invFun := EquivLike.inv f, left_inv := EquivLike.left_inv f, right_inv := EquivLike.right_inv f }⟩

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible]
def Equivₓ.Perm (α : Sort _) :=
  Equivₓ α α

namespace Equivₓ

instance : EquivLike (α ≃ β) α β where
  coe := toFun
  inv := invFun
  left_inv := left_inv
  right_inv := right_inv
  coe_injective' := fun e₁ e₂ h₁ h₂ => by
    cases e₁
    cases e₂
    congr

instance : CoeFun (α ≃ β) fun _ => α → β :=
  ⟨toFun⟩

@[simp]
theorem coe_fn_mk (f : α → β) (g l r) : (Equivₓ.mk f g l r : α → β) = f :=
  rfl

/-- The map `coe_fn : (r ≃ s) → (r → s)` is injective. -/
theorem coe_fn_injective : @Function.Injective (α ≃ β) (α → β) coeFn :=
  FunLike.coe_injective

protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ :=
  FunLike.coe_fn_eq

@[ext]
theorem ext {f g : Equivₓ α β} (H : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g H

protected theorem congr_arg {f : Equivₓ α β} {x x' : α} : x = x' → f x = f x' :=
  FunLike.congr_arg f

protected theorem congr_fun {f g : Equivₓ α β} (h : f = g) (x : α) : f x = g x :=
  FunLike.congr_fun h x

theorem ext_iff {f g : Equivₓ α β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[ext]
theorem Perm.ext {σ τ : Equivₓ.Perm α} (H : ∀ x, σ x = τ x) : σ = τ :=
  Equivₓ.ext H

protected theorem Perm.congr_arg {f : Equivₓ.Perm α} {x x' : α} : x = x' → f x = f x' :=
  Equivₓ.congr_arg

protected theorem Perm.congr_fun {f g : Equivₓ.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equivₓ.congr_fun h x

theorem Perm.ext_iff {σ τ : Equivₓ.Perm α} : σ = τ ↔ ∀ x, σ x = τ x :=
  ext_iff

/-- Any type is equivalent to itself. -/
@[refl]
protected def refl (α : Sort _) : α ≃ α :=
  ⟨id, id, fun x => rfl, fun x => rfl⟩

instance inhabited' : Inhabited (α ≃ α) :=
  ⟨Equivₓ.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm]
protected def symm (e : α ≃ β) : β ≃ α :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : α ≃ β) : β → α :=
  e.symm

initialize_simps_projections Equiv (toFun → apply, invFun → symmApply)

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans]
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simp]
theorem to_fun_as_coe (e : α ≃ β) : e.toFun = e :=
  rfl

@[simp]
theorem inv_fun_as_coe (e : α ≃ β) : e.invFun = e.symm :=
  rfl

protected theorem injective (e : α ≃ β) : Injective e :=
  EquivLike.injective e

protected theorem surjective (e : α ≃ β) : Surjective e :=
  EquivLike.surjective e

protected theorem bijective (e : α ≃ β) : Bijective e :=
  EquivLike.bijective e

protected theorem subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.Injective.Subsingleton

protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.Injective.Subsingleton

theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun h => e.symm.subsingleton, fun h => e.subsingleton⟩

instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  ⟨fun f g => Equivₓ.ext fun x => Subsingleton.elimₓ _ _⟩

instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  ⟨fun f g => Equivₓ.ext fun x => @Subsingleton.elimₓ _ (Equivₓ.subsingleton.symm f) _ _⟩

instance permUnique [Subsingleton α] : Unique (Perm α) :=
  uniqueOfSubsingleton (Equivₓ.refl α)

theorem Perm.subsingleton_eq_refl [Subsingleton α] (e : Perm α) : e = Equivₓ.refl α :=
  Subsingleton.elimₓ _ _

/-- Transfer `decidable_eq` across an equivalence. -/
protected def decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.Injective.DecidableEq

theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β :=
  Nonempty.congr e e.symm

protected theorem nonempty (e : α ≃ β) [Nonempty β] : Nonempty α :=
  e.nonempty_congr.mpr ‹_›

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited [Inhabited β] (e : α ≃ β) : Inhabited α :=
  ⟨e.symm default⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique [Unique β] (e : α ≃ β) : Unique α :=
  e.symm.Surjective.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β :=
  ⟨cast h, cast h.symm, fun x => by
    cases h
    rfl, fun x => by
    cases h
    rfl⟩

@[simp]
theorem coe_fn_symm_mk (f : α → β) (g l r) : ((Equivₓ.mk f g l r).symm : β → α) = g :=
  rfl

@[simp]
theorem coe_refl : ⇑(Equivₓ.refl α) = id :=
  rfl

/-- This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synonym α`, when
`synonym α` is semireducible. This makes a mess of `multiplicative.of_add` etc. -/
theorem Perm.coe_subsingleton {α : Type _} [Subsingleton α] (e : Perm α) : ⇑e = id := by
  rw [perm.subsingleton_eq_refl e, coe_refl]

theorem refl_apply (x : α) : Equivₓ.refl α x = x :=
  rfl

@[simp]
theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : ⇑(f.trans g) = g ∘ f :=
  rfl

theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[simp]
theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x :=
  e.right_inv x

@[simp]
theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x

@[simp]
theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[simp]
theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) : (f.trans g).symm a = f.symm (g.symm a) :=
  rfl

-- The `simp` attribute is needed to make this a `dsimp` lemma.
-- `simp` will always rewrite with `equiv.symm_symm` before this has a chance to fire.
@[simp, nolint simp_nf]
theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b :=
  rfl

theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y :=
  EquivLike.apply_eq_iff_eq f

theorem apply_eq_iff_eq_symm_apply {α β : Sort _} (f : α ≃ β) {x : α} {y : β} : f x = y ↔ x = f.symm y := by
  conv_lhs => rw [← apply_symm_apply f y]
  rw [apply_eq_iff_eq]

@[simp]
theorem cast_apply {α β} (h : α = β) (x : α) : Equivₓ.cast h x = cast h x :=
  rfl

@[simp]
theorem cast_symm {α β} (h : α = β) : (Equivₓ.cast h).symm = Equivₓ.cast h.symm :=
  rfl

@[simp]
theorem cast_refl {α} (h : α = α := rfl) : Equivₓ.cast h = Equivₓ.refl α :=
  rfl

@[simp]
theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
    (Equivₓ.cast h).trans (Equivₓ.cast h2) = Equivₓ.cast (h.trans h2) :=
  ext fun x => by
    substs h h2
    rfl

theorem cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equivₓ.cast h a = b ↔ HEq a b := by
  subst h
  simp

theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
  ⟨fun H => by
    simp [← H.symm], fun H => by
    simp [← H]⟩

theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
  (eq_comm.trans e.symm_apply_eq).trans eq_comm

@[simp]
theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by
  cases e
  rfl

@[simp]
theorem trans_refl (e : α ≃ β) : e.trans (Equivₓ.refl β) = e := by
  cases e
  rfl

@[simp]
theorem refl_symm : (Equivₓ.refl α).symm = Equivₓ.refl α :=
  rfl

@[simp]
theorem refl_trans (e : α ≃ β) : (Equivₓ.refl α).trans e = e := by
  cases e
  rfl

@[simp]
theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equivₓ.refl β :=
  ext
    (by
      simp )

@[simp]
theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equivₓ.refl α :=
  ext
    (by
      simp )

theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) : (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
  Equivₓ.ext fun a => rfl

theorem left_inverse_symm (f : Equivₓ α β) : LeftInverse f.symm f :=
  f.left_inv

theorem right_inverse_symm (f : Equivₓ α β) : Function.RightInverse f.symm f :=
  f.right_inv

theorem injective_comp (e : α ≃ β) (f : β → γ) : Injective (f ∘ e) ↔ Injective f :=
  EquivLike.injective_comp e f

theorem comp_injective (f : α → β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f :=
  EquivLike.comp_injective f e

theorem surjective_comp (e : α ≃ β) (f : β → γ) : Surjective (f ∘ e) ↔ Surjective f :=
  EquivLike.surjective_comp e f

theorem comp_surjective (f : α → β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective f :=
  EquivLike.comp_surjective f e

theorem bijective_comp (e : α ≃ β) (f : β → γ) : Bijective (f ∘ e) ↔ Bijective f :=
  EquivLike.bijective_comp e f

theorem comp_bijective (f : α → β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f :=
  EquivLike.comp_bijective f e

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equivCongr {δ} (ab : α ≃ β) (cd : γ ≃ δ) : α ≃ γ ≃ (β ≃ δ) :=
  ⟨fun ac => (ab.symm.trans ac).trans cd, fun bd => ab.trans <| bd.trans <| cd.symm, fun ac => by
    ext x
    simp , fun ac => by
    ext x
    simp ⟩

@[simp]
theorem equiv_congr_refl {α β} : (Equivₓ.refl α).equivCongr (Equivₓ.refl β) = Equivₓ.refl (α ≃ β) := by
  ext
  rfl

@[simp]
theorem equiv_congr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) : (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm := by
  ext
  rfl

@[simp]
theorem equiv_congr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
    (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef) := by
  ext
  rfl

@[simp]
theorem equiv_congr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) : (Equivₓ.refl α).equivCongr bg e = e.trans bg :=
  rfl

@[simp]
theorem equiv_congr_refl_right {α β} (ab e : α ≃ β) : ab.equivCongr (Equivₓ.refl β) e = ab.symm.trans e :=
  rfl

@[simp]
theorem equiv_congr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
    ab.equivCongr cd e x = cd (e (ab.symm x)) :=
  rfl

section PermCongr

variable {α' β' : Type _} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def permCongr : Perm α' ≃ Perm β' :=
  equivCongr e e

theorem perm_congr_def (p : Equivₓ.Perm α') : e.permCongr p = (e.symm.trans p).trans e :=
  rfl

@[simp]
theorem perm_congr_refl : e.permCongr (Equivₓ.refl _) = Equivₓ.refl _ := by
  simp [← perm_congr_def]

@[simp]
theorem perm_congr_symm : e.permCongr.symm = e.symm.permCongr :=
  rfl

@[simp]
theorem perm_congr_apply (p : Equivₓ.Perm α') (x) : e.permCongr p x = e (p (e.symm x)) :=
  rfl

theorem perm_congr_symm_apply (p : Equivₓ.Perm β') (x) : e.permCongr.symm p x = e.symm (p (e x)) :=
  rfl

theorem perm_congr_trans (p p' : Equivₓ.Perm α') : (e.permCongr p).trans (e.permCongr p') = e.permCongr (p.trans p') :=
  by
  ext
  simp

end PermCongr

/-- Two empty types are equivalent. -/
def equivOfIsEmpty (α β : Sort _) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty :=
  equivOfIsEmpty α _

/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def equivPempty (α : Sort v) [IsEmpty α] : α ≃ Pempty.{u} :=
  equivOfIsEmpty α _

/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.is_empty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun p => rfl⟩

/-- The `Sort` of proofs of a false proposition is equivalent to `pempty`. -/
def propEquivPempty {p : Prop} (h : ¬p) : p ≃ Pempty :=
  @equivPempty p <| IsEmpty.prop_iff.2 h

/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
def equivOfUnique (α β : Sort _) [Unique α] [Unique β] : α ≃ β where
  toFun := default
  invFun := default
  left_inv := fun _ => Subsingleton.elimₓ _ _
  right_inv := fun _ => Subsingleton.elimₓ _ _

/-- If `α` has a unique element, then it is equivalent to any `punit`. -/
def equivPunit (α : Sort _) [Unique α] : α ≃ PUnit.{v} :=
  equivOfUnique α _

/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def propEquivPunit {p : Prop} (h : p) : p ≃ PUnit :=
  @equivPunit p <| uniqueProp h

/-- `ulift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := false }) apply symmApply]
protected def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, fun a => rfl⟩

/-- `plift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := false }) apply symmApply]
protected def plift : Plift α ≃ α :=
  ⟨Plift.down, Plift.up, Plift.up_down, Plift.down_up⟩

/-- `pprod α β` is equivalent to `α × β` -/
@[simps apply symmApply]
def pprodEquivProd {α β : Type _} : PProd α β ≃ α × β where
  toFun := fun x => (x.1, x.2)
  invFun := fun x => ⟨x.1, x.2⟩
  left_inv := fun ⟨x, y⟩ => rfl
  right_inv := fun ⟨x, y⟩ => rfl

/-- Product of two equivalences, in terms of `pprod`. If `α ≃ β` and `γ ≃ δ`, then
`pprod α γ ≃ pprod β δ`. -/
@[congr, simps apply]
def pprodCongr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PProd α γ ≃ PProd β δ where
  toFun := fun x => ⟨e₁ x.1, e₂ x.2⟩
  invFun := fun x => ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := fun ⟨x, y⟩ => by
    simp
  right_inv := fun ⟨x, y⟩ => by
    simp

/-- Combine two equivalences using `pprod` in the domain and `prod` in the codomain. -/
@[simps apply symmApply]
def pprodProd {α₁ β₁ : Sort _} {α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : PProd α₁ β₁ ≃ α₂ × β₂ :=
  (ea.pprodCongr eb).trans pprodEquivProd

/-- Combine two equivalences using `pprod` in the codomain and `prod` in the domain. -/
@[simps apply symmApply]
def prodPprod {α₁ β₁ : Type _} {α₂ β₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ × β₁ ≃ PProd α₂ β₂ :=
  (ea.symm.pprodProd eb.symm).symm

/-- `pprod α β` is equivalent to `plift α × plift β` -/
@[simps apply symmApply]
def pprodEquivProdPlift {α β : Sort _} : PProd α β ≃ Plift α × Plift β :=
  Equivₓ.plift.symm.pprodProd Equivₓ.plift.symm

/-- equivalence of propositions is the same as iff -/
def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q where
  toFun := h.mp
  invFun := h.mpr
  left_inv := fun x => rfl
  right_inv := fun y => rfl

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[congr, simps apply]
def arrowCongr {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) where
  toFun := fun f => e₂ ∘ f ∘ e₁.symm
  invFun := fun f => e₂.symm ∘ f ∘ e₁
  left_inv := fun f =>
    funext fun x => by
      simp
  right_inv := fun f =>
    funext fun x => by
      simp

theorem arrow_congr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ → β₁)
    (g : β₁ → γ₁) : arrowCongr ea ec (g ∘ f) = arrowCongr eb ec g ∘ arrowCongr ea eb f := by
  ext
  simp only [← comp, ← arrow_congr_apply, ← eb.symm_apply_apply]

@[simp]
theorem arrow_congr_refl {α β : Sort _} : arrowCongr (Equivₓ.refl α) (Equivₓ.refl β) = Equivₓ.refl (α → β) :=
  rfl

@[simp]
theorem arrow_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
theorem arrow_congr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- A version of `equiv.arrow_congr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `equiv.arrow_congr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[congr, simps apply]
def arrowCongr' {α₁ β₁ α₂ β₂ : Type _} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equivₓ.arrowCongr hα hβ

@[simp]
theorem arrow_congr'_refl {α β : Type _} : arrowCongr' (Equivₓ.refl α) (Equivₓ.refl β) = Equivₓ.refl (α → β) :=
  rfl

@[simp]
theorem arrow_congr'_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

@[simp]
theorem arrow_congr'_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
@[simps apply]
def conj (e : α ≃ β) : (α → α) ≃ (β → β) :=
  arrowCongr e e

@[simp]
theorem conj_refl : conj (Equivₓ.refl α) = Equivₓ.refl (α → α) :=
  rfl

@[simp]
theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj :=
  rfl

@[simp]
theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : (e₁.trans e₂).conj = e₁.conj.trans e₂.conj :=
  rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := λ x, x`.  This causes nontermination.
theorem conj_comp (e : α ≃ β) (f₁ f₂ : α → α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ := by
  apply arrow_congr_comp

theorem eq_comp_symm {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : f = g ∘ e.symm ↔ f ∘ e = g :=
  (e.arrowCongr (Equivₓ.refl γ)).symm_apply_eq.symm

theorem comp_symm_eq {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : g ∘ e.symm = f ↔ g = f ∘ e :=
  (e.arrowCongr (Equivₓ.refl γ)).eq_symm_apply.symm

theorem eq_symm_comp {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : f = e.symm ∘ g ↔ e ∘ f = g :=
  ((Equivₓ.refl γ).arrowCongr e).eq_symm_apply

theorem symm_comp_eq {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : e.symm ∘ g = f ↔ g = e ∘ f :=
  ((Equivₓ.refl γ).arrowCongr e).symm_apply_eq

section BinaryOp

variable {α₁ β₁ : Type _} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

theorem semiconj_conj (f : α₁ → α₁) : Semiconj e f (e.conj f) := fun x => by
  simp

theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by
  simp

instance [IsAssociative α₁ f] : IsAssociative β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).is_associative_right e.Surjective

instance [IsIdempotent α₁ f] : IsIdempotent β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).is_idempotent_right e.Surjective

instance [IsLeftCancel α₁ f] : IsLeftCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.Surjective.forall₃.2 fun x y z => by
      simpa using @IsLeftCancel.left_cancel _ f _ x y z⟩

instance [IsRightCancel α₁ f] : IsRightCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.Surjective.forall₃.2 fun x y z => by
      simpa using @IsRightCancel.right_cancel _ f _ x y z⟩

end BinaryOp

/-- `punit` sorts in any two universes are equivalent. -/
def punitEquivPunit : PUnit.{v} ≃ PUnit.{w} :=
  ⟨fun _ => PUnit.unit, fun _ => PUnit.unit, fun u => by
    cases u
    rfl, fun u => by
    cases u
    rfl⟩

section

/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrowPunitEquivPunit (α : Sort _) : (α → PUnit.{v}) ≃ PUnit.{w} :=
  ⟨fun f => PUnit.unit, fun u f => PUnit.unit, fun f => by
    funext x
    cases f x
    rfl, fun u => by
    cases u
    rfl⟩

/-- If `α` is `subsingleton` and `a : α`, then the type of dependent functions `Π (i : α), β
i` is equivalent to `β i`. -/
@[simps]
def piSubsingleton {α} (β : α → Sort _) [Subsingleton α] (a : α) : (∀ a', β a') ≃ β a where
  toFun := eval a
  invFun := fun x b => cast (congr_arg β <| Subsingleton.elimₓ a b) x
  left_inv := fun f =>
    funext fun b => by
      rw [Subsingleton.elimₓ b a]
      rfl
  right_inv := fun b => rfl

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (α β) [Unique α] : (α → β) ≃ β :=
  piSubsingleton _ default

/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punitArrowEquiv (α : Sort _) : (PUnit.{u} → α) ≃ α :=
  funUnique _ _

/-- The sort of maps from `true` is equivalent to the codomain. -/
def trueArrowEquiv (α : Sort _) : (True → α) ≃ α :=
  funUnique _ _

/-- The sort of maps from a type that `is_empty` is equivalent to `punit`. -/
def arrowPunitOfIsEmpty (α β : Sort _) [IsEmpty α] : (α → β) ≃ PUnit.{u} :=
  ⟨fun f => PUnit.unit, fun u => isEmptyElim, fun f => funext isEmptyElim, fun u => by
    cases u
    rfl⟩

/-- The sort of maps from `empty` is equivalent to `punit`. -/
def emptyArrowEquivPunit (α : Sort _) : (Empty → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _

/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pemptyArrowEquivPunit (α : Sort _) : (Pempty → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _

/-- The sort of maps from `false` is equivalent to `punit`. -/
def falseArrowEquivPunit (α : Sort _) : (False → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _

end

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. This is
`prod.map` as an equivalence. -/
@[congr, simps apply]
def prodCongr {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by
    simp , fun ⟨a, b⟩ => by
    simp ⟩

@[simp]
theorem prod_congr_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (prodCongr e₁ e₂).symm = prodCongr e₁.symm e₂.symm :=
  rfl

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. This is `prod.swap` as an
equivalence.-/
@[simps apply]
def prodComm (α β : Type _) : α × β ≃ β × α :=
  ⟨Prod.swap, Prod.swap, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

@[simp]
theorem prod_comm_symm (α β) : (prodComm α β).symm = prodComm β α :=
  rfl

/-- Type product is associative up to an equivalence. -/
@[simps]
def prodAssoc (α β γ : Sort _) : (α × β) × γ ≃ α × β × γ :=
  ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨a, b⟩, c⟩ => rfl, fun ⟨a, ⟨b, c⟩⟩ => rfl⟩

/-- Functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps (config := { fullyApplied := false })]
def curry (α β γ : Type _) : (α × β → γ) ≃ (α → β → γ) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

section

/-- `punit` is a right identity for type product up to an equivalence. -/
@[simps]
def prodPunit (α : Type _) : α × PUnit.{u + 1} ≃ α :=
  ⟨fun p => p.1, fun a => (a, PUnit.unit), fun ⟨_, PUnit.unit⟩ => rfl, fun a => rfl⟩

/-- `punit` is a left identity for type product up to an equivalence. -/
@[simps]
def punitProd (α : Type _) : PUnit.{u + 1} × α ≃ α :=
  calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPunit _
    

/-- Any `unique` type is a right identity for type product up to equivalence. -/
def prodUnique (α β : Type _) [Unique β] : α × β ≃ α :=
  ((Equivₓ.refl α).prodCongr <| equivPunit β).trans <| prodPunit α

/-- Any `unique` type is a left identity for type product up to equivalence. -/
def uniqueProd (α β : Type _) [Unique β] : β × α ≃ α :=
  ((equivPunit β).prodCongr <| Equivₓ.refl α).trans <| punitProd α

/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prodEmpty (α : Type _) : α × Empty ≃ Empty :=
  equivEmpty _

/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def emptyProd (α : Type _) : Empty × α ≃ Empty :=
  equivEmpty _

/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prodPempty (α : Type _) : α × Pempty ≃ Pempty :=
  equivPempty _

/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pemptyProd (α : Type _) : Pempty × α ≃ Pempty :=
  equivPempty _

end

section

open Sum

/-- `psum` is equivalent to `sum`. -/
def psumEquivSum (α β : Type _) : PSum α β ≃ Sum α β where
  toFun := fun s => PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv := fun s => by
    cases s <;> rfl
  right_inv := fun s => by
    cases s <;> rfl

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. This is `sum.map` as an equivalence. -/
@[simps apply]
def sumCongr {α₁ β₁ α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : Sum α₁ β₁ ≃ Sum α₂ β₂ :=
  ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by
    simp , fun x => by
    simp ⟩

/-- If `α ≃ α'` and `β ≃ β'`, then `psum α β ≃ psum α' β'`. -/
def psumCongr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PSum α γ ≃ PSum β δ where
  toFun := fun x => PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun := fun x => PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by
    rintro (x | x) <;> simp
  right_inv := by
    rintro (x | x) <;> simp

/-- Combine two `equiv`s using `psum` in the domain and `sum` in the codomain. -/
def psumSum {α₁ β₁ : Sort _} {α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : PSum α₁ β₁ ≃ Sum α₂ β₂ :=
  (ea.psumCongr eb).trans (psumEquivSum _ _)

/-- Combine two `equiv`s using `sum` in the domain and `psum` in the codomain. -/
def sumPsum {α₁ β₁ : Type _} {α₂ β₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : Sum α₁ β₁ ≃ PSum α₂ β₂ :=
  (ea.symm.psumSum eb.symm).symm

@[simp]
theorem sum_congr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort _} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
    (Equivₓ.sumCongr e f).trans (Equivₓ.sumCongr g h) = Equivₓ.sumCongr (e.trans g) (f.trans h) := by
  ext i
  cases i <;> rfl

@[simp]
theorem sum_congr_symm {α β γ δ : Sort _} (e : α ≃ β) (f : γ ≃ δ) :
    (Equivₓ.sumCongr e f).symm = Equivₓ.sumCongr e.symm f.symm :=
  rfl

@[simp]
theorem sum_congr_refl {α β : Sort _} : Equivₓ.sumCongr (Equivₓ.refl α) (Equivₓ.refl β) = Equivₓ.refl (Sum α β) := by
  ext i
  cases i <;> rfl

namespace Perm

/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
@[reducible]
def sumCongr {α β : Type _} (ea : Equivₓ.Perm α) (eb : Equivₓ.Perm β) : Equivₓ.Perm (Sum α β) :=
  Equivₓ.sumCongr ea eb

@[simp]
theorem sum_congr_apply {α β : Type _} (ea : Equivₓ.Perm α) (eb : Equivₓ.Perm β) (x : Sum α β) :
    sumCongr ea eb x = Sum.map (⇑ea) (⇑eb) x :=
  Equivₓ.sum_congr_apply ea eb x

@[simp]
theorem sum_congr_trans {α β : Sort _} (e : Equivₓ.Perm α) (f : Equivₓ.Perm β) (g : Equivₓ.Perm α) (h : Equivₓ.Perm β) :
    (sumCongr e f).trans (sumCongr g h) = sumCongr (e.trans g) (f.trans h) :=
  Equivₓ.sum_congr_trans e f g h

@[simp]
theorem sum_congr_symm {α β : Sort _} (e : Equivₓ.Perm α) (f : Equivₓ.Perm β) :
    (sumCongr e f).symm = sumCongr e.symm f.symm :=
  Equivₓ.sum_congr_symm e f

@[simp]
theorem sum_congr_refl {α β : Sort _} : sumCongr (Equivₓ.refl α) (Equivₓ.refl β) = Equivₓ.refl (Sum α β) :=
  Equivₓ.sum_congr_refl

end Perm

/-- `bool` is equivalent the sum of two `punit`s. -/
def boolEquivPunitSumPunit : Bool ≃ Sum PUnit.{u + 1} PUnit.{v + 1} :=
  ⟨fun b => cond b (inr PUnit.unit) (inl PUnit.unit), fun s => Sum.recOn s (fun _ => false) fun _ => true, fun b => by
    cases b <;> rfl, fun s => by
    rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩

/-- `Prop` is noncomputably equivalent to `bool`. -/
noncomputable def propEquivBool : Prop ≃ Bool :=
  ⟨fun p => @toBool p (Classical.propDecidable _), fun b => b, fun p => by
    simp , fun b => by
    simp ⟩

/-- Sum of types is commutative up to an equivalence. This is `sum.swap` as an equivalence. -/
@[simps (config := { fullyApplied := false }) apply]
def sumComm (α β : Type _) : Sum α β ≃ Sum β α :=
  ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩

@[simp]
theorem sum_comm_symm (α β) : (sumComm α β).symm = sumComm β α :=
  rfl

/-- Sum of types is associative up to an equivalence. -/
def sumAssoc (α β γ : Type _) : Sum (Sum α β) γ ≃ Sum α (Sum β γ) :=
  ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
    Sum.elim (Sum.inl ∘ Sum.inl) <| Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr, by
    rintro (⟨_ | _⟩ | _) <;> rfl, by
    rintro (_ | ⟨_ | _⟩) <;> rfl⟩

@[simp]
theorem sum_assoc_apply_inl_inl {α β γ} (a) : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl

@[simp]
theorem sum_assoc_apply_inl_inr {α β γ} (b) : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl

@[simp]
theorem sum_assoc_apply_inr {α β γ} (c) : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl

@[simp]
theorem sum_assoc_symm_apply_inl {α β γ} (a) : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
theorem sum_assoc_symm_apply_inr_inl {α β γ} (b) : (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
theorem sum_assoc_symm_apply_inr_inr {α β γ} (c) : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/-- Sum with `empty` is equivalent to the original type. -/
@[simps symmApply]
def sumEmpty (α β : Type _) [IsEmpty β] : Sum α β ≃ α :=
  ⟨Sum.elim id isEmptyElim, inl, fun s => by
    rcases s with (_ | x)
    rfl
    exact isEmptyElim x, fun a => rfl⟩

@[simp]
theorem sum_empty_apply_inl {α β : Type _} [IsEmpty β] (a : α) : sumEmpty α β (Sum.inl a) = a :=
  rfl

/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
@[simps symmApply]
def emptySum (α β : Type _) [IsEmpty α] : Sum α β ≃ β :=
  (sumComm _ _).trans <| sumEmpty _ _

@[simp]
theorem empty_sum_apply_inr {α β : Type _} [IsEmpty α] (b : β) : emptySum α β (Sum.inr b) = b :=
  rfl

/-- `option α` is equivalent to `α ⊕ punit` -/
def optionEquivSumPunit (α : Type _) : Option α ≃ Sum α PUnit.{u + 1} :=
  ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none, fun o => by
    cases o <;> rfl, fun s => by
    rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩

@[simp]
theorem option_equiv_sum_punit_none {α} : optionEquivSumPunit α none = Sum.inr PUnit.unit :=
  rfl

@[simp]
theorem option_equiv_sum_punit_some {α} (a) : optionEquivSumPunit α (some a) = Sum.inl a :=
  rfl

@[simp]
theorem option_equiv_sum_punit_coe {α} (a : α) : optionEquivSumPunit α a = Sum.inl a :=
  rfl

@[simp]
theorem option_equiv_sum_punit_symm_inl {α} (a) : (optionEquivSumPunit α).symm (Sum.inl a) = a :=
  rfl

@[simp]
theorem option_equiv_sum_punit_symm_inr {α} (a) : (optionEquivSumPunit α).symm (Sum.inr a) = none :=
  rfl

/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
@[simps]
def optionIsSomeEquiv (α : Type _) : { x : Option α // x.isSome } ≃ α where
  toFun := fun o => Option.getₓ o.2
  invFun := fun x =>
    ⟨some x, by
      decide⟩
  left_inv := fun o => Subtype.eq <| Option.some_getₓ _
  right_inv := fun x => Option.get_some _ _

/-- The product over `option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
def piOptionEquivProd {α : Type _} {β : Option α → Type _} : (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a) where
  toFun := fun f => (f none, fun a => f (some a))
  invFun := fun x a => Option.casesOn a x.fst x.snd
  left_inv := fun f =>
    funext fun a => by
      cases a <;> rfl
  right_inv := fun x => by
    simp

/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot by used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ulift` to work around this
difficulty. -/
def sumEquivSigmaBool (α β : Type u) : Sum α β ≃ Σb : Bool, cond b α β :=
  ⟨fun s => s.elim (fun x => ⟨true, x⟩) fun x => ⟨false, x⟩, fun s =>
    match s with
    | ⟨tt, a⟩ => inl a
    | ⟨ff, b⟩ => inr b,
    fun s => by
    cases s <;> rfl, fun s => by
    rcases s with ⟨_ | _, _⟩ <;> rfl⟩

/-- `sigma_fiber_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
-- See also `equiv.sigma_preimage_equiv`.
@[simps]
def sigmaFiberEquiv {α β : Type _} (f : α → β) : (Σy : β, { x // f x = y }) ≃ α :=
  ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨y, x, rfl⟩ => rfl, fun x => rfl⟩

end

section SumCompl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtype_or_equiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `is_compl p q`.  -/
def sumCompl {α : Type _} (p : α → Prop) [DecidablePred p] : Sum { a // p a } { a // ¬p a } ≃ α where
  toFun := Sum.elim coe coe
  invFun := fun a => if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp' <;> [rw [dif_pos], rw [dif_neg]]
  right_inv := fun a => by
    dsimp'
    split_ifs <;> rfl

@[simp]
theorem sum_compl_apply_inl {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // p a }) :
    sumCompl p (Sum.inl x) = x :=
  rfl

@[simp]
theorem sum_compl_apply_inr {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // ¬p a }) :
    sumCompl p (Sum.inr x) = x :=
  rfl

@[simp]
theorem sum_compl_apply_symm_of_pos {α : Type _} (p : α → Prop) [DecidablePred p] (a : α) (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h

@[simp]
theorem sum_compl_apply_symm_of_neg {α : Type _} (p : α → Prop) [DecidablePred p] (a : α) (h : ¬p a) :
    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
  dif_neg h

/-- Combines an `equiv` between two subtypes with an `equiv` between their complements to form a
  permutation. -/
def subtypeCongr {α : Type _} {p q : α → Prop} [DecidablePred p] [DecidablePred q] (e : { x // p x } ≃ { x // q x })
    (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α :=
  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))

open Equivₓ

variable {ε : Type _} {p : ε → Prop} [DecidablePred p]

variable (ep ep' : Perm { a // p a }) (en en' : Perm { a // ¬p a })

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def Perm.subtypeCongr : Equivₓ.Perm ε :=
  permCongr (sumCompl p) (sumCongr ep en)

theorem Perm.subtypeCongr.apply (a : ε) : ep.subtypeCongr en a = if h : p a then ep ⟨a, h⟩ else en ⟨a, h⟩ := by
  by_cases' h : p a <;> simp [← perm.subtype_congr, ← h]

@[simp]
theorem Perm.subtypeCongr.left_apply {a : ε} (h : p a) : ep.subtypeCongr en a = ep ⟨a, h⟩ := by
  simp [← perm.subtype_congr.apply, ← h]

@[simp]
theorem Perm.subtypeCongr.left_apply_subtype (a : { a // p a }) : ep.subtypeCongr en a = ep a := by
  convert perm.subtype_congr.left_apply _ _ a.property
  simp

@[simp]
theorem Perm.subtypeCongr.right_apply {a : ε} (h : ¬p a) : ep.subtypeCongr en a = en ⟨a, h⟩ := by
  simp [← perm.subtype_congr.apply, ← h]

@[simp]
theorem Perm.subtypeCongr.right_apply_subtype (a : { a // ¬p a }) : ep.subtypeCongr en a = en a := by
  convert perm.subtype_congr.right_apply _ _ a.property
  simp

@[simp]
theorem Perm.subtypeCongr.refl :
    Perm.subtypeCongr (Equivₓ.refl { a // p a }) (Equivₓ.refl { a // ¬p a }) = Equivₓ.refl ε := by
  ext x
  by_cases' h : p x <;> simp [← h]

@[simp]
theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm := by
  ext x
  by_cases' h : p x
  · have : p (ep.symm ⟨x, h⟩) := Subtype.property _
    simp [← perm.subtype_congr.apply, ← h, ← symm_apply_eq, ← this]
    
  · have : ¬p (en.symm ⟨x, h⟩) := Subtype.property (en.symm _)
    simp [← perm.subtype_congr.apply, ← h, ← symm_apply_eq, ← this]
    

@[simp]
theorem Perm.subtypeCongr.trans :
    (ep.subtypeCongr en).trans (ep'.subtypeCongr en') = Perm.subtypeCongr (ep.trans ep') (en.trans en') := by
  ext x
  by_cases' h : p x
  · have : p (ep ⟨x, h⟩) := Subtype.property _
    simp [← perm.subtype_congr.apply, ← h, ← this]
    
  · have : ¬p (en ⟨x, h⟩) := Subtype.property (en _)
    simp [← perm.subtype_congr.apply, ← h, ← symm_apply_eq, ← this]
    

end SumCompl

section SubtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtypePreimage : { x : α → β // x ∘ coe = x₀ } ≃ ({ a // ¬p a } → β) where
  toFun := fun (x : { x : α → β // x ∘ coe = x₀ }) a => (x : α → β) a
  invFun := fun x => ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨a, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.val_injective <|
      funext fun a => by
        dsimp'
        split_ifs <;> [rw [← hx], skip] <;> rfl
  right_inv := fun x =>
    funext fun ⟨a, h⟩ =>
      show dite (p a) _ _ = _ by
        dsimp'
        rw [dif_neg h]

theorem subtype_preimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h

theorem subtype_preimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h

end SubtypePreimage

section

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def piCongrRight {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ ∀ a, β₂ a :=
  ⟨fun H a => F a (H a), fun H a => (F a).symm (H a), fun H =>
    funext <| by
      simp ,
    fun H =>
    funext <| by
      simp ⟩

/-- Given `φ : α → β → Sort*`, we have an equivalence between `Π a b, φ a b` and `Π b a, φ a b`.
This is `function.swap` as an `equiv`. -/
@[simps apply]
def piComm {α β} (φ : α → β → Sort _) : (∀ a b, φ a b) ≃ ∀ b a, φ a b :=
  ⟨swap, swap, fun x => rfl, fun y => rfl⟩

@[simp]
theorem Pi_comm_symm {α β} {φ : α → β → Sort _} : (piComm φ).symm = (Pi_comm <| swap φ) :=
  rfl

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `sigma.curry` and `sigma.uncurry` together as an equiv. -/
def piCurry {α} {β : α → Sort _} (γ : ∀ a, β a → Sort _) : (∀ x : Σi, β i, γ x.1 x.2) ≃ ∀ a b, γ a b where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry

end

section

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symmApply]
def psigmaEquivSigma {α} (β : α → Type _) : (Σ'i, β i) ≃ Σi, β i :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symmApply]
def psigmaEquivSigmaPlift {α} (β : α → Sort _) : (Σ'i, β i) ≃ Σi : Plift α, Plift (β i.down) :=
  ⟨fun a => ⟨Plift.up a.1, Plift.up a.2⟩, fun a => ⟨a.1.down, a.2.down⟩, fun ⟨a, b⟩ => rfl, fun ⟨⟨a⟩, ⟨b⟩⟩ => rfl⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps apply]
def psigmaCongrRight {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ'a, β₁ a) ≃ Σ'a, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩, fun ⟨a, b⟩ =>
    congr_arg (PSigma.mk a) <| symm_apply_apply (F a) b, fun ⟨a, b⟩ =>
    congr_arg (PSigma.mk a) <| apply_symm_apply (F a) b⟩

@[simp]
theorem psigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (psigmaCongrRight F).trans (psigmaCongrRight G) = psigmaCongrRight fun a => (F a).trans (G a) := by
  ext1 x
  cases x
  rfl

@[simp]
theorem psigma_congr_right_symm {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) :
    (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm := by
  ext1 x
  cases x
  rfl

@[simp]
theorem psigma_congr_right_refl {α} {β : α → Sort _} :
    (psigmaCongrRight fun a => Equivₓ.refl (β a)) = Equivₓ.refl (Σ'a, β a) := by
  ext1 x
  cases x
  rfl

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps apply]
def sigmaCongrRight {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σa, β₁ a) ≃ Σa, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩, fun ⟨a, b⟩ =>
    congr_arg (Sigma.mk a) <| symm_apply_apply (F a) b, fun ⟨a, b⟩ =>
    congr_arg (Sigma.mk a) <| apply_symm_apply (F a) b⟩

@[simp]
theorem sigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) := by
  ext1 x
  cases x
  rfl

@[simp]
theorem sigma_congr_right_symm {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm := by
  ext1 x
  cases x
  rfl

@[simp]
theorem sigma_congr_right_refl {α} {β : α → Type _} :
    (sigmaCongrRight fun a => Equivₓ.refl (β a)) = Equivₓ.refl (Σa, β a) := by
  ext1 x
  cases x
  rfl

/-- A `psigma` with `Prop` fibers is equivalent to the subtype.  -/
def psigmaEquivSubtype {α : Type v} (P : α → Prop) : (Σ'i, P i) ≃ Subtype P where
  toFun := fun x => ⟨x.1, x.2⟩
  invFun := fun x => ⟨x.1, x.2⟩
  left_inv := fun x => by
    cases x
    rfl
  right_inv := fun x => by
    cases x
    rfl

/-- A `sigma` with `plift` fibers is equivalent to the subtype. -/
def sigmaPliftEquivSubtype {α : Type v} (P : α → Prop) : (Σi, Plift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans (psigmaCongrRight fun a => Equivₓ.plift)).trans (psigmaEquivSubtype P)

/-- A `sigma` with `λ i, ulift (plift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigma_plift_equiv_subtype`.
-/
def sigmaUliftPliftEquivSubtype {α : Type v} (P : α → Prop) : (Σi, ULift (Plift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun a => Equivₓ.ulift).trans (sigmaPliftEquivSubtype P)

namespace Perm

/-- A family of permutations `Π a, perm (β a)` generates a permuation `perm (Σ a, β₁ a)`. -/
@[reducible]
def sigmaCongrRight {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) : Perm (Σa, β a) :=
  Equivₓ.sigmaCongrRight F

@[simp]
theorem sigma_congr_right_trans {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) (G : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  Equivₓ.sigma_congr_right_trans F G

@[simp]
theorem sigma_congr_right_symm {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  Equivₓ.sigma_congr_right_symm F

@[simp]
theorem sigma_congr_right_refl {α} {β : α → Sort _} :
    (sigmaCongrRight fun a => Equivₓ.refl (β a)) = Equivₓ.refl (Σa, β a) :=
  Equivₓ.sigma_congr_right_refl

end Perm

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps apply]
def sigmaCongrLeft {α₁ α₂} {β : α₂ → Sort _} (e : α₁ ≃ α₂) : (Σa : α₁, β (e a)) ≃ Σa : α₂, β a :=
  ⟨fun a => ⟨e a.1, a.2⟩, fun a => ⟨e.symm a.1, @Eq.ndrec β a.2 (e.right_inv a.1).symm⟩, fun ⟨a, b⟩ =>
    match e.symm (e a), e.left_inv a with
    | _, rfl => rfl,
    fun ⟨a, b⟩ =>
    match e (e.symm a), _ with
    | _, rfl => rfl⟩

/-- Transporting a sigma type through an equivalence of the base -/
def sigmaCongrLeft' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) : (Σa : α₁, β a) ≃ Σa : α₂, β (f.symm a) :=
  (sigmaCongrLeft f.symm).symm

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigmaCongr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂) (F : ∀ a, β₁ a ≃ β₂ (f a)) :
    Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)

/-- `sigma` type with a constant fiber is equivalent to the product. -/
@[simps apply symmApply]
def sigmaEquivProd (α β : Type _) : (Σ_ : α, β) ≃ α × β :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigmaEquivProdOfEquiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)

/-- Dependent product of types is associative up to an equivalence. -/
def sigmaAssoc {α : Type _} {β : α → Type _} (γ : ∀ a : α, β a → Type _) :
    (Σab : Σa : α, β a, γ ab.1 ab.2) ≃ Σa : α, Σb : β a, γ a b where
  toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun ⟨⟨a, b⟩, c⟩ => rfl
  right_inv := fun ⟨a, ⟨b, c⟩⟩ => rfl

end

section ProdCongr

variable {α₁ β₁ β₂ : Type _} (e : α₁ → β₁ ≃ β₂)

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prodCongrLeft : β₁ × α₁ ≃ β₂ × α₁ where
  toFun := fun ab => ⟨e ab.2 ab.1, ab.2⟩
  invFun := fun ab => ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp

@[simp]
theorem prod_congr_left_apply (b : β₁) (a : α₁) : prodCongrLeft e (b, a) = (e a b, a) :=
  rfl

theorem prod_congr_refl_right (e : β₁ ≃ β₂) : prodCongr e (Equivₓ.refl α₁) = prodCongrLeft fun _ => e := by
  ext ⟨a, b⟩ : 1
  simp

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prodCongrRight : α₁ × β₁ ≃ α₁ × β₂ where
  toFun := fun ab => ⟨ab.1, e ab.1 ab.2⟩
  invFun := fun ab => ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp

@[simp]
theorem prod_congr_right_apply (a : α₁) (b : β₁) : prodCongrRight e (a, b) = (a, e a b) :=
  rfl

theorem prod_congr_refl_left (e : β₁ ≃ β₂) : prodCongr (Equivₓ.refl α₁) e = prodCongrRight fun _ => e := by
  ext ⟨a, b⟩ : 1
  simp

@[simp]
theorem prod_congr_left_trans_prod_comm :
    (prodCongrLeft e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp

@[simp]
theorem prod_congr_right_trans_prod_comm :
    (prodCongrRight e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrLeft e) := by
  ext ⟨a, b⟩ : 1
  simp

theorem sigma_congr_right_sigma_equiv_prod :
    (sigmaCongrRight e).trans (sigmaEquivProd α₁ β₂) = (sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp

theorem sigma_equiv_prod_sigma_congr_right :
    (sigmaEquivProd α₁ β₁).symm.trans (sigmaCongrRight e) = (prodCongrRight e).trans (sigmaEquivProd α₁ β₂).symm := by
  ext ⟨a, b⟩ : 1
  simp

/-- A family of equivalences between fibers gives an equivalence between domains. -/
-- See also `equiv.of_preimage_equiv`.
@[simps]
def ofFiberEquiv {α β γ : Type _} {f : α → γ} {g : β → γ} (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
  (sigmaFiberEquiv f).symm.trans <| (Equivₓ.sigmaCongrRight e).trans (sigmaFiberEquiv g)

theorem of_fiber_equiv_map {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) (a : α) :
    g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).Prop

/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps (config := { fullyApplied := false })]
def prodShear {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ where
  toFun := fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by
    rintro ⟨x₁, y₁⟩
    simp only [← symm_apply_apply]
  right_inv := by
    rintro ⟨x₁, y₁⟩
    simp only [← apply_symm_apply]

end ProdCongr

namespace Perm

variable {α₁ β₁ β₂ : Type _} [DecidableEq α₁] (a : α₁) (e : Perm β₁)

/-- `prod_extend_right a e` extends `e : perm β` to `perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prodExtendRight : Perm (α₁ × β₁) where
  toFun := fun ab => if ab.fst = a then (a, e ab.snd) else ab
  invFun := fun ab => if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by
    rintro ⟨k', x⟩
    dsimp' only
    split_ifs with h <;> simp [← h]
  right_inv := by
    rintro ⟨k', x⟩
    dsimp' only
    split_ifs with h <;> simp [← h]

@[simp]
theorem prod_extend_right_apply_eq (b : β₁) : prodExtendRight a e (a, b) = (a, e b) :=
  if_pos rfl

theorem prod_extend_right_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) : prodExtendRight a e (a', b) = (a', b) :=
  if_neg h

theorem eq_of_prod_extend_right_ne {e : Perm β₁} {a a' : α₁} {b : β₁} (h : prodExtendRight a e (a', b) ≠ (a', b)) :
    a' = a := by
  contrapose! h
  exact prod_extend_right_apply_ne _ h _

@[simp]
theorem fst_prod_extend_right (ab : α₁ × β₁) : (prodExtendRight a e ab).fst = ab.fst := by
  rw [prod_extend_right, coe_fn_mk]
  split_ifs with h
  · rw [h]
    
  · rfl
    

end Perm

section

/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrowProdEquivProdArrow (α β γ : Type _) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
  ⟨fun f => (fun c => (f c).1, fun c => (f c).2), fun p c => (p.1 c, p.2 c), fun f => funext fun c => Prod.mk.eta,
    fun p => by
    cases p
    rfl⟩

open Sum

/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sumArrowEquivProdArrow (α β γ : Type _) : (Sum α β → γ) ≃ (α → γ) × (β → γ) :=
  ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by
    ext ⟨⟩ <;> rfl, fun p => by
    cases p
    rfl⟩

@[simp]
theorem sum_arrow_equiv_prod_arrow_apply_fst {α β γ} (f : Sum α β → γ) (a : α) :
    (sumArrowEquivProdArrow α β γ f).1 a = f (inl a) :=
  rfl

@[simp]
theorem sum_arrow_equiv_prod_arrow_apply_snd {α β γ} (f : Sum α β → γ) (b : β) :
    (sumArrowEquivProdArrow α β γ f).2 b = f (inr b) :=
  rfl

@[simp]
theorem sum_arrow_equiv_prod_arrow_symm_apply_inl {α β γ} (f : α → γ) (g : β → γ) (a : α) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inl a) = f a :=
  rfl

@[simp]
theorem sum_arrow_equiv_prod_arrow_symm_apply_inr {α β γ} (f : α → γ) (g : β → γ) (b : β) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inr b) = g b :=
  rfl

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sumProdDistrib (α β γ : Sort _) : Sum α β × γ ≃ Sum (α × γ) (β × γ) :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2), fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
    rintro ⟨_ | _, _⟩ <;> rfl, by
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩

@[simp]
theorem sum_prod_distrib_apply_left {α β γ} (a : α) (c : γ) : sumProdDistrib α β γ (Sum.inl a, c) = Sum.inl (a, c) :=
  rfl

@[simp]
theorem sum_prod_distrib_apply_right {α β γ} (b : β) (c : γ) : sumProdDistrib α β γ (Sum.inr b, c) = Sum.inr (b, c) :=
  rfl

@[simp]
theorem sum_prod_distrib_symm_apply_left {α β γ} (a : α × γ) : (sumProdDistrib α β γ).symm (inl a) = (inl a.1, a.2) :=
  rfl

@[simp]
theorem sum_prod_distrib_symm_apply_right {α β γ} (b : β × γ) : (sumProdDistrib α β γ).symm (inr b) = (inr b.1, b.2) :=
  rfl

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prodSumDistrib (α β γ : Sort _) : α × Sum β γ ≃ Sum (α × β) (α × γ) :=
  calc
    α × Sum β γ ≃ Sum β γ × α := prodComm _ _
    _ ≃ Sum (β × α) (γ × α) := sumProdDistrib _ _ _
    _ ≃ Sum (α × β) (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)
    

@[simp]
theorem prod_sum_distrib_apply_left {α β γ} (a : α) (b : β) : prodSumDistrib α β γ (a, Sum.inl b) = Sum.inl (a, b) :=
  rfl

@[simp]
theorem prod_sum_distrib_apply_right {α β γ} (a : α) (c : γ) : prodSumDistrib α β γ (a, Sum.inr c) = Sum.inr (a, c) :=
  rfl

@[simp]
theorem prod_sum_distrib_symm_apply_left {α β γ} (a : α × β) : (prodSumDistrib α β γ).symm (inl a) = (a.1, inl a.2) :=
  rfl

@[simp]
theorem prod_sum_distrib_symm_apply_right {α β γ} (a : α × γ) : (prodSumDistrib α β γ).symm (inr a) = (a.1, inr a.2) :=
  rfl

/-- An indexed sum of disjoint sums of types is equivalent to the sum of the indexed sums. -/
@[simps]
def sigmaSumDistrib {ι : Type _} (α β : ι → Type _) : (Σi, Sum (α i) (β i)) ≃ Sum (Σi, α i) (Σi, β i) :=
  ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by
    rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩

/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigmaProdDistrib {ι : Type _} (α : ι → Type _) (β : Type _) : (Σi, α i) × β ≃ Σi, α i × β :=
  ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), fun p => by
    rcases p with ⟨⟨_, _⟩, _⟩
    rfl, fun p => by
    rcases p with ⟨_, ⟨_, _⟩⟩
    rfl⟩

/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
def sigmaNatSucc (f : ℕ → Type u) : (Σn, f n) ≃ Sum (f 0) (Σn, f (n + 1)) :=
  ⟨fun x =>
    @Sigma.casesOn ℕ f (fun _ => Sum (f 0) (Σn, f (n + 1))) x fun n =>
      @Nat.casesOn (fun i => f i → Sum (f 0) (Σn : ℕ, f (n + 1))) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by
    rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩

/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
def boolProdEquivSum (α : Type u) : Bool × α ≃ Sum α α :=
  calc
    Bool × α ≃ Sum Unit Unit × α := prodCongr boolEquivPunitSumPunit (Equivₓ.refl _)
    _ ≃ Sum (Unit × α) (Unit × α) := sumProdDistrib _ _ _
    _ ≃ Sum α α := sumCongr (punitProd _) (punitProd _)
    

/-- The function type `bool → α` is equivalent to `α × α`. -/
@[simps]
def boolArrowEquivProd (α : Type u) : (Bool → α) ≃ α × α where
  toFun := fun f => (f true, f false)
  invFun := fun p b => cond b p.1 p.2
  left_inv := fun f => funext <| Bool.forall_bool.2 ⟨rfl, rfl⟩
  right_inv := fun ⟨x, y⟩ => rfl

end

section

open Sum Nat

/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def natEquivNatSumPunit : ℕ ≃ Sum ℕ PUnit.{u + 1} :=
  ⟨fun n =>
    match n with
    | zero => inr PUnit.unit
    | succ a => inl a,
    fun s =>
    match s with
    | inl n => succ n
    | inr PUnit.unit => zero,
    fun n => by
    cases n
    repeat'
      rfl,
    fun s => by
    cases' s with a u
    · rfl
      
    · cases u
      · rfl
        
      ⟩

/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def natSumPunitEquivNat : Sum ℕ PUnit.{u + 1} ≃ ℕ :=
  natEquivNatSumPunit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ Sum ℕ ℕ := by
  refine' ⟨_, _, _, _⟩ <;>
    intro z <;>
      first |
        · cases z <;> [left, right] <;> assumption
          |
        · cases z <;> rfl
          

end

/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def listEquivOfEquiv {α β : Type _} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv := fun l => by
    rw [List.map_mapₓ, e.symm_comp_self, List.map_id]
  right_inv := fun l => by
    rw [List.map_mapₓ, e.self_comp_symm, List.map_id]

/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `unique β`. -/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where
  toFun := fun h => @Equivₓ.unique _ _ h e.symm
  invFun := fun h => @Equivₓ.unique _ _ h e
  left_inv := fun _ => Subsingleton.elimₓ _ _
  right_inv := fun _ => Subsingleton.elimₓ _ _

/-- If `α` is equivalent to `β`, then `is_empty α` is equivalent to `is_empty β`. -/
theorem is_empty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.is_empty _ _ h e.symm, fun h => @Function.is_empty _ _ h e⟩

protected theorem is_empty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.is_empty_congr.mpr ‹_›

section

open Subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `perm.subtype_perm`. -/
def subtypeEquiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ { b : β // q b } where
  toFun := fun a => ⟨e a, (h _).mp a.Prop⟩
  invFun := fun b => ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.Prop)⟩
  left_inv := fun a =>
    Subtype.ext <| by
      simp
  right_inv := fun b =>
    Subtype.ext <| by
      simp

@[simp]
theorem subtype_equiv_refl {p : α → Prop} (h : ∀ a, p a ↔ p (Equivₓ.refl _ a) := fun a => Iff.rfl) :
    (Equivₓ.refl α).subtypeEquiv h = Equivₓ.refl { a : α // p a } := by
  ext
  rfl

@[simp]
theorem subtype_equiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) :
    (e.subtypeEquiv h).symm =
      e.symm.subtypeEquiv fun a => by
        convert (h <| e.symm a).symm
        exact (e.apply_symm_apply a).symm :=
  rfl

@[simp]
theorem subtype_equiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : ∀ a : α, p a ↔ q (e a)) (h' : ∀ b : β, q b ↔ r (f b)) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h') = (e.trans f).subtypeEquiv fun a => (h a).trans (h' <| e a) :=
  rfl

@[simp]
theorem subtype_equiv_apply {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) (x : { x // p x }) :
    e.subtypeEquiv h x = ⟨e x, (h _).1 x.2⟩ :=
  rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps]
def subtypeEquivRight {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equivₓ.refl _) e

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtypeEquivOfSubtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtypeEquiv e <| by
    simp

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtypeEquivOfSubtype' {p : α → Prop} (e : α ≃ β) : { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtypeEquivProp {α : Type _} {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equivₓ.refl α) fun a => h ▸ Iff.rfl

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
def subtypeSubtypeEquivSubtypeExists {α : Type u} (p : α → Prop) (q : Subtype p → Prop) :
    Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨a, ha⟩, h⟩ => rfl, fun ⟨a, h₁, h₂⟩ => rfl⟩

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps]
def subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α → Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtypeSubtypeEquivSubtypeExists p _).trans <| subtype_equiv_right fun x => exists_prop

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps]
def subtypeSubtypeEquivSubtype {α : Type u} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtypeSubtypeEquivSubtypeInter p _).trans <| subtype_equiv_right fun x => and_iff_right_of_imp h

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symmApply]
def subtypeUnivEquiv {α : Type u} {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun x => Subtype.eq rfl, fun x => rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtypeSigmaEquiv {α : Type u} (p : α → Type v) (q : α → Prop) : { y : Sigma p // q y.1 } ≃ Σx : Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun ⟨⟨x, h⟩, y⟩ => rfl, fun ⟨⟨x, y⟩, h⟩ => rfl⟩

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigmaSubtypeEquivOfSubset {α : Type u} (p : α → Type v) (q : α → Prop) (h : ∀ x, p x → q x) :
    (Σx : Subtype q, p x) ≃ Σx : α, p x :=
  (subtypeSigmaEquiv p q).symm.trans <| subtype_univ_equiv fun x => h x.1 x.2

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigmaSubtypeFiberEquiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
    (Σy : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σy : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun y ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f
    

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigmaSubtypeFiberEquivSubtype {α : Type u} {β : Type v} (f : α → β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (f x)) : (Σy : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σy : Subtype q, { x : α // f x = y }) ≃ Σy : Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } :=
      by
      apply sigma_congr_right
      intro y
      symm
      refine' (subtype_subtype_equiv_subtype_exists _ _).trans (subtype_equiv_right _)
      intro x
      exact ⟨fun ⟨hp, h'⟩ => congr_arg Subtype.val h', fun h' => ⟨(h x).2 (h'.symm ▸ y.2), Subtype.eq h'⟩⟩
    _ ≃ Subtype p := sigmaFiberEquiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)
    

/-- A sigma type over an `option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigmaOptionEquivOfSome {α : Type u} (p : Option α → Type v) (h : p none → False) :
    (Σx : Option α, p x) ≃ Σx : α, p (some x) := by
  have h' : ∀ x, p x → x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n
      
    · intro s
      exact rfl
      
  exact (sigma_subtype_equiv_of_subset _ _ h').symm.trans (sigma_congr_left' (option_is_some_equiv α))

/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def piEquivSubtypeSigma (ι : Type _) (π : ι → Type _) : (∀ i, π i) ≃ { f : ι → Σi, π i // ∀ i, (f i).1 = i } :=
  ⟨fun f => ⟨fun i => ⟨i, f i⟩, fun i => rfl⟩, fun f i => by
    rw [← f.2 i]
    exact (f.1 i).2, fun f => funext fun i => rfl, fun ⟨f, hf⟩ =>
    Subtype.eq <|
      funext fun i => Sigma.eq (hf i).symm <| eq_of_heq <| rec_heq_of_heq _ <| rec_heq_of_heq _ <| HEq.refl _⟩

/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtypePiEquivPi {α : Sort u} {β : α → Sort v} {p : ∀ a, β a → Prop} :
    { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } :=
  ⟨fun f a => ⟨f.1 a, f.2 a⟩, fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩, by
    rintro ⟨f, h⟩
    rfl, by
    rintro f
    funext a
    exact Subtype.ext_val rfl⟩

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtypeProdEquivProd {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} :
    { c : α × β // p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } :=
  ⟨fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩, fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl,
    fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl⟩

/-- A subtype of a `prod` is equivalent to a sigma type whose fibers are subtypes. -/
def subtypeProdEquivSigmaSubtype {α β : Type _} (p : α → β → Prop) :
    { x : α × β // p x.1 x.2 } ≃ Σa, { b : β // p a b } where
  toFun := fun x => ⟨x.1.1, x.1.2, x.Prop⟩
  invFun := fun x => ⟨⟨x.1, x.2⟩, x.2.Prop⟩
  left_inv := fun x => by
    ext <;> rfl
  right_inv := fun ⟨a, b, pab⟩ => rfl

/-- The type `Π (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps]
def piEquivPiSubtypeProd {α : Type _} (p : α → Prop) (β : α → Type _) [DecidablePred p] :
    (∀ i : α, β i) ≃ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i where
  toFun := fun f => (fun x => f x, fun x => f x)
  invFun := fun f x => if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    ext1 <;>
      · ext y
        rcases y with ⟨⟩
        simp only [← y_property, ← dif_pos, ← dif_neg, ← not_false_iff, ← Subtype.coe_mk]
        rfl
        
  left_inv := fun f => by
    ext x
    by_cases' h : p x <;>
      · simp only [← h, ← dif_neg, ← dif_pos, ← not_false_iff]
        rfl
        

end

section SubtypeEquivCodomain

variable {X : Type _} {Y : Type _} [DecidableEq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) : { g : X → Y // g ∘ coe = f } ≃ Y :=
  (subtypePreimage _ f).trans <|
    @funUnique { x' // ¬x' ≠ x } _ <|
      show Unique { x' // ¬x' ≠ x } from
        @Equivₓ.unique _ _
          (show Unique { x' // x' = x } from { default := ⟨x, rfl⟩, uniq := fun ⟨x', h⟩ => Subtype.val_injective h })
          (subtype_equiv_right fun a => not_not)

@[simp]
theorem coe_subtype_equiv_codomain (f : { x' // x' ≠ x } → Y) :
    (subtypeEquivCodomain f : { g : X → Y // g ∘ coe = f } → Y) = fun g => (g : X → Y) x :=
  rfl

@[simp]
theorem subtype_equiv_codomain_apply (f : { x' // x' ≠ x } → Y) (g : { g : X → Y // g ∘ coe = f }) :
    subtypeEquivCodomain f g = (g : X → Y) x :=
  rfl

theorem coe_subtype_equiv_codomain_symm (f : { x' // x' ≠ x } → Y) :
    ((subtypeEquivCodomain f).symm : Y → { g : X → Y // g ∘ coe = f }) = fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y, by
        funext x'
        dsimp'
        erw [dif_pos x'.2, Subtype.coe_eta]⟩ :=
  rfl

@[simp]
theorem subtype_equiv_codomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl

@[simp]
theorem subtype_equiv_codomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)

theorem subtype_equiv_codomain_symm_apply_ne (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) (h : x' ≠ x) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h

end SubtypeEquivCodomain

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := Function.surjInv hf.Surjective
  left_inv := Function.left_inverse_surj_inv hf
  right_inv := Function.right_inverse_surj_inv _

theorem of_bijective_apply_symm_apply (f : α → β) (hf : Bijective f) (x : β) : f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
theorem of_bijective_symm_apply_apply (f : α → β) (hf : Bijective f) (x : α) : (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

instance : CanLift (α → β) (α ≃ β) where
  coe := coeFn
  cond := Bijective
  prf := fun f hf => ⟨ofBijective f hf, rfl⟩

section

variable {α' β' : Type _} (e : Perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/-- Extend the domain of `e : equiv.perm α` to one that is over `β` via `f : α → subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `set.range f` fixed. For this use-case `equiv` given by `f` can
be constructed by `equiv.of_left_inverse'` or `equiv.of_left_inverse` when there is a known
inverse, or `equiv.of_injective` in the general case.`.
-/
def Perm.extendDomain : Perm β' :=
  (permCongr f e).subtypeCongr (Equivₓ.refl _)

@[simp]
theorem Perm.extend_domain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by
  simp [← perm.extend_domain]

theorem Perm.extend_domain_apply_subtype {b : β'} (h : p b) : e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by
  simp [← perm.extend_domain, ← h]

theorem Perm.extend_domain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [← perm.extend_domain, ← h]

@[simp]
theorem Perm.extend_domain_refl : Perm.extendDomain (Equivₓ.refl _) f = Equivₓ.refl _ := by
  simp [← perm.extend_domain]

@[simp]
theorem Perm.extend_domain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl

theorem Perm.extend_domain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [← perm.extend_domain, ← perm_congr_trans]

end

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtypeQuotientEquivQuotientSubtype (p₁ : α → Prop) [s₁ : Setoidₓ α] [s₂ : Setoidₓ (Subtype p₁)]
    (p₂ : Quotientₓ s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧) (h : ∀ x y : Subtype p₁, @Setoidₓ.R _ s₂ x y ↔ (x : α) ≈ y) :
    { x // p₂ x } ≃ Quotientₓ s₂ where
  toFun := fun a =>
    Quotientₓ.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab =>
        hfunext
          (by
            rw [Quotientₓ.sound hab])
          fun h₁ h₂ _ => heq_of_eq (Quotientₓ.sound ((h _ _).2 hab)))
      a.2
  invFun := fun a =>
    Quotientₓ.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun a b hab =>
      Subtype.ext_val (Quotientₓ.sound ((h _ _).1 hab))
  left_inv := fun ⟨a, ha⟩ => Quotientₓ.induction_on a (fun a ha => rfl) ha
  right_inv := fun a => Quotientₓ.induction_on a fun ⟨a, ha⟩ => rfl

@[simp]
theorem subtype_quotient_equiv_quotient_subtype_mk (p₁ : α → Prop) [s₁ : Setoidₓ α] [s₂ : Setoidₓ (Subtype p₁)]
    (p₂ : Quotientₓ s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧) (h : ∀ x y : Subtype p₁, @Setoidₓ.R _ s₂ x y ↔ (x : α) ≈ y)
    (x hx) : subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl

@[simp]
theorem subtype_quotient_equiv_quotient_subtype_symm_mk (p₁ : α → Prop) [s₁ : Setoidₓ α] [s₂ : Setoidₓ (Subtype p₁)]
    (p₂ : Quotientₓ s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧) (h : ∀ x y : Subtype p₁, @Setoidₓ.R _ s₂ x y ↔ (x : α) ≈ y)
    (x) : (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.Prop⟩ :=
  rfl

section Swap

variable [DecidableEq α]

/-- A helper function for `equiv.swap`. -/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r

theorem swap_core_self (r a : α) : swapCore a a r = r := by
  unfold swap_core
  split_ifs <;> cc

theorem swap_core_swap_core (r a b : α) : swapCore a b (swapCore a b r) = r := by
  unfold swap_core
  split_ifs <;> cc

theorem swap_core_comm (r a b : α) : swapCore a b r = swapCore b a r := by
  unfold swap_core
  split_ifs <;> cc

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swap_core_swap_core r a b, fun r => swap_core_swap_core r a b⟩

@[simp]
theorem swap_self (a : α) : swap a a = Equivₓ.refl _ :=
  ext fun r => swap_core_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swap_core_comm r _ _

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl

@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl

@[simp]
theorem swap_apply_right (a b : α) : swap a b b = a := by
  by_cases' h : b = a <;> simp [← swap_apply_def, ← h]

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x := by
  simp (config := { contextual := true })[← swap_apply_def]

@[simp]
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equivₓ.refl _ :=
  ext fun x => swap_core_swap_core _ _ _

@[simp]
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl

@[simp]
theorem swap_eq_refl_iff {x y : α} : swap x y = Equivₓ.refl _ ↔ x = y := by
  refine' ⟨fun h => (Equivₓ.refl _).Injective _, fun h => h ▸ swap_self _⟩
  rw [← h, swap_apply_left, h, refl_apply]

theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x := by
  cases π
  rfl

theorem swap_eq_update (i j : α) : (Equivₓ.swap i j : α → α) = update (update id j i) i j :=
  funext fun x => by
    rw [update_apply _ i j, update_apply _ j i, Equivₓ.swap_apply_def, id.def]

theorem comp_swap_eq_update (i j : α) (f : α → β) : f ∘ Equivₓ.swap i j = update (update f j (f i)) i (f j) := by
  rw [swap_eq_update, comp_update, comp_update, comp.right_id]

@[simp]
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
  Equivₓ.ext fun x => by
    have : ∀ a, e.symm x = a ↔ x = e a := fun a => by
      rw [@eq_comm _ (e.symm x)]
      constructor <;> intros <;> simp_all
    simp [← swap_apply_def, ← this]
    split_ifs <;> simp

@[simp]
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm

@[simp]
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  rw [← Equivₓ.trans_apply, Equivₓ.swap_swap, Equivₓ.refl_apply]

/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) : v (swap i j k) = v k := by
  by_cases' hi : k = i
  · rw [hi, swap_apply_left, hv]
    
  by_cases' hj : k = j
  · rw [hj, swap_apply_right, hv]
    
  rw [swap_apply_of_ne_of_ne hi hj]

theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  rw [apply_eq_iff_eq_symm_apply, symm_swap]

theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) := by
  by_cases' hab : a = b
  · simp [← hab]
    
  by_cases' hax : x = a
  · simp [← hax, ← eq_comm]
    
  by_cases' hbx : x = b
  · simp [← hbx]
    
  simp [← hab, ← hax, ← hbx, ← swap_apply_of_ne_of_ne]

namespace Perm

@[simp]
theorem sum_congr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equivₓ.Perm.sumCongr (Equivₓ.swap i j) (Equivₓ.refl β) = Equivₓ.swap (Sum.inl i) (Sum.inl j) := by
  ext x
  cases x
  · simp [← Sum.map, ← swap_apply_def]
    split_ifs <;> rfl
    
  · simp [← Sum.map, ← swap_apply_of_ne_of_ne]
    

@[simp]
theorem sum_congr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equivₓ.Perm.sumCongr (Equivₓ.refl α) (Equivₓ.swap i j) = Equivₓ.swap (Sum.inr i) (Sum.inr j) := by
  ext x
  cases x
  · simp [← Sum.map, ← swap_apply_of_ne_of_ne]
    
  · simp [← Sum.map, ← swap_apply_def]
    split_ifs <;> rfl
    

end Perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f

@[simp]
theorem set_value_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b := by
  dsimp' [← set_value]
  simp [← swap_apply_left]

end Swap

end Equivₓ

namespace Function.Involutive

/-- Convert an involutive function `f` to a permutation with `to_fun = inv_fun = f`. -/
def toPerm (f : α → α) (h : Involutive f) : Equivₓ.Perm α :=
  ⟨f, f, h.LeftInverse, h.RightInverse⟩

@[simp]
theorem coe_to_perm {f : α → α} (h : Involutive f) : (h.toPerm f : α → α) = f :=
  rfl

@[simp]
theorem to_perm_symm {f : α → α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl

theorem to_perm_involutive {f : α → α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h

end Function.Involutive

theorem Plift.eq_up_iff_down_eq {x : Plift α} {y : α} : x = Plift.up y ↔ x.down = y :=
  Equivₓ.plift.eq_symm_apply

theorem Function.Injective.map_swap {α β : Type _} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) : f (Equivₓ.swap x y z) = Equivₓ.swap (f x) (f y) (f z) := by
  conv_rhs => rw [Equivₓ.swap_apply_def]
  split_ifs with h₁ h₂
  · rw [hf h₁, Equivₓ.swap_apply_left]
    
  · rw [hf h₂, Equivₓ.swap_apply_right]
    
  · rw [Equivₓ.swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)]
    

namespace Equivₓ

protected theorem exists_unique_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p x ↔ q (f x)) :
    (∃! x, p x) ↔ ∃! y, q y := by
  constructor
  · rintro ⟨a, ha₁, ha₂⟩
    exact
      ⟨f a, h.1 ha₁, fun b hb =>
        f.symm_apply_eq.1
          (ha₂ (f.symm b)
            (h.2
              (by
                simpa using hb)))⟩
    
  · rintro ⟨b, hb₁, hb₂⟩
    exact
      ⟨f.symm b,
        h.2
          (by
            simpa using hb₁),
        fun y hy => (eq_symm_apply f).2 (hb₂ _ (h.1 hy))⟩
    

protected theorem exists_unique_congr_left' {p : α → Prop} (f : α ≃ β) : (∃! x, p x) ↔ ∃! y, p (f.symm y) :=
  Equivₓ.exists_unique_congr f fun x => by
    simp

protected theorem exists_unique_congr_left {p : β → Prop} (f : α ≃ β) : (∃! x, p (f x)) ↔ ∃! y, p y :=
  (Equivₓ.exists_unique_congr_left' f.symm).symm

protected theorem forall_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p x ↔ q (f x)) :
    (∀ x, p x) ↔ ∀ y, q y := by
  constructor <;> intro h₂ x
  · rw [← f.right_inv x]
    apply h.mp
    apply h₂
    
  apply h.mpr
  apply h₂

protected theorem forall_congr' {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p (f.symm x) ↔ q x) :
    (∀ x, p x) ↔ ∀ y, q y :=
  (Equivₓ.forall_congr f.symm fun x => h.symm).symm

-- We next build some higher arity versions of `equiv.forall_congr`.
-- Although they appear to just be repeated applications of `equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)
universe ua1 ua2 ub1 ub2 ug1 ug2

variable {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {γ₁ : Sort ug1} {γ₂ : Sort ug2}

protected theorem forall₂_congr {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (h : ∀ {x y}, p x y ↔ q (eα x) (eβ y)) : (∀ x y, p x y) ↔ ∀ x y, q x y := by
  apply Equivₓ.forall_congr
  intros
  apply Equivₓ.forall_congr
  intros
  apply h

protected theorem forall₂_congr' {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (h : ∀ {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) : (∀ x y, p x y) ↔ ∀ x y, q x y :=
  (Equivₓ.forall₂_congr eα.symm eβ.symm fun x y => h.symm).symm

protected theorem forall₃_congr {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) : (∀ x y z, p x y z) ↔ ∀ x y z, q x y z := by
  apply Equivₓ.forall₂_congr
  intros
  apply Equivₓ.forall_congr
  intros
  apply h

protected theorem forall₃_congr' {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  (Equivₓ.forall₃_congr eα.symm eβ.symm eγ.symm fun x y z => h.symm).symm

protected theorem forall_congr_left' {p : α → Prop} (f : α ≃ β) : (∀ x, p x) ↔ ∀ y, p (f.symm y) :=
  Equivₓ.forall_congr f fun x => by
    simp

protected theorem forall_congr_left {p : β → Prop} (f : α ≃ β) : (∀ x, p (f x)) ↔ ∀ y, p y :=
  (Equivₓ.forall_congr_left' f.symm).symm

protected theorem exists_congr_left {α β} (f : α ≃ β) {p : α → Prop} : (∃ a, p a) ↔ ∃ b, p (f.symm b) :=
  ⟨fun ⟨a, h⟩ =>
    ⟨f a, by
      simpa using h⟩,
    fun ⟨b, h⟩ => ⟨_, h⟩⟩

section

variable (P : α → Sort w) (e : α ≃ β)

/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps]
def piCongrLeft' : (∀ a, P a) ≃ ∀ b, P (e.symm b) where
  toFun := fun f x => f (e.symm x)
  invFun := fun f x => by
    rw [← e.symm_apply_apply x]
    exact f (e x)
  left_inv := fun f =>
    funext fun x =>
      eq_of_heq
        ((eq_rec_heq _ _).trans
          (by
            dsimp'
            rw [e.symm_apply_apply]))
  right_inv := fun f =>
    funext fun x =>
      eq_of_heq
        ((eq_rec_heq _ _).trans
          (by
            rw [e.apply_symm_apply]))

end

section

variable (P : β → Sort w) (e : α ≃ β)

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def piCongrLeft : (∀ a, P (e a)) ≃ ∀ b, P b :=
  (piCongrLeft' P e.symm).symm

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ a : α, W a ≃ Z (h₁ a))

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def piCongr : (∀ a, W a) ≃ ∀ b, Z b :=
  (Equivₓ.piCongrRight h₂).trans (Equivₓ.piCongrLeft _ h₁)

@[simp]
theorem coe_Pi_congr_symm : ((h₁.piCongr h₂).symm : (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl

theorem Pi_congr_symm_apply (f : ∀ b, Z b) : (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp]
theorem Pi_congr_apply_apply (f : ∀ a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) := by
  change cast _ ((h₂ (h₁.symm (h₁ a))) (f (h₁.symm (h₁ a)))) = (h₂ a) (f a)
  generalize_proofs hZa
  revert hZa
  rw [h₁.symm_apply_apply a]
  simp

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ b : β, W (h₁.symm b) ≃ Z b)

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def piCongr' : (∀ a, W a) ≃ ∀ b, Z b :=
  (piCongr h₁.symm fun b => (h₂ b).symm).symm

@[simp]
theorem coe_Pi_congr' : (h₁.piCongr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b <| f <| h₁.symm b :=
  rfl

theorem Pi_congr'_apply (f : ∀ a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b <| f <| h₁.symm b :=
  rfl

@[simp]
theorem Pi_congr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) := by
  change cast _ ((h₂ (h₁ (h₁.symm b))).symm (f (h₁ (h₁.symm b)))) = (h₂ b).symm (f b)
  generalize_proofs hWb
  revert hWb
  generalize hb : h₁ (h₁.symm b) = b'
  rw [h₁.apply_symm_apply b] at hb
  subst hb
  simp

end

end Equivₓ

theorem Function.Injective.swap_apply [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (x y z : α) : Equivₓ.swap (f x) (f y) (f z) = f (Equivₓ.swap x y z) := by
  by_cases' hx : z = x
  · simp [← hx]
    
  by_cases' hy : z = y
  · simp [← hy]
    
  rw [Equivₓ.swap_apply_of_ne_of_ne hx hy, Equivₓ.swap_apply_of_ne_of_ne (hf.ne hx) (hf.ne hy)]

theorem Function.Injective.swap_comp [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y : α) :
    Equivₓ.swap (f x) (f y) ∘ f = f ∘ Equivₓ.swap x y :=
  funext fun z => hf.swap_apply _ _ _

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingletonProdSelfEquiv {α : Type _} [Subsingleton α] : α × α ≃ α where
  toFun := fun p => p.1
  invFun := fun a => (a, a)
  left_inv := fun p => Subsingleton.elimₓ _ _
  right_inv := fun p => Subsingleton.elimₓ _ _

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) : α ≃ β where
  toFun := f
  invFun := g
  left_inv := fun _ => Subsingleton.elimₓ _ _
  right_inv := fun _ => Subsingleton.elimₓ _ _

/-- A nonempty subsingleton type is (noncomputably) equivalent to `punit`. -/
noncomputable def Equivₓ.punitOfNonemptyOfSubsingleton {α : Sort _} [h : Nonempty α] [Subsingleton α] : α ≃ PUnit.{v} :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

/-- `unique (unique α)` is equivalent to `unique α`. -/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elimₓ _ _ }

namespace Quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β) (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    Quot ra ≃ Quot rb where
  toFun := Quot.map e fun a₁ a₂ => (Eq a₁ a₂).1
  invFun :=
    Quot.map e.symm fun b₁ b₂ h =>
      (Eq (e.symm b₁) (e.symm b₂)).2 ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by
    rintro ⟨a⟩
    dunfold Quot.map
    simp only [← Equivₓ.symm_apply_apply]
  right_inv := by
    rintro ⟨a⟩
    dunfold Quot.map
    simp only [← Equivₓ.apply_symm_apply]

@[simp]
theorem congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β) (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂))
    (a : α) : Quot.congr e Eq (Quot.mk ra a) = Quot.mk rb (e a) :=
  rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quot r ≃ Quot r' :=
  Quot.congr (Equivₓ.refl α) Eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congrLeft {r : α → α → Prop} (e : α ≃ β) : Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  @Quot.congr α β r (fun b b' => r (e.symm b) (e.symm b')) e fun a₁ a₂ => by
    simp only [← e.symm_apply_apply]

end Quot

namespace Quotientₓ

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : Setoidₓ α} {rb : Setoidₓ β} (e : α ≃ β)
    (eq : ∀ a₁ a₂, @Setoidₓ.R α ra a₁ a₂ ↔ @Setoidₓ.R β rb (e a₁) (e a₂)) : Quotientₓ ra ≃ Quotientₓ rb :=
  Quot.congr e Eq

@[simp]
theorem congr_mk {ra : Setoidₓ α} {rb : Setoidₓ β} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, Setoidₓ.R a₁ a₂ ↔ Setoidₓ.R (e a₁) (e a₂)) (a : α) :
    Quotientₓ.congr e Eq (Quotientₓ.mk a) = Quotientₓ.mk (e a) :=
  rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : Setoidₓ α} (eq : ∀ a₁ a₂, @Setoidₓ.R α r a₁ a₂ ↔ @Setoidₓ.R α r' a₁ a₂) :
    Quotientₓ r ≃ Quotientₓ r' :=
  Quot.congrRight Eq

end Quotientₓ

namespace Function

theorem update_comp_equiv {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α) (v : β) :
    update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]

theorem update_apply_equiv_apply {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α)
    (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'

theorem Pi_congr_left'_update [DecidableEq α] [DecidableEq β] (P : α → Sort _) (e : α ≃ β) (f : ∀ a, P a) (b : β)
    (x : P (e.symm b)) : e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x := by
  ext b'
  rcases eq_or_ne b' b with (rfl | h)
  · simp
    
  · simp [← h]
    

theorem Pi_congr_left'_symm_update [DecidableEq α] [DecidableEq β] (P : α → Sort _) (e : α ≃ β) (f : ∀ b, P (e.symm b))
    (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [← (e.Pi_congr_left' P).symm_apply_eq, ← Pi_congr_left'_update]

end Function

