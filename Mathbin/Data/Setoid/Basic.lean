/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/
import Mathbin.Logic.Relation
import Mathbin.Order.GaloisConnection

/-!
# Equivalence relations

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The function `rel` and lemmas ending in ' make it easier to talk about different
equivalence relations on the same type.

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`complete_lattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `filter.complete_lattice` in
`order/filter/basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/


variable {α : Type _} {β : Type _}

/-- A version of `setoid.r` that takes the equivalence relation as an explicit argument. -/
def Setoidₓ.Rel (r : Setoidₓ α) : α → α → Prop :=
  @Setoidₓ.R _ r

instance Setoidₓ.decidableRel (r : Setoidₓ α) [h : DecidableRel r.R] : DecidableRel r.Rel :=
  h

/-- A version of `quotient.eq'` compatible with `setoid.rel`, to make rewriting possible. -/
theorem Quotientₓ.eq_rel {r : Setoidₓ α} {x y} : (Quotientₓ.mk' x : Quotientₓ r) = Quotientₓ.mk' y ↔ r.Rel x y :=
  Quotientₓ.eq

namespace Setoidₓ

@[ext]
theorem ext' {r s : Setoidₓ α} (H : ∀ a b, r.Rel a b ↔ s.Rel a b) : r = s :=
  ext H

theorem ext_iff {r s : Setoidₓ α} : r = s ↔ ∀ a b, r.Rel a b ↔ s.Rel a b :=
  ⟨fun h a b => h ▸ Iff.rfl, ext'⟩

/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
theorem eq_iff_rel_eq {r₁ r₂ : Setoidₓ α} : r₁ = r₂ ↔ r₁.Rel = r₂.Rel :=
  ⟨fun h => h ▸ rfl, fun h => Setoidₓ.ext' fun x y => h ▸ Iff.rfl⟩

/-- Defining `≤` for equivalence relations. -/
instance : LE (Setoidₓ α) :=
  ⟨fun r s => ∀ ⦃x y⦄, r.Rel x y → s.Rel x y⟩

theorem le_def {r s : Setoidₓ α} : r ≤ s ↔ ∀ {x y}, r.Rel x y → s.Rel x y :=
  Iff.rfl

@[refl]
theorem refl' (r : Setoidₓ α) (x) : r.Rel x x :=
  r.2.1 x

@[symm]
theorem symm' (r : Setoidₓ α) : ∀ {x y}, r.Rel x y → r.Rel y x := fun _ _ h => r.2.2.1 h

@[trans]
theorem trans' (r : Setoidₓ α) : ∀ {x y z}, r.Rel x y → r.Rel y z → r.Rel x z := fun _ _ _ hx => r.2.2.2 hx

theorem comm' (s : Setoidₓ α) {x y} : s.Rel x y ↔ s.Rel y x :=
  ⟨s.symm', s.symm'⟩

/-- The kernel of a function is an equivalence relation. -/
def ker (f : α → β) : Setoidₓ α :=
  ⟨(· = ·) on f, eq_equivalence.comap f⟩

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp]
theorem ker_mk_eq (r : Setoidₓ α) : ker (@Quotientₓ.mk _ r) = r :=
  ext' fun x y => Quotientₓ.eq

theorem ker_apply_mk_out {f : α → β} (a : α) :
    f
        (have := Setoidₓ.ker f
        ⟦a⟧.out) =
      f a :=
  @Quotientₓ.mk_out _ (Setoidₓ.ker f) a

theorem ker_apply_mk_out' {f : α → β} (a : α) : f (Quotientₓ.mk' a : Quotientₓ <| Setoidₓ.ker f).out' = f a :=
  @Quotientₓ.mk_out' _ (Setoidₓ.ker f) a

theorem ker_def {f : α → β} {x y : α} : (ker f).Rel x y ↔ f x = f y :=
  Iff.rfl

/-- Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s` on `β`:
    `(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y₁`
    by `r` and `x₂` is related to `y₂` by `s`. -/
protected def prod (r : Setoidₓ α) (s : Setoidₓ β) : Setoidₓ (α × β) where
  R := fun x y => r.Rel x.1 y.1 ∧ s.Rel x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun _ _ h => ⟨r.symm' h.1, s.symm' h.2⟩, fun _ _ _ h1 h2 =>
      ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩

/-- The infimum of two equivalence relations. -/
instance : HasInf (Setoidₓ α) :=
  ⟨fun r s =>
    ⟨fun x y => r.Rel x y ∧ s.Rel x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun _ _ h => ⟨r.symm' h.1, s.symm' h.2⟩, fun _ _ _ h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum
    of the underlying binary operations. -/
theorem inf_def {r s : Setoidₓ α} : (r⊓s).Rel = r.Rel⊓s.Rel :=
  rfl

theorem inf_iff_and {r s : Setoidₓ α} {x y} : (r⊓s).Rel x y ↔ r.Rel x y ∧ s.Rel x y :=
  Iff.rfl

/-- The infimum of a set of equivalence relations. -/
instance : HasInfₓ (Setoidₓ α) :=
  ⟨fun S =>
    ⟨fun x y => ∀, ∀ r ∈ S, ∀, Rel r x y,
      ⟨fun x r hr => r.refl' x, fun _ _ h r hr => r.symm' <| h r hr, fun _ _ _ h1 h2 r hr =>
        r.trans' (h1 r hr) <| h2 r hr⟩⟩⟩

/-- The underlying binary operation of the infimum of a set of equivalence relations
    is the infimum of the set's image under the map to the underlying binary operation. -/
theorem Inf_def {s : Set (Setoidₓ α)} : (inf s).Rel = inf (rel '' s) := by
  ext
  simp only [← Inf_image, ← infi_apply, ← infi_Prop_eq]
  rfl

instance : PartialOrderₓ (Setoidₓ α) where
  le := (· ≤ ·)
  lt := fun r s => r ≤ s ∧ ¬s ≤ r
  le_refl := fun _ _ _ => id
  le_trans := fun _ _ _ hr hs _ _ h => hs <| hr h
  lt_iff_le_not_le := fun _ _ => Iff.rfl
  le_antisymm := fun r s h1 h2 => Setoidₓ.ext' fun x y => ⟨fun h => h1 h, fun h => h2 h⟩

/-- The complete lattice of equivalence relations on a type, with bottom element `=`
    and top element the trivial equivalence relation. -/
instance completeLattice : CompleteLattice (Setoidₓ α) :=
  { (completeLatticeOfInf (Setoidₓ α)) fun s => ⟨fun r hr x y h => h _ hr, fun r hr x y h r' hr' => hr hr' h⟩ with
    inf := HasInf.inf, inf_le_left := fun _ _ _ _ h => h.1, inf_le_right := fun _ _ _ _ h => h.2,
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩,
    top := ⟨fun _ _ => True, ⟨fun _ => trivialₓ, fun _ _ h => h, fun _ _ _ h1 h2 => h1⟩⟩,
    le_top := fun _ _ _ _ => trivialₓ,
    bot := ⟨(· = ·), ⟨fun _ => rfl, fun _ _ h => h.symm, fun _ _ _ h1 h2 => h1.trans h2⟩⟩,
    bot_le := fun r x y h => h ▸ r.2.1 x }

@[simp]
theorem top_def : (⊤ : Setoidₓ α).Rel = ⊤ :=
  rfl

@[simp]
theorem bot_def : (⊥ : Setoidₓ α).Rel = (· = ·) :=
  rfl

theorem eq_top_iff {s : Setoidₓ α} : s = (⊤ : Setoidₓ α) ↔ ∀ x y : α, s.Rel x y := by
  simp [← eq_top_iff, ← Setoidₓ.le_def, ← Setoidₓ.top_def, ← Pi.top_apply]

/-- The inductively defined equivalence closure of a binary relation r is the infimum
    of the set of all equivalence relations containing r. -/
theorem eqv_gen_eq (r : α → α → Prop) : EqvGen.setoid r = inf { s : Setoidₓ α | ∀ ⦃x y⦄, r x y → s.Rel x y } :=
  le_antisymmₓ
    (fun _ _ H => EqvGen.ndrec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _) (fun _ _ _ _ _ => trans' _) H)
    (Inf_le fun _ _ h => EqvGen.rel _ _ h)

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation `x is related to y by r or s`. -/
theorem sup_eq_eqv_gen (r s : Setoidₓ α) : r⊔s = EqvGen.setoid fun x y => r.Rel x y ∨ s.Rel x y := by
  rw [eqv_gen_eq]
  apply congr_arg Inf
  simp only [← le_def, ← or_imp_distrib, forall_and_distrib]

/-- The supremum of 2 equivalence relations r and s is the equivalence closure of the
    supremum of the underlying binary operations. -/
theorem sup_def {r s : Setoidₓ α} : r⊔s = EqvGen.setoid (r.Rel⊔s.Rel) := by
  rw [sup_eq_eqv_gen] <;> rfl

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation `there exists r ∈ S relating x and y`. -/
theorem Sup_eq_eqv_gen (S : Set (Setoidₓ α)) : sup S = EqvGen.setoid fun x y => ∃ r : Setoidₓ α, r ∈ S ∧ r.Rel x y := by
  rw [eqv_gen_eq]
  apply congr_arg Inf
  simp only [← UpperBounds, ← le_def, ← and_imp, ← exists_imp_distrib]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩

/-- The supremum of a set of equivalence relations is the equivalence closure of the
    supremum of the set's image under the map to the underlying binary operation. -/
theorem Sup_def {s : Set (Setoidₓ α)} : sup s = EqvGen.setoid (sup (rel '' s)) := by
  rw [Sup_eq_eqv_gen, Sup_image]
  congr with x y
  simp only [← supr_apply, ← supr_Prop_eq, ← exists_prop]

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp]
theorem eqv_gen_of_setoid (r : Setoidₓ α) : EqvGen.setoid r.R = r :=
  le_antisymmₓ
    (by
      rw [eqv_gen_eq] <;> exact Inf_le fun _ _ => id)
    EqvGen.rel

/-- Equivalence closure is idempotent. -/
@[simp]
theorem eqv_gen_idem (r : α → α → Prop) : EqvGen.setoid (EqvGen.setoid r).Rel = EqvGen.setoid r :=
  eqv_gen_of_setoid _

/-- The equivalence closure of a binary relation r is contained in any equivalence
    relation containing r. -/
theorem eqv_gen_le {r : α → α → Prop} {s : Setoidₓ α} (h : ∀ x y, r x y → s.Rel x y) : EqvGen.setoid r ≤ s := by
  rw [eqv_gen_eq] <;> exact Inf_le h

/-- Equivalence closure of binary relations is monotone. -/
theorem eqv_gen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) : EqvGen.setoid r ≤ EqvGen.setoid s :=
  eqv_gen_le fun _ _ hr => EqvGen.rel _ _ <| h _ _ hr

/-- There is a Galois insertion of equivalence relations on α into binary relations
    on α, with equivalence closure the lower adjoint. -/
def gi : @GaloisInsertion (α → α → Prop) (Setoidₓ α) _ _ EqvGen.setoid Rel where
  choice := fun r h => EqvGen.setoid r
  gc := fun r s => ⟨fun H _ _ h => H <| EqvGen.rel _ _ h, fun H => eqv_gen_of_setoid s ▸ eqv_gen_mono H⟩
  le_l_u := fun x => (eqv_gen_of_setoid x).symm ▸ le_reflₓ x
  choice_eq := fun _ _ => rfl

open Function

/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
    of equivalence relations on α. -/
theorem injective_iff_ker_bot (f : α → β) : Injective f ↔ ker f = ⊥ :=
  (@eq_bot_iff (Setoidₓ α) _ _ (ker f)).symm

/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
theorem ker_iff_mem_preimage {f : α → β} {x y} : (ker f).Rel x y ↔ x ∈ f ⁻¹' {f y} :=
  Iff.rfl

/-- Equivalence between functions `α → β` such that `r x y → f x = f y` and functions
`quotient r → β`. -/
def liftEquiv (r : Setoidₓ α) : { f : α → β // r ≤ ker f } ≃ (Quotientₓ r → β) where
  toFun := fun f => Quotientₓ.lift (f : α → β) f.2
  invFun := fun f =>
    ⟨f ∘ Quotientₓ.mk, fun x y h => by
      simp [← ker_def, ← Quotientₓ.sound h]⟩
  left_inv := fun ⟨f, hf⟩ => Subtype.eq <| funext fun x => rfl
  right_inv := fun f => funext fun x => (Quotientₓ.induction_on' x) fun x => rfl

/-- The uniqueness part of the universal property for quotients of an arbitrary type. -/
theorem lift_unique {r : Setoidₓ α} {f : α → β} (H : r ≤ ker f) (g : Quotientₓ r → β) (Hg : f = g ∘ Quotientₓ.mk) :
    Quotientₓ.lift f H = g := by
  ext ⟨x⟩
  erw [Quotientₓ.lift_mk f H, Hg]
  rfl

/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is
    injective. -/
theorem ker_lift_injective (f : α → β) : Injective (@Quotientₓ.lift _ _ (ker f) f fun _ _ h => h) := fun x y =>
  (Quotientₓ.induction_on₂' x y) fun a b h => Quotientₓ.sound' h

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
theorem ker_eq_lift_of_injective {r : Setoidₓ α} (f : α → β) (H : ∀ x y, r.Rel x y → f x = f y)
    (h : Injective (Quotientₓ.lift f H)) : ker f = r :=
  le_antisymmₓ (fun x y hk => Quotientₓ.exact <| h <| show Quotientₓ.lift f H ⟦x⟧ = Quotientₓ.lift f H ⟦y⟧ from hk) H

variable (r : Setoidₓ α) (f : α → β)

/-- The first isomorphism theorem for sets: the quotient of α by the kernel of a function f
    bijects with f's image. -/
noncomputable def quotientKerEquivRange : Quotientₓ (ker f) ≃ Set.Range f :=
  Equivₓ.ofBijective
    ((@Quotientₓ.lift _ (Set.Range f) (ker f) fun x => ⟨f x, Set.mem_range_self x⟩) fun _ _ h => Subtype.ext_val h)
    ⟨fun x y h =>
      ker_lift_injective f <| by
        rcases x with ⟨⟩ <;> rcases y with ⟨⟩ <;> injections,
      fun ⟨w, z, hz⟩ =>
      ⟨@Quotientₓ.mk _ (ker f) z, by
        rw [Quotientₓ.lift_mk] <;> exact Subtype.ext_iff_val.2 hz⟩⟩

/-- If `f` has a computable right-inverse, then the quotient by its kernel is equivalent to its
domain. -/
@[simps]
def quotientKerEquivOfRightInverse (g : β → α) (hf : Function.RightInverse g f) : Quotientₓ (ker f) ≃ β where
  toFun := fun a => (Quotientₓ.liftOn' a f) fun _ _ => id
  invFun := fun b => Quotientₓ.mk' (g b)
  left_inv := fun a => (Quotientₓ.induction_on' a) fun a => Quotientₓ.sound' <| hf (f a)
  right_inv := hf

/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain.

If a specific right-inverse of `f` is known, `setoid.quotient_ker_equiv_of_right_inverse` can be
definitionally more useful. -/
noncomputable def quotientKerEquivOfSurjective (hf : Surjective f) : Quotientₓ (ker f) ≃ β :=
  quotientKerEquivOfRightInverse _ (Function.surjInv hf) (right_inverse_surj_inv hf)

variable {r f}

/-- Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalence
    closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are
    related to the elements of `f⁻¹(y)` by `r`.' -/
def map (r : Setoidₓ α) (f : α → β) : Setoidₓ β :=
  EqvGen.setoid fun x y => ∃ a b, f a = x ∧ f b = y ∧ r.Rel a b

/-- Given a surjective function f whose kernel is contained in an equivalence relation r, the
    equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) are related to
    the elements of f⁻¹(y) by r. -/
def mapOfSurjective (r) (f : α → β) (h : ker f ≤ r) (hf : Surjective f) : Setoidₓ β :=
  ⟨fun x y => ∃ a b, f a = x ∧ f b = y ∧ r.Rel a b,
    ⟨fun x =>
      let ⟨y, hy⟩ := hf x
      ⟨y, y, hy, hy, r.refl' y⟩,
      fun _ _ ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, r.symm' h⟩, fun _ _ _ ⟨x, y, hx, hy, h₁⟩ ⟨y', z, hy', hz, h₂⟩ =>
      ⟨x, z, hx, hz,
        r.trans' h₁ <|
          r.trans'
            (h <| by
              rwa [← hy'] at hy)
            h₂⟩⟩⟩

/-- A special case of the equivalence closure of an equivalence relation r equalling r. -/
theorem map_of_surjective_eq_map (h : ker f ≤ r) (hf : Surjective f) : map r f = mapOfSurjective r f h hf := by
  rw [← eqv_gen_of_setoid (map_of_surjective r f h hf)] <;> rfl

/-- Given a function `f : α → β`, an equivalence relation `r` on `β` induces an equivalence
relation on `α` defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `r`'.

See note [reducible non-instances]. -/
@[reducible]
def comap (f : α → β) (r : Setoidₓ β) : Setoidₓ α :=
  ⟨r.Rel on f, r.iseqv.comap _⟩

theorem comap_rel (f : α → β) (r : Setoidₓ β) (x y : α) : (comap f r).Rel x y ↔ r.Rel (f x) (f y) :=
  Iff.rfl

/-- Given a map `f : N → M` and an equivalence relation `r` on `β`, the equivalence relation
    induced on `α` by `f` equals the kernel of `r`'s quotient map composed with `f`. -/
theorem comap_eq {f : α → β} {r : Setoidₓ β} : comap f r = ker (@Quotientₓ.mk _ r ∘ f) :=
  ext fun x y =>
    show _ ↔ ⟦_⟧ = ⟦_⟧ by
      rw [Quotientₓ.eq] <;> rfl

/-- The second isomorphism theorem for sets. -/
noncomputable def comapQuotientEquiv (f : α → β) (r : Setoidₓ β) :
    Quotientₓ (comap f r) ≃ Set.Range (@Quotientₓ.mk _ r ∘ f) :=
  (Quotientₓ.congrRight <| ext_iff.1 comap_eq).trans <| quotient_ker_equiv_range <| Quotientₓ.mk ∘ f

variable (r f)

/-- The third isomorphism theorem for sets. -/
def quotientQuotientEquivQuotient (s : Setoidₓ α) (h : r ≤ s) : Quotientₓ (ker (Quot.mapRight h)) ≃ Quotientₓ s where
  toFun := fun x =>
    (Quotientₓ.liftOn' x fun w => (Quotientₓ.liftOn' w (@Quotientₓ.mk _ s)) fun x y H => Quotientₓ.sound <| h H)
      fun x y => (Quotientₓ.induction_on₂' x y) fun w z H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun := fun x =>
    (Quotientₓ.liftOn' x fun w => @Quotientₓ.mk _ (ker <| Quot.mapRight h) <| @Quotientₓ.mk _ r w) fun x y H =>
      Quotientₓ.sound' <| show @Quot.mk _ _ _ = @Quot.mk _ _ _ from Quotientₓ.sound H
  left_inv := fun x =>
    (Quotientₓ.induction_on' x) fun y =>
      (Quotientₓ.induction_on' y) fun w => by
        show ⟦_⟧ = _ <;> rfl
  right_inv := fun x =>
    (Quotientₓ.induction_on' x) fun y => by
      show ⟦_⟧ = _ <;> rfl

variable {r f}

open Quotientₓ

/-- Given an equivalence relation `r` on `α`, the order-preserving bijection between the set of
equivalence relations containing `r` and the equivalence relations on the quotient of `α` by `r`. -/
def correspondence (r : Setoidₓ α) : { s // r ≤ s } ≃o Setoidₓ (Quotientₓ r) where
  toFun := fun s => mapOfSurjective s.1 Quotientₓ.mk ((ker_mk_eq r).symm ▸ s.2) exists_rep
  invFun := fun s =>
    ⟨comap Quotientₓ.mk' s, fun x y h => by
      rw [comap_rel, eq_rel.2 h]⟩
  left_inv := fun s =>
    Subtype.ext_iff_val.2 <|
      ext' fun _ _ =>
        ⟨fun h =>
          let ⟨a, b, hx, hy, H⟩ := h
          s.1.trans' (s.1.symm' <| s.2 <| eq_rel.1 hx) <| s.1.trans' H <| s.2 <| eq_rel.1 hy,
          fun h => ⟨_, _, rfl, rfl, h⟩⟩
  right_inv := fun s =>
    let Hm : ker Quotientₓ.mk' ≤ comap Quotientₓ.mk' s := fun x y h => by
      rw [comap_rel, (@eq_rel _ r x y).2 (ker_mk_eq r ▸ h)]
    ext' fun x y =>
      ⟨fun h =>
        let ⟨a, b, hx, hy, H⟩ := h
        hx ▸ hy ▸ H,
        (Quotientₓ.induction_on₂ x y) fun w z h => ⟨w, z, rfl, rfl, h⟩⟩
  map_rel_iff' := fun s t =>
    ⟨fun h x y hs =>
      let ⟨a, b, hx, hy, ht⟩ := h ⟨x, y, rfl, rfl, hs⟩
      t.1.trans' (t.1.symm' <| t.2 <| eq_rel.1 hx) <| t.1.trans' ht <| t.2 <| eq_rel.1 hy,
      fun h x y hs =>
      let ⟨a, b, hx, hy, Hs⟩ := hs
      ⟨a, b, hx, hy, h Hs⟩⟩

end Setoidₓ

@[simp]
theorem Quotientₓ.subsingleton_iff {s : Setoidₓ α} : Subsingleton (Quotientₓ s) ↔ s = ⊤ := by
  simp only [← subsingleton_iff, ← eq_top_iff, ← Setoidₓ.le_def, ← Setoidₓ.top_def, ← Pi.top_apply, ← forall_const]
  refine' (surjective_quotient_mk _).forall.trans (forall_congrₓ fun a => _)
  refine' (surjective_quotient_mk _).forall.trans (forall_congrₓ fun b => _)
  exact Quotientₓ.eq'

theorem Quot.subsingleton_iff (r : α → α → Prop) : Subsingleton (Quot r) ↔ EqvGen r = ⊤ := by
  simp only [← subsingleton_iff, ← _root_.eq_top_iff, ← Pi.le_def, ← Pi.top_apply, ← forall_const]
  refine' (surjective_quot_mk _).forall.trans (forall_congrₓ fun a => _)
  refine' (surjective_quot_mk _).forall.trans (forall_congrₓ fun b => _)
  rw [Quot.eq]
  simp only [← forall_const, ← le_Prop_eq]

