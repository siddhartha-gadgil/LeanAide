/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.RingTheory.Ideal.Operations

/-!

# Local rings

Define local rings as commutative rings having a unique maximal ideal.

## Main definitions

* `local_ring`: A predicate on commutative semirings, stating that for any pair of elements that
  adds up to `1`, one of them is a unit. This is shown to be equivalent to the condition that there
  exists a unique maximal ideal.
* `local_ring.maximal_ideal`: The unique maximal ideal for a local rings. Its carrier set is the
  set of non units.
* `is_local_ring_hom`: A predicate on semiring homomorphisms, requiring that it maps nonunits
  to nonunits. For local rings, this means that the image of the unique maximal ideal is again
  contained in the unique maximal ideal.
* `local_ring.residue_field`: The quotient of a local ring by its maximal ideal.

-/


universe u v w u'

variable {R : Type u} {S : Type v} {T : Type w} {K : Type u'}

/-- A semiring is local if it is nontrivial and `a` or `b` is a unit whenever `a + b = 1`.
Note that `local_ring` is a predicate. -/
class LocalRing (R : Type u) [Semiringₓ R] extends Nontrivial R : Prop where of_is_unit_or_is_unit_of_add_one ::
  is_unit_or_is_unit_of_add_one {a b : R} (h : a + b = 1) : IsUnit a ∨ IsUnit b

section CommSemiringₓ

variable [CommSemiringₓ R]

namespace LocalRing

theorem of_is_unit_or_is_unit_of_is_unit_add [Nontrivial R] (h : ∀ a b : R, IsUnit (a + b) → IsUnit a ∨ IsUnit b) :
    LocalRing R :=
  ⟨fun a b hab => h a b <| hab.symm ▸ is_unit_one⟩

/-- A semiring is local if it is nontrivial and the set of nonunits is closed under the addition. -/
theorem of_nonunits_add [Nontrivial R] (h : ∀ a b : R, a ∈ Nonunits R → b ∈ Nonunits R → a + b ∈ Nonunits R) :
    LocalRing R :=
  ⟨fun a b hab => or_iff_not_and_not.2 fun H => h a b H.1 H.2 <| hab.symm ▸ is_unit_one⟩

/-- A semiring is local if it has a unique maximal ideal. -/
theorem of_unique_max_ideal (h : ∃! I : Ideal R, I.IsMaximal) : LocalRing R :=
  (@of_nonunits_add _ _
      (nontrivial_of_ne (0 : R) 1 <|
        let ⟨I, Imax, _⟩ := h
        fun H : 0 = 1 => Imax.1.1 <| I.eq_top_iff_one.2 <| H ▸ I.zero_mem))
    fun x y hx hy H =>
    let ⟨I, Imax, Iuniq⟩ := h
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx
    let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy
    have xmemI : x ∈ I := Iuniq Ix Ixmax ▸ Hx
    have ymemI : y ∈ I := Iuniq Iy Iymax ▸ Hy
    Imax.1.1 <| I.eq_top_of_is_unit_mem (I.add_mem xmemI ymemI) H

theorem of_unique_nonzero_prime (h : ∃! P : Ideal R, P ≠ ⊥ ∧ Ideal.IsPrime P) : LocalRing R :=
  of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine' ⟨P, ⟨⟨hPnot_top, _⟩⟩, fun M hM => hPunique _ ⟨_, Ideal.IsMaximal.is_prime hM⟩⟩
      · refine' Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_ltₓ hPM _
        exact (hPunique _ ⟨ne_bot_of_gt hPM, Ideal.IsMaximal.is_prime hM⟩).symm
        
      · rintro rfl
        exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero))
        )

variable [LocalRing R]

theorem is_unit_or_is_unit_of_is_unit_add {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_addₓ] at hu
  apply Or.imp _ _ (is_unit_or_is_unit_of_add_one hu) <;> exact is_unit_of_mul_is_unit_right

theorem nonunits_add {a b : R} (ha : a ∈ Nonunits R) (hb : b ∈ Nonunits R) : a + b ∈ Nonunits R := fun H =>
  not_orₓ ha hb (is_unit_or_is_unit_of_is_unit_add H)

variable (R)

/-- The ideal of elements that are not units. -/
def maximalIdeal : Ideal R where
  Carrier := Nonunits R
  zero_mem' := zero_mem_nonunits.2 <| zero_ne_one
  add_mem' := fun x y hx hy => nonunits_add hx hy
  smul_mem' := fun a x => mul_mem_nonunits_right

instance maximalIdeal.is_maximal : (maximalIdeal R).IsMaximal := by
  rw [Ideal.is_maximal_iff]
  constructor
  · intro h
    apply h
    exact is_unit_one
    
  · intro I x hI hx H
    erw [not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H
    

theorem maximal_ideal_unique : ∃! I : Ideal R, I.IsMaximal :=
  ⟨maximalIdeal R, maximalIdeal.is_maximal R, fun I hI =>
    (hI.eq_of_le (maximalIdeal.is_maximal R).1.1) fun x hx => hI.1.1 ∘ I.eq_top_of_is_unit_mem hx⟩

variable {R}

theorem eq_maximal_ideal {I : Ideal R} (hI : I.IsMaximal) : I = maximalIdeal R :=
  unique_of_exists_unique (maximal_ideal_unique R) hI <| maximalIdeal.is_maximal R

theorem le_maximal_ideal {J : Ideal R} (hJ : J ≠ ⊤) : J ≤ maximalIdeal R := by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximal_ideal hM1]

@[simp]
theorem mem_maximal_ideal (x) : x ∈ maximalIdeal R ↔ x ∈ Nonunits R :=
  Iff.rfl

end LocalRing

end CommSemiringₓ

section CommRingₓ

variable [CommRingₓ R]

namespace LocalRing

theorem of_is_unit_or_is_unit_one_sub_self [Nontrivial R] (h : ∀ a : R, IsUnit a ∨ IsUnit (1 - a)) : LocalRing R :=
  ⟨fun a b hab => add_sub_cancel' a b ▸ hab.symm ▸ h a⟩

variable [LocalRing R]

theorem is_unit_or_is_unit_one_sub_self (a : R) : IsUnit a ∨ IsUnit (1 - a) :=
  is_unit_or_is_unit_of_is_unit_add <| (add_sub_cancel'_right a 1).symm ▸ is_unit_one

theorem is_unit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a ∈ Nonunits R) : IsUnit a :=
  or_iff_not_imp_right.1 (is_unit_or_is_unit_one_sub_self a) h

theorem is_unit_one_sub_self_of_mem_nonunits (a : R) (h : a ∈ Nonunits R) : IsUnit (1 - a) :=
  or_iff_not_imp_left.1 (is_unit_or_is_unit_one_sub_self a) h

theorem of_surjective' [CommRingₓ S] [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) : LocalRing S :=
  of_is_unit_or_is_unit_one_sub_self
    (by
      intro b
      obtain ⟨a, rfl⟩ := hf b
      apply (is_unit_or_is_unit_one_sub_self a).imp f.is_unit_map _
      rw [← f.map_one, ← f.map_sub]
      apply f.is_unit_map)

end LocalRing

end CommRingₓ

/-- A local ring homomorphism is a homomorphism `f` between local rings such that `a` in the domain
  is a unit if `f a` is a unit for any `a`. See `local_ring.local_hom_tfae` for other equivalent
  definitions. -/
class IsLocalRingHom [Semiringₓ R] [Semiringₓ S] (f : R →+* S) : Prop where
  map_nonunit : ∀ a, IsUnit (f a) → IsUnit a

section

variable [Semiringₓ R] [Semiringₓ S] [Semiringₓ T]

instance is_local_ring_hom_id (R : Type _) [Semiringₓ R] :
    IsLocalRingHom (RingHom.id R) where map_nonunit := fun a => id

@[simp]
theorem is_unit_map_iff (f : R →+* S) [IsLocalRingHom f] (a) : IsUnit (f a) ↔ IsUnit a :=
  ⟨IsLocalRingHom.map_nonunit a, f.is_unit_map⟩

@[simp]
theorem map_mem_nonunits_iff (f : R →+* S) [IsLocalRingHom f] (a) : f a ∈ Nonunits S ↔ a ∈ Nonunits R :=
  ⟨fun h ha => h <| (is_unit_map_iff f a).mpr ha, fun h ha => h <| (is_unit_map_iff f a).mp ha⟩

instance is_local_ring_hom_comp (g : S →+* T) (f : R →+* S) [IsLocalRingHom g] [IsLocalRingHom f] :
    IsLocalRingHom
      (g.comp f) where map_nonunit := fun a => IsLocalRingHom.map_nonunit a ∘ IsLocalRingHom.map_nonunit (f a)

instance is_local_ring_hom_equiv (f : R ≃+* S) :
    IsLocalRingHom (f : R →+* S) where map_nonunit := fun a ha => by
    convert (f.symm : S →+* R).is_unit_map ha
    exact (RingEquiv.symm_apply_apply f a).symm

@[simp]
theorem is_unit_of_map_unit (f : R →+* S) [IsLocalRingHom f] (a) (h : IsUnit (f a)) : IsUnit a :=
  IsLocalRingHom.map_nonunit a h

theorem of_irreducible_map (f : R →+* S) [h : IsLocalRingHom f] {x} (hfx : Irreducible (f x)) : Irreducible x :=
  ⟨fun h => hfx.not_unit <| IsUnit.map f h, fun p q hx =>
    let ⟨H⟩ := h
    Or.imp (H p) (H q) <| hfx.is_unit_or_is_unit <| f.map_mul p q ▸ congr_arg f hx⟩

theorem is_local_ring_hom_of_comp (f : R →+* S) (g : S →+* T) [IsLocalRingHom (g.comp f)] : IsLocalRingHom f :=
  ⟨fun a ha => (is_unit_map_iff (g.comp f) _).mp (g.is_unit_map ha)⟩

instance _root_.CommRing.is_local_ring_hom_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) [IsLocalRingHom g]
    [IsLocalRingHom f] : IsLocalRingHom (f ≫ g) :=
  is_local_ring_hom_comp _ _

/-- If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is. -/
theorem _root_.ring_hom.domain_local_ring {R S : Type _} [CommSemiringₓ R] [CommSemiringₓ S] [H : LocalRing S]
    (f : R →+* S) [IsLocalRingHom f] : LocalRing R := by
  have : Nontrivial R := pullback_nonzero f f.map_zero f.map_one
  apply LocalRing.of_nonunits_add
  intro a b
  simp_rw [← map_mem_nonunits_iff f, f.map_add]
  exact LocalRing.nonunits_add

section

open CategoryTheory

theorem is_local_ring_hom_of_iso {R S : CommRingₓₓ} (f : R ≅ S) : IsLocalRingHom f.hom :=
  { map_nonunit := fun a ha => by
      convert f.inv.is_unit_map ha
      rw [CategoryTheory.Iso.hom_inv_id_apply] }

-- see Note [lower instance priority]
instance (priority := 100) is_local_ring_hom_of_is_iso {R S : CommRingₓₓ} (f : R ⟶ S) [IsIso f] : IsLocalRingHom f :=
  is_local_ring_hom_of_iso (asIso f)

end

end

section

open LocalRing

variable [CommSemiringₓ R] [LocalRing R] [CommSemiringₓ S] [LocalRing S]

/-- The image of the maximal ideal of the source is contained within the maximal ideal of the target.
-/
theorem map_nonunit (f : R →+* S) [IsLocalRingHom f] (a : R) (h : a ∈ maximalIdeal R) : f a ∈ maximalIdeal S := fun H =>
  h <| is_unit_of_map_unit f a H

end

namespace LocalRing

section

variable [CommSemiringₓ R] [LocalRing R] [CommSemiringₓ S] [LocalRing S]

/-- A ring homomorphism between local rings is a local ring hom iff it reflects units,
i.e. any preimage of a unit is still a unit. https://stacks.math.columbia.edu/tag/07BJ
-/
theorem local_hom_tfae (f : R →+* S) :
    Tfae
      [IsLocalRingHom f, f '' (maximalIdeal R).1 ⊆ maximalIdeal S, (maximalIdeal R).map f ≤ maximalIdeal S,
        maximalIdeal R ≤ (maximalIdeal S).comap f, (maximalIdeal S).comap f = maximalIdeal R] :=
  by
  tfae_have 1 → 2
  rintro _ _ ⟨a, ha, rfl⟩
  skip
  exact map_nonunit f a ha
  tfae_have 2 → 4
  exact Set.image_subset_iff.1
  tfae_have 3 ↔ 4
  exact Ideal.map_le_iff_le_comap
  tfae_have 4 → 1
  intro h
  fconstructor
  exact fun x => not_imp_not.1 (@h x)
  tfae_have 1 → 5
  intro
  skip
  ext
  exact not_iff_not.2 (is_unit_map_iff f x)
  tfae_have 5 → 4
  exact fun h => le_of_eqₓ h.symm
  tfae_finish

end

theorem of_surjective [CommSemiringₓ R] [LocalRing R] [CommSemiringₓ S] [Nontrivial S] (f : R →+* S) [IsLocalRingHom f]
    (hf : Function.Surjective f) : LocalRing S :=
  of_is_unit_or_is_unit_of_is_unit_add
    (by
      intro a b hab
      obtain ⟨a, rfl⟩ := hf a
      obtain ⟨b, rfl⟩ := hf b
      rw [← map_add] at hab
      exact (is_unit_or_is_unit_of_is_unit_add <| IsLocalRingHom.map_nonunit _ hab).imp f.is_unit_map f.is_unit_map)

section

variable (R) [CommRingₓ R] [LocalRing R] [CommRingₓ S] [LocalRing S]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def ResidueField :=
  R ⧸ maximalIdeal R

noncomputable instance ResidueField.field : Field (ResidueField R) :=
  Ideal.Quotient.field (maximalIdeal R)

noncomputable instance : Inhabited (ResidueField R) :=
  ⟨37⟩

/-- The quotient map from a local ring to its residue field. -/
def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _

noncomputable instance ResidueField.algebra : Algebra R (ResidueField R) :=
  (residue R).toAlgebra

variable {R}

namespace ResidueField

/-- The map on residue fields induced by a local homomorphism between local rings -/
noncomputable def map (f : R →+* S) [IsLocalRingHom f] : ResidueField R →+* ResidueField S :=
  (Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f)) fun a ha => by
    erw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha

end ResidueField

theorem ker_eq_maximal_ideal [Field K] (φ : R →+* K) (hφ : Function.Surjective φ) : φ.ker = maximalIdeal R :=
  LocalRing.eq_maximal_ideal <| (RingHom.ker_is_maximal_of_surjective φ) hφ

end

end LocalRing

namespace Field

variable (K) [Field K]

open Classical

-- see Note [lower instance priority]
instance (priority := 100) : LocalRing K :=
  LocalRing.of_is_unit_or_is_unit_one_sub_self fun a =>
    if h : a = 0 then
      Or.inr
        (by
          rw [h, sub_zero] <;> exact is_unit_one)
    else Or.inl <| IsUnit.mk0 a h

end Field

