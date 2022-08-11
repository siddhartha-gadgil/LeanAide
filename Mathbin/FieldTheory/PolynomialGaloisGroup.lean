/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathbin.Analysis.Complex.Polynomial
import Mathbin.FieldTheory.Galois
import Mathbin.GroupTheory.Perm.Cycle.Type

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.splitting_field`, and some specific
results about the Galois groups of ℚ-polynomials with specific numbers of non-real roots.

## Main definitions

- `polynomial.gal p`: the Galois group of a polynomial p.
- `polynomial.gal.restrict p E`: the restriction homomorphism `(E ≃ₐ[F] E) → gal p`.
- `polynomial.gal.gal_action p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `polynomial.gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `polynomial.gal.gal_action_hom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `polynomial.gal.restrict_prod_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `polynomial.gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`.
- `polynomial.gal.gal_action_hom_bijective_of_prime_degree`:
An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
equals the number of real roots plus the number of roots not fixed by complex conjugation
(i.e. with some imaginary component).

-/


noncomputable section

open Classical Polynomial

open FiniteDimensional

namespace Polynomial

variable {F : Type _} [Field F] (p q : F[X]) (E : Type _) [Field E] [Algebra F E]

/-- The Galois group of a polynomial. -/
def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField deriving Groupₓ, Fintype

namespace Gal

instance : CoeFun p.Gal fun _ => p.SplittingField → p.SplittingField :=
  AlgEquiv.hasCoeToFun

@[ext]
theorem ext {σ τ : p.Gal} (h : ∀, ∀ x ∈ p.RootSet p.SplittingField, ∀, σ x = τ x) : σ = τ := by
  refine'
    AlgEquiv.ext fun x =>
      (AlgHom.mem_equalizer σ.to_alg_hom τ.to_alg_hom x).mp ((set_like.ext_iff.mp _ x).mpr Algebra.mem_top)
  rwa [eq_top_iff, ← splitting_field.adjoin_roots, Algebra.adjoin_le_iff]

/-- If `p` splits in `F` then the `p.gal` is trivial. -/
def uniqueGalOfSplits (h : p.Splits (RingHom.id F)) : Unique p.Gal where
  default := 1
  uniq := fun f =>
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        algebra.mem_bot.mp ((set_like.ext_iff.mp ((is_splitting_field.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes, AlgEquiv.commutes]

instance [h : Fact (p.Splits (RingHom.id F))] : Unique p.Gal :=
  uniqueGalOfSplits _ h.1

instance uniqueGalZero : Unique (0 : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_zero _)

instance uniqueGalOne : Unique (1 : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_one _)

instance uniqueGalC (x : F) : Unique (c x).Gal :=
  uniqueGalOfSplits _ (splits_C _ _)

instance uniqueGalX : Unique (x : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_X _)

instance uniqueGalXSubC (x : F) : Unique (X - c x).Gal :=
  uniqueGalOfSplits _ (splits_X_sub_C _)

instance uniqueGalXPow (n : ℕ) : Unique (X ^ n : F[X]).Gal :=
  uniqueGalOfSplits _ (splits_X_pow _ _)

instance [h : Fact (p.Splits (algebraMap F E))] : Algebra p.SplittingField E :=
  (IsSplittingField.lift p.SplittingField p h.1).toRingHom.toAlgebra

instance [h : Fact (p.Splits (algebraMap F E))] : IsScalarTower F p.SplittingField E :=
  IsScalarTower.of_algebra_map_eq fun x => ((IsSplittingField.lift p.SplittingField p h.1).commutes x).symm

/-- Restrict from a superfield automorphism into a member of `gal p`. -/
-- The `algebra p.splitting_field E` instance above behaves badly when
-- `E := p.splitting_field`, since it may result in a unification problem
-- `is_splitting_field.lift.to_ring_hom.to_algebra =?= algebra.id`,
-- which takes an extremely long time to resolve, causing timeouts.
-- Since we don't really care about this definition, marking it as irreducible
-- causes that unification to error out early.
def restrict [Fact (p.Splits (algebraMap F E))] : (E ≃ₐ[F] E) →* p.Gal :=
  AlgEquiv.restrictNormalHom p.SplittingField

theorem restrict_surjective [Fact (p.Splits (algebraMap F E))] [Normal F E] : Function.Surjective (restrict p E) :=
  AlgEquiv.restrict_normal_hom_surjective E

section RootsAction

/-- The function taking `roots p p.splitting_field` to `roots p E`. This is actually a bijection,
see `polynomial.gal.map_roots_bijective`. -/
def mapRoots [Fact (p.Splits (algebraMap F E))] : RootSet p p.SplittingField → RootSet p E := fun x =>
  ⟨IsScalarTower.toAlgHom F p.SplittingField E x, by
    have key := Subtype.mem x
    by_cases' p = 0
    · simp only [← h, ← root_set_zero] at key
      exact False.ndrec _ key
      
    · rw [mem_root_set h, aeval_alg_hom_apply, (mem_root_set h).mp key, AlgHom.map_zero]
      ⟩

theorem map_roots_bijective [h : Fact (p.Splits (algebraMap F E))] : Function.Bijective (mapRoots p E) := by
  constructor
  · exact fun _ _ h => Subtype.ext (RingHom.injective _ (subtype.ext_iff.mp h))
    
  · intro y
    -- this is just an equality of two different ways to write the roots of `p` as an `E`-polynomial
    have key :=
      roots_map (IsScalarTower.toAlgHom F p.splitting_field E : p.splitting_field →+* E)
        ((splits_id_iff_splits _).mpr (is_splitting_field.splits p.splitting_field p))
    rw [map_map, AlgHom.comp_algebra_map] at key
    have hy := Subtype.mem y
    simp only [← root_set, ← Finset.mem_coe, ← Multiset.mem_to_finset, ← key, ← Multiset.mem_map] at hy
    rcases hy with ⟨x, hx1, hx2⟩
    exact ⟨⟨x, multiset.mem_to_finset.mpr hx1⟩, Subtype.ext hx2⟩
    

/-- The bijection between `root_set p p.splitting_field` and `root_set p E`. -/
def rootsEquivRoots [Fact (p.Splits (algebraMap F E))] : RootSet p p.SplittingField ≃ RootSet p E :=
  Equivₓ.ofBijective (mapRoots p E) (map_roots_bijective p E)

instance galActionAux : MulAction p.Gal (RootSet p p.SplittingField) where
  smul := fun ϕ x =>
    ⟨ϕ x, by
      have key := Subtype.mem x
      --simp only [root_set, finset.mem_coe, multiset.mem_to_finset] at *,
      by_cases' p = 0
      · simp only [← h, ← root_set_zero] at key
        exact False.ndrec _ key
        
      · rw [mem_root_set h]
        change aeval (ϕ.to_alg_hom x) p = 0
        rw [aeval_alg_hom_apply, (mem_root_set h).mp key, AlgHom.map_zero]
        ⟩
  one_smul := fun _ => by
    ext
    rfl
  mul_smul := fun _ _ _ => by
    ext
    rfl

/-- The action of `gal p` on the roots of `p` in `E`. -/
instance galAction [Fact (p.Splits (algebraMap F E))] : MulAction p.Gal (RootSet p E) where
  smul := fun ϕ x => rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)
  one_smul := fun _ => by
    simp only [← Equivₓ.apply_symm_apply, ← one_smul]
  mul_smul := fun _ _ _ => by
    simp only [← Equivₓ.apply_symm_apply, ← Equivₓ.symm_apply_apply, ← mul_smul]

variable {p E}

/-- `polynomial.gal.restrict p E` is compatible with `polynomial.gal.gal_action p E`. -/
@[simp]
theorem restrict_smul [Fact (p.Splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : RootSet p E) :
    ↑(restrict p E ϕ • x) = ϕ x := by
  let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.splitting_field E)
  change ↑(ψ (ψ.symm _)) = ϕ x
  rw [AlgEquiv.apply_symm_apply ψ]
  change ϕ (roots_equiv_roots p E ((roots_equiv_roots p E).symm x)) = ϕ x
  rw [Equivₓ.apply_symm_apply (roots_equiv_roots p E)]

variable (p E)

/-- `polynomial.gal.gal_action` as a permutation representation -/
def galActionHom [Fact (p.Splits (algebraMap F E))] : p.Gal →* Equivₓ.Perm (RootSet p E) where
  toFun := fun ϕ =>
    Equivₓ.mk (fun x => ϕ • x) (fun x => ϕ⁻¹ • x) (fun x => inv_smul_smul ϕ x) fun x => smul_inv_smul ϕ x
  map_one' := by
    ext1 x
    exact MulAction.one_smul x
  map_mul' := fun x y => by
    ext1 z
    exact MulAction.mul_smul x y z

theorem gal_action_hom_restrict [Fact (p.Splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : RootSet p E) :
    ↑(galActionHom p E (restrict p E ϕ) x) = ϕ x :=
  restrict_smul ϕ x

/-- `gal p` embeds as a subgroup of permutations of the roots of `p` in `E`. -/
theorem gal_action_hom_injective [Fact (p.Splits (algebraMap F E))] : Function.Injective (galActionHom p E) := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext x hx
  have key := equiv.perm.ext_iff.mp hϕ (roots_equiv_roots p E ⟨x, hx⟩)
  change
    roots_equiv_roots p E (ϕ • (roots_equiv_roots p E).symm (roots_equiv_roots p E ⟨x, hx⟩)) =
      roots_equiv_roots p E ⟨x, hx⟩ at
    key
  rw [Equivₓ.symm_apply_apply] at key
  exact subtype.ext_iff.mp (Equivₓ.injective (roots_equiv_roots p E) key)

end RootsAction

variable {p q}

/-- `polynomial.gal.restrict`, when both fields are splitting fields of polynomials. -/
def restrictDvd (hpq : p ∣ q) : q.Gal →* p.Gal :=
  if hq : q = 0 then 1
  else @restrict F _ p _ _ _ ⟨splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q) hpq⟩

theorem restrict_dvd_surjective (hpq : p ∣ q) (hq : q ≠ 0) : Function.Surjective (restrictDvd hpq) := by
  simp only [← restrict_dvd, ← dif_neg hq, ← restrict_surjective]

variable (p q)

/-- The Galois group of a product maps into the product of the Galois groups.  -/
def restrictProd : (p * q).Gal →* p.Gal × q.Gal :=
  MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))

/-- `polynomial.gal.restrict_prod` is actually a subgroup embedding. -/
theorem restrict_prod_injective : Function.Injective (restrictProd p q) := by
  by_cases' hpq : p * q = 0
  · have : Unique (p * q).Gal := by
      rw [hpq]
      infer_instance
    exact fun f g h => Eq.trans (Unique.eq_default f) (Unique.eq_default g).symm
    
  intro f g hfg
  dsimp' only [← restrict_prod, ← restrict_dvd]  at hfg
  simp only [← dif_neg hpq, ← MonoidHom.prod_apply, ← Prod.mk.inj_iff] at hfg
  ext x hx
  rw [root_set, Polynomial.map_mul, Polynomial.roots_mul] at hx
  cases' multiset.mem_add.mp (multiset.mem_to_finset.mp hx) with h h
  · have : Fact (p.splits (algebraMap F (p * q).SplittingField)) :=
      ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits (p * q)) (dvd_mul_right p q)⟩
    have key :
      x =
        algebraMap p.splitting_field (p * q).SplittingField
          ((roots_equiv_roots p _).invFun ⟨x, multiset.mem_to_finset.mpr h⟩) :=
      subtype.ext_iff.mp (Equivₓ.apply_symm_apply (roots_equiv_roots p _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrict_normal_commutes, ← AlgEquiv.restrict_normal_commutes]
    exact congr_arg _ (alg_equiv.ext_iff.mp hfg.1 _)
    
  · have : Fact (q.splits (algebraMap F (p * q).SplittingField)) :=
      ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits (p * q)) (dvd_mul_left q p)⟩
    have key :
      x =
        algebraMap q.splitting_field (p * q).SplittingField
          ((roots_equiv_roots q _).invFun ⟨x, multiset.mem_to_finset.mpr h⟩) :=
      subtype.ext_iff.mp (Equivₓ.apply_symm_apply (roots_equiv_roots q _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrict_normal_commutes, ← AlgEquiv.restrict_normal_commutes]
    exact congr_arg _ (alg_equiv.ext_iff.mp hfg.2 _)
    
  · rwa [Ne.def, mul_eq_zero, map_eq_zero, map_eq_zero, ← mul_eq_zero]
    

theorem mul_splits_in_splitting_field_of_mul {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (h₁ : p₁.Splits (algebraMap F q₁.SplittingField)) (h₂ : p₂.Splits (algebraMap F q₂.SplittingField)) :
    (p₁ * p₂).Splits (algebraMap F (q₁ * q₂).SplittingField) := by
  apply splits_mul
  · rw [←
      (splitting_field.lift q₁
          (splits_of_splits_of_dvd _ (mul_ne_zero hq₁ hq₂) (splitting_field.splits _)
            (dvd_mul_right q₁ q₂))).comp_algebra_map]
    exact splits_comp_of_splits _ _ h₁
    
  · rw [←
      (splitting_field.lift q₂
          (splits_of_splits_of_dvd _ (mul_ne_zero hq₁ hq₂) (splitting_field.splits _)
            (dvd_mul_left q₂ q₁))).comp_algebra_map]
    exact splits_comp_of_splits _ _ h₂
    

/-- `p` splits in the splitting field of `p ∘ q`, for `q` non-constant. -/
theorem splits_in_splitting_field_of_comp (hq : q.natDegree ≠ 0) : p.Splits (algebraMap F (p.comp q).SplittingField) :=
  by
  let P : F[X] → Prop := fun r => r.Splits (algebraMap F (r.comp q).SplittingField)
  have key1 : ∀ {r : F[X]}, Irreducible r → P r := by
    intro r hr
    by_cases' hr' : nat_degree r = 0
    · exact splits_of_nat_degree_le_one _ (le_transₓ (le_of_eqₓ hr') zero_le_one)
      
    obtain ⟨x, hx⟩ :=
      exists_root_of_splits _ (splitting_field.splits (r.comp q)) fun h =>
        hr' ((mul_eq_zero.mp (nat_degree_comp.symm.trans (nat_degree_eq_of_degree_eq_some h))).resolve_right hq)
    rw [← aeval_def, aeval_comp] at hx
    have h_normal : Normal F (r.comp q).SplittingField := splitting_field.normal (r.comp q)
    have qx_int := Normal.is_integral h_normal (aeval x q)
    exact
      splits_of_splits_of_dvd _ (minpoly.ne_zero qx_int) (Normal.splits h_normal _)
        ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx))
  have key2 : ∀ {p₁ p₂ : F[X]}, P p₁ → P p₂ → P (p₁ * p₂) := by
    intro p₁ p₂ hp₁ hp₂
    by_cases' h₁ : p₁.comp q = 0
    · cases' comp_eq_zero_iff.mp h₁ with h h
      · rw [h, zero_mul]
        exact splits_zero _
        
      · exact
          False.ndrec _
            (hq
              (by
                rw [h.2, nat_degree_C]))
        
      
    by_cases' h₂ : p₂.comp q = 0
    · cases' comp_eq_zero_iff.mp h₂ with h h
      · rw [h, mul_zero]
        exact splits_zero _
        
      · exact
          False.ndrec _
            (hq
              (by
                rw [h.2, nat_degree_C]))
        
      
    have key := mul_splits_in_splitting_field_of_mul h₁ h₂ hp₁ hp₂
    rwa [← mul_comp] at key
  exact
    WfDvdMonoid.induction_on_irreducible p (splits_zero _) (fun _ => splits_of_is_unit _) fun _ _ _ h => key2 (key1 h)

/-- `polynomial.gal.restrict` for the composition of polynomials. -/
def restrictComp (hq : q.natDegree ≠ 0) : (p.comp q).Gal →* p.Gal :=
  @restrict F _ p _ _ _ ⟨splits_in_splitting_field_of_comp p q hq⟩

theorem restrict_comp_surjective (hq : q.natDegree ≠ 0) : Function.Surjective (restrictComp p q hq) := by
  simp only [← restrict_comp, ← restrict_surjective]

variable {p q}

/-- For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`. -/
theorem card_of_separable (hp : p.Separable) : Fintype.card p.Gal = finrank F p.SplittingField := by
  have : IsGalois F p.splitting_field := IsGalois.of_separable_splitting_field hp
  exact IsGalois.card_aut_eq_finrank F p.splitting_field

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p) (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Fintype.card p.Gal := by
  rw [gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := fun h => Nat.Prime.ne_zero p_deg (nat_degree_eq_zero_iff_degree_le_zero.mpr (le_of_eqₓ h))
  let α : p.splitting_field := root_of_splits (algebraMap F p.splitting_field) (splitting_field.splits p) hp
  have hα : IsIntegral F α := Algebra.is_integral_of_finite _ _ α
  use FiniteDimensional.finrank F⟮⟯ p.splitting_field
  suffices (minpoly F α).natDegree = p.nat_degree by
    rw [← FiniteDimensional.finrank_mul_finrank F F⟮⟯ p.splitting_field, IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymmₓ
    · exact nat_degree_le_of_dvd this p_irr.ne_zero
      
    · exact nat_degree_le_of_dvd key (minpoly.ne_zero hα)
      
  apply minpoly.dvd F α
  rw [aeval_def, map_root_of_splits _ (splitting_field.splits p) hp]

section Rationals

theorem splits_ℚ_ℂ {p : ℚ[X]} : Fact (p.Splits (algebraMap ℚ ℂ)) :=
  ⟨IsAlgClosed.splits_codomain p⟩

attribute [local instance] splits_ℚ_ℂ

/-- The number of complex roots equals the number of real roots plus
    the number of roots not fixed by complex conjugation (i.e. with some imaginary component). -/
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv (p : ℚ[X]) :
    (p.RootSet ℂ).toFinset.card =
      (p.RootSet ℝ).toFinset.card + (galActionHom p ℂ (restrict p ℂ (Complex.conjAe.restrictScalars ℚ))).support.card :=
  by
  by_cases' hp : p = 0
  · simp_rw [hp, root_set_zero, set.to_finset_eq_empty_iff.mpr rfl, Finset.card_empty, zero_addₓ]
    refine' Eq.symm (nat.le_zero_iff.mp ((Finset.card_le_univ _).trans (le_of_eqₓ _)))
    simp_rw [hp, root_set_zero, Fintype.card_eq_zero_iff]
    infer_instance
    
  have inj : Function.Injective (IsScalarTower.toAlgHom ℚ ℝ ℂ) := (algebraMap ℝ ℂ).Injective
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective, ← Finset.card_image_of_injective _ inj]
  let a : Finset ℂ := _
  let b : Finset ℂ := _
  let c : Finset ℂ := _
  change a.card = b.card + c.card
  have ha : ∀ z : ℂ, z ∈ a ↔ aeval z p = 0 := fun z => by
    rw [Set.mem_to_finset, mem_root_set hp]
  have hb : ∀ z : ℂ, z ∈ b ↔ aeval z p = 0 ∧ z.im = 0 := by
    intro z
    simp_rw [Finset.mem_image, exists_prop, Set.mem_to_finset, mem_root_set hp]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact
        ⟨by
          rw [aeval_alg_hom_apply, hw, AlgHom.map_zero], rfl⟩
      
    · rintro ⟨hz1, hz2⟩
      have key : IsScalarTower.toAlgHom ℚ ℝ ℂ z.re = z := by
        ext
        rfl
        rw [hz2]
        rfl
      exact
        ⟨z.re,
          inj
            (by
              rwa [← aeval_alg_hom_apply, key, AlgHom.map_zero]),
          key⟩
      
  have hc0 :
    ∀ w : p.root_set ℂ, gal_action_hom p ℂ (restrict p ℂ (complex.conj_ae.restrict_scalars ℚ)) w = w ↔ w.val.im = 0 :=
    by
    intro w
    rw [Subtype.ext_iff, gal_action_hom_restrict]
    exact Complex.eq_conj_iff_im
  have hc : ∀ z : ℂ, z ∈ c ↔ aeval z p = 0 ∧ z.im ≠ 0 := by
    intro z
    simp_rw [Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(mem_root_set hp).mp w.2, mt (hc0 w).mpr (equiv.perm.mem_support.mp hw)⟩
      
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, (mem_root_set hp).mpr hz1⟩, equiv.perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩
      
  rw [← Finset.card_disjoint_union]
  · apply congr_arg Finset.card
    simp_rw [Finset.ext_iff, Finset.mem_union, ha, hb, hc]
    tauto
    
  · intro z
    rw [Finset.inf_eq_inter, Finset.mem_inter, hb, hc]
    tauto
    
  · infer_instance
    

/-- An irreducible polynomial of prime degree with two non-real roots has full Galois group. -/
theorem gal_action_hom_bijective_of_prime_degree {p : ℚ[X]} (p_irr : Irreducible p) (p_deg : p.natDegree.Prime)
    (p_roots : Fintype.card (p.RootSet ℂ) = Fintype.card (p.RootSet ℝ) + 2) : Function.Bijective (galActionHom p ℂ) :=
  by
  have h1 : Fintype.card (p.root_set ℂ) = p.nat_degree := by
    simp_rw [root_set_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.to_finset_card_of_nodup, ← nat_degree_eq_card_roots]
    · exact IsAlgClosed.splits_codomain p
      
    · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr p_irr.separable)
      
  have h2 : Fintype.card p.gal = Fintype.card (gal_action_hom p ℂ).range :=
    Fintype.card_congr (MonoidHom.ofInjective (gal_action_hom_injective p ℂ)).toEquiv
  let conj := restrict p ℂ (complex.conj_ae.restrict_scalars ℚ)
  refine'
    ⟨gal_action_hom_injective p ℂ, fun x =>
      (congr_arg (HasMem.Mem x) (show (gal_action_hom p ℂ).range = ⊤ from _)).mpr (Subgroup.mem_top x)⟩
  apply Equivₓ.Perm.subgroup_eq_top_of_swap_mem
  · rwa [h1]
    
  · rw [h1]
    convert prime_degree_dvd_card p_irr p_deg using 1
    convert h2.symm
    
  · exact ⟨conj, rfl⟩
    
  · rw [← Equivₓ.Perm.card_support_eq_two]
    apply Nat.add_left_cancel
    rw [← p_roots, ← Set.to_finset_card (root_set p ℝ), ← Set.to_finset_card (root_set p ℂ)]
    exact (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm
    

/-- An irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group. -/
theorem gal_action_hom_bijective_of_prime_degree' {p : ℚ[X]} (p_irr : Irreducible p) (p_deg : p.natDegree.Prime)
    (p_roots1 : Fintype.card (p.RootSet ℝ) + 1 ≤ Fintype.card (p.RootSet ℂ))
    (p_roots2 : Fintype.card (p.RootSet ℂ) ≤ Fintype.card (p.RootSet ℝ) + 3) : Function.Bijective (galActionHom p ℂ) :=
  by
  apply gal_action_hom_bijective_of_prime_degree p_irr p_deg
  let n := (gal_action_hom p ℂ (restrict p ℂ (complex.conj_ae.restrict_scalars ℚ))).support.card
  have hn : 2 ∣ n :=
    Equivₓ.Perm.two_dvd_card_support
      (by
        rw [← MonoidHom.map_pow, ← MonoidHom.map_pow,
          show AlgEquiv.restrictScalars ℚ Complex.conjAe ^ 2 = 1 from AlgEquiv.ext Complex.conj_conj, MonoidHom.map_one,
          MonoidHom.map_one])
  have key := card_complex_roots_eq_card_real_add_card_not_gal_inv p
  simp_rw [Set.to_finset_card] at key
  rw [key, add_le_add_iff_left] at p_roots1 p_roots2
  rw [key, add_right_injₓ]
  suffices ∀ m : ℕ, 2 ∣ m → 1 ≤ m → m ≤ 3 → m = 2 by
    exact this n hn p_roots1 p_roots2
  rintro m ⟨k, rfl⟩ h2 h3
  exact
    le_antisymmₓ (nat.lt_succ_iff.mp (lt_of_le_of_neₓ h3 (show 2 * k ≠ 2 * 1 + 1 from Nat.two_mul_ne_two_mul_add_one)))
      (nat.succ_le_iff.mpr (lt_of_le_of_neₓ h2 (show 2 * 0 + 1 ≠ 2 * k from nat.two_mul_ne_two_mul_add_one.symm)))

end Rationals

end Gal

end Polynomial

