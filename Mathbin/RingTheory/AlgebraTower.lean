/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Invertible
import Mathbin.RingTheory.Adjoin.Fg
import Mathbin.LinearAlgebra.Basis
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Algebra.Algebra.RestrictScalars

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `field_theory/tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is a `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/


open Pointwise

universe u v w u₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace IsScalarTower

section Semiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A] [Semiringₓ B]

variable [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

variable (R S A B)

/-- Suppose that `R -> S -> A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
def Invertible.algebraTower (r : R) [Invertible (algebraMap R S r)] : Invertible (algebraMap R A r) :=
  Invertible.copy (Invertible.map (algebraMap S A) (algebraMap R S r)) (algebraMap R A r)
    (IsScalarTower.algebra_map_apply R S A r)

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
def invertibleAlgebraCoeNat (n : ℕ) [inv : Invertible (n : R)] : Invertible (n : A) := by
  have : Invertible (algebraMap ℕ R n) := inv
  exact invertible.algebra_tower ℕ R A n

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ A] [CommSemiringₓ B]

variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

end CommSemiringₓ

end IsScalarTower

namespace Algebra

theorem adjoin_algebra_map (R : Type u) (S : Type v) (A : Type w) [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (s : Set S) :
    adjoin R (algebraMap S A '' s) = Subalgebra.map (adjoin R s) (IsScalarTower.toAlgHom R S A) :=
  le_antisymmₓ (adjoin_le <| Set.image_subset_iff.2 fun y hy => ⟨y, subset_adjoin hy, rfl⟩)
    (Subalgebra.map_le.2 <| adjoin_le fun y hy => subset_adjoin ⟨y, hy, rfl⟩)

theorem adjoin_restrict_scalars (C D E : Type _) [CommSemiringₓ C] [CommSemiringₓ D] [CommSemiringₓ E] [Algebra C D]
    [Algebra C E] [Algebra D E] [IsScalarTower C D E] (S : Set E) :
    (Algebra.adjoin D S).restrictScalars C =
      (Algebra.adjoin ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars C :=
  by
  suffices
    Set.Range (algebraMap D E) = Set.Range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E) by
    ext x
    change x ∈ Subsemiring.closure (_ ∪ S) ↔ x ∈ Subsemiring.closure (_ ∪ S)
    rw [this]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨algebraMap D E y, ⟨y, ⟨Algebra.mem_top, rfl⟩⟩⟩, hy⟩
    
  · rintro ⟨⟨y, ⟨z, ⟨h0, h1⟩⟩⟩, h2⟩
    exact ⟨z, Eq.trans h1 h2⟩
    

theorem adjoin_res_eq_adjoin_res (C D E F : Type _) [CommSemiringₓ C] [CommSemiringₓ D] [CommSemiringₓ E]
    [CommSemiringₓ F] [Algebra C D] [Algebra C E] [Algebra C F] [Algebra D F] [Algebra E F] [IsScalarTower C D F]
    [IsScalarTower C E F] {S : Set D} {T : Set E} (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) :
    (Algebra.adjoin E (algebraMap D F '' S)).restrictScalars C =
      (Algebra.adjoin D (algebraMap E F '' T)).restrictScalars C :=
  by
  rw [adjoin_restrict_scalars C E, adjoin_restrict_scalars C D, ← hS, ← hT, ← Algebra.adjoin_image, ←
    Algebra.adjoin_image, ← AlgHom.coe_to_ring_hom, ← AlgHom.coe_to_ring_hom, IsScalarTower.coe_to_alg_hom,
    IsScalarTower.coe_to_alg_hom, ← adjoin_union_eq_adjoin_adjoin, ← adjoin_union_eq_adjoin_adjoin, Set.union_comm]

end Algebra

section

open Classical

theorem Algebra.fg_trans' {R S A : Type _} [CommSemiringₓ R] [CommSemiringₓ S] [CommSemiringₓ A] [Algebra R S]
    [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤ : Subalgebra R S).Fg) (hSA : (⊤ : Subalgebra S A).Fg) :
    (⊤ : Subalgebra R A).Fg :=
  let ⟨s, hs⟩ := hRS
  let ⟨t, ht⟩ := hSA
  ⟨s.Image (algebraMap S A) ∪ t, by
    rw [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union_eq_adjoin_adjoin, Algebra.adjoin_algebra_map, hs,
      Algebra.map_top, IsScalarTower.adjoin_range_to_alg_hom, ht, Subalgebra.restrict_scalars_top]⟩

end

section AlgebraMapCoeffs

variable {R} (A) {ι M : Type _} [CommSemiringₓ R] [Semiringₓ A] [AddCommMonoidₓ M]

variable [Algebra R A] [Module A M] [Module R M] [IsScalarTower R A M]

variable (b : Basis ι R M) (h : Function.Bijective (algebraMap R A))

/-- If `R` and `A` have a bijective `algebra_map R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module. -/
@[simps]
noncomputable def Basis.algebraMapCoeffs : Basis ι A M :=
  b.mapCoeffs (RingEquiv.ofBijective _ h) fun c x => by
    simp

theorem Basis.algebra_map_coeffs_apply (i : ι) : b.algebraMapCoeffs A h i = b i :=
  b.map_coeffs_apply _ _ _

@[simp]
theorem Basis.coe_algebra_map_coeffs : (b.algebraMapCoeffs A h : ι → M) = b :=
  b.coe_map_coeffs _ _

end AlgebraMapCoeffs

section Semiringₓ

open Finsupp

open BigOperators Classical

universe v₁ w₁

variable {R S A}

variable [CommSemiringₓ R] [Semiringₓ S] [AddCommMonoidₓ A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem linear_independent_smul {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A} (hb : LinearIndependent R b)
    (hc : LinearIndependent S c) : LinearIndependent R fun p : ι × ι' => b p.1 • c p.2 := by
  rw [linear_independent_iff'] at hb hc
  rw [linear_independent_iff'']
  rintro s g hg hsg ⟨i, k⟩
  by_cases' hik : (i, k) ∈ s
  · have h1 : (∑ i in (s.image Prod.fst).product (s.image Prod.snd), g i • b i.1 • c i.2) = 0 := by
      rw [← hsg]
      exact
        ((Finset.sum_subset Finset.subset_product) fun p _ hp =>
            show g p • b p.1 • c p.2 = 0 by
              rw [hg p hp, zero_smul]).symm
    rw [Finset.sum_product_right] at h1
    simp_rw [← smul_assoc, ← Finset.sum_smul] at h1
    exact hb _ _ (hc _ _ h1 k (Finset.mem_image_of_mem _ hik)) i (Finset.mem_image_of_mem _ hik)
    
  exact hg _ hik

/-- `basis.smul (b : basis ι R S) (c : basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable def Basis.smul {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) : Basis (ι × ι') R A :=
  Basis.of_repr
    (c.repr.restrictScalars R ≪≫ₗ
      (Finsupp.lcongr (Equivₓ.refl _) b.repr ≪≫ₗ
        ((finsuppProdLequiv R).symm ≪≫ₗ Finsupp.lcongr (Equivₓ.prodComm ι' ι) (LinearEquiv.refl _ _))))

@[simp]
theorem Basis.smul_repr {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) (x ij) :
    (b.smul c).repr x ij = b.repr (c.repr x ij.2) ij.1 := by
  simp [← Basis.smul]

theorem Basis.smul_repr_mk {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) (x i j) :
    (b.smul c).repr x (i, j) = b.repr (c.repr x j) i :=
  b.smul_repr c x (i, j)

@[simp]
theorem Basis.smul_apply {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) (ij) :
    (b.smul c) ij = b ij.1 • c ij.2 := by
  obtain ⟨i, j⟩ := ij
  rw [Basis.apply_eq_iff]
  ext ⟨i', j'⟩
  rw [Basis.smul_repr, LinearEquiv.map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  dsimp' only
  split_ifs with hi
  · simp [← hi, ← Finsupp.single_apply]
    
  · simp [← hi]
    

end Semiringₓ

section Ringₓ

variable {R S}

variable [CommRingₓ R] [Ringₓ S] [Algebra R S]

theorem Basis.algebra_map_injective {ι : Type _} [NoZeroDivisors R] [Nontrivial S] (b : Basis ι R S) :
    Function.Injective (algebraMap R S) :=
  have : NoZeroSmulDivisors R S := b.NoZeroSmulDivisors
  NoZeroSmulDivisors.algebra_map_injective R S

end Ringₓ

section ArtinTate

variable (C : Type _)

section Semiringₓ

variable [CommSemiringₓ A] [CommSemiringₓ B] [Semiringₓ C]

variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

open Finset Submodule

open Classical

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (yi yj yk «expr ∈ » y)
theorem exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra A C).Fg) (hBC : (⊤ : Submodule B C).Fg) :
    ∃ B₀ : Subalgebra A B, B₀.Fg ∧ (⊤ : Submodule B₀ C).Fg := by
  cases' hAC with x hx
  cases' hBC with y hy
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f hf
  let s : Finset B := (Finset.product (x ∪ y * y) y).Image (Function.uncurry f)
  have hsx : ∀, ∀ xi ∈ x, ∀, ∀ yj ∈ y, ∀, f xi yj ∈ s := fun xi hxi yj hyj =>
    show Function.uncurry f (xi, yj) ∈ s from mem_image_of_mem _ <| mem_product.2 ⟨mem_union_left _ hxi, hyj⟩
  have hsy : ∀ (yi yj yk) (_ : yi ∈ y) (_ : yj ∈ y) (_ : yk ∈ y), f (yi * yj) yk ∈ s := fun yi hyi yj hyj yk hyk =>
    show Function.uncurry f (yi * yj, yk) ∈ s from
      mem_image_of_mem _ <| mem_product.2 ⟨mem_union_right _ <| Finset.mul_mem_mul hyi hyj, hyk⟩
  have hxy : ∀, ∀ xi ∈ x, ∀, xi ∈ span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    fun xi hxi =>
    hf xi ▸
      sum_mem fun yj hyj =>
        smul_mem (span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C))
          ⟨f xi yj, Algebra.subset_adjoin <| hsx xi hxi yj hyj⟩ (subset_span <| mem_insert_of_mem hyj)
  have hyy :
    span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) *
        span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) ≤
      span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    by
    rw [span_mul_span, span_le, coe_insert]
    rintro _ ⟨yi, yj, rfl | hyi, rfl | hyj, rfl⟩
    · rw [mul_oneₓ]
      exact subset_span (Set.mem_insert _ _)
      
    · rw [one_mulₓ]
      exact subset_span (Set.mem_insert_of_mem _ hyj)
      
    · rw [mul_oneₓ]
      exact subset_span (Set.mem_insert_of_mem _ hyi)
      
    · rw [← hf (yi * yj)]
      exact
        SetLike.mem_coe.2
          (sum_mem fun yk hyk =>
            smul_mem (span (Algebra.adjoin A (↑s : Set B)) (insert 1 ↑y : Set C))
              ⟨f (yi * yj) yk, Algebra.subset_adjoin <| hsy yi hyi yj hyj yk hyk⟩
              (subset_span <| Set.mem_insert_of_mem _ hyk : yk ∈ _))
      
  refine' ⟨Algebra.adjoin A (↑s : Set B), Subalgebra.fg_adjoin_finset _, insert 1 y, _⟩
  refine' restrict_scalars_injective A _ _ _
  rw [restrict_scalars_top, eq_top_iff, ← Algebra.top_to_submodule, ← hx, Algebra.adjoin_eq_span, span_le]
  refine' fun r hr =>
    Submonoid.closure_induction hr (fun c hc => hxy c hc) (subset_span <| mem_insert_self _ _) fun p q hp hq =>
      hyy <| Submodule.mul_mem_mul hp hq

end Semiringₓ

section Ringₓ

variable [CommRingₓ A] [CommRingₓ B] [CommRingₓ C]

variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Artin--Tate lemma: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).Fg) (hBC : (⊤ : Submodule B C).Fg)
    (hBCi : Function.Injective (algebraMap B C)) : (⊤ : Subalgebra A B).Fg :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
  Algebra.fg_trans' (B₀.fg_top.2 hAB₀) <|
    Subalgebra.fg_of_submodule_fg <|
      have : IsNoetherianRing B₀ := is_noetherian_ring_of_fg hAB₀
      have : IsNoetherian B₀ C := is_noetherian_of_fg_of_noetherian' hB₀C
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi

end Ringₓ

end ArtinTate

section AlgHomTower

variable {A} {C D : Type _} [CommSemiringₓ A] [CommSemiringₓ C] [CommSemiringₓ D] [Algebra A C] [Algebra A D]

variable (f : C →ₐ[A] D) (B) [CommSemiringₓ B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]

/-- Restrict the domain of an `alg_hom`. -/
def AlgHom.restrictDomain : B →ₐ[A] D :=
  f.comp (IsScalarTower.toAlgHom A B C)

/-- Extend the scalars of an `alg_hom`. -/
def AlgHom.extendScalars : @AlgHom B C D _ _ _ _ (f.restrictDomain B).toRingHom.toAlgebra :=
  { f with commutes' := fun _ => rfl }

variable {B}

/-- `alg_hom`s from the top of a tower are equivalent to a pair of `alg_hom`s. -/
def algHomEquivSigma : (C →ₐ[A] D) ≃ Σf : B →ₐ[A] D, @AlgHom B C D _ _ _ _ f.toRingHom.toAlgebra where
  toFun := fun f => ⟨f.restrictDomain B, f.extendScalars B⟩
  invFun := fun fg =>
    let alg := fg.1.toRingHom.toAlgebra
    fg.2.restrictScalars A
  left_inv := fun f => by
    dsimp' only
    ext
    rfl
  right_inv := by
    rintro ⟨⟨f, _, _, _, _, _⟩, g, _, _, _, _, hg⟩
    obtain rfl : f = fun x => g (algebraMap B C x) := by
      ext
      exact (hg x).symm
    rfl

end AlgHomTower

