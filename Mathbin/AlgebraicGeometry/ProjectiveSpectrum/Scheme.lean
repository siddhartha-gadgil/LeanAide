/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathbin.AlgebraicGeometry.Spec

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`       : the degree zero part of localized ring `Aₓ`

## Implementation

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any `f : A`, `Proj.T | (pbo f)` is homeomorphic to `Spec.T A⁰_f`:
  - forward direction :
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `x ∩ span {g / 1 | g ∈ A}` (see `Top_component.forward.carrier`). This ideal is prime, the proof
    is in `Top_component.forward.to_fun`. The fact that this function is continuous is found in
    `Top_component.forward`
  - backward direction : TBC

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Top_component.forward`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Top_component.forward.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero, then the preimage
  of `sbo a/f^m` under `forward f` is `pbo f ∩ pbo a`.


* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/


noncomputable section

namespace AlgebraicGeometry

open DirectSum BigOperators Pointwise BigOperators

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

variable {R A : Type _}

variable [CommRingₓ R] [CommRingₓ A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

open Top TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

-- mathport name: «exprProj»
local notation "Proj" => Proj.toLocallyRingedSpace 𝒜

-- mathport name: «exprProj.T»
-- `Proj` as a locally ringed space
local notation "Proj.T" => Proj.1.1.1

-- mathport name: «exprProj| »
-- the underlying topological space of `Proj`
local notation "Proj| " U => Proj.restrict (Opens.open_embedding (U : Opens Proj.T))

-- mathport name: «exprProj.T| »
-- `Proj` restrict to some open set
local notation "Proj.T| " U =>
  (Proj.restrict (Opens.open_embedding (U : Opens Proj.T))).toSheafedSpace.toPresheafedSpace.1

-- mathport name: «exprpbo »
-- the underlying topological space of `Proj` restricted to some open set
local notation "pbo" x => ProjectiveSpectrum.basicOpen 𝒜 x

-- mathport name: «exprsbo »
-- basic open sets in `Proj`
local notation "sbo" f => PrimeSpectrum.basicOpen f

-- mathport name: «exprSpec »
-- basic open sets in `Spec`
local notation "Spec" ring => Spec.locallyRingedSpaceObj (CommRingₓₓ.of Ringₓ)

-- mathport name: «exprSpec.T »
-- `Spec` as a locally ringed space
local notation "Spec.T" ring => (Spec.locallyRingedSpaceObj (CommRingₓₓ.of Ringₓ)).toSheafedSpace.toPresheafedSpace.1

-- the underlying topological space of `Spec`
section

variable {𝒜}

/-- The degree zero part of the localized ring `Aₓ` is the subring of elements of the form `a/x^n` such
that `a` and `x^n` have the same degree.
-/
def degreeZeroPart {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) : Subring (Away f) where
  Carrier := { y | ∃ (n : ℕ)(a : 𝒜 (m * n)), y = mk a.1 ⟨f ^ n, ⟨n, rfl⟩⟩ }
  mul_mem' := fun _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩ =>
    h.symm ▸
      h'.symm ▸
        ⟨n + n',
          ⟨⟨a.1 * b.1, (mul_addₓ m n n').symm ▸ mul_mem a.2 b.2⟩, by
            rw [mk_mul]
            congr 1
            simp only [← pow_addₓ]
            rfl⟩⟩
  one_mem' :=
    ⟨0, ⟨1, (mul_zero m).symm ▸ one_mem⟩, by
      symm
      convert ← mk_self 1
      simp only [← pow_zeroₓ]
      rfl⟩
  add_mem' := fun _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩ =>
    h.symm ▸
      h'.symm ▸
        ⟨n + n',
          ⟨⟨f ^ n * b.1 + f ^ n' * a.1,
              (mul_addₓ m n n').symm ▸
                add_mem
                  (mul_mem
                    (by
                      rw [mul_comm]
                      exact SetLike.GradedMonoid.pow_mem n f_deg)
                    b.2)
                  (by
                    rw [add_commₓ]
                    refine' mul_mem _ a.2
                    rw [mul_comm]
                    exact SetLike.GradedMonoid.pow_mem _ f_deg)⟩,
            by
            rw [add_mk]
            congr 1
            simp only [← pow_addₓ]
            rfl⟩⟩
  zero_mem' := ⟨0, ⟨0, (mk_zero _).symm⟩⟩
  neg_mem' := fun x ⟨n, ⟨a, h⟩⟩ => h.symm ▸ ⟨n, ⟨-a, neg_mk _ _⟩⟩

end

-- mathport name: «exprA⁰_ »
local notation "A⁰_" f_deg => degreeZeroPart f_deg

section

variable {𝒜}

instance (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) : CommRingₓ (A⁰_f_deg) :=
  (degreeZeroPart f_deg).toCommRing

/-- Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks this natural number `n`
-/
def degreeZeroPart.deg {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_f_deg) : ℕ :=
  x.2.some

/-- Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks the numerator `a`
-/
def degreeZeroPart.num {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_f_deg) : A :=
  x.2.some_spec.some.1

theorem degreeZeroPart.num_mem {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_f_deg) :
    degreeZeroPart.num x ∈ 𝒜 (m * degreeZeroPart.deg x) :=
  x.2.some_spec.some.2

theorem degreeZeroPart.eq {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_f_deg) :
    (x : Away f) = mk (degreeZeroPart.num x) ⟨f ^ degreeZeroPart.deg x, ⟨_, rfl⟩⟩ :=
  x.2.some_spec.some_spec

theorem degreeZeroPart.coe_mul {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x y : A⁰_f_deg) : (↑(x * y) : Away f) = x * y :=
  rfl

end

namespace ProjIsoSpecTopComponent

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/
namespace ToSpec

open Ideal

-- This section is to construct the forward direction :
-- So for any `x` in `Proj| (pbo f)`, we need some point in `Spec A⁰_f`, i.e. a prime ideal,
-- and we need this correspondence to be continuous in their Zariski topology.
variable {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : Proj| pbo f)

/-- For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `Top_component.forward.to_fun`-/
def carrier : Ideal (A⁰_f_deg) :=
  Ideal.comap (algebraMap (A⁰_f_deg) (Away f)) (Ideal.span <| algebraMap A (Away f) '' x.1.asHomogeneousIdeal)

theorem mem_carrier_iff (z : A⁰_f_deg) :
    z ∈ carrier f_deg x ↔ ↑z ∈ Ideal.span (algebraMap A (Away f) '' x.1.asHomogeneousIdeal) :=
  Iff.rfl

theorem MemCarrier.clear_denominator [DecidableEq (Away f)] {z : A⁰_f_deg} (hz : z ∈ carrier f_deg x) :
    ∃ (c : algebraMap A (Away f) '' x.1.asHomogeneousIdeal →₀ Away f)(N : ℕ)(acd : ∀, ∀ y ∈ c.Support.Image c, ∀, A),
      f ^ N • ↑z =
        algebraMap A (Away f)
          (∑ i in c.Support.attach, acd (c i) (Finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * Classical.some i.1.2) :=
  by
  rw [mem_carrier_iff, ← submodule_span_eq, Finsupp.span_eq_range_total, LinearMap.mem_range] at hz
  rcases hz with ⟨c, eq1⟩
  rw [Finsupp.total_apply, Finsupp.sum] at eq1
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers f) (c.support.image c)
  choose acd hacd using hN
  have prop1 : ∀ i, i ∈ c.support → c i ∈ Finset.image c c.support := by
    intro i hi
    rw [Finset.mem_image]
    refine' ⟨_, hi, rfl⟩
  refine' ⟨c, N, acd, _⟩
  rw [← eq1, smul_sum, map_sum, ← sum_attach]
  congr 1
  ext i
  rw [_root_.map_mul, hacd, (Classical.some_spec i.1.2).2, smul_eq_mul, smul_mul_assoc]
  rfl

theorem disjoint : Disjoint (x.1.asHomogeneousIdeal.toIdeal : Set A) (Submonoid.powers f : Set A) := by
  by_contra rid
  rw [Set.not_disjoint_iff] at rid
  choose g hg using rid
  obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg
  by_cases' k_ineq : 0 < k
  · erw [x.1.IsPrime.pow_mem_iff_mem _ k_ineq] at hg1
    exact x.2 hg1
    
  · erw
      [show k = 0 by
        linarith,
      pow_zeroₓ, ← Ideal.eq_top_iff_one] at hg1
    apply x.1.IsPrime.1
    exact hg1
    

theorem carrier_ne_top : carrier f_deg x ≠ ⊤ := by
  have eq_top := Disjoint x
  classical
  contrapose! eq_top
  obtain ⟨c, N, acd, eq1⟩ := mem_carrier.clear_denominator _ x ((Ideal.eq_top_iff_one _).mp eq_top)
  rw [Algebra.smul_def, Subring.coe_one, mul_oneₓ] at eq1
  change Localization.mk (f ^ N) 1 = mk (∑ _, _) 1 at eq1
  simp only [← mk_eq_mk', ← IsLocalization.eq] at eq1
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
  erw [mul_oneₓ, mul_oneₓ] at eq1
  change f ^ _ * f ^ _ = _ * f ^ _ at eq1
  rw [Set.not_disjoint_iff_nonempty_inter]
  refine'
    ⟨f ^ N * f ^ M, eq1.symm ▸ mul_mem_right _ _ (sum_mem _ fun i hi => mul_mem_left _ _ _),
      ⟨N + M, by
        rw [pow_addₓ]⟩⟩
  generalize_proofs h
  exact (Classical.some_spec h).1

/-- The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.
-/
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_f_deg :=
  ⟨carrier f_deg x, carrier_ne_top f_deg x, fun x1 x2 hx12 => by
    classical
    rcases x1, x2 with ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩
    induction' x1 using Localization.induction_on with data_x1
    induction' x2 using Localization.induction_on with data_x2
    rcases data_x1, data_x2 with ⟨⟨a1, _, ⟨n1, rfl⟩⟩, ⟨a2, _, ⟨n2, rfl⟩⟩⟩
    rcases mem_carrier.clear_denominator f_deg x hx12 with ⟨c, N, acd, eq1⟩
    simp only [← degree_zero_part.coe_mul, ← Algebra.smul_def] at eq1
    change Localization.mk (f ^ N) 1 * (mk _ _ * mk _ _) = mk (∑ _, _) _ at eq1
    simp only [← Localization.mk_mul, ← one_mulₓ] at eq1
    simp only [← mk_eq_mk', ← IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
    rw [Submonoid.coe_one, mul_oneₓ] at eq1
    change _ * _ * f ^ _ = _ * (f ^ _ * f ^ _) * f ^ _ at eq1
    rcases x.1.IsPrime.mem_or_mem (show a1 * a2 * f ^ N * f ^ M ∈ _ from _) with (h1 | rid2)
    rcases x.1.IsPrime.mem_or_mem h1 with (h1 | rid1)
    rcases x.1.IsPrime.mem_or_mem h1 with (h1 | h2)
    · left
      rw [mem_carrier_iff]
      simp only [←
        show (mk a1 ⟨f ^ n1, _⟩ : away f) = mk a1 1 * mk 1 ⟨f ^ n1, ⟨n1, rfl⟩⟩ by
          rw [Localization.mk_mul, mul_oneₓ, one_mulₓ]]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, h1, rfl⟩)
      
    · right
      rw [mem_carrier_iff]
      simp only [←
        show (mk a2 ⟨f ^ n2, _⟩ : away f) = mk a2 1 * mk 1 ⟨f ^ n2, ⟨n2, rfl⟩⟩ by
          rw [Localization.mk_mul, mul_oneₓ, one_mulₓ]]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, h2, rfl⟩)
      
    · exact False.elim (x.2 (x.1.IsPrime.mem_of_pow_mem N rid1))
      
    · exact False.elim (x.2 (x.1.IsPrime.mem_of_pow_mem M rid2))
      
    · rw [mul_comm _ (f ^ N), eq1]
      refine' mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ fun i hi => mul_mem_left _ _ _))
      generalize_proofs h
      exact (Classical.some_spec h).1
      ⟩

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in  `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
theorem preimage_eq (a : A) (n : ℕ) (a_mem_degree_zero : (mk a ⟨f ^ n, ⟨n, rfl⟩⟩ : Away f) ∈ A⁰_f_deg) :
    toFun 𝒜 f_deg ⁻¹'
        (sbo(⟨mk a ⟨f ^ n, ⟨_, rfl⟩⟩, a_mem_degree_zero⟩ : A⁰_f_deg) : Set (PrimeSpectrum { x // x ∈ A⁰_f_deg })) =
      { x | x.1 ∈ (pbo f)⊓pbo a } :=
  by
  classical
  ext1 y
  constructor <;> intro hy
  · refine' ⟨y.2, _⟩
    rw [Set.mem_preimage, opens.mem_coe, PrimeSpectrum.mem_basic_open] at hy
    rw [ProjectiveSpectrum.mem_coe_basic_open]
    intro a_mem_y
    apply hy
    rw [to_fun, mem_carrier_iff]
    simp only [←
      show (mk a ⟨f ^ n, ⟨_, rfl⟩⟩ : away f) = mk 1 ⟨f ^ n, ⟨_, rfl⟩⟩ * mk a 1 by
        rw [mk_mul, one_mulₓ, mul_oneₓ]]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, a_mem_y, rfl⟩)
    
  · change y.1 ∈ _ at hy
    rcases hy with ⟨hy1, hy2⟩
    rw [ProjectiveSpectrum.mem_coe_basic_open] at hy1 hy2
    rw [Set.mem_preimage, to_fun, opens.mem_coe, PrimeSpectrum.mem_basic_open]
    intro rid
    rcases mem_carrier.clear_denominator f_deg _ rid with ⟨c, N, acd, eq1⟩
    rw [Algebra.smul_def] at eq1
    change Localization.mk (f ^ N) 1 * mk _ _ = mk (∑ _, _) _ at eq1
    rw [mk_mul, one_mulₓ, mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
    rw [Submonoid.coe_one, mul_oneₓ] at eq1
    simp only [← Subtype.coe_mk] at eq1
    rcases y.1.IsPrime.mem_or_mem (show a * f ^ N * f ^ M ∈ _ from _) with (H1 | H3)
    rcases y.1.IsPrime.mem_or_mem H1 with (H1 | H2)
    · exact hy2 H1
      
    · exact y.2 (y.1.IsPrime.mem_of_pow_mem N H2)
      
    · exact y.2 (y.1.IsPrime.mem_of_pow_mem M H3)
      
    · rw [mul_comm _ (f ^ N), eq1]
      refine' mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ fun i hi => mul_mem_left _ _ _))
      generalize_proofs h
      exact (Classical.some_spec h).1
      
    

end ToSpec

section

variable {𝒜}

/-- The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
open set in `Spec A⁰_f`.
-/
def toSpec {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) : (Proj.T| pbo f) ⟶ Spec.T A⁰_f_deg where
  toFun := ToSpec.toFun 𝒜 f_deg
  continuous_to_fun := by
    apply is_topological_basis.continuous PrimeSpectrum.is_topological_basis_basic_opens
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    induction' g using Localization.induction_on with data
    obtain ⟨a, ⟨_, ⟨n, rfl⟩⟩⟩ := data
    erw [to_Spec.preimage_eq]
    refine' is_open_induced_iff.mpr ⟨(pbo f).1⊓(pbo a).1, IsOpen.inter (pbo f).2 (pbo a).2, _⟩
    ext z
    constructor <;> intro hz <;> simpa [← Set.mem_preimage]

end

end ProjIsoSpecTopComponent

end AlgebraicGeometry

