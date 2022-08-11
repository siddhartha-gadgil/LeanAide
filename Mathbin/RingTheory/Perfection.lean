/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.CharP.Pi
import Mathbin.Algebra.CharP.Quotient
import Mathbin.Algebra.CharP.Subring
import Mathbin.Algebra.Ring.Pi
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.FieldTheory.PerfectClosure
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Subring.Basic
import Mathbin.RingTheory.Valuation.Integers

/-!
# Ring Perfection and Tilt

In this file we define the perfection of a ring of characteristic p, and the tilt of a field
given a valuation to `ℝ≥0`.

## TODO

Define the valuation on the tilt, and define a characteristic predicate for the tilt.

-/


universe u₁ u₂ u₃ u₄

open Nnreal

/-- The perfection of a monoid `M`, defined to be the projective limit of `M`
using the `p`-th power maps `M → M` indexed by the natural numbers, implemented as
`{ f : ℕ → M | ∀ n, f (n + 1) ^ p = f n }`. -/
def Monoidₓ.perfection (M : Type u₁) [CommMonoidₓ M] (p : ℕ) : Submonoid (ℕ → M) where
  Carrier := { f | ∀ n, f (n + 1) ^ p = f n }
  one_mem' := fun n => one_pow _
  mul_mem' := fun f g hf hg n => (mul_powₓ _ _ _).trans <| congr_arg2ₓ _ (hf n) (hg n)

/-- The perfection of a ring `R` with characteristic `p`, as a subsemiring,
defined to be the projective limit of `R` using the Frobenius maps `R → R`
indexed by the natural numbers, implemented as `{ f : ℕ → R | ∀ n, f (n + 1) ^ p = f n }`. -/
def Ringₓ.perfectionSubsemiring (R : Type u₁) [CommSemiringₓ R] (p : ℕ) [hp : Fact p.Prime] [CharP R p] :
    Subsemiring (ℕ → R) :=
  { Monoidₓ.perfection R p with zero_mem' := fun n => zero_pow <| hp.1.Pos,
    add_mem' := fun f g hf hg n => (frobenius_add R p _ _).trans <| congr_arg2ₓ _ (hf n) (hg n) }

/-- The perfection of a ring `R` with characteristic `p`, as a subring,
defined to be the projective limit of `R` using the Frobenius maps `R → R`
indexed by the natural numbers, implemented as `{ f : ℕ → R | ∀ n, f (n + 1) ^ p = f n }`. -/
def Ringₓ.perfectionSubring (R : Type u₁) [CommRingₓ R] (p : ℕ) [hp : Fact p.Prime] [CharP R p] : Subring (ℕ → R) :=
  (Ringₓ.perfectionSubsemiring R p).toSubring fun n => by
    simp_rw [← frobenius_def, Pi.neg_apply, Pi.one_apply, RingHom.map_neg, RingHom.map_one]

/-- The perfection of a ring `R` with characteristic `p`,
defined to be the projective limit of `R` using the Frobenius maps `R → R`
indexed by the natural numbers, implemented as `{f : ℕ → R // ∀ n, f (n + 1) ^ p = f n}`. -/
def Ringₓ.Perfection (R : Type u₁) [CommSemiringₓ R] (p : ℕ) : Type u₁ :=
  { f // ∀ n : ℕ, (f : ℕ → R) (n + 1) ^ p = f n }

namespace Perfection

variable (R : Type u₁) [CommSemiringₓ R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

include hp

instance : CommSemiringₓ (Ringₓ.Perfection R p) :=
  (Ringₓ.perfectionSubsemiring R p).toCommSemiring

instance : CharP (Ringₓ.Perfection R p) p :=
  CharP.subsemiring (ℕ → R) p (Ringₓ.perfectionSubsemiring R p)

instance ring (R : Type u₁) [CommRingₓ R] [CharP R p] : Ringₓ (Ringₓ.Perfection R p) :=
  (Ringₓ.perfectionSubring R p).toRing

instance commRing (R : Type u₁) [CommRingₓ R] [CharP R p] : CommRingₓ (Ringₓ.Perfection R p) :=
  (Ringₓ.perfectionSubring R p).toCommRing

instance : Inhabited (Ringₓ.Perfection R p) :=
  ⟨0⟩

/-- The `n`-th coefficient of an element of the perfection. -/
def coeff (n : ℕ) : Ringₓ.Perfection R p →+* R where
  toFun := fun f => f.1 n
  map_one' := rfl
  map_mul' := fun f g => rfl
  map_zero' := rfl
  map_add' := fun f g => rfl

variable {R p}

@[ext]
theorem ext {f g : Ringₓ.Perfection R p} (h : ∀ n, coeff R p n f = coeff R p n g) : f = g :=
  Subtype.eq <| funext h

variable (R p)

/-- The `p`-th root of an element of the perfection. -/
def pthRoot : Ringₓ.Perfection R p →+* Ringₓ.Perfection R p where
  toFun := fun f => ⟨fun n => coeff R p (n + 1) f, fun n => f.2 _⟩
  map_one' := rfl
  map_mul' := fun f g => rfl
  map_zero' := rfl
  map_add' := fun f g => rfl

variable {R p}

@[simp]
theorem coeff_mk (f : ℕ → R) (hf) (n : ℕ) : coeff R p n ⟨f, hf⟩ = f n :=
  rfl

theorem coeff_pth_root (f : Ringₓ.Perfection R p) (n : ℕ) : coeff R p n (pthRoot R p f) = coeff R p (n + 1) f :=
  rfl

theorem coeff_pow_p (f : Ringₓ.Perfection R p) (n : ℕ) : coeff R p (n + 1) (f ^ p) = coeff R p n f := by
  rw [RingHom.map_pow]
  exact f.2 n

theorem coeff_pow_p' (f : Ringₓ.Perfection R p) (n : ℕ) : coeff R p (n + 1) f ^ p = coeff R p n f :=
  f.2 n

theorem coeff_frobenius (f : Ringₓ.Perfection R p) (n : ℕ) : coeff R p (n + 1) (frobenius _ p f) = coeff R p n f := by
  apply coeff_pow_p f n

-- `coeff_pow_p f n` also works but is slow!
theorem coeff_iterate_frobenius (f : Ringₓ.Perfection R p) (n m : ℕ) :
    coeff R p (n + m) ((frobenius _ p^[m]) f) = coeff R p n f :=
  (Nat.recOn m rfl) fun m ih => by
    erw [Function.iterate_succ_apply', coeff_frobenius, ih]

theorem coeff_iterate_frobenius' (f : Ringₓ.Perfection R p) (n m : ℕ) (hmn : m ≤ n) :
    coeff R p n ((frobenius _ p^[m]) f) = coeff R p (n - m) f :=
  Eq.symm <| (coeff_iterate_frobenius _ _ m).symm.trans <| (tsub_add_cancel_of_le hmn).symm ▸ rfl

theorem pth_root_frobenius : (pthRoot R p).comp (frobenius _ p) = RingHom.id _ :=
  RingHom.ext fun x =>
    ext fun n => by
      rw [RingHom.comp_apply, RingHom.id_apply, coeff_pth_root, coeff_frobenius]

theorem frobenius_pth_root : (frobenius _ p).comp (pthRoot R p) = RingHom.id _ :=
  RingHom.ext fun x =>
    ext fun n => by
      rw [RingHom.comp_apply, RingHom.id_apply, RingHom.map_frobenius, coeff_pth_root, ← RingHom.map_frobenius,
        coeff_frobenius]

theorem coeff_add_ne_zero {f : Ringₓ.Perfection R p} {n : ℕ} (hfn : coeff R p n f ≠ 0) (k : ℕ) :
    coeff R p (n + k) f ≠ 0 :=
  (Nat.recOn k hfn) fun k ih h =>
    ih <| by
      erw [← coeff_pow_p, RingHom.map_pow, h, zero_pow hp.1.Pos]

theorem coeff_ne_zero_of_le {f : Ringₓ.Perfection R p} {m n : ℕ} (hfm : coeff R p m f ≠ 0) (hmn : m ≤ n) :
    coeff R p n f ≠ 0 :=
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  hk.symm ▸ coeff_add_ne_zero hfm k

variable (R p)

instance perfectRing : PerfectRing (Ringₓ.Perfection R p) p where
  pthRoot' := pthRoot R p
  frobenius_pth_root' := congr_fun <| congr_arg RingHom.toFun <| @frobenius_pth_root R _ p _ _
  pth_root_frobenius' := congr_fun <| congr_arg RingHom.toFun <| @pth_root_frobenius R _ p _ _

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* perfection S p`. -/
@[simps]
def lift (R : Type u₁) [CommSemiringₓ R] [CharP R p] [PerfectRing R p] (S : Type u₂) [CommSemiringₓ S] [CharP S p] :
    (R →+* S) ≃ (R →+* Ringₓ.Perfection S p) where
  toFun := fun f =>
    { toFun := fun r =>
        ⟨fun n => f <| (pthRoot R p^[n]) r, fun n => by
          rw [← f.map_pow, Function.iterate_succ_apply', pth_root_pow_p]⟩,
      map_one' := ext fun n => (congr_arg f <| RingHom.iterate_map_one _ _).trans f.map_one,
      map_mul' := fun x y => ext fun n => (congr_arg f <| RingHom.iterate_map_mul _ _ _ _).trans <| f.map_mul _ _,
      map_zero' := ext fun n => (congr_arg f <| RingHom.iterate_map_zero _ _).trans f.map_zero,
      map_add' := fun x y => ext fun n => (congr_arg f <| RingHom.iterate_map_add _ _ _ _).trans <| f.map_add _ _ }
  invFun := RingHom.comp <| coeff S p 0
  left_inv := fun f => RingHom.ext fun r => rfl
  right_inv := fun f =>
    RingHom.ext fun r =>
      ext fun n =>
        show coeff S p 0 (f ((pthRoot R p^[n]) r)) = coeff S p n (f r) by
          rw [← coeff_iterate_frobenius _ 0 n, zero_addₓ, ← RingHom.map_iterate_frobenius,
            right_inverse_pth_root_frobenius.iterate]

theorem hom_ext {R : Type u₁} [CommSemiringₓ R] [CharP R p] [PerfectRing R p] {S : Type u₂} [CommSemiringₓ S]
    [CharP S p] {f g : R →+* Ringₓ.Perfection S p} (hfg : ∀ x, coeff S p 0 (f x) = coeff S p 0 (g x)) : f = g :=
  (lift p R S).symm.Injective <| RingHom.ext hfg

variable {R} {S : Type u₂} [CommSemiringₓ S] [CharP S p]

/-- A ring homomorphism `R →+* S` induces `perfection R p →+* perfection S p` -/
@[simps]
def map (φ : R →+* S) : Ringₓ.Perfection R p →+* Ringₓ.Perfection S p where
  toFun := fun f =>
    ⟨fun n => φ (coeff R p n f), fun n => by
      rw [← φ.map_pow, coeff_pow_p']⟩
  map_one' := Subtype.eq <| funext fun n => φ.map_one
  map_mul' := fun f g => Subtype.eq <| funext fun n => φ.map_mul _ _
  map_zero' := Subtype.eq <| funext fun n => φ.map_zero
  map_add' := fun f g => Subtype.eq <| funext fun n => φ.map_add _ _

theorem coeff_map (φ : R →+* S) (f : Ringₓ.Perfection R p) (n : ℕ) : coeff S p n (map p φ f) = φ (coeff R p n f) :=
  rfl

end Perfection

/-- A perfection map to a ring of characteristic `p` is a map that is isomorphic
to its perfection. -/
@[nolint has_inhabited_instance]
structure PerfectionMap (p : ℕ) [Fact p.Prime] {R : Type u₁} [CommSemiringₓ R] [CharP R p] {P : Type u₂}
  [CommSemiringₓ P] [CharP P p] [PerfectRing P p] (π : P →+* R) : Prop where
  Injective : ∀ ⦃x y : P⦄, (∀ n, π ((pthRoot P p^[n]) x) = π ((pthRoot P p^[n]) y)) → x = y
  Surjective : ∀ f : ℕ → R, (∀ n, f (n + 1) ^ p = f n) → ∃ x : P, ∀ n, π ((pthRoot P p^[n]) x) = f n

namespace PerfectionMap

variable {p : ℕ} [Fact p.Prime]

variable {R : Type u₁} [CommSemiringₓ R] [CharP R p]

variable {P : Type u₃} [CommSemiringₓ P] [CharP P p] [PerfectRing P p]

/-- Create a `perfection_map` from an isomorphism to the perfection. -/
@[simps]
theorem mk' {f : P →+* R} (g : P ≃+* Ringₓ.Perfection R p) (hfg : Perfection.lift p P R f = g) : PerfectionMap p f :=
  { Injective := fun x y hxy =>
      g.Injective <|
        (RingHom.ext_iff.1 hfg x).symm.trans <|
          Eq.symm <| (RingHom.ext_iff.1 hfg y).symm.trans <| Perfection.ext fun n => (hxy n).symm,
    Surjective := fun y hy =>
      let ⟨x, hx⟩ := g.Surjective ⟨y, hy⟩
      ⟨x, fun n =>
        show Perfection.coeff R p n (Perfection.lift p P R f x) = Perfection.coeff R p n ⟨y, hy⟩ by
          rw [hfg, ← coe_fn_coe_base, hx]⟩ }

variable (p R P)

/-- The canonical perfection map from the perfection of a ring. -/
theorem of : PerfectionMap p (Perfection.coeff R p 0) :=
  mk' (RingEquiv.refl _) <| (Equivₓ.apply_eq_iff_eq_symm_apply _).2 rfl

/-- For a perfect ring, it itself is the perfection. -/
theorem id [PerfectRing R p] : PerfectionMap p (RingHom.id R) :=
  { Injective := fun x y hxy => hxy 0,
    Surjective := fun f hf =>
      ⟨f 0, fun n =>
        show (pthRoot R p^[n]) (f 0) = f n from
          (Nat.recOn n rfl) fun n ih =>
            injective_pow_p p <| by
              rw [Function.iterate_succ_apply', pth_root_pow_p _, ih, hf]⟩ }

variable {p R P}

/-- A perfection map induces an isomorphism to the prefection. -/
noncomputable def equiv {π : P →+* R} (m : PerfectionMap p π) : P ≃+* Ringₓ.Perfection R p :=
  RingEquiv.ofBijective (Perfection.lift p P R π)
    ⟨fun x y hxy => m.Injective fun n => (congr_arg (Perfection.coeff R p n) hxy : _), fun f =>
      let ⟨x, hx⟩ := m.Surjective f.1 f.2
      ⟨x, Perfection.ext <| hx⟩⟩

theorem equiv_apply {π : P →+* R} (m : PerfectionMap p π) (x : P) : m.Equiv x = Perfection.lift p P R π x :=
  rfl

theorem comp_equiv {π : P →+* R} (m : PerfectionMap p π) (x : P) : Perfection.coeff R p 0 (m.Equiv x) = π x :=
  rfl

theorem comp_equiv' {π : P →+* R} (m : PerfectionMap p π) : (Perfection.coeff R p 0).comp ↑m.Equiv = π :=
  RingHom.ext fun x => rfl

theorem comp_symm_equiv {π : P →+* R} (m : PerfectionMap p π) (f : Ringₓ.Perfection R p) :
    π (m.Equiv.symm f) = Perfection.coeff R p 0 f :=
  (m.comp_equiv _).symm.trans <| congr_arg _ <| m.Equiv.apply_symm_apply f

theorem comp_symm_equiv' {π : P →+* R} (m : PerfectionMap p π) : π.comp ↑m.Equiv.symm = Perfection.coeff R p 0 :=
  RingHom.ext m.comp_symm_equiv

variable (p R P)

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* P`,
where `P` is any perfection of `S`. -/
@[simps]
noncomputable def lift [PerfectRing R p] (S : Type u₂) [CommSemiringₓ S] [CharP S p] (P : Type u₃) [CommSemiringₓ P]
    [CharP P p] [PerfectRing P p] (π : P →+* S) (m : PerfectionMap p π) : (R →+* S) ≃ (R →+* P) where
  toFun := fun f => RingHom.comp ↑m.Equiv.symm <| Perfection.lift p R S f
  invFun := fun f => π.comp f
  left_inv := fun f => by
    simp_rw [← RingHom.comp_assoc, comp_symm_equiv']
    exact (Perfection.lift p R S).symm_apply_apply f
  right_inv := fun f =>
    RingHom.ext fun x =>
      m.Equiv.Injective <|
        (m.Equiv.apply_symm_apply _).trans <|
          show Perfection.lift p R S (π.comp f) x = RingHom.comp (↑m.Equiv) f x from
            RingHom.ext_iff.1 ((Perfection.lift p R S).apply_eq_iff_eq_symm_apply.2 rfl) _

variable {R p}

theorem hom_ext [PerfectRing R p] {S : Type u₂} [CommSemiringₓ S] [CharP S p] {P : Type u₃} [CommSemiringₓ P]
    [CharP P p] [PerfectRing P p] (π : P →+* S) (m : PerfectionMap p π) {f g : R →+* P} (hfg : ∀ x, π (f x) = π (g x)) :
    f = g :=
  (lift p R S P π m).symm.Injective <| RingHom.ext hfg

variable {R P} (p) {S : Type u₂} [CommSemiringₓ S] [CharP S p]

variable {Q : Type u₄} [CommSemiringₓ Q] [CharP Q p] [PerfectRing Q p]

/-- A ring homomorphism `R →+* S` induces `P →+* Q`, a map of the respective perfections. -/
@[nolint unused_arguments]
noncomputable def map {π : P →+* R} (m : PerfectionMap p π) {σ : Q →+* S} (n : PerfectionMap p σ) (φ : R →+* S) :
    P →+* Q :=
  lift p P S Q σ n <| φ.comp π

theorem comp_map {π : P →+* R} (m : PerfectionMap p π) {σ : Q →+* S} (n : PerfectionMap p σ) (φ : R →+* S) :
    σ.comp (map p m n φ) = φ.comp π :=
  (lift p P S Q σ n).symm_apply_apply _

theorem map_map {π : P →+* R} (m : PerfectionMap p π) {σ : Q →+* S} (n : PerfectionMap p σ) (φ : R →+* S) (x : P) :
    σ (map p m n φ x) = φ (π x) :=
  RingHom.ext_iff.1 (comp_map p m n φ) x

-- Why is this slow?
theorem map_eq_map (φ : R →+* S) : @map p _ R _ _ _ _ _ _ S _ _ _ _ _ _ _ (of p R) _ (of p S) φ = Perfection.map p φ :=
  (hom_ext _ (of p S)) fun f => by
    rw [map_map, Perfection.coeff_map]

end PerfectionMap

section Perfectoid

variable (K : Type u₁) [Field K] (v : Valuation K ℝ≥0 )

variable (O : Type u₂) [CommRingₓ O] [Algebra O K] (hv : v.Integers O)

variable (p : ℕ)

include hv

/-- `O/(p)` for `O`, ring of integers of `K`. -/
@[nolint unused_arguments has_inhabited_instance]
def ModP :=
  O ⧸ (Ideal.span {p} : Ideal O)

variable [hp : Fact p.Prime] [hvp : Fact (v p ≠ 1)]

namespace ModP

instance : CommRingₓ (ModP K v O hv p) :=
  Ideal.Quotient.commRing _

include hp hvp

instance : CharP (ModP K v O hv p) p :=
  CharP.quotient O p <| mt hv.one_of_is_unit <| (map_nat_cast (algebraMap O K) p).symm ▸ hvp.1

instance : Nontrivial (ModP K v O hv p) :=
  CharP.nontrivial_of_char_ne_one hp.1.ne_one

section Classical

attribute [local instance] Classical.dec

omit hp hvp

/-- For a field `K` with valuation `v : K → ℝ≥0` and ring of integers `O`,
a function `O/(p) → ℝ≥0` that sends `0` to `0` and `x + (p)` to `v(x)` as long as `x ∉ (p)`. -/
noncomputable def preVal (x : ModP K v O hv p) : ℝ≥0 :=
  if x = 0 then 0 else v (algebraMap O K x.out')

variable {K v O hv p}

theorem pre_val_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP K v O hv p) ≠ 0) :
    preVal K v O hv p (Ideal.Quotient.mk _ x) = v (algebraMap O K x) := by
  obtain ⟨r, hr⟩ :=
    Ideal.mem_span_singleton'.1
      (Ideal.Quotient.eq.1 <| Quotientₓ.sound' <| @Quotientₓ.mk_out' O (Ideal.span {p} : Ideal O).quotientRel x)
  refine' (if_neg hx).trans (v.map_eq_of_sub_lt <| lt_of_not_le _)
  erw [← RingHom.map_sub, ← hr, hv.le_iff_dvd]
  exact fun hprx => hx (Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 <| dvd_of_mul_left_dvd hprx)

theorem pre_val_zero : preVal K v O hv p 0 = 0 :=
  if_pos rfl

theorem pre_val_mul {x y : ModP K v O hv p} (hxy0 : x * y ≠ 0) :
    preVal K v O hv p (x * y) = preVal K v O hv p x * preVal K v O hv p y := by
  have hx0 : x ≠ 0 :=
    mt
      (by
        rintro rfl
        rw [zero_mul])
      hxy0
  have hy0 : y ≠ 0 :=
    mt
      (by
        rintro rfl
        rw [mul_zero])
      hxy0
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← RingHom.map_mul] at hxy0⊢
  rw [pre_val_mk hx0, pre_val_mk hy0, pre_val_mk hxy0, RingHom.map_mul, v.map_mul]

theorem pre_val_add (x y : ModP K v O hv p) :
    preVal K v O hv p (x + y) ≤ max (preVal K v O hv p x) (preVal K v O hv p y) := by
  by_cases' hx0 : x = 0
  · rw [hx0, zero_addₓ]
    exact le_max_rightₓ _ _
    
  by_cases' hy0 : y = 0
  · rw [hy0, add_zeroₓ]
    exact le_max_leftₓ _ _
    
  by_cases' hxy0 : x + y = 0
  · rw [hxy0, pre_val_zero]
    exact zero_le _
    
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← RingHom.map_add] at hxy0⊢
  rw [pre_val_mk hx0, pre_val_mk hy0, pre_val_mk hxy0, RingHom.map_add]
  exact v.map_add _ _

theorem v_p_lt_pre_val {x : ModP K v O hv p} : v p < preVal K v O hv p x ↔ x ≠ 0 := by
  refine'
    ⟨fun h hx => by
      rw [hx, pre_val_zero] at h
      exact not_lt_zero' h, fun h => lt_of_not_le fun hp => h _⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pre_val_mk h, ← map_nat_cast (algebraMap O K) p, hv.le_iff_dvd] at hp
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact hp

theorem pre_val_eq_zero {x : ModP K v O hv p} : preVal K v O hv p x = 0 ↔ x = 0 :=
  ⟨fun hvx =>
    Classical.by_contradiction fun hx0 : x ≠ 0 => by
      rw [← v_p_lt_pre_val, hvx] at hx0
      exact not_lt_zero' hx0,
    fun hx => hx.symm ▸ pre_val_zero⟩

variable (hv hvp)

theorem v_p_lt_val {x : O} : v p < v (algebraMap O K x) ↔ (Ideal.Quotient.mk _ x : ModP K v O hv p) ≠ 0 := by
  rw [lt_iff_not_le, not_iff_not, ← map_nat_cast (algebraMap O K) p, hv.le_iff_dvd, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

open Nnreal

variable {hv} (hvp)

include hp

theorem mul_ne_zero_of_pow_p_ne_zero {x y : ModP K v O hv p} (hx : x ^ p ≠ 0) (hy : y ^ p ≠ 0) : x * y ≠ 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1p : (0 : ℝ) < 1 / p := one_div_pos.2 (Nat.cast_pos.2 hp.1.Pos)
  rw [← RingHom.map_mul]
  rw [← RingHom.map_pow] at hx hy
  rw [← v_p_lt_val hv] at hx hy⊢
  rw [RingHom.map_pow, v.map_pow, ← rpow_lt_rpow_iff h1p, ← rpow_nat_cast, ← rpow_mul,
    mul_one_div_cancel (Nat.cast_ne_zero.2 hp.1.ne_zero : (p : ℝ) ≠ 0), rpow_one] at hx hy
  rw [RingHom.map_mul, v.map_mul]
  refine' lt_of_le_of_ltₓ _ (mul_lt_mul₀ hx hy)
  by_cases' hvp : v p = 0
  · rw [hvp]
    exact zero_le _
    
  replace hvp := zero_lt_iff.2 hvp
  conv_lhs => rw [← rpow_one (v p)]
  rw [← rpow_add (ne_of_gtₓ hvp)]
  refine' rpow_le_rpow_of_exponent_ge hvp (map_nat_cast (algebraMap O K) p ▸ hv.2 _) _
  rw [← add_div, div_le_one (Nat.cast_pos.2 hp.1.Pos : 0 < (p : ℝ))]
  exact_mod_cast hp.1.two_le

end Classical

end ModP

/-- Perfection of `O/(p)` where `O` is the ring of integers of `K`. -/
@[nolint has_inhabited_instance]
def PreTilt :=
  Ringₓ.Perfection (ModP K v O hv p) p

include hp hvp

namespace PreTilt

instance : CommRingₓ (PreTilt K v O hv p) :=
  Perfection.commRing p _

instance : CharP (PreTilt K v O hv p) p :=
  Perfection.char_p (ModP K v O hv p) p

section Classical

open Classical

open Perfection

/-- The valuation `Perfection(O/(p)) → ℝ≥0` as a function.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `pre_val(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
noncomputable def valAux (f : PreTilt K v O hv p) : ℝ≥0 :=
  if h : ∃ n, coeff _ _ n f ≠ 0 then ModP.preVal K v O hv p (coeff _ _ (Nat.findₓ h) f) ^ p ^ Nat.findₓ h else 0

variable {K v O hv p}

theorem coeff_nat_find_add_ne_zero {f : PreTilt K v O hv p} {h : ∃ n, coeff _ _ n f ≠ 0} (k : ℕ) :
    coeff _ _ (Nat.findₓ h + k) f ≠ 0 :=
  coeff_add_ne_zero (Nat.find_specₓ h) k

theorem val_aux_eq {f : PreTilt K v O hv p} {n : ℕ} (hfn : coeff _ _ n f ≠ 0) :
    valAux K v O hv p f = ModP.preVal K v O hv p (coeff _ _ n f) ^ p ^ n := by
  have h : ∃ n, coeff _ _ n f ≠ 0 := ⟨n, hfn⟩
  rw [val_aux, dif_pos h]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min'ₓ h hfn)
  induction' k with k ih
  · rfl
    
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (coeff _ _ (Nat.findₓ h + k + 1) f)
  have h1 : (Ideal.Quotient.mk _ x : ModP K v O hv p) ≠ 0 := hx.symm ▸ hfn
  have h2 : (Ideal.Quotient.mk _ (x ^ p) : ModP K v O hv p) ≠ 0 := by
    erw [RingHom.map_pow, hx, ← RingHom.map_pow, coeff_pow_p]
    exact coeff_nat_find_add_ne_zero k
  erw [ih (coeff_nat_find_add_ne_zero k), ← hx, ← coeff_pow_p, RingHom.map_pow, ← hx, ← RingHom.map_pow,
    ModP.pre_val_mk h1, ModP.pre_val_mk h2, RingHom.map_pow, v.map_pow, ← pow_mulₓ, pow_succₓ]
  rfl

theorem val_aux_zero : valAux K v O hv p 0 = 0 :=
  dif_neg fun ⟨n, hn⟩ => hn rfl

theorem val_aux_one : valAux K v O hv p 1 = 1 :=
  (val_aux_eq <| show coeff (ModP K v O hv p) p 0 1 ≠ 0 from one_ne_zero).trans <| by
    rw [pow_zeroₓ, pow_oneₓ, RingHom.map_one, ← (Ideal.Quotient.mk _).map_one, ModP.pre_val_mk, RingHom.map_one,
      v.map_one]
    exact @one_ne_zero (ModP K v O hv p) _ _

theorem val_aux_mul (f g : PreTilt K v O hv p) :
    valAux K v O hv p (f * g) = valAux K v O hv p f * valAux K v O hv p g := by
  by_cases' hf : f = 0
  · rw [hf, zero_mul, val_aux_zero, zero_mul]
    
  by_cases' hg : g = 0
  · rw [hg, mul_zero, val_aux_zero, mul_zero]
    
  obtain ⟨m, hm⟩ : ∃ n, coeff _ _ n f ≠ 0 := not_forall.1 fun h => hf <| Perfection.ext h
  obtain ⟨n, hn⟩ : ∃ n, coeff _ _ n g ≠ 0 := not_forall.1 fun h => hg <| Perfection.ext h
  replace hm := coeff_ne_zero_of_le hm (le_max_leftₓ m n)
  replace hn := coeff_ne_zero_of_le hn (le_max_rightₓ m n)
  have hfg : coeff _ _ (max m n + 1) (f * g) ≠ 0 := by
    rw [RingHom.map_mul]
    refine' ModP.mul_ne_zero_of_pow_p_ne_zero _ _
    · rw [← RingHom.map_pow, coeff_pow_p f]
      assumption
      
    · rw [← RingHom.map_pow, coeff_pow_p g]
      assumption
      
  rw [val_aux_eq (coeff_add_ne_zero hm 1), val_aux_eq (coeff_add_ne_zero hn 1), val_aux_eq hfg]
  rw [RingHom.map_mul] at hfg⊢
  rw [ModP.pre_val_mul hfg, mul_powₓ]

theorem val_aux_add (f g : PreTilt K v O hv p) :
    valAux K v O hv p (f + g) ≤ max (valAux K v O hv p f) (valAux K v O hv p g) := by
  by_cases' hf : f = 0
  · rw [hf, zero_addₓ, val_aux_zero, max_eq_rightₓ]
    exact zero_le _
    
  by_cases' hg : g = 0
  · rw [hg, add_zeroₓ, val_aux_zero, max_eq_leftₓ]
    exact zero_le _
    
  by_cases' hfg : f + g = 0
  · rw [hfg, val_aux_zero]
    exact zero_le _
    
  replace hf : ∃ n, coeff _ _ n f ≠ 0 := not_forall.1 fun h => hf <| Perfection.ext h
  replace hg : ∃ n, coeff _ _ n g ≠ 0 := not_forall.1 fun h => hg <| Perfection.ext h
  replace hfg : ∃ n, coeff _ _ n (f + g) ≠ 0 := not_forall.1 fun h => hfg <| Perfection.ext h
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  obtain ⟨k, hk⟩ := hfg
  replace hm := coeff_ne_zero_of_le hm (le_transₓ (le_max_leftₓ m n) (le_max_leftₓ _ k))
  replace hn := coeff_ne_zero_of_le hn (le_transₓ (le_max_rightₓ m n) (le_max_leftₓ _ k))
  replace hk := coeff_ne_zero_of_le hk (le_max_rightₓ (max m n) k)
  rw [val_aux_eq hm, val_aux_eq hn, val_aux_eq hk, RingHom.map_add]
  cases' le_max_iff.1 (ModP.pre_val_add (coeff _ _ (max (max m n) k) f) (coeff _ _ (max (max m n) k) g)) with h h
  · exact le_max_of_le_left (pow_le_pow_of_le_left' h _)
    
  · exact le_max_of_le_right (pow_le_pow_of_le_left' h _)
    

variable (K v O hv p)

/-- The valuation `Perfection(O/(p)) → ℝ≥0`.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `pre_val(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
noncomputable def val : Valuation (PreTilt K v O hv p) ℝ≥0 where
  toFun := valAux K v O hv p
  map_one' := val_aux_one
  map_mul' := val_aux_mul
  map_zero' := val_aux_zero
  map_add_le_max' := val_aux_add

variable {K v O hv p}

theorem map_eq_zero {f : PreTilt K v O hv p} : val K v O hv p f = 0 ↔ f = 0 := by
  by_cases' hf0 : f = 0
  · rw [hf0]
    exact iff_of_true (Valuation.map_zero _) rfl
    
  obtain ⟨n, hn⟩ : ∃ n, coeff _ _ n f ≠ 0 := not_forall.1 fun h => hf0 <| Perfection.ext h
  show val_aux K v O hv p f = 0 ↔ f = 0
  refine' iff_of_false (fun hvf => hn _) hf0
  rw [val_aux_eq hn] at hvf
  replace hvf := pow_eq_zero hvf
  rwa [ModP.pre_val_eq_zero] at hvf

end Classical

instance : IsDomain (PreTilt K v O hv p) :=
  { (inferInstance : CommRingₓ (PreTilt K v O hv p)) with
    exists_pair_ne := (CharP.nontrivial_of_char_ne_one hp.1.ne_one).1,
    eq_zero_or_eq_zero_of_mul_eq_zero := fun f g hfg => by
      simp_rw [← map_eq_zero] at hfg⊢
      contrapose! hfg
      rw [Valuation.map_mul]
      exact mul_ne_zero hfg.1 hfg.2 }

end PreTilt

/-- The tilt of a field, as defined in Perfectoid Spaces by Peter Scholze, as in
[scholze2011perfectoid]. Given a field `K` with valuation `K → ℝ≥0` and ring of integers `O`,
this is implemented as the fraction field of the perfection of `O/(p)`. -/
@[nolint has_inhabited_instance]
def Tilt :=
  FractionRing (PreTilt K v O hv p)

namespace Tilt

noncomputable instance : Field (Tilt K v O hv p) :=
  FractionRing.field

end Tilt

end Perfectoid

