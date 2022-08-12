/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Order.WellFoundedSet
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.RingTheory.Valuation.Basic
import Mathbin.Algebra.Module.Pi
import Mathbin.RingTheory.PowerSeries.Basic
import Mathbin.Data.Finsupp.Pwo

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `hahn_series Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `hahn_series Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `hahn_series Γ R` is a
valued field, with value group `Γ`.

These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `ring_theory/laurent_series`.

## Main Definitions
  * If `Γ` is ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series Γ R`.
  * If `R` is a (comm_)(semi)ring, then so is `hahn_series Γ R`.
  * `hahn_series.add_val Γ R` defines an `add_valuation` on `hahn_series Γ R` when `Γ` is linearly
    ordered.
  * A `hahn_series.summable_family` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `hahn_series.summable_family.hsum`, which can be bundled as a `linear_map` as
  `hahn_series.summable_family.lsum`. Note that this is different from `summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `hahn_series.summable_family`, and formally summable families whose sums do not converge
  topologically.
  * Laurent series over `R` are implemented as `hahn_series ℤ R` in the file
    `ring_theory/laurent_series`.

## TODO
  * Build an API for the variable `X` (defined to be `single 1 1 : hahn_series Γ R`) in analogy to
    `X : R[X]` and `X : power_series R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]

-/


open Finset Function

open BigOperators Classical Pointwise Polynomial

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure HahnSeries (Γ : Type _) (R : Type _) [PartialOrderₓ Γ] [Zero R] where
  coeff : Γ → R
  is_pwo_support' : (Support coeff).IsPwo

variable {Γ : Type _} {R : Type _}

namespace HahnSeries

section Zero

variable [PartialOrderₓ Γ] [Zero R]

theorem coeff_injective : Injective (coeff : HahnSeries Γ R → Γ → R) :=
  ext

@[simp]
theorem coeff_inj {x y : HahnSeries Γ R} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
def Support (x : HahnSeries Γ R) : Set Γ :=
  Support x.coeff

@[simp]
theorem is_pwo_support (x : HahnSeries Γ R) : x.Support.IsPwo :=
  x.is_pwo_support'

@[simp]
theorem is_wf_support (x : HahnSeries Γ R) : x.Support.IsWf :=
  x.is_pwo_support.IsWf

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.Support ↔ x.coeff a ≠ 0 :=
  Iff.refl _

instance : Zero (HahnSeries Γ R) :=
  ⟨{ coeff := 0,
      is_pwo_support' := by
        simp }⟩

instance : Inhabited (HahnSeries Γ R) :=
  ⟨0⟩

instance [Subsingleton R] : Subsingleton (HahnSeries Γ R) :=
  ⟨fun a b => a.ext b (Subsingleton.elimₓ _ _)⟩

@[simp]
theorem zero_coeff {a : Γ} : (0 : HahnSeries Γ R).coeff a = 0 :=
  rfl

@[simp]
theorem coeff_fun_eq_zero_iff {x : HahnSeries Γ R} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl

theorem ne_zero_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : x ≠ 0 :=
  mt (fun x0 => (x0.symm ▸ zero_coeff : x.coeff g = 0)) h

@[simp]
theorem support_zero : Support (0 : HahnSeries Γ R) = ∅ :=
  Function.support_zero

@[simp]
theorem support_nonempty_iff {x : HahnSeries Γ R} : x.Support.Nonempty ↔ x ≠ 0 := by
  rw [support, support_nonempty_iff, Ne.def, coeff_fun_eq_zero_iff]

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.Support = ∅ ↔ x = 0 :=
  support_eq_empty_iff.trans coeff_fun_eq_zero_iff

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R) where
  toFun := fun r =>
    { coeff := Pi.single a r, is_pwo_support' := (Set.is_pwo_singleton a).mono Pi.support_single_subset }
  map_zero' := ext _ _ (Pi.single_zero _)

variable {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r :=
  Pi.single_eq_same a r

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 :=
  Pi.single_eq_of_ne h r

theorem single_coeff : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [← h]

@[simp]
theorem support_single_of_ne (h : r ≠ 0) : Support (single a r) = {a} :=
  Pi.support_single_of_ne h

theorem support_single_subset : Support (single a r) ⊆ {a} :=
  Pi.support_single_subset

theorem eq_of_mem_support_single {b : Γ} (h : b ∈ Support (single a r)) : b = a :=
  support_single_subset h

@[simp]
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) := fun r s rs => by
  rw [← single_coeff_same a r, ← single_coeff_same a s, rs]

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con => h (single_injective a (Con.trans single_eq_zero.symm))

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 := by
  constructor
  · contrapose!
    exact single_ne_zero
    
  · simp (config := { contextual := true })
    

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine' ⟨single (arbitrary Γ) r, single (arbitrary Γ) s, fun con => rs _⟩
    rw [← single_coeff_same (arbitrary Γ) r, Con, single_coeff_same]⟩

section Order

variable [Zero Γ]

/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.is_wf_support.min (support_nonempty_iff.2 h)

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

theorem order_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : order x = x.is_wf_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 := by
  rw [order_of_ne hx]
  exact x.is_wf_support.min_mem (support_nonempty_iff.2 hx)

theorem order_le_of_coeff_ne_zero {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x : HahnSeries Γ R} {g : Γ}
    (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_transₓ (le_of_eqₓ (order_of_ne (ne_zero_of_coeff_ne_zero h))) (Set.IsWf.min_le _ _ ((mem_support _ _).2 h))

@[simp]
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset ((single a r).is_wf_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) : x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
    
  contrapose! hi
  rw [← Ne.def, ← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWf.not_lt_min _ _ hi

end Order

section Domain

variable {Γ' : Type _} [PartialOrderₓ Γ']

/-- Extends the domain of a `hahn_series` by an `order_embedding`. -/
def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.Support then x.coeff (Classical.some h) else 0,
    is_pwo_support' :=
      (x.is_pwo_support.image_of_monotone f.Monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support, dif_neg hb, not_not] }

@[simp]
theorem emb_domain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} : (embDomain f x).coeff (f a) = x.coeff a := by
  rw [emb_domain]
  dsimp' only
  by_cases' ha : a ∈ x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.some_spec (Set.mem_image_of_mem f ha)).2)
    
  · rw [dif_neg, not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose! ha
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    rwa [f.injective hb2] at hb1
    

@[simp]
theorem emb_domain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f) (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g')
    {x : HahnSeries Γ R} {a : Γ} : (embDomain ⟨⟨f, hfi⟩, hf⟩ x).coeff (f a) = x.coeff a :=
  emb_domain_coeff

theorem emb_domain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ f '' x.Support) :
    (embDomain f x).coeff b = 0 :=
  dif_neg hb

theorem support_emb_domain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} : Support (embDomain f x) ⊆ f '' x.Support := by
  intro g hg
  contrapose! hg
  rw [mem_support, emb_domain_notin_image_support hg, not_not]

theorem emb_domain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.Range f) :
    (embDomain f x).coeff b = 0 :=
  emb_domain_notin_image_support fun con => hb (Set.image_subset_range _ _ Con)

@[simp]
theorem emb_domain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 := by
  ext
  simp [← emb_domain_notin_image_support]

@[simp]
theorem emb_domain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} : embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases' h : g' = f g
  · simp [← h]
    
  rw [emb_domain_notin_image_support, single_coeff_of_ne h]
  by_cases' hr : r = 0
  · simp [← hr]
    
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]

theorem emb_domain_injective {f : Γ ↪o Γ'} : Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) :=
  fun x y xy => by
  ext g
  rw [ext_iff, Function.funext_iffₓ] at xy
  have xyg := xy (f g)
  rwa [emb_domain_coeff, emb_domain_coeff] at xyg

end Domain

end Zero

section Addition

variable [PartialOrderₓ Γ]

section AddMonoidₓ

variable [AddMonoidₓ R]

instance :
    Add
      (HahnSeries Γ
        R) where add := fun x y =>
    { coeff := x.coeff + y.coeff,
      is_pwo_support' := (x.is_pwo_support.union y.is_pwo_support).mono (Function.support_add _ _) }

instance : AddMonoidₓ (HahnSeries Γ R) where
  zero := 0
  add := (· + ·)
  add_assoc := fun x y z => by
    ext
    apply add_assocₓ
  zero_add := fun x => by
    ext
    apply zero_addₓ
  add_zero := fun x => by
    ext
    apply add_zeroₓ

@[simp]
theorem add_coeff' {x y : HahnSeries Γ R} : (x + y).coeff = x.coeff + y.coeff :=
  rfl

theorem add_coeff {x y : HahnSeries Γ R} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a :=
  rfl

theorem support_add_subset {x y : HahnSeries Γ R} : Support (x + y) ⊆ Support x ∪ Support y := fun a ha => by
  rw [mem_support, add_coeff] at ha
  rw [Set.mem_union, mem_support, mem_support]
  contrapose! ha
  rw [ha.1, ha.2, add_zeroₓ]

theorem min_order_le_order_add {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x y : HahnSeries Γ R} (hxy : x + y ≠ 0) :
    min x.order y.order ≤ (x + y).order := by
  by_cases' hx : x = 0
  · simp [← hx]
    
  by_cases' hy : y = 0
  · simp [← hy]
    
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  refine' le_transₓ _ (Set.IsWf.min_le_min_of_subset support_add_subset)
  · exact x.is_wf_support.union y.is_wf_support
    
  · exact Set.Nonempty.mono (Set.subset_union_left _ _) (support_nonempty_iff.2 hx)
    
  rw [Set.IsWf.min_union]

/-- `single` as an additive monoid/group homomorphism -/
@[simps]
def single.addMonoidHom (a : Γ) : R →+ HahnSeries Γ R :=
  { single a with
    map_add' := fun x y => by
      ext b
      by_cases' h : b = a <;> simp [← h] }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
def coeff.addMonoidHom (g : Γ) : HahnSeries Γ R →+ R where
  toFun := fun f => f.coeff g
  map_zero' := zero_coeff
  map_add' := fun x y => add_coeff

section Domain

variable {Γ' : Type _} [PartialOrderₓ Γ']

theorem emb_domain_add (f : Γ ↪o Γ') (x y : HahnSeries Γ R) : embDomain f (x + y) = embDomain f x + embDomain f y := by
  ext g
  by_cases' hg : g ∈ Set.Range f
  · obtain ⟨a, rfl⟩ := hg
    simp
    
  · simp [← emb_domain_notin_range, ← hg]
    

end Domain

end AddMonoidₓ

instance [AddCommMonoidₓ R] : AddCommMonoidₓ (HahnSeries Γ R) :=
  { HahnSeries.addMonoid with
    add_comm := fun x y => by
      ext
      apply add_commₓ }

section AddGroupₓ

variable [AddGroupₓ R]

instance : AddGroupₓ (HahnSeries Γ R) :=
  { HahnSeries.addMonoid with
    neg := fun x =>
      { coeff := fun a => -x.coeff a,
        is_pwo_support' := by
          rw [Function.support_neg]
          exact x.is_pwo_support },
    add_left_neg := fun x => by
      ext
      apply add_left_negₓ }

@[simp]
theorem neg_coeff' {x : HahnSeries Γ R} : (-x).coeff = -x.coeff :=
  rfl

theorem neg_coeff {x : HahnSeries Γ R} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl

@[simp]
theorem support_neg {x : HahnSeries Γ R} : (-x).Support = x.Support := by
  ext
  simp

@[simp]
theorem sub_coeff' {x y : HahnSeries Γ R} : (x - y).coeff = x.coeff - y.coeff := by
  ext
  simp [← sub_eq_add_neg]

theorem sub_coeff {x y : HahnSeries Γ R} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a := by
  simp

end AddGroupₓ

instance [AddCommGroupₓ R] : AddCommGroupₓ (HahnSeries Γ R) :=
  { HahnSeries.addCommMonoid, HahnSeries.addGroup with }

end Addition

section DistribMulAction

variable [PartialOrderₓ Γ] {V : Type _} [Monoidₓ R] [AddMonoidₓ V] [DistribMulAction R V]

instance : HasSmul R (HahnSeries Γ V) :=
  ⟨fun r x =>
    { coeff := r • x.coeff, is_pwo_support' := x.is_pwo_support.mono (Function.support_smul_subset_right r x.coeff) }⟩

@[simp]
theorem smul_coeff {r : R} {x : HahnSeries Γ V} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl

instance : DistribMulAction R (HahnSeries Γ V) where
  smul := (· • ·)
  one_smul := fun _ => by
    ext
    simp
  smul_zero := fun _ => by
    ext
    simp
  smul_add := fun _ _ _ => by
    ext
    simp [← smul_add]
  mul_smul := fun _ _ _ => by
    ext
    simp [← mul_smul]

variable {S : Type _} [Monoidₓ S] [DistribMulAction S V]

instance [HasSmul R S] [IsScalarTower R S V] : IsScalarTower R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    simp ⟩

instance [SmulCommClass R S V] : SmulCommClass R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    simp [← smul_comm]⟩

end DistribMulAction

section Module

variable [PartialOrderₓ Γ] [Semiringₓ R] {V : Type _} [AddCommMonoidₓ V] [Module R V]

instance : Module R (HahnSeries Γ V) :=
  { HahnSeries.distribMulAction with
    zero_smul := fun _ => by
      ext
      simp ,
    add_smul := fun _ _ _ => by
      ext
      simp [← add_smul] }

/-- `single` as a linear map -/
@[simps]
def single.linearMap (a : Γ) : R →ₗ[R] HahnSeries Γ R :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases' h : b = a <;> simp [← h] }

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linearMap (g : Γ) : HahnSeries Γ R →ₗ[R] R :=
  { coeff.addMonoidHom g with map_smul' := fun r s => rfl }

section Domain

variable {Γ' : Type _} [PartialOrderₓ Γ']

theorem emb_domain_smul (f : Γ ↪o Γ') (r : R) (x : HahnSeries Γ R) : embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases' hg : g ∈ Set.Range f
  · obtain ⟨a, rfl⟩ := hg
    simp
    
  · simp [← emb_domain_notin_range, ← hg]
    

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
def embDomainLinearMap (f : Γ ↪o Γ') : HahnSeries Γ R →ₗ[R] HahnSeries Γ' R where
  toFun := embDomain f
  map_add' := emb_domain_add f
  map_smul' := emb_domain_smul f

end Domain

end Module

section Multiplication

variable [OrderedCancelAddCommMonoid Γ]

instance [Zero R] [One R] : One (HahnSeries Γ R) :=
  ⟨single 0 1⟩

@[simp]
theorem one_coeff [Zero R] [One R] {a : Γ} : (1 : HahnSeries Γ R).coeff a = if a = 0 then 1 else 0 :=
  single_coeff

@[simp]
theorem single_zero_one [Zero R] [One R] : single 0 (1 : R) = 1 :=
  rfl

@[simp]
theorem support_one [MulZeroOneClassₓ R] [Nontrivial R] : Support (1 : HahnSeries Γ R) = {0} :=
  support_single_of_ne one_ne_zero

@[simp]
theorem order_one [MulZeroOneClassₓ R] : order (1 : HahnSeries Γ R) = 0 := by
  cases' subsingleton_or_nontrivial R with h h <;> have := h
  · rw [Subsingleton.elimₓ (1 : HahnSeries Γ R) 0, order_zero]
    
  · exact order_single one_ne_zero
    

instance [NonUnitalNonAssocSemiringₓ R] :
    Mul
      (HahnSeries Γ
        R) where mul := fun x y =>
    { coeff := fun a => ∑ ij in addAntidiagonal x.is_pwo_support y.is_pwo_support a, x.coeff ij.fst * y.coeff ij.snd,
      is_pwo_support' := by
        have h :
          { a : Γ |
              (∑ ij : Γ × Γ in add_antidiagonal x.is_pwo_support y.is_pwo_support a, x.coeff ij.fst * y.coeff ij.snd) ≠
                0 } ⊆
            { a : Γ | (add_antidiagonal x.is_pwo_support y.is_pwo_support a).Nonempty } :=
          by
          intro a ha
          contrapose! ha
          simp [← not_nonempty_iff_eq_empty.1 ha]
        exact is_pwo_support_add_antidiagonal.mono h }

@[simp]
theorem mul_coeff [NonUnitalNonAssocSemiringₓ R] {x y : HahnSeries Γ R} {a : Γ} :
    (x * y).coeff a = ∑ ij in addAntidiagonal x.is_pwo_support y.is_pwo_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl

theorem mul_coeff_right' [NonUnitalNonAssocSemiringₓ R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ} (hs : s.IsPwo)
    (hys : y.Support ⊆ s) :
    (x * y).coeff a = ∑ ij in addAntidiagonal x.is_pwo_support hs a, x.coeff ij.fst * y.coeff ij.snd := by
  rw [mul_coeff]
  apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_right hys) _ fun _ _ => rfl
  intro b hb
  simp only [← not_and, ← not_not, ← mem_sdiff, ← mem_add_antidiagonal, ← Ne.def, ← Set.mem_set_of_eq, ← mem_support] at
    hb
  rw [hb.2 hb.1.1 hb.1.2.1, mul_zero]

theorem mul_coeff_left' [NonUnitalNonAssocSemiringₓ R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ} (hs : s.IsPwo)
    (hxs : x.Support ⊆ s) :
    (x * y).coeff a = ∑ ij in addAntidiagonal hs y.is_pwo_support a, x.coeff ij.fst * y.coeff ij.snd := by
  rw [mul_coeff]
  apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_left hxs) _ fun _ _ => rfl
  intro b hb
  simp only [← not_and, ← not_not, ← mem_sdiff, ← mem_add_antidiagonal, ← Ne.def, ← Set.mem_set_of_eq, ← mem_support] at
    hb
  rw [not_not.1 fun con => hb.1.2.2 (hb.2 hb.1.1 Con), zero_mul]

instance [NonUnitalNonAssocSemiringₓ R] : Distribₓ (HahnSeries Γ R) :=
  { HahnSeries.hasMul, HahnSeries.hasAdd with
    left_distrib := fun x y z => by
      ext a
      have hwf := y.is_pwo_support.union z.is_pwo_support
      rw [mul_coeff_right' hwf, add_coeff, mul_coeff_right' hwf (Set.subset_union_right _ _),
        mul_coeff_right' hwf (Set.subset_union_left _ _)]
      · simp only [← add_coeff, ← mul_addₓ, ← sum_add_distrib]
        
      · intro b
        simp only [← add_coeff, ← Ne.def, ← Set.mem_union_eq, ← Set.mem_set_of_eq, ← mem_support]
        contrapose!
        intro h
        rw [h.1, h.2, add_zeroₓ]
        ,
    right_distrib := fun x y z => by
      ext a
      have hwf := x.is_pwo_support.union y.is_pwo_support
      rw [mul_coeff_left' hwf, add_coeff, mul_coeff_left' hwf (Set.subset_union_right _ _),
        mul_coeff_left' hwf (Set.subset_union_left _ _)]
      · simp only [← add_coeff, ← add_mulₓ, ← sum_add_distrib]
        
      · intro b
        simp only [← add_coeff, ← Ne.def, ← Set.mem_union_eq, ← Set.mem_set_of_eq, ← mem_support]
        contrapose!
        intro h
        rw [h.1, h.2, add_zeroₓ]
         }

theorem single_mul_coeff_add [NonUnitalNonAssocSemiringₓ R] {r : R} {x : HahnSeries Γ R} {a : Γ} {b : Γ} :
    (single b r * x).coeff (a + b) = r * x.coeff a := by
  by_cases' hr : r = 0
  · simp [← hr]
    
  simp only [← hr, ← smul_coeff, ← mul_coeff, ← support_single_of_ne, ← Ne.def, ← not_false_iff, ← smul_eq_mul]
  by_cases' hx : x.coeff a = 0
  · simp only [← hx, ← mul_zero]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [← not_mem_empty, ← not_and, ← Set.mem_singleton_iff, ← not_not, ← mem_add_antidiagonal, ←
      Set.mem_set_of_eq, ← iff_falseₓ]
    rintro h1 rfl h2
    rw [add_commₓ] at h1
    rw [← add_right_cancelₓ h1] at hx
    exact h2 hx
    
  trans ∑ ij : Γ × Γ in {(b, a)}, (single b r).coeff ij.fst * x.coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [← Set.mem_singleton_iff, ← Prod.mk.inj_iff, ← mem_add_antidiagonal, ← mem_singleton, ← Set.mem_set_of_eq]
    constructor
    · rintro ⟨h1, rfl, h2⟩
      rw [add_commₓ] at h1
      refine' ⟨rfl, add_right_cancelₓ h1⟩
      
    · rintro ⟨rfl, rfl⟩
      refine' ⟨add_commₓ _ _, _⟩
      simp [← hx]
      
    
  · simp
    

theorem mul_single_coeff_add [NonUnitalNonAssocSemiringₓ R] {r : R} {x : HahnSeries Γ R} {a : Γ} {b : Γ} :
    (x * single b r).coeff (a + b) = x.coeff a * r := by
  by_cases' hr : r = 0
  · simp [← hr]
    
  simp only [← hr, ← smul_coeff, ← mul_coeff, ← support_single_of_ne, ← Ne.def, ← not_false_iff, ← smul_eq_mul]
  by_cases' hx : x.coeff a = 0
  · simp only [← hx, ← zero_mul]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [← not_mem_empty, ← not_and, ← Set.mem_singleton_iff, ← not_not, ← mem_add_antidiagonal, ←
      Set.mem_set_of_eq, ← iff_falseₓ]
    rintro h1 h2 rfl
    rw [← add_right_cancelₓ h1] at hx
    exact h2 hx
    
  trans ∑ ij : Γ × Γ in {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [← Set.mem_singleton_iff, ← Prod.mk.inj_iff, ← mem_add_antidiagonal, ← mem_singleton, ← Set.mem_set_of_eq]
    constructor
    · rintro ⟨h1, h2, rfl⟩
      refine' ⟨add_right_cancelₓ h1, rfl⟩
      
    · rintro ⟨rfl, rfl⟩
      simp [← hx]
      
    
  · simp
    

@[simp]
theorem mul_single_zero_coeff [NonUnitalNonAssocSemiringₓ R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    (x * single 0 r).coeff a = x.coeff a * r := by
  rw [← add_zeroₓ a, mul_single_coeff_add, add_zeroₓ]

theorem single_zero_mul_coeff [NonUnitalNonAssocSemiringₓ R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    (single 0 r * x).coeff a = r * x.coeff a := by
  rw [← add_zeroₓ a, single_mul_coeff_add, add_zeroₓ]

@[simp]
theorem single_zero_mul_eq_smul [Semiringₓ R] {r : R} {x : HahnSeries Γ R} : single 0 r * x = r • x := by
  ext
  exact single_zero_mul_coeff

theorem support_mul_subset_add_support [NonUnitalNonAssocSemiringₓ R] {x y : HahnSeries Γ R} :
    Support (x * y) ⊆ Support x + Support y := by
  apply Set.Subset.trans (fun x hx => _) support_add_antidiagonal_subset_add
  · exact x.is_pwo_support
    
  · exact y.is_pwo_support
    
  contrapose! hx
  simp only [← not_nonempty_iff_eq_empty, ← Ne.def, ← Set.mem_set_of_eq] at hx
  simp [← hx]

theorem mul_coeff_order_add_order {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiringₓ R]
    (x y : HahnSeries Γ R) : (x * y).coeff (x.order + y.order) = x.coeff x.order * y.coeff y.order := by
  by_cases' hx : x = 0
  · simp [← hx]
    
  by_cases' hy : y = 0
  · simp [← hy]
    
  rw [order_of_ne hx, order_of_ne hy, mul_coeff, Finset.add_antidiagonal_min_add_min, Finset.sum_singleton]

private theorem mul_assoc' [NonUnitalSemiringₓ R] (x y z : HahnSeries Γ R) : x * y * z = x * (y * z) := by
  ext b
  rw [mul_coeff_left' (x.is_pwo_support.add y.is_pwo_support) support_mul_subset_add_support,
    mul_coeff_right' (y.is_pwo_support.add z.is_pwo_support) support_mul_subset_add_support]
  simp only [← mul_coeff, ← add_coeff, ← sum_mul, ← mul_sum, ← sum_sigma']
  refine' sum_bij_ne_zero (fun a has ha0 => ⟨⟨a.2.1, a.2.2 + a.1.2⟩, ⟨a.2.2, a.1.2⟩⟩) _ _ _ _
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    simp only [← true_andₓ, ← Set.image2_add, ← eq_self_iff_true, ← mem_add_antidiagonal, ← Ne.def, ← Set.image_prod, ←
      mem_sigma, ← Set.mem_set_of_eq] at H1 H2⊢
    obtain ⟨⟨rfl, ⟨H3, nz⟩⟩, ⟨rfl, nx, ny⟩⟩ := H1
    refine' ⟨⟨(add_assocₓ _ _ _).symm, nx, Set.add_mem_add ny nz⟩, ny, nz⟩
    
  · rintro ⟨⟨i1, j1⟩, ⟨k1, l1⟩⟩ ⟨⟨i2, j2⟩, ⟨k2, l2⟩⟩ H1 H2 H3 H4 H5
    simp only [← Set.image2_add, ← Prod.mk.inj_iff, ← mem_add_antidiagonal, ← Ne.def, ← Set.image_prod, ← mem_sigma, ←
      Set.mem_set_of_eq, ← heq_iff_eq] at H1 H3 H5
    obtain ⟨⟨rfl, H⟩, rfl, rfl⟩ := H5
    simp only [← and_trueₓ, ← Prod.mk.inj_iff, ← eq_self_iff_true, ← heq_iff_eq]
    exact add_right_cancelₓ (H1.1.1.trans H3.1.1.symm)
    
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    simp only [← exists_prop, ← Set.image2_add, ← Prod.mk.inj_iff, ← mem_add_antidiagonal, ← Sigma.exists, ← Ne.def, ←
      Set.image_prod, ← mem_sigma, ← Set.mem_set_of_eq, ← heq_iff_eq, ← Prod.exists] at H1 H2⊢
    obtain ⟨⟨rfl, nx, H⟩, rfl, ny, nz⟩ := H1
    exact
      ⟨i + k, l, i, k, ⟨⟨add_assocₓ _ _ _, Set.add_mem_add nx ny, nz⟩, rfl, nx, ny⟩, fun con =>
        H2 ((mul_assoc _ _ _).symm.trans Con), ⟨rfl, rfl⟩, rfl, rfl⟩
    
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    simp [← mul_assoc]
    

instance [NonUnitalNonAssocSemiringₓ R] : NonUnitalNonAssocSemiringₓ (HahnSeries Γ R) :=
  { HahnSeries.addCommMonoid, HahnSeries.distrib with zero := 0, add := (· + ·), mul := (· * ·),
    zero_mul := fun _ => by
      ext
      simp ,
    mul_zero := fun _ => by
      ext
      simp }

instance [NonUnitalSemiringₓ R] : NonUnitalSemiringₓ (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocSemiring with zero := 0, add := (· + ·), mul := (· * ·), mul_assoc := mul_assoc' }

instance [NonAssocSemiringₓ R] : NonAssocSemiringₓ (HahnSeries Γ R) :=
  { AddMonoidWithOneₓ.unary, HahnSeries.nonUnitalNonAssocSemiring with zero := 0, one := 1, add := (· + ·),
    mul := (· * ·),
    one_mul := fun x => by
      ext
      exact single_zero_mul_coeff.trans (one_mulₓ _),
    mul_one := fun x => by
      ext
      exact mul_single_zero_coeff.trans (mul_oneₓ _) }

instance [Semiringₓ R] : Semiringₓ (HahnSeries Γ R) :=
  { HahnSeries.nonAssocSemiring, HahnSeries.nonUnitalSemiring with zero := 0, one := 1, add := (· + ·), mul := (· * ·) }

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalSemiring with
    mul_comm := fun x y => by
      ext
      simp_rw [mul_coeff, mul_comm]
      refine'
        sum_bij (fun a ha => ⟨a.2, a.1⟩) _
          (fun a ha => by
            simp )
          _ _
      · intro a ha
        simp only [← mem_add_antidiagonal, ← Ne.def, ← Set.mem_set_of_eq] at ha⊢
        obtain ⟨h1, h2, h3⟩ := ha
        refine' ⟨_, h3, h2⟩
        rw [add_commₓ, h1]
        
      · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ha hb hab
        rw [Prod.ext_iff] at *
        refine' ⟨hab.2, hab.1⟩
        
      · intro a ha
        refine'
          ⟨a.swap, _, by
            simp ⟩
        simp only [← Prod.fst_swap, ← mem_add_antidiagonal, ← Prod.snd_swap, ← Ne.def, ← Set.mem_set_of_eq] at ha⊢
        exact ⟨(add_commₓ _ _).trans ha.1, ha.2.2, ha.2.1⟩
         }

instance [CommSemiringₓ R] : CommSemiringₓ (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalCommSemiring, HahnSeries.semiring with }

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocSemiring, HahnSeries.addGroup with }

instance [NonUnitalRing R] : NonUnitalRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocRing, HahnSeries.nonUnitalSemiring with }

instance [NonAssocRing R] : NonAssocRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocRing, HahnSeries.nonAssocSemiring with }

instance [Ringₓ R] : Ringₓ (HahnSeries Γ R) :=
  { HahnSeries.semiring, HahnSeries.addCommGroup with }

instance [NonUnitalCommRing R] : NonUnitalCommRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalCommSemiring, HahnSeries.nonUnitalRing with }

instance [CommRingₓ R] : CommRingₓ (HahnSeries Γ R) :=
  { HahnSeries.commSemiring, HahnSeries.ring with }

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiringₓ R] [NoZeroDivisors R] :
    NoZeroDivisors (HahnSeries Γ R) where eq_zero_or_eq_zero_of_mul_eq_zero := fun x y xy => by
    by_cases' hx : x = 0
    · left
      exact hx
      
    right
    contrapose! xy
    rw [HahnSeries.ext_iff, Function.funext_iffₓ, not_forall]
    refine' ⟨x.order + y.order, _⟩
    rw [mul_coeff_order_add_order x y, zero_coeff, mul_eq_zero]
    simp [← coeff_order_ne_zero, ← hx, ← xy]

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Ringₓ R] [IsDomain R] : IsDomain (HahnSeries Γ R) :=
  { HahnSeries.no_zero_divisors, HahnSeries.nontrivial, HahnSeries.ring with }

@[simp]
theorem order_mul {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiringₓ R] [NoZeroDivisors R]
    {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0) : (x * y).order = x.order + y.order := by
  apply le_antisymmₓ
  · apply order_le_of_coeff_ne_zero
    rw [mul_coeff_order_add_order x y]
    exact mul_ne_zero (coeff_order_ne_zero hx) (coeff_order_ne_zero hy)
    
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWf.min_add]
    exact Set.IsWf.min_le_min_of_subset support_mul_subset_add_support
    

@[simp]
theorem order_pow {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Semiringₓ R] [NoZeroDivisors R] (x : HahnSeries Γ R)
    (n : ℕ) : (x ^ n).order = n • x.order := by
  induction' n with h IH
  · simp
    
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
    
  rw [pow_succ'ₓ, order_mul (pow_ne_zero _ hx) hx, succ_nsmul', IH]

section NonUnitalNonAssocSemiringₓ

variable [NonUnitalNonAssocSemiringₓ R]

@[simp]
theorem single_mul_single {a b : Γ} {r s : R} : single a r * single b s = single (a + b) (r * s) := by
  ext x
  by_cases' h : x = a + b
  · rw [h, mul_single_coeff_add]
    simp
    
  · rw [single_coeff_of_ne h, mul_coeff, sum_eq_zero]
    rintro ⟨y1, y2⟩ hy
    obtain ⟨rfl, hy1, hy2⟩ := mem_add_antidiagonal.1 hy
    rw [eq_of_mem_support_single hy1, eq_of_mem_support_single hy2] at h
    exact (h rfl).elim
    

end NonUnitalNonAssocSemiringₓ

section NonAssocSemiringₓ

variable [NonAssocSemiringₓ R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
def c : R →+* HahnSeries Γ R where
  toFun := single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' := fun x y => by
    ext a
    by_cases' h : a = 0 <;> simp [← h]
  map_mul' := fun x y => by
    rw [single_mul_single, zero_addₓ]

@[simp]
theorem C_zero : c (0 : R) = (0 : HahnSeries Γ R) :=
  c.map_zero

@[simp]
theorem C_one : c (1 : R) = (1 : HahnSeries Γ R) :=
  c.map_one

theorem C_injective : Function.Injective (c : R → HahnSeries Γ R) := by
  intro r s rs
  rw [ext_iff, Function.funext_iffₓ] at rs
  have h := rs 0
  rwa [C_apply, single_coeff_same, C_apply, single_coeff_same] at h

theorem C_ne_zero {r : R} (h : r ≠ 0) : (c r : HahnSeries Γ R) ≠ 0 := by
  contrapose! h
  rw [← C_zero] at h
  exact C_injective h

theorem order_C {r : R} : order (c r : HahnSeries Γ R) = 0 := by
  by_cases' h : r = 0
  · rw [h, C_zero, order_zero]
    
  · exact order_single h
    

end NonAssocSemiringₓ

section Semiringₓ

variable [Semiringₓ R]

theorem C_mul_eq_smul {r : R} {x : HahnSeries Γ R} : c r * x = r • x :=
  single_zero_mul_eq_smul

end Semiringₓ

section Domain

variable {Γ' : Type _} [OrderedCancelAddCommMonoid Γ']

theorem emb_domain_mul [NonUnitalNonAssocSemiringₓ R] (f : Γ ↪o Γ') (hf : ∀ x y, f (x + y) = f x + f y)
    (x y : HahnSeries Γ R) : embDomain f (x * y) = embDomain f x * embDomain f y := by
  ext g
  by_cases' hg : g ∈ Set.Range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [← mul_coeff, ← emb_domain_coeff]
    trans
      ∑ ij in
        (add_antidiagonal x.is_pwo_support y.is_pwo_support g).map
          (Function.Embedding.prodMap f.to_embedding f.to_embedding),
        (emb_domain f x).coeff ij.1 * (emb_domain f y).coeff ij.2
    · simp
      
    apply sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [← exists_prop, ← mem_map, ← Prod.mk.inj_iff, ← mem_add_antidiagonal, ← Ne.def, ←
        Function.Embedding.coe_prod_map, ← mem_support, ← Prod.exists] at hij
      obtain ⟨i, j, ⟨rfl, hx, hy⟩, rfl, rfl⟩ := hij
      simp [← hx, ← hy, ← hf]
      
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).1
      obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).2
      simp only [← exists_prop, ← mem_map, ← Prod.mk.inj_iff, ← mem_add_antidiagonal, ← Ne.def, ←
        Function.Embedding.coe_prod_map, ← mem_support, ← Prod.exists]
      simp only [← mem_add_antidiagonal, ← emb_domain_coeff, ← Ne.def, ← mem_support, hf] at h1
      exact ⟨i, j, ⟨f.injective h1.1, h1.2⟩, rfl⟩
      
    
  · rw [emb_domain_notin_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, _, hi, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg)
    obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset hi
    obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset hj
    refine' ⟨i + j, hf i j⟩
    

theorem emb_domain_one [NonAssocSemiringₓ R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
    embDomain f (1 : HahnSeries Γ R) = (1 : HahnSeries Γ' R) :=
  emb_domain_single.trans <| hf.symm ▸ rfl

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
def embDomainRingHom [NonAssocSemiringₓ R] (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ R →+* HahnSeries Γ' R where
  toFun := embDomain ⟨⟨f, hfi⟩, hf⟩
  map_one' := emb_domain_one _ f.map_zero
  map_mul' := emb_domain_mul _ f.map_add
  map_zero' := emb_domain_zero
  map_add' := emb_domain_add _

theorem emb_domain_ring_hom_C [NonAssocSemiringₓ R] {f : Γ →+ Γ'} {hfi : Function.Injective f}
    {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} : embDomainRingHom f hfi hf (c r) = c r :=
  emb_domain_single.trans
    (by
      simp )

end Domain

section Algebra

variable [CommSemiringₓ R] {A : Type _} [Semiringₓ A] [Algebra R A]

instance : Algebra R (HahnSeries Γ A) where
  toRingHom := c.comp (algebraMap R A)
  smul_def' := fun r x => by
    ext
    simp
  commutes' := fun r x => by
    ext
    simp only [← smul_coeff, ← single_zero_mul_eq_smul, ← RingHom.coe_comp, ← RingHom.to_fun_eq_coe, ← C_apply, ←
      Function.comp_app, ← algebra_map_smul, ← mul_single_zero_coeff]
    rw [← Algebra.commutes, Algebra.smul_def]

theorem C_eq_algebra_map : C = algebraMap R (HahnSeries Γ R) :=
  rfl

theorem algebra_map_apply {r : R} : algebraMap R (HahnSeries Γ A) r = c (algebraMap R A r) :=
  rfl

instance [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R (HahnSeries Γ R)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne.def, SetLike.ext_iff, not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine' ⟨single a 1, _⟩
      simp only [← Algebra.mem_bot, ← not_exists, ← Set.mem_range, ← iff_trueₓ, ← Algebra.mem_top]
      intro x
      rw [ext_iff, Function.funext_iffₓ, not_forall]
      refine' ⟨a, _⟩
      rw [single_coeff_same, algebra_map_apply, C_apply, single_coeff_of_ne ha]
      exact zero_ne_one⟩⟩

section Domain

variable {Γ' : Type _} [OrderedCancelAddCommMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps]
def embDomainAlgHom (f : Γ →+ Γ') (hfi : Function.Injective f) (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') :
    HahnSeries Γ A →ₐ[R] HahnSeries Γ' A :=
  { embDomainRingHom f hfi hf with commutes' := fun r => emb_domain_ring_hom_C }

end Domain

end Algebra

end Multiplication

section Semiringₓ

variable [Semiringₓ R]

/-- The ring `hahn_series ℕ R` is isomorphic to `power_series R`. -/
@[simps]
def toPowerSeries : HahnSeries ℕ R ≃+* PowerSeries R where
  toFun := fun f => PowerSeries.mk f.coeff
  invFun := fun f => ⟨fun n => PowerSeries.coeff R n f, (Nat.lt_wf.IsWf _).IsPwo⟩
  left_inv := fun f => by
    ext
    simp
  right_inv := fun f => by
    ext
    simp
  map_add' := fun f g => by
    ext
    simp
  map_mul' := fun f g => by
    ext n
    simp only [← PowerSeries.coeff_mul, ← PowerSeries.coeff_mk, ← mul_coeff, ← is_pwo_support]
    classical
    refine' sum_filter_ne_zero.symm.trans ((sum_congr _ fun _ _ => rfl).trans sum_filter_ne_zero)
    ext m
    simp only [← nat.mem_antidiagonal, ← And.congr_left_iff, ← mem_add_antidiagonal, ← Ne.def, ← and_iff_left_iff_imp, ←
      mem_filter, ← mem_support]
    intro h1 h2
    contrapose h1
    rw [← Decidable.or_iff_not_and_not] at h1
    cases h1 <;> simp [← h1]

theorem coeff_to_power_series {f : HahnSeries ℕ R} {n : ℕ} : PowerSeries.coeff R n f.toPowerSeries = f.coeff n :=
  PowerSeries.coeff_mk _ _

theorem coeff_to_power_series_symm {f : PowerSeries R} {n : ℕ} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff R n f :=
  rfl

variable (Γ) (R) [OrderedSemiring Γ] [Nontrivial Γ]

/-- Casts a power series as a Hahn series with coefficients from an `ordered_semiring`. -/
def ofPowerSeries : PowerSeries R →+* HahnSeries Γ R :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strict_mono_cast.Injective fun _ _ => Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)

variable {Γ} {R}

theorem of_power_series_injective : Function.Injective (ofPowerSeries Γ R) :=
  emb_domain_injective.comp toPowerSeries.symm.Injective

@[simp]
theorem of_power_series_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x =
      HahnSeries.embDomain
        ⟨⟨(coe : ℕ → Γ), Nat.strict_mono_cast.Injective⟩, fun a b => by
          simp only [← Function.Embedding.coe_fn_mk]
          exact Nat.cast_le⟩
        (toPowerSeries.symm x) :=
  rfl

theorem of_power_series_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff R n x := by
  simp

@[simp]
theorem of_power_series_C (r : R) : ofPowerSeries Γ R (PowerSeries.c R r) = HahnSeries.c r := by
  ext n
  simp only [← C, ← single_coeff, ← of_power_series_apply, ← RingHom.coe_mk]
  split_ifs with hn hn
  · subst hn
    convert @emb_domain_coeff _ _ _ _ _ _ _ _ 0 <;> simp
    
  · rw [emb_domain_notin_image_support]
    simp only [← not_exists, ← Set.mem_image, ← to_power_series_symm_apply_coeff, ← mem_support, ← PowerSeries.coeff_C]
    intro
    simp (config := { contextual := true })[← Ne.symm hn]
    

@[simp]
theorem of_power_series_X : ofPowerSeries Γ R PowerSeries.x = single 1 1 := by
  ext n
  simp only [← single_coeff, ← of_power_series_apply, ← RingHom.coe_mk]
  split_ifs with hn hn
  · rw [hn]
    convert @emb_domain_coeff _ _ _ _ _ _ _ _ 1 <;> simp
    
  · rw [emb_domain_notin_image_support]
    simp only [← not_exists, ← Set.mem_image, ← to_power_series_symm_apply_coeff, ← mem_support, ← PowerSeries.coeff_X]
    intro
    simp (config := { contextual := true })[← Ne.symm hn]
    

@[simp]
theorem of_power_series_X_pow {R} [CommSemiringₓ R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.x ^ n) = single (n : Γ) 1 := by
  rw [RingHom.map_pow]
  induction' n with n ih
  · simp
    rfl
    
  rw [pow_succₓ, ih, of_power_series_X, mul_comm, single_mul_single, one_mulₓ, Nat.cast_succₓ]

/-- The ring `hahn_series (σ →₀ ℕ) R` is isomorphic to `mv_power_series σ R` for a `fintype` `σ`.
We take the index set of the hahn series to be `finsupp` rather than `pi`,
even though we assume `fintype σ` as this is more natural for alignment with `mv_power_series`.
After importing `algebra.order.pi` the ring `hahn_series (σ → ℕ) R` could be constructed instead.
 -/
-- Lemmas about converting hahn_series over fintype to and from mv_power_series
@[simps]
def toMvPowerSeries {σ : Type _} [Fintype σ] : HahnSeries (σ →₀ ℕ) R ≃+* MvPowerSeries σ R where
  toFun := fun f => f.coeff
  invFun := fun f => ⟨(f : (σ →₀ ℕ) → R), Finsupp.is_pwo _⟩
  left_inv := fun f => by
    ext
    simp
  right_inv := fun f => by
    ext
    simp
  map_add' := fun f g => by
    ext
    simp
  map_mul' := fun f g => by
    ext n
    simp only [← MvPowerSeries.coeff_mul]
    classical
    change (f * g).coeff n = _
    simp_rw [mul_coeff]
    refine' sum_filter_ne_zero.symm.trans ((sum_congr _ fun _ _ => rfl).trans sum_filter_ne_zero)
    ext m
    simp only [← And.congr_left_iff, ← mem_add_antidiagonal, ← Ne.def, ← and_iff_left_iff_imp, ← mem_filter, ←
      mem_support, ← Finsupp.mem_antidiagonal]
    intro h1 h2
    contrapose h1
    rw [← Decidable.or_iff_not_and_not] at h1
    cases h1 <;> simp [← h1]

variable {σ : Type _} [Fintype σ]

theorem coeff_to_mv_power_series {f : HahnSeries (σ →₀ ℕ) R} {n : σ →₀ ℕ} :
    MvPowerSeries.coeff R n f.toMvPowerSeries = f.coeff n :=
  rfl

theorem coeff_to_mv_power_series_symm {f : MvPowerSeries σ R} {n : σ →₀ ℕ} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff R n f :=
  rfl

end Semiringₓ

section Algebra

variable (R) [CommSemiringₓ R] {A : Type _} [Semiringₓ A] [Algebra R A]

/-- The `R`-algebra `hahn_series ℕ A` is isomorphic to `power_series A`. -/
@[simps]
def toPowerSeriesAlg : HahnSeries ℕ A ≃ₐ[R] PowerSeries A :=
  { toPowerSeries with
    commutes' := fun r => by
      ext n
      simp only [← algebra_map_apply, ← PowerSeries.algebra_map_apply, ← RingEquiv.to_fun_eq_coe, ← C_apply, ←
        coeff_to_power_series]
      cases n
      · simp only [← PowerSeries.coeff_zero_eq_constant_coeff, ← single_coeff_same]
        rfl
        
      · simp only [← n.succ_ne_zero, ← Ne.def, ← not_false_iff, ← single_coeff_of_ne]
        rw [PowerSeries.coeff_C, if_neg n.succ_ne_zero]
         }

variable (Γ) (R) [OrderedSemiring Γ] [Nontrivial Γ]

/-- Casting a power series as a Hahn series with coefficients from an `ordered_semiring`
  is an algebra homomorphism. -/
@[simps]
def ofPowerSeriesAlg : PowerSeries A →ₐ[R] HahnSeries Γ A :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strict_mono_cast.Injective fun _ _ => Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)

instance powerSeriesAlgebra {S : Type _} [CommSemiringₓ S] [Algebra S (PowerSeries R)] : Algebra S (HahnSeries Γ R) :=
  RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))

variable {R} {S : Type _} [CommSemiringₓ S] [Algebra S (PowerSeries R)]

theorem algebra_map_apply' (x : S) :
    algebraMap S (HahnSeries Γ R) x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl

@[simp]
theorem _root_.polynomial.algebra_map_hahn_series_apply (f : R[X]) :
    algebraMap R[X] (HahnSeries Γ R) f = ofPowerSeries Γ R f :=
  rfl

theorem _root_.polynomial.algebra_map_hahn_series_injective : Function.Injective (algebraMap R[X] (HahnSeries Γ R)) :=
  of_power_series_injective.comp (Polynomial.coe_injective R)

end Algebra

section Valuation

variable (Γ R) [LinearOrderedAddCommGroup Γ] [Ringₓ R] [IsDomain R]

/-- The additive valuation on `hahn_series Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def addVal : AddValuation (HahnSeries Γ R) (WithTop Γ) :=
  AddValuation.of (fun x => if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order) (if_pos rfl)
    ((if_neg one_ne_zero).trans
      (by
        simp [← order_of_ne]))
    (fun x y => by
      by_cases' hx : x = 0
      · by_cases' hy : y = 0 <;>
          · simp [← hx, ← hy]
            
        
      · by_cases' hy : y = 0
        · simp [← hx, ← hy]
          
        · simp only [← hx, ← hy, ← support_nonempty_iff, ← if_neg, ← not_false_iff, ← is_wf_support]
          by_cases' hxy : x + y = 0
          · simp [← hxy]
            
          rw [if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
          exact min_order_le_order_add hxy
          
        )
    fun x y => by
    by_cases' hx : x = 0
    · simp [← hx]
      
    by_cases' hy : y = 0
    · simp [← hy]
      
    rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe, order_mul hx hy]

variable {Γ} {R}

theorem add_val_apply {x : HahnSeries Γ R} :
    addVal Γ R x = if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order :=
  AddValuation.of_apply _

@[simp]
theorem add_val_apply_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : addVal Γ R x = x.order :=
  if_neg hx

theorem add_val_le_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : addVal Γ R x ≤ g := by
  rw [add_val_apply_of_ne (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
  exact order_le_of_coeff_ne_zero h

end Valuation

theorem is_pwo_Union_support_powers [LinearOrderedAddCommGroup Γ] [Ringₓ R] [IsDomain R] {x : HahnSeries Γ R}
    (hx : 0 < addVal Γ R x) : (⋃ n : ℕ, (x ^ n).Support).IsPwo := by
  apply (x.is_wf_support.is_pwo.add_submonoid_closure fun g hg => _).mono _
  · exact WithTop.coe_le_coe.1 (le_transₓ (le_of_ltₓ hx) (add_val_le_of_coeff_ne_zero hg))
    
  refine' Set.Union_subset fun n => _
  induction' n with n ih <;> intro g hn
  · simp only [← exists_prop, ← and_trueₓ, ← Set.mem_singleton_iff, ← Set.set_of_eq_eq_singleton, ← mem_support, ←
      ite_eq_right_iff, ← Ne.def, ← not_false_iff, ← one_ne_zero, ← pow_zeroₓ, ← not_forall, ← one_coeff] at hn
    rw [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
    
  · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hi) (ih hj))
    

section

variable (Γ) (R) [PartialOrderₓ Γ] [AddCommMonoidₓ R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
structure SummableFamily (α : Type _) where
  toFun : α → HahnSeries Γ R
  is_pwo_Union_support' : Set.IsPwo (⋃ a : α, (to_fun a).Support)
  finite_co_support' : ∀ g : Γ, { a | (to_fun a).coeff g ≠ 0 }.Finite

end

namespace SummableFamily

section AddCommMonoidₓ

variable [PartialOrderₓ Γ] [AddCommMonoidₓ R] {α : Type _}

instance : CoeFun (SummableFamily Γ R α) fun _ => α → HahnSeries Γ R :=
  ⟨toFun⟩

theorem is_pwo_Union_support (s : SummableFamily Γ R α) : Set.IsPwo (⋃ a : α, (s a).Support) :=
  s.is_pwo_Union_support'

theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) : (Function.Support fun a => (s a).coeff g).Finite :=
  s.finite_co_support' g

theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α → HahnSeries Γ R) coeFn
  | ⟨f1, hU1, hf1⟩, ⟨f2, hU2, hf2⟩, h => by
    change f1 = f2 at h
    subst h

@[ext]
theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  coe_injective <| funext h

instance : Add (SummableFamily Γ R α) :=
  ⟨fun x y =>
    { toFun := x + y,
      is_pwo_Union_support' :=
        (x.is_pwo_Union_support.union y.is_pwo_Union_support).mono
          (by
            rw [← Set.Union_union_distrib]
            exact Set.Union_mono fun a => support_add_subset),
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).Subset
          (by
            intro a ha
            change (x a).coeff g + (y a).coeff g ≠ 0 at ha
            rw [Set.mem_union, Function.mem_support, Function.mem_support]
            contrapose! ha
            rw [ha.1, ha.2, add_zeroₓ]) }⟩

instance : Zero (SummableFamily Γ R α) :=
  ⟨⟨0, by
      simp , by
      simp ⟩⟩

instance : Inhabited (SummableFamily Γ R α) :=
  ⟨0⟩

@[simp]
theorem coe_add {s t : SummableFamily Γ R α} : ⇑(s + t) = s + t :=
  rfl

theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
  rfl

@[simp]
theorem coe_zero : ((0 : SummableFamily Γ R α) : α → HahnSeries Γ R) = 0 :=
  rfl

theorem zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0 :=
  rfl

instance : AddCommMonoidₓ (SummableFamily Γ R α) where
  add := (· + ·)
  zero := 0
  zero_add := fun s => by
    ext
    apply zero_addₓ
  add_zero := fun s => by
    ext
    apply add_zeroₓ
  add_comm := fun s t => by
    ext
    apply add_commₓ
  add_assoc := fun r s t => by
    ext
    apply add_assocₓ

/-- The infinite sum of a `summable_family` of Hahn series. -/
def hsum (s : SummableFamily Γ R α) : HahnSeries Γ R where
  coeff := fun g => ∑ᶠ i, (s i).coeff g
  is_pwo_support' :=
    s.is_pwo_Union_support.mono fun g => by
      contrapose
      rw [Set.mem_Union, not_exists, Function.mem_support, not_not]
      simp_rw [mem_support, not_not]
      intro h
      rw [finsum_congr h, finsum_zero]

@[simp]
theorem hsum_coeff {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl

theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.Support ⊆ ⋃ a : α, (s a).Support := fun g hg => by
  rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, h1, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_Union]
  exact ⟨a, h2⟩

@[simp]
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  simp only [← hsum_coeff, ← add_coeff, ← add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

end AddCommMonoidₓ

section AddCommGroupₓ

variable [PartialOrderₓ Γ] [AddCommGroupₓ R] {α : Type _} {s t : SummableFamily Γ R α} {a : α}

instance : AddCommGroupₓ (SummableFamily Γ R α) :=
  { SummableFamily.addCommMonoid with
    neg := fun s =>
      { toFun := fun a => -s a,
        is_pwo_Union_support' := by
          simp_rw [support_neg]
          exact s.is_pwo_Union_support',
        finite_co_support' := fun g => by
          simp only [← neg_coeff', ← Pi.neg_apply, ← Ne.def, ← neg_eq_zero]
          exact s.finite_co_support g },
    add_left_neg := fun a => by
      ext
      apply add_left_negₓ }

@[simp]
theorem coe_neg : ⇑(-s) = -s :=
  rfl

theorem neg_apply : (-s) a = -s a :=
  rfl

@[simp]
theorem coe_sub : ⇑(s - t) = s - t :=
  rfl

theorem sub_apply : (s - t) a = s a - t a :=
  rfl

end AddCommGroupₓ

section Semiringₓ

variable [OrderedCancelAddCommMonoid Γ] [Semiringₓ R] {α : Type _}

instance :
    HasSmul (HahnSeries Γ R)
      (SummableFamily Γ R α) where smul := fun x s =>
    { toFun := fun a => x * s a,
      is_pwo_Union_support' := by
        apply (x.is_pwo_support.add s.is_pwo_Union_support).mono
        refine' Set.Subset.trans (Set.Union_mono fun a => support_mul_subset_add_support) _
        intro g
        simp only [← Set.mem_Union, ← exists_imp_distrib]
        exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_Union _ a)) ha,
      finite_co_support' := fun g => by
        refine'
          ((add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g).finite_to_set.bUnion' fun ij hij => _).Subset
            fun a ha => _
        · exact fun ij hij => Function.Support fun a => (s a).coeff ij.2
          
        · apply s.finite_co_support
          
        · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support ha
          simp only [← exists_prop, ← Set.mem_Union, ← mem_add_antidiagonal, ← mul_coeff, ← Ne.def, ← mem_support, ←
            is_pwo_support, ← Prod.exists]
          refine' ⟨i, j, mem_coe.2 (mem_add_antidiagonal.2 ⟨rfl, hi, Set.mem_Union.2 ⟨a, hj⟩⟩), hj⟩
           }

@[simp]
theorem smul_apply {x : HahnSeries Γ R} {s : SummableFamily Γ R α} {a : α} : (x • s) a = x * s a :=
  rfl

instance : Module (HahnSeries Γ R) (SummableFamily Γ R α) where
  smul := (· • ·)
  smul_zero := fun x => ext fun a => mul_zero _
  zero_smul := fun x => ext fun a => zero_mul _
  one_smul := fun x => ext fun a => one_mulₓ _
  add_smul := fun x y s => ext fun a => add_mulₓ _ _ _
  smul_add := fun x s t => ext fun a => mul_addₓ _ _ _
  mul_smul := fun x y s => ext fun a => mul_assoc _ _ _

@[simp]
theorem hsum_smul {x : HahnSeries Γ R} {s : SummableFamily Γ R α} : (x • s).hsum = x * s.hsum := by
  ext g
  simp only [← mul_coeff, ← hsum_coeff, ← smul_apply]
  have h : ∀ i, (s i).Support ⊆ ⋃ j, (s j).Support := Set.subset_Union _
  refine'
    (Eq.trans (finsum_congr fun a => _)
          (finsum_sum_comm (add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g)
            (fun i ij => x.coeff (Prod.fst ij) * (s i).coeff ij.snd) _)).trans
      _
  · refine' sum_subset (add_antidiagonal_mono_right (Set.subset_Union _ a)) _
    rintro ⟨i, j⟩ hU ha
    rw [mem_add_antidiagonal] at *
    rw [not_not.1 fun con => ha ⟨hU.1, hU.2.1, Con⟩, mul_zero]
    
  · rintro ⟨i, j⟩ hij
    refine' (s.finite_co_support j).Subset _
    simp_rw [Function.support_subset_iff', Function.mem_support, not_not]
    intro a ha
    rw [ha, mul_zero]
    
  · refine' (sum_congr rfl _).trans (sum_subset (add_antidiagonal_mono_right _) _).symm
    · rintro ⟨i, j⟩ hij
      rw [mul_finsum]
      apply s.finite_co_support
      
    · intro x hx
      simp only [← Set.mem_Union, ← Ne.def, ← mem_support]
      contrapose! hx
      simp [← hx]
      
    · rintro ⟨i, j⟩ hU ha
      rw [mem_add_antidiagonal] at *
      rw [← hsum_coeff, not_not.1 fun con => ha ⟨hU.1, hU.2.1, Con⟩, mul_zero]
      
    

/-- The summation of a `summable_family` as a `linear_map`. -/
@[simps]
def lsum : SummableFamily Γ R α →ₗ[HahnSeries Γ R] HahnSeries Γ R where
  toFun := hsum
  map_add' := fun _ _ => hsum_add
  map_smul' := fun _ _ => hsum_smul

@[simp]
theorem hsum_sub {R : Type _} [Ringₓ R] {s t : SummableFamily Γ R α} : (s - t).hsum = s.hsum - t.hsum := by
  rw [← lsum_apply, LinearMap.map_sub, lsum_apply, lsum_apply]

end Semiringₓ

section OfFinsupp

variable [PartialOrderₓ Γ] [AddCommMonoidₓ R] {α : Type _}

/-- A family with only finitely many nonzero elements is summable. -/
def ofFinsupp (f : α →₀ HahnSeries Γ R) : SummableFamily Γ R α where
  toFun := f
  is_pwo_Union_support' := by
    apply (f.support.is_pwo_sup (fun a => (f a).Support) fun a ha => (f a).is_pwo_support).mono
    intro g hg
    obtain ⟨a, ha⟩ := Set.mem_Union.1 hg
    have haf : a ∈ f.support := by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, ha⟩
    have h : (fun i => (f i).Support) a ≤ _ := le_sup haf
    exact h ha
  finite_co_support' := fun g => by
    refine' f.support.finite_to_set.subset fun a ha => _
    simp only [← coeff.add_monoid_hom_apply, ← mem_coe, ← Finsupp.mem_support_iff, ← Ne.def, ← Function.mem_support]
    contrapose! ha
    simp [← ha]

@[simp]
theorem coe_of_finsupp {f : α →₀ HahnSeries Γ R} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl

@[simp]
theorem hsum_of_finsupp {f : α →₀ HahnSeries Γ R} : (ofFinsupp f).hsum = f.Sum fun a => id := by
  ext g
  simp only [← hsum_coeff, ← coe_of_finsupp, ← Finsupp.sum, ← Ne.def]
  simp_rw [← coeff.add_monoid_hom_apply, id.def]
  rw [AddMonoidHom.map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [← coeff.add_monoid_hom_apply, ← mem_coe, ← Finsupp.mem_support_iff, ← Ne.def]
  contrapose! h
  simp [← h]

end OfFinsupp

section EmbDomain

variable [PartialOrderₓ Γ] [AddCommMonoidₓ R] {α β : Type _}

/-- A summable family can be reindexed by an embedding without changing its sum. -/
def embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β where
  toFun := fun b => if h : b ∈ Set.Range f then s (Classical.some h) else 0
  is_pwo_Union_support' := by
    refine' s.is_pwo_Union_support.mono (Set.Union_subset fun b g h => _)
    by_cases' hb : b ∈ Set.Range f
    · rw [dif_pos hb] at h
      exact Set.mem_Union.2 ⟨Classical.some hb, h⟩
      
    · contrapose! h
      simp [← hb]
      
  finite_co_support' := fun g =>
    ((s.finite_co_support g).Image f).Subset
      (by
        intro b h
        by_cases' hb : b ∈ Set.Range f
        · simp only [← Ne.def, ← Set.mem_set_of_eq, ← dif_pos hb] at h
          exact ⟨Classical.some hb, h, Classical.some_spec hb⟩
          
        · contrapose! h
          simp only [← Ne.def, ← Set.mem_set_of_eq, ← dif_neg hb, ← not_not, ← zero_coeff]
          )

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

theorem emb_domain_apply : s.embDomain f b = if h : b ∈ Set.Range f then s (Classical.some h) else 0 :=
  rfl

@[simp]
theorem emb_domain_image : s.embDomain f (f a) = s a := by
  rw [emb_domain_apply, dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.some_spec (Set.mem_range_self a)))

@[simp]
theorem emb_domain_notin_range (h : b ∉ Set.Range f) : s.embDomain f b = 0 := by
  rw [emb_domain_apply, dif_neg h]

@[simp]
theorem hsum_emb_domain : (s.embDomain f).hsum = s.hsum := by
  ext g
  simp only [← hsum_coeff, ← emb_domain_apply, ← apply_dite HahnSeries.coeff, ← dite_apply, ← zero_coeff]
  exact finsum_emb_domain f fun a => (s a).coeff g

end EmbDomain

section Powers

variable [LinearOrderedAddCommGroup Γ] [CommRingₓ R] [IsDomain R]

/-- The powers of an element of positive valuation form a summable family. -/
def powers (x : HahnSeries Γ R) (hx : 0 < addVal Γ R x) : SummableFamily Γ R ℕ where
  toFun := fun n => x ^ n
  is_pwo_Union_support' := is_pwo_Union_support_powers hx
  finite_co_support' := fun g => by
    have hpwo := is_pwo_Union_support_powers hx
    by_cases' hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
    swap
    · exact set.finite_empty.subset fun n hn => hg (Set.mem_Union.2 ⟨n, hn⟩)
      
    apply hpwo.is_wf.induction hg
    intro y ys hy
    refine'
      ((((add_antidiagonal x.is_pwo_support hpwo y).finite_to_set.bUnion fun ij hij => hy ij.snd _ _).Image
                Nat.succ).union
            (Set.finite_singleton 0)).Subset
        _
    · exact (mem_add_antidiagonal.1 (mem_coe.1 hij)).2.2
      
    · obtain ⟨rfl, hi, hj⟩ := mem_add_antidiagonal.1 (mem_coe.1 hij)
      rw [← zero_addₓ ij.snd, ← add_assocₓ, add_zeroₓ]
      exact add_lt_add_right (WithTop.coe_lt_coe.1 (lt_of_lt_of_leₓ hx (add_val_le_of_coeff_ne_zero hi))) _
      
    · intro n hn
      cases n
      · exact Set.mem_union_right _ (Set.mem_singleton 0)
        
      · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn
        refine' Set.mem_union_left _ ⟨n, Set.mem_Union.2 ⟨⟨i, j⟩, Set.mem_Union.2 ⟨_, hj⟩⟩, rfl⟩
        simp only [← true_andₓ, ← Set.mem_Union, ← mem_add_antidiagonal, ← mem_coe, ← eq_self_iff_true, ← Ne.def, ←
          mem_support, ← Set.mem_set_of_eq]
        exact ⟨hi, ⟨n, hj⟩⟩
        
      

variable {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x)

@[simp]
theorem coe_powers : ⇑(powers x hx) = pow x :=
  rfl

theorem emb_domain_succ_smul_powers :
    (x • powers x hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ = powers x hx - ofFinsupp (Finsupp.single 0 1) := by
  apply summable_family.ext fun n => _
  cases n
  · rw [emb_domain_notin_range, sub_apply, coe_powers, pow_zeroₓ, coe_of_finsupp, Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
    
  · refine' Eq.trans (emb_domain_image _ ⟨Nat.succ, Nat.succ_injective⟩) _
    simp only [← pow_succₓ, ← coe_powers, ← coe_sub, ← smul_apply, ← coe_of_finsupp, ← Pi.sub_apply]
    rw [Finsupp.single_eq_of_ne n.succ_ne_zero.symm, sub_zero]
    

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul, one_smul, hsum_sub, ← hsum_emb_domain (x • powers x hx) ⟨Nat.succ, Nat.succ_injective⟩,
    emb_domain_succ_smul_powers]
  simp

end Powers

end SummableFamily

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section IsDomain

variable [CommRingₓ R] [IsDomain R]

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.coeff x.order = 1) :
    0 < addVal Γ R (1 - c r * single (-x.order) 1 * x) := by
  have h10 : (1 : R) ≠ 0 := one_ne_zero
  have x0 : x ≠ 0 := ne_zero_of_coeff_ne_zero (right_ne_zero_of_mul_eq_one hr)
  refine' lt_of_le_of_neₓ ((add_val Γ R).map_le_sub (ge_of_eq (add_val Γ R).map_one) _) _
  · simp only [← AddValuation.map_mul]
    rw [add_val_apply_of_ne x0, add_val_apply_of_ne (single_ne_zero h10), add_val_apply_of_ne _, order_C,
      order_single h10, WithTop.coe_zero, zero_addₓ, ← WithTop.coe_add, neg_add_selfₓ, WithTop.coe_zero]
    · exact le_reflₓ 0
      
    · exact C_ne_zero (left_ne_zero_of_mul_eq_one hr)
      
    
  · rw [add_val_apply, ← WithTop.coe_zero]
    split_ifs
    · apply WithTop.coe_ne_top
      
    rw [Ne.def, WithTop.coe_eq_coe]
    intro con
    apply coeff_order_ne_zero h
    rw [← Con, mul_assoc, sub_coeff, one_coeff, if_pos rfl, C_mul_eq_smul, smul_coeff, smul_eq_mul, ←
      add_neg_selfₓ x.order, single_mul_coeff_add, one_mulₓ, hr, sub_self]
    

theorem is_unit_iff {x : HahnSeries Γ R} : IsUnit x ↔ IsUnit (x.coeff x.order) := by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine' is_unit_of_mul_eq_one (u.coeff u.order) (i.coeff i.order) ((mul_coeff_order_add_order u i).symm.trans _)
    rw [ui, one_coeff, if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
    
  · rintro ⟨⟨u, i, ui, iu⟩, h⟩
    rw [Units.coe_mk] at h
    rw [h] at iu
    have h := summable_family.one_sub_self_mul_hsum_powers (unit_aux x iu)
    rw [sub_sub_cancel] at h
    exact is_unit_of_mul_is_unit_right (is_unit_of_mul_eq_one _ _ h)
    

end IsDomain

instance [Field R] : Field (HahnSeries Γ R) :=
  { HahnSeries.is_domain, HahnSeries.commRing with
    inv := fun x =>
      if x0 : x = 0 then 0
      else
        c (x.coeff x.order)⁻¹ * (single (-x.order)) 1 *
          (SummableFamily.powers _ (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))).hsum,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun x x0 => by
      refine' (congr rfl (dif_neg x0)).trans _
      have h := summable_family.one_sub_self_mul_hsum_powers (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))
      rw [sub_sub_cancel] at h
      rw [← mul_assoc, mul_comm x, h] }

end Inversion

end HahnSeries

