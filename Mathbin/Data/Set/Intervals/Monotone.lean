/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Set.Intervals.Disjoint
import Mathbin.Tactic.FieldSimp

/-!
# Monotonicity on intervals

In this file we prove that a function is (strictly) monotone (or antitone) on a linear order `α`
provided that it is (strictly) monotone on `(-∞, a]` and on `[a, +∞)`. We also provide an order
isomorphism `order_iso_Ioo_neg_one_one` between the open interval `(-1, 1)` in a linear ordered
field and the whole field.
-/


open Set

section

variable {α β : Type _} [LinearOrderₓ α] [Preorderₓ β] {a : α} {f : α → β}

/-- If `f` is strictly monotone both on `(-∞, a]` and `[a, ∞)`, then it is strictly monotone on the
whole line. -/
protected theorem StrictMonoOn.Iic_union_Ici (h₁ : StrictMonoOn f (Iic a)) (h₂ : StrictMonoOn f (Ici a)) :
    StrictMono f := by
  intro x y hxy
  cases' lt_or_leₓ a x with hax hxa <;> [skip, cases' le_or_ltₓ y a with hya hay]
  exacts[h₂ hax.le (hax.trans hxy).le hxy, h₁ hxa hya hxy,
    (h₁.monotone_on hxa le_rfl hxa).trans_lt (h₂ le_rfl hay.le hay)]

/-- If `f` is strictly antitone both on `(-∞, a]` and `[a, ∞)`, then it is strictly antitone on the
whole line. -/
protected theorem StrictAntiOn.Iic_union_Ici (h₁ : StrictAntiOn f (Iic a)) (h₂ : StrictAntiOn f (Ici a)) :
    StrictAnti f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

protected theorem MonotoneOn.Iic_union_Ici (h₁ : MonotoneOn f (Iic a)) (h₂ : MonotoneOn f (Ici a)) : Monotone f := by
  intro x y hxy
  cases' le_totalₓ x a with hxa hax <;> [cases' le_totalₓ y a with hya hay, skip]
  exacts[h₁ hxa hya hxy, (h₁ hxa le_rfl hxa).trans (h₂ le_rfl hay hay), h₂ hax (hax.trans hxy) hxy]

protected theorem AntitoneOn.Iic_union_Ici (h₁ : AntitoneOn f (Iic a)) (h₂ : AntitoneOn f (Ici a)) : Antitone f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

end

section OrderedGroup

variable {G H : Type _} [LinearOrderedAddCommGroup G] [OrderedAddCommGroup H]

theorem strict_mono_of_odd_strict_mono_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x) (h₂ : StrictMonoOn f (Ici 0)) :
    StrictMono f := by
  refine' StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 _) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)

theorem monotone_of_odd_of_monotone_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x) (h₂ : MonotoneOn f (Ici 0)) :
    Monotone f := by
  refine' MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 _) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)

end OrderedGroup

/-- In a linear ordered field, the whole field is order isomorphic to the open interval `(-1, 1)`.
We consider the actual implementation to be a "black box", so it is irreducible.
-/
irreducible_def orderIsoIooNegOneOne (k : Type _) [LinearOrderedField k] : k ≃o Ioo (-1 : k) 1 := by
  refine' StrictMono.orderIsoOfRightInverse _ _ (fun x => x / (1 - abs x)) _
  · refine' cod_restrict (fun x => x / (1 + abs x)) _ fun x => abs_lt.1 _
    have H : 0 < 1 + abs x := (abs_nonneg x).trans_lt (lt_one_add _)
    calc abs (x / (1 + abs x)) = abs x / (1 + abs x) := by
        rw [abs_div, abs_of_pos H]_ < 1 := (div_lt_one H).2 (lt_one_add _)
    
  · refine' (strict_mono_of_odd_strict_mono_on_nonneg _ _).codRestrict _
    · intro x
      simp only [← abs_neg, ← neg_div]
      
    · rintro x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy
      simp [← abs_of_nonneg, ← mul_addₓ, ← mul_comm x y, ← div_lt_div_iff, ← hx.trans_lt (lt_one_add _), ←
        hy.trans_lt (lt_one_add _), *]
      
    
  · refine' fun x => Subtype.ext _
    have : 0 < 1 - abs (x : k) := sub_pos.2 (abs_lt.2 x.2)
    field_simp [← abs_div, ← this.ne', ← abs_of_pos this]
    

section Ixx

variable {α β : Type _} [Preorderₓ α] [Preorderₓ β] {f g : α → β} {s : Set α}

theorem antitone_Ici : Antitone (Ici : α → Set α) := fun _ _ => Ici_subset_Ici.2

theorem monotone_Iic : Monotone (Iic : α → Set α) := fun _ _ => Iic_subset_Iic.2

theorem antitone_Ioi : Antitone (Ioi : α → Set α) := fun _ _ => Ioi_subset_Ioi

theorem monotone_Iio : Monotone (Iio : α → Set α) := fun _ _ => Iio_subset_Iio

protected theorem Monotone.Ici (hf : Monotone f) : Antitone fun x => Ici (f x) :=
  antitone_Ici.comp_monotone hf

protected theorem MonotoneOn.Ici (hf : MonotoneOn f s) : AntitoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_monotone_on hf

protected theorem Antitone.Ici (hf : Antitone f) : Monotone fun x => Ici (f x) :=
  antitone_Ici.comp hf

protected theorem AntitoneOn.Ici (hf : AntitoneOn f s) : MonotoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_antitone_on hf

protected theorem Monotone.Iic (hf : Monotone f) : Monotone fun x => Iic (f x) :=
  monotone_Iic.comp hf

protected theorem MonotoneOn.Iic (hf : MonotoneOn f s) : MonotoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_monotone_on hf

protected theorem Antitone.Iic (hf : Antitone f) : Antitone fun x => Iic (f x) :=
  monotone_Iic.comp_antitone hf

protected theorem AntitoneOn.Iic (hf : AntitoneOn f s) : AntitoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_antitone_on hf

protected theorem Monotone.Ioi (hf : Monotone f) : Antitone fun x => Ioi (f x) :=
  antitone_Ioi.comp_monotone hf

protected theorem MonotoneOn.Ioi (hf : MonotoneOn f s) : AntitoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_monotone_on hf

protected theorem Antitone.Ioi (hf : Antitone f) : Monotone fun x => Ioi (f x) :=
  antitone_Ioi.comp hf

protected theorem AntitoneOn.Ioi (hf : AntitoneOn f s) : MonotoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_antitone_on hf

protected theorem Monotone.Iio (hf : Monotone f) : Monotone fun x => Iio (f x) :=
  monotone_Iio.comp hf

protected theorem MonotoneOn.Iio (hf : MonotoneOn f s) : MonotoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_monotone_on hf

protected theorem Antitone.Iio (hf : Antitone f) : Antitone fun x => Iio (f x) :=
  monotone_Iio.comp_antitone hf

protected theorem AntitoneOn.Iio (hf : AntitoneOn f s) : AntitoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_antitone_on hf

protected theorem Monotone.Icc (hf : Monotone f) (hg : Antitone g) : Antitone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic

protected theorem MonotoneOn.Icc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic

protected theorem Antitone.Icc (hf : Antitone f) (hg : Monotone g) : Monotone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic

protected theorem AntitoneOn.Icc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic

protected theorem Monotone.Ico (hf : Monotone f) (hg : Antitone g) : Antitone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio

protected theorem MonotoneOn.Ico (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio

protected theorem Antitone.Ico (hf : Antitone f) (hg : Monotone g) : Monotone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio

protected theorem AntitoneOn.Ico (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio

protected theorem Monotone.Ioc (hf : Monotone f) (hg : Antitone g) : Antitone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic

protected theorem MonotoneOn.Ioc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic

protected theorem Antitone.Ioc (hf : Antitone f) (hg : Monotone g) : Monotone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic

protected theorem AntitoneOn.Ioc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic

protected theorem Monotone.Ioo (hf : Monotone f) (hg : Antitone g) : Antitone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio

protected theorem MonotoneOn.Ioo (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio

protected theorem Antitone.Ioo (hf : Antitone f) (hg : Monotone g) : Monotone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio

protected theorem AntitoneOn.Ioo (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio

end Ixx

section Union

variable {α β : Type _} [SemilatticeSup α] [LinearOrderₓ β] {f g : α → β} {a b : β}

theorem Union_Ioo_of_mono_of_is_glb_of_is_lub (hf : Antitone f) (hg : Monotone g) (ha : IsGlb (Range f) a)
    (hb : IsLub (Range g) b) : (⋃ x, Ioo (f x) (g x)) = Ioo a b :=
  calc
    (⋃ x, Ioo (f x) (g x)) = (⋃ x, Ioi (f x)) ∩ ⋃ x, Iio (g x) := Union_inter_of_monotone hf.Ioi hg.Iio
    _ = Ioi a ∩ Iio b := congr_arg2ₓ (· ∩ ·) ha.Union_Ioi_eq hb.Union_Iio_eq
    

end Union

