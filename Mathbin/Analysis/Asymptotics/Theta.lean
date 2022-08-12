/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# Asymptotic equivalence up to a constant

In this file we define `asymptotics.is_Theta l f g` (notation: `f =Θ[l] g`) as
`f =O[l] g ∧ g =O[l] f`, then prove basic properties of this equivalence relation.
-/


open Filter

open TopologicalSpace

namespace Asymptotics

variable {α : Type _} {β : Type _} {E : Type _} {F : Type _} {G : Type _} {E' : Type _} {F' : Type _} {G' : Type _}
  {E'' : Type _} {F'' : Type _} {G'' : Type _} {R : Type _} {R' : Type _} {𝕜 : Type _} {𝕜' : Type _}

variable [HasNorm E] [HasNorm F] [HasNorm G]

variable [SemiNormedGroup E'] [SemiNormedGroup F'] [SemiNormedGroup G']

variable [NormedGroup E''] [NormedGroup F''] [NormedGroup G'']

variable [SemiNormedRing R] [SemiNormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']

variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}

variable {f' : α → E'} {g' : α → F'} {k' : α → G'}

variable {f'' : α → E''} {g'' : α → F''}

variable {l l' : Filter α}

/-- We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and
`g =O[l] f`. -/
def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  IsO l f g ∧ IsO l g f

-- mathport name: «expr =Θ[ ] »
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g

theorem IsO.antisymm (h₁ : f =O[l] g) (h₂ : g =O[l] f) : f =Θ[l] g :=
  ⟨h₁, h₂⟩

@[refl]
theorem is_Theta_refl (f : α → E) (l : Filter α) : f =Θ[l] f :=
  ⟨is_O_refl _ _, is_O_refl _ _⟩

theorem is_Theta_rfl : f =Θ[l] f :=
  is_Theta_refl _ _

@[symm]
theorem IsTheta.symm (h : f =Θ[l] g) : g =Θ[l] f :=
  h.symm

theorem is_Theta_comm : f =Θ[l] g ↔ g =Θ[l] f :=
  ⟨fun h => h.symm, fun h => h.symm⟩

@[trans]
theorem IsTheta.trans {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g) (h₂ : g =Θ[l] k) : f =Θ[l] k :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

@[trans]
theorem IsO.trans_is_Theta {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =O[l] g) (h₂ : g =Θ[l] k) : f =O[l] k :=
  h₁.trans h₂.1

@[trans]
theorem IsTheta.trans_is_O {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g) (h₂ : g =O[l] k) : f =O[l] k :=
  h₁.1.trans h₂

@[trans]
theorem IsOₓ.trans_is_Theta {f : α → E} {g : α → F} {k : α → G'} (h₁ : f =o[l] g) (h₂ : g =Θ[l] k) : f =o[l] k :=
  h₁.trans_is_O h₂.1

@[trans]
theorem IsTheta.trans_is_o {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g) (h₂ : g =o[l] k) : f =o[l] k :=
  h₁.1.trans_is_o h₂

@[trans]
theorem IsTheta.trans_eventually_eq {f : α → E} {g₁ g₂ : α → F} (h : f =Θ[l] g₁) (hg : g₁ =ᶠ[l] g₂) : f =Θ[l] g₂ :=
  ⟨h.1.trans_eventually_eq hg, hg.symm.trans_is_O h.2⟩

@[trans]
theorem _root_.filter.eventually_eq.trans_is_Theta {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂) (h : f₂ =Θ[l] g) :
    f₁ =Θ[l] g :=
  ⟨hf.trans_is_O h.1, h.2.trans_eventually_eq hf.symm⟩

@[simp]
theorem is_Theta_norm_left : (fun x => ∥f' x∥) =Θ[l] g ↔ f' =Θ[l] g := by
  simp [← is_Theta]

@[simp]
theorem is_Theta_norm_right : (f =Θ[l] fun x => ∥g' x∥) ↔ f =Θ[l] g' := by
  simp [← is_Theta]

alias is_Theta_norm_left ↔ is_Theta.of_norm_left is_Theta.norm_left

alias is_Theta_norm_right ↔ is_Theta.of_norm_right is_Theta.norm_right

theorem is_Theta_of_norm_eventually_eq (h : (fun x => ∥f x∥) =ᶠ[l] fun x => ∥g x∥) : f =Θ[l] g :=
  ⟨IsO.of_bound 1 <| by
      simpa only [← one_mulₓ] using h.le,
    IsO.of_bound 1 <| by
      simpa only [← one_mulₓ] using h.symm.le⟩

theorem is_Theta_of_norm_eventually_eq' {g : α → ℝ} (h : (fun x => ∥f' x∥) =ᶠ[l] g) : f' =Θ[l] g :=
  is_Theta_of_norm_eventually_eq <|
    h.mono fun x hx => by
      simp only [hx, ← norm_norm]

theorem IsTheta.is_o_congr_left (h : f' =Θ[l] g') : f' =o[l] k ↔ g' =o[l] k :=
  ⟨h.symm.trans_is_o, h.trans_is_o⟩

theorem IsTheta.is_o_congr_right (h : g' =Θ[l] k') : f =o[l] g' ↔ f =o[l] k' :=
  ⟨fun H => H.trans_is_Theta h, fun H => H.trans_is_Theta h.symm⟩

theorem IsTheta.is_O_congr_left (h : f' =Θ[l] g') : f' =O[l] k ↔ g' =O[l] k :=
  ⟨h.symm.trans_is_O, h.trans_is_O⟩

theorem IsTheta.is_O_congr_right (h : g' =Θ[l] k') : f =O[l] g' ↔ f =O[l] k' :=
  ⟨fun H => H.trans_is_Theta h, fun H => H.trans_is_Theta h.symm⟩

theorem IsTheta.mono (h : f =Θ[l] g) (hl : l' ≤ l) : f =Θ[l'] g :=
  ⟨h.1.mono hl, h.2.mono hl⟩

theorem IsTheta.sup (h : f' =Θ[l] g') (h' : f' =Θ[l'] g') : f' =Θ[l⊔l'] g' :=
  ⟨h.1.sup h'.1, h.2.sup h'.2⟩

@[simp]
theorem is_Theta_sup : f' =Θ[l⊔l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

theorem IsTheta.eq_zero_iff (h : f'' =Θ[l] g'') : ∀ᶠ x in l, f'' x = 0 ↔ g'' x = 0 :=
  h.1.eq_zero_imp.mp <| h.2.eq_zero_imp.mono fun x => Iff.intro

theorem IsTheta.tendsto_zero_iff (h : f'' =Θ[l] g'') : Tendsto f'' l (𝓝 0) ↔ Tendsto g'' l (𝓝 0) := by
  simp only [is_o_one_iff ℝ, ← h.is_o_congr_left]

theorem IsTheta.tendsto_norm_at_top_iff (h : f' =Θ[l] g') : Tendsto (norm ∘ f') l atTop ↔ Tendsto (norm ∘ g') l atTop :=
  by
  simp only [is_o_const_left_of_ne (@one_ne_zero ℝ _ _), ← h.is_o_congr_right]

theorem IsTheta.is_bounded_under_le_iff (h : f' =Θ[l] g') :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f') ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ g') := by
  simp only [is_O_const_of_ne (@one_ne_zero ℝ _ _), ← h.is_O_congr_left]

theorem IsTheta.smul [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {f₁ : α → 𝕜} {f₂ : α → 𝕜'} {g₁ : α → E'} {g₂ : α → F'}
    (hf : f₁ =Θ[l] f₂) (hg : g₁ =Θ[l] g₂) : (fun x => f₁ x • g₁ x) =Θ[l] fun x => f₂ x • g₂ x :=
  ⟨hf.1.smul hg.1, hf.2.smul hg.2⟩

theorem IsTheta.mul {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x => f₁ x * f₂ x) =Θ[l] fun x => g₁ x * g₂ x :=
  h₁.smul h₂

theorem IsTheta.inv {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) : (fun x => (f x)⁻¹) =Θ[l] fun x => (g x)⁻¹ :=
  ⟨h.2.inv_rev h.1.eq_zero_imp, h.1.inv_rev h.2.eq_zero_imp⟩

@[simp]
theorem is_Theta_inv {f : α → 𝕜} {g : α → 𝕜'} : ((fun x => (f x)⁻¹) =Θ[l] fun x => (g x)⁻¹) ↔ f =Θ[l] g :=
  ⟨fun h => by
    simpa only [← inv_invₓ] using h.inv, IsTheta.inv⟩

theorem IsTheta.div {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x => f₁ x / f₂ x) =Θ[l] fun x => g₁ x / g₂ x := by
  simpa only [← div_eq_mul_inv] using h₁.mul h₂.inv

theorem IsTheta.pow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℕ) : (fun x => f x ^ n) =Θ[l] fun x => g x ^ n :=
  ⟨h.1.pow n, h.2.pow n⟩

theorem IsTheta.zpow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℤ) : (fun x => f x ^ n) =Θ[l] fun x => g x ^ n := by
  cases n
  · simpa only [← zpow_of_nat] using h.pow _
    
  · simpa only [← zpow_neg_succ_of_nat] using (h.pow _).inv
    

theorem is_Theta_const_const {c₁ : E''} {c₂ : F''} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) : (fun x : α => c₁) =Θ[l] fun x => c₂ :=
  ⟨is_O_const_const _ h₂ _, is_O_const_const _ h₁ _⟩

@[simp]
theorem is_Theta_const_const_iff [NeBot l] {c₁ : E''} {c₂ : F''} :
    ((fun x : α => c₁) =Θ[l] fun x => c₂) ↔ (c₁ = 0 ↔ c₂ = 0) := by
  simpa only [← is_Theta, ← is_O_const_const_iff, iff_def] using Iff.comm

@[simp]
theorem is_Theta_zero_left : (fun x => (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0 := by
  simp only [← is_Theta, ← is_O_zero, ← is_O_zero_right_iff, ← true_andₓ]

@[simp]
theorem is_Theta_zero_right : (f'' =Θ[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  is_Theta_comm.trans is_Theta_zero_left

theorem is_Theta_const_smul_left [NormedSpace 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =Θ[l] g ↔ f' =Θ[l] g :=
  and_congr (is_O_const_smul_left hc) (is_O_const_smul_right hc)

alias is_Theta_const_smul_left ↔ is_Theta.of_const_smul_left is_Theta.const_smul_left

theorem is_Theta_const_smul_right [NormedSpace 𝕜 F'] {c : 𝕜} (hc : c ≠ 0) : (f =Θ[l] fun x => c • g' x) ↔ f =Θ[l] g' :=
  and_congr (is_O_const_smul_right hc) (is_O_const_smul_left hc)

alias is_Theta_const_smul_right ↔ is_Theta.of_const_smul_right is_Theta.const_smul_right

theorem is_Theta_const_mul_left {c : 𝕜} {f : α → 𝕜} (hc : c ≠ 0) : (fun x => c * f x) =Θ[l] g ↔ f =Θ[l] g := by
  simpa only [smul_eq_mul] using is_Theta_const_smul_left hc

alias is_Theta_const_mul_left ↔ is_Theta.of_const_mul_left is_Theta.const_mul_left

theorem is_Theta_const_mul_right {c : 𝕜} {g : α → 𝕜} (hc : c ≠ 0) : (f =Θ[l] fun x => c * g x) ↔ f =Θ[l] g := by
  simpa only [smul_eq_mul] using is_Theta_const_smul_right hc

alias is_Theta_const_mul_right ↔ is_Theta.of_const_mul_right is_Theta.const_mul_right

end Asymptotics

