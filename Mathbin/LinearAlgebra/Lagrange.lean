/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s x` where `s : finset F` and `x : F`: the Lagrange basis polynomial
  that evaluates to `1` at `x` and `0` at other elements of `s`.
* `lagrange.interpolate s f` where `s : finset F` and `f : F → F`: the Lagrange interpolant
  that evaluates to `f x` at `x` for `x ∈ s`.
-/


noncomputable section

open BigOperators Classical Polynomial

universe u

namespace Lagrange

variable {F : Type u} [DecidableEq F] [Field F] (s : Finset F)

variable {F' : Type u} [Field F'] (s' : Finset F')

open Polynomial

/-- Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/
def basis (x : F) : F[X] :=
  ∏ y in s.erase x, c (x - y)⁻¹ * (X - c y)

@[simp]
theorem basis_empty (x : F) : basis ∅ x = 1 :=
  rfl

@[simp]
theorem basis_singleton_self (x : F) : basis {x} x = 1 := by
  rw [Basis, Finset.erase_singleton, Finset.prod_empty]

@[simp]
theorem eval_basis_self (x : F) : (basis s x).eval x = 1 := by
  rw [Basis, ← coe_eval_ring_hom, (eval_ring_hom x).map_prod, coe_eval_ring_hom, Finset.prod_eq_one]
  intro y hy
  simp_rw [eval_mul, eval_sub, eval_C, eval_X]
  exact inv_mul_cancel (sub_ne_zero_of_ne (Finset.ne_of_mem_erase hy).symm)

@[simp]
theorem eval_basis_ne (x y : F) (h1 : y ∈ s) (h2 : y ≠ x) : (basis s x).eval y = 0 := by
  rw [Basis, ← coe_eval_ring_hom, (eval_ring_hom y).map_prod, coe_eval_ring_hom,
    Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h2, h1⟩)]
  simp_rw [eval_mul, eval_sub, eval_C, eval_X, sub_self, mul_zero]

theorem eval_basis (x y : F) (h : y ∈ s) : (basis s x).eval y = if y = x then 1 else 0 := by
  split_ifs with H
  · subst H
    apply eval_basis_self
    
  · exact eval_basis_ne s x y h H
    

@[simp]
theorem nat_degree_basis (x : F) (hx : x ∈ s) : (basis s x).natDegree = s.card - 1 := by
  unfold Basis
  generalize hsx : s.erase x = sx
  have : x ∉ sx := hsx ▸ Finset.not_mem_erase x s
  rw [← Finset.insert_erase hx, hsx, Finset.card_insert_of_not_mem this, add_tsub_cancel_right]
  clear hx hsx s
  revert this
  apply sx.induction_on
  · intro hx
    rw [Finset.prod_empty, nat_degree_one]
    rfl
    
  · intro y s hys ih hx
    rw [Finset.mem_insert, not_or_distrib] at hx
    have h1 : C (x - y)⁻¹ ≠ C 0 := fun h => hx.1 (eq_of_sub_eq_zero <| inv_eq_zero.1 <| C_inj.1 h)
    have h2 : X ^ 1 - C y ≠ 0 := by
      convert X_pow_sub_C_ne_zero zero_lt_one y
    rw [C_0] at h1
    rw [pow_oneₓ] at h2
    rw [Finset.prod_insert hys, nat_degree_mul (mul_ne_zero h1 h2), ih hx.2, Finset.card_insert_of_not_mem hys,
      nat_degree_mul h1 h2, nat_degree_C, zero_addₓ, nat_degree, degree_X_sub_C, add_commₓ]
    rfl
    rw [Ne, Finset.prod_eq_zero_iff]
    rintro ⟨z, hzs, hz⟩
    rw [mul_eq_zero] at hz
    cases' hz with hz hz
    · rw [← C_0, C_inj, inv_eq_zero, sub_eq_zero] at hz
      exact hx.2 (hz.symm ▸ hzs)
      
    · rw [← pow_oneₓ (X : F[X])] at hz
      exact X_pow_sub_C_ne_zero zero_lt_one _ hz
      
    

variable (f : F → F)

/-- Lagrange interpolation: given a finset `s` and a function `f : F → F`,
`interpolate s f` is the unique polynomial of degree `< s.card`
that takes value `f x` on all `x` in `s`. -/
def interpolate : F[X] :=
  ∑ x in s, c (f x) * basis s x

@[simp]
theorem interpolate_empty (f) : interpolate (∅ : Finset F) f = 0 :=
  rfl

@[simp]
theorem interpolate_singleton (f) (x : F) : interpolate {x} f = c (f x) := by
  rw [interpolate, Finset.sum_singleton, basis_singleton_self, mul_oneₓ]

@[simp]
theorem eval_interpolate (x) (H : x ∈ s) : eval x (interpolate s f) = f x := by
  rw [interpolate, ← coe_eval_ring_hom, RingHom.map_sum, coe_eval_ring_hom, Finset.sum_eq_single x]
  · simp
    
  · intro y hy hxy
    simp [← eval_basis_ne s y x H hxy.symm]
    
  · intro h
    exact (h H).elim
    

theorem degree_interpolate_lt : (interpolate s f).degree < s.card :=
  if H : s = ∅ then by
    subst H
    rw [interpolate_empty, degree_zero]
    exact WithBot.bot_lt_coe _
  else
    (degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff <| WithBot.bot_lt_coe s.card).2 fun b _ =>
        calc
          (c (f b) * basis s b).degree ≤ (c (f b)).degree + (basis s b).degree := degree_mul_le _ _
          _ ≤ 0 + (basis s b).degree := add_le_add_right degree_C_le _
          _ = (basis s b).degree := zero_addₓ _
          _ ≤ (basis s b).natDegree := degree_le_nat_degree
          _ = (s.card - 1 : ℕ) := by
            rwa [nat_degree_basis]
          _ < s.card := WithBot.coe_lt_coe.2 (Nat.pred_ltₓ <| mt Finset.card_eq_zero.1 H)
          

theorem degree_interpolate_erase {x} (hx : x ∈ s) : (interpolate (s.erase x) f).degree < (s.card - 1 : ℕ) := by
  convert degree_interpolate_lt (s.erase x) f
  rw [Finset.card_erase_of_mem hx]

theorem interpolate_eq_of_eval_eq (f g : F → F) {s : Finset F} (hs : ∀, ∀ x ∈ s, ∀, f x = g x) :
    interpolate s f = interpolate s g := by
  rw [interpolate, interpolate]
  refine' Finset.sum_congr rfl fun x hx => _
  rw [hs x hx]

/-- Linear version of `interpolate`. -/
def linterpolate : (F → F) →ₗ[F] Polynomial F where
  toFun := interpolate s
  map_add' := fun f g => by
    simp_rw [interpolate, ← Finset.sum_add_distrib, ← add_mulₓ, ← C_add]
    rfl
  map_smul' := fun c f => by
    simp_rw [interpolate, Finset.smul_sum, C_mul', smul_smul]
    rfl

@[simp]
theorem interpolate_add (f g) : interpolate s (f + g) = interpolate s f + interpolate s g :=
  (linterpolate s).map_add f g

@[simp]
theorem interpolate_zero : interpolate s 0 = 0 :=
  (linterpolate s).map_zero

@[simp]
theorem interpolate_neg (f) : interpolate s (-f) = -interpolate s f :=
  (linterpolate s).map_neg f

@[simp]
theorem interpolate_sub (f g) : interpolate s (f - g) = interpolate s f - interpolate s g :=
  (linterpolate s).map_sub f g

@[simp]
theorem interpolate_smul (c : F) (f) : interpolate s (c • f) = c • interpolate s f :=
  (linterpolate s).map_smul c f

theorem eq_zero_of_eval_eq_zero {f : F'[X]} (hf1 : f.degree < s'.card) (hf2 : ∀, ∀ x ∈ s', ∀, f.eval x = 0) : f = 0 :=
  by_contradiction fun hf3 =>
    not_le_of_lt hf1 <|
      calc
        (s'.card : WithBot ℕ) ≤ f.roots.toFinset.card :=
          WithBot.coe_le_coe.2 <|
            Finset.card_le_of_subset fun x hx => Multiset.mem_to_finset.mpr <| (mem_roots hf3).2 <| hf2 x hx
        _ ≤ f.roots.card := WithBot.coe_le_coe.2 <| f.roots.to_finset_card_le
        _ ≤ f.degree := card_roots hf3
        

theorem eq_of_eval_eq {f g : F'[X]} (hf : f.degree < s'.card) (hg : g.degree < s'.card)
    (hfg : ∀, ∀ x ∈ s', ∀, f.eval x = g.eval x) : f = g :=
  eq_of_sub_eq_zero <|
    eq_zero_of_eval_eq_zero s' (lt_of_le_of_ltₓ (degree_sub_le f g) <| max_ltₓ hf hg) fun x hx => by
      rw [eval_sub, hfg x hx, sub_self]

theorem eq_interpolate_of_eval_eq {g : F[X]} (hg : g.degree < s.card) (hgf : ∀, ∀ x ∈ s, ∀, g.eval x = f x) :
    interpolate s f = g :=
  (eq_of_eval_eq s (degree_interpolate_lt _ _) hg) fun x hx => by
    rw [hgf x hx]
    exact eval_interpolate _ _ _ hx

theorem eq_interpolate (f : F[X]) (hf : f.degree < s.card) : (interpolate s fun x => f.eval x) = f :=
  (eq_of_eval_eq s (degree_interpolate_lt s _) hf) fun x hx => eval_interpolate s _ x hx

/-- Lagrange interpolation induces isomorphism between functions from `s` and polynomials
of degree less than `s.card`. -/
def funEquivDegreeLt : degreeLt F s.card ≃ₗ[F] s → F where
  toFun := fun f x => f.1.eval x
  map_add' := fun f g => funext fun x => eval_add
  map_smul' := fun c f =>
    funext <| by
      simp
  invFun := fun f =>
    ⟨interpolate s fun x => if hx : x ∈ s then f ⟨x, hx⟩ else 0, mem_degree_lt.2 <| degree_interpolate_lt _ _⟩
  left_inv := fun f => by
    apply Subtype.eq
    simp only [← Subtype.coe_mk, ← Subtype.val_eq_coe, ← dite_eq_ite]
    convert eq_interpolate s f (mem_degree_lt.1 f.2) using 1
    rw [interpolate_eq_of_eval_eq]
    intro x hx
    rw [if_pos hx]
  right_inv := fun f =>
    funext fun ⟨x, hx⟩ => by
      convert eval_interpolate s _ x hx
      simp_rw [dif_pos hx]

theorem interpolate_eq_interpolate_erase_add {x y : F} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    interpolate s f = c (y - x)⁻¹ * ((X - c x) * interpolate (s.erase x) f + (c y - X) * interpolate (s.erase y) f) :=
  by
  refine' eq_interpolate_of_eval_eq _ _ _ fun z hz => _
  · rw [degree_mul, degree_C (inv_ne_zero (sub_ne_zero.2 hxy.symm)), zero_addₓ]
    refine' lt_of_le_of_ltₓ (degree_add_le _ _) (max_ltₓ _ _)
    · rw [degree_mul, degree_X_sub_C]
      convert (WithBot.add_lt_add_iff_left WithBot.coe_ne_bot).2 (degree_interpolate_erase s f hx)
      simp [← Nat.one_add, ← Nat.sub_one, ← Nat.succ_pred_eq_of_posₓ (Finset.card_pos.2 ⟨x, hx⟩)]
      
    · rw [degree_mul, ← neg_sub, degree_neg, degree_X_sub_C]
      convert (WithBot.add_lt_add_iff_left WithBot.coe_ne_bot).2 (degree_interpolate_erase s f hy)
      simp [← Nat.one_add, ← Nat.sub_one, ← Nat.succ_pred_eq_of_posₓ (Finset.card_pos.2 ⟨y, hy⟩)]
      
    
  · by_cases' hzx : z = x
    · simp [← hzx, ← eval_interpolate (s.erase y) f x (Finset.mem_erase_of_ne_of_mem hxy hx), ←
        inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hxy.symm)]
      
    · by_cases' hzy : z = y
      · simp [← hzy, ← eval_interpolate (s.erase x) f y (Finset.mem_erase_of_ne_of_mem hxy.symm hy), ←
          inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hxy.symm)]
        
      · simp only [← eval_interpolate (s.erase x) f z (Finset.mem_erase_of_ne_of_mem hzx hz), ←
          eval_interpolate (s.erase y) f z (Finset.mem_erase_of_ne_of_mem hzy hz), ←
          inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hxy.symm), ← eval_mul, ← eval_C, ← eval_add, ← eval_sub, ← eval_X]
        ring
        
      
    

end Lagrange

