/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.LinearAlgebra.SpecialLinearGroup

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a given group
parametrized by some Type. This is modeled on the slash action of `GL_pos (fin 2) ℝ` on the space
of modular forms.
-/


open Complex UpperHalfPlane

open UpperHalfPlane

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Finₓ 2) (Finₓ 2) _) _

-- mathport name: «exprGL( , )⁺»
local notation "GL(" n ", " R ")" "⁺" => Matrix.gLPos (Finₓ n) R

-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Finₓ n) R

/-- A general version of the slash action of the space of modular forms.-/
class SlashAction (β : Type _) (G : Type _) (α : Type _) (γ : Type _) [Groupₓ G] [Ringₓ α] [HasSmul γ α] where
  map : β → G → α → α
  mul_zero : ∀ (k : β) (g : G), map k g 0 = 0
  one_mul : ∀ (k : β) (a : α), map k 1 a = a
  right_action : ∀ (k : β) (g h : G) (a : α), map k h (map k g a) = map k (g * h) a
  smul_action : ∀ (k : β) (g : G) (a : α) (z : γ), map k g (z • a) = z • map k g a
  AddAction : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b

/-- Slash_action induced by a monoid homomorphism.-/
def monoidHomSlashAction {β : Type _} {G : Type _} {H : Type _} {α : Type _} {γ : Type _} [Groupₓ G] [Ringₓ α]
    [HasSmul γ α] [Groupₓ H] [SlashAction β G α γ] (h : H →* G) : SlashAction β H α γ where
  map := fun k g a => SlashAction.map γ k (h g) a
  mul_zero := by
    intro k g
    apply SlashAction.mul_zero k (h g)
  one_mul := by
    intro k a
    simp only [← map_one]
    apply SlashAction.one_mul
  right_action := by
    simp only [← map_mul]
    intro k g gg a
    apply SlashAction.right_action
  smul_action := by
    intro k g a z
    apply SlashAction.smul_action
  AddAction := by
    intro k g a b
    apply SlashAction.add_action

namespace ModularForms

noncomputable section

/-- The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash : ℤ → GL(2, ℝ)⁺ → (ℍ → ℂ) → ℍ → ℂ := fun k γ f => fun x : ℍ =>
  f (γ • x) * ((↑ₘγ).det : ℝ) ^ (k - 1) * UpperHalfPlane.denom γ x ^ -k

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ℍ → ℂ)

-- mathport name: «expr ∣[ ] »
localized [ModularForms] notation:100 f " ∣[" k "]" γ:100 => slash k γ f

theorem slash_right_action (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ) : (f ∣[k]A) ∣[k]B = f ∣[k](A * B) := by
  ext1
  simp_rw [slash, UpperHalfPlane.denom_cocycle A B x]
  have e3 : (A * B) • x = A • B • x := by
    convert UpperHalfPlane.mul_smul' A B x
  rw [e3]
  simp only [← UpperHalfPlane.num, ← UpperHalfPlane.denom, ← of_real_mul, ← Subgroup.coe_mul, ← coe_coe, ←
    UpperHalfPlane.coe_smul, ← Units.coe_mul, ← Matrix.mul_eq_mul, ← Matrix.det_mul, ← UpperHalfPlane.smulAux, ←
    UpperHalfPlane.smulAux', ← Subtype.coe_mk] at *
  field_simp
  have :
    (((↑(↑A : GL (Finₓ 2) ℝ) : Matrix (Finₓ 2) (Finₓ 2) ℝ).det : ℂ) *
          ((↑(↑B : GL (Finₓ 2) ℝ) : Matrix (Finₓ 2) (Finₓ 2) ℝ).det : ℂ)) ^
        (k - 1) =
      ((↑(↑A : GL (Finₓ 2) ℝ) : Matrix (Finₓ 2) (Finₓ 2) ℝ).det : ℂ) ^ (k - 1) *
        ((↑(↑B : GL (Finₓ 2) ℝ) : Matrix (Finₓ 2) (Finₓ 2) ℝ).det : ℂ) ^ (k - 1) :=
    by
    simp_rw [← mul_zpow]
  simp_rw [this, ← mul_assoc, ← mul_zpow]

theorem slash_add (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) : (f + g) ∣[k]A = f ∣[k]A + g ∣[k]A := by
  simp only [← slash, ← Pi.add_apply, ← Matrix.GeneralLinearGroup.coe_det_apply, ← Subtype.val_eq_coe, ← coe_coe]
  ext1
  simp only [← Pi.add_apply]
  ring

theorem slash_mul_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k]1 = f := by
  simp_rw [slash]
  ext1
  simp

theorem smul_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : ℂ) : (c • f) ∣[k]A = c • f ∣[k]A := by
  ext1
  simp_rw [slash]
  simp only [← slash, ← Algebra.id.smul_eq_mul, ← Matrix.GeneralLinearGroup.coe_det_apply, ← Pi.smul_apply, ←
    Subtype.val_eq_coe, ← coe_coe]
  ring

instance : SlashAction ℤ GL(2, ℝ)⁺ (ℍ → ℂ) ℂ where
  map := slash
  mul_zero := by
    intro k g
    rw [slash]
    simp only [← Pi.zero_apply, ← zero_mul]
    rfl
  one_mul := by
    apply slash_mul_one
  right_action := by
    apply slash_right_action
  smul_action := by
    apply smul_slash
  AddAction := by
    apply slash_add

instance subgroupAction (Γ : Subgroup SL(2, ℤ)) : SlashAction ℤ Γ (ℍ → ℂ) ℂ :=
  monoidHomSlashAction
    (MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
      (MonoidHom.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (Subgroup.subtype Γ)))

instance sLAction : SlashAction ℤ SL(2, ℤ) (ℍ → ℂ) ℂ :=
  monoidHomSlashAction
    (MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))

end ModularForms

