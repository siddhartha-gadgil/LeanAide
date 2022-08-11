/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Geometry.Manifold.DerivationBundle

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivation for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `left_invariant_derivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

-/


noncomputable section

open LieGroup Manifold Derivation

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type _) [TopologicalSpace G] [ChartedSpace H G] [Monoidₓ G]
  [HasSmoothMul I G] (g h : G)

-- Generate trivial has_sizeof instance. It prevents weird type class inference timeout problems
@[local nolint instance_priority, local instance]
private def disable_has_sizeof {α} : SizeOf α :=
  ⟨fun _ => 0⟩

/-- Left-invariant global derivations.

A global derivation is left-invariant if it is equal to its pullback along left multiplication by
an arbitrary element of `G`.
-/
structure LeftInvariantDerivation extends Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  left_invariant'' :
    ∀ g, 𝒅ₕ (smooth_left_mul_one I g) (Derivation.evalAt 1 to_derivation) = Derivation.evalAt g to_derivation

variable {I G}

namespace LeftInvariantDerivation

instance : Coe (LeftInvariantDerivation I G) (Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  ⟨fun X => X.toDerivation⟩

instance : CoeFun (LeftInvariantDerivation I G) fun _ => C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯ :=
  ⟨fun X => X.toDerivation.toFun⟩

variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {x : M} {r : 𝕜} {X Y : LeftInvariantDerivation I G}
  {f f' : C^∞⟮I, G; 𝕜⟯}

theorem to_fun_eq_coe : X.toFun = ⇑X :=
  rfl

theorem coe_to_linear_map : ⇑(X : C^∞⟮I, G; 𝕜⟯ →ₗ[𝕜] C^∞⟮I, G; 𝕜⟯) = X :=
  rfl

@[simp]
theorem to_derivation_eq_coe : X.toDerivation = X :=
  rfl

theorem coe_injective : @Function.Injective (LeftInvariantDerivation I G) (_ → C^⊤⟮I, G; 𝕜⟯) coeFn := fun X Y h => by
  cases X
  cases Y
  congr
  exact Derivation.coe_injective h

@[ext]
theorem ext (h : ∀ f, X f = Y f) : X = Y :=
  coe_injective <| funext h

variable (X Y f)

theorem coe_derivation : ⇑(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯) :=
  rfl

theorem coe_derivation_injective :
    Function.Injective (coe : LeftInvariantDerivation I G → Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) := fun X Y h => by
  cases X
  cases Y
  congr
  exact h

/-- Premature version of the lemma. Prefer using `left_invariant` instead. -/
theorem left_invariant' : 𝒅ₕ (smooth_left_mul_one I g) (Derivation.evalAt (1 : G) ↑X) = Derivation.evalAt g ↑X :=
  left_invariant'' X g

@[simp]
theorem map_add : X (f + f') = X f + X f' :=
  Derivation.map_add X f f'

@[simp]
theorem map_zero : X 0 = 0 :=
  Derivation.map_zero X

@[simp]
theorem map_neg : X (-f) = -X f :=
  Derivation.map_neg X f

@[simp]
theorem map_sub : X (f - f') = X f - X f' :=
  Derivation.map_sub X f f'

@[simp]
theorem map_smul : X (r • f) = r • X f :=
  Derivation.map_smul X r f

@[simp]
theorem leibniz : X (f * f') = f • X f' + f' • X f :=
  X.leibniz' _ _

instance : Zero (LeftInvariantDerivation I G) :=
  ⟨⟨0, fun g => by
      simp only [← LinearMap.map_zero, ← Derivation.coe_zero]⟩⟩

instance : Inhabited (LeftInvariantDerivation I G) :=
  ⟨0⟩

instance :
    Add (LeftInvariantDerivation I G) where add := fun X Y =>
    ⟨X + Y, fun g => by
      simp only [← LinearMap.map_add, ← Derivation.coe_add, ← left_invariant', ← Pi.add_apply]⟩

instance :
    Neg (LeftInvariantDerivation I G) where neg := fun X =>
    ⟨-X, fun g => by
      simp [← left_invariant']⟩

instance :
    Sub (LeftInvariantDerivation I G) where sub := fun X Y =>
    ⟨X - Y, fun g => by
      simp [← left_invariant']⟩

@[simp]
theorem coe_add : ⇑(X + Y) = X + Y :=
  rfl

@[simp]
theorem coe_zero : ⇑(0 : LeftInvariantDerivation I G) = 0 :=
  rfl

@[simp]
theorem coe_neg : ⇑(-X) = -X :=
  rfl

@[simp]
theorem coe_sub : ⇑(X - Y) = X - Y :=
  rfl

@[simp, norm_cast]
theorem lift_add : (↑(X + Y) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y :=
  rfl

@[simp, norm_cast]
theorem lift_zero : (↑(0 : LeftInvariantDerivation I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0 :=
  rfl

instance hasNatScalar :
    HasSmul ℕ (LeftInvariantDerivation I G) where smul := fun r X =>
    ⟨r • X, fun g => by
      simp_rw [LinearMap.map_smul_of_tower, left_invariant']⟩

instance hasIntScalar :
    HasSmul ℤ (LeftInvariantDerivation I G) where smul := fun r X =>
    ⟨r • X, fun g => by
      simp_rw [LinearMap.map_smul_of_tower, left_invariant']⟩

instance : AddCommGroupₓ (LeftInvariantDerivation I G) :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance :
    HasSmul 𝕜 (LeftInvariantDerivation I G) where smul := fun r X =>
    ⟨r • X, fun g => by
      simp_rw [LinearMap.map_smul, left_invariant']⟩

variable (r X)

@[simp]
theorem coe_smul : ⇑(r • X) = r • X :=
  rfl

@[simp]
theorem lift_smul (k : 𝕜) : (↑(k • X) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = k • X :=
  rfl

variable (I G)

/-- The coercion to function is a monoid homomorphism. -/
@[simps]
def coeFnAddMonoidHom : LeftInvariantDerivation I G →+ C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯ :=
  ⟨fun X => X.toDerivation.toFun, coe_zero, coe_add⟩

variable {I G}

instance : Module 𝕜 (LeftInvariantDerivation I G) :=
  coe_injective.Module _ (coeFnAddMonoidHom I G) coe_smul

/-- Evaluation at a point for left invariant derivation. Same thing as for generic global
derivations (`derivation.eval_at`). -/
def evalAt : LeftInvariantDerivation I G →ₗ[𝕜] PointDerivation I g where
  toFun := fun X => Derivation.evalAt g ↑X
  map_add' := fun X Y => rfl
  map_smul' := fun k X => rfl

theorem eval_at_apply : evalAt g X f = (X f) g :=
  rfl

@[simp]
theorem eval_at_coe : Derivation.evalAt g ↑X = evalAt g X :=
  rfl

theorem left_invariant : 𝒅ₕ (smooth_left_mul_one I g) (evalAt (1 : G) X) = evalAt g X :=
  X.left_invariant'' g

theorem eval_at_mul : evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X) := by
  ext f
  rw [← left_invariant, apply_hfdifferential, apply_hfdifferential, L_mul, fdifferential_comp, apply_fdifferential,
    LinearMap.comp_apply, apply_fdifferential, ← apply_hfdifferential, left_invariant]

theorem comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g)) := by
  ext h <;>
    rw [ContMdiffMap.comp_apply, L_apply, ← eval_at_apply, eval_at_mul, apply_hfdifferential, apply_fdifferential,
      eval_at_apply]

instance :
    HasBracket (LeftInvariantDerivation I G)
      (LeftInvariantDerivation I
        G) where bracket := fun X Y =>
    ⟨⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯),Y⁆, fun g => by
      ext f
      have hX := Derivation.congr_fun (left_invariant' g X) (Y f)
      have hY := Derivation.congr_fun (left_invariant' g Y) (X f)
      rw [apply_hfdifferential, apply_fdifferential, Derivation.eval_at_apply] at hX hY⊢
      rw [comp_L] at hX hY
      rw [Derivation.commutator_apply, SmoothMap.coe_sub, Pi.sub_apply, coe_derivation]
      rw [coe_derivation] at hX hY⊢
      rw [hX, hY]
      rfl⟩

@[simp]
theorem commutator_coe_derivation :
    ⇑⁅X,Y⁆ = (⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯),Y⁆ : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  rfl

theorem commutator_apply : ⁅X,Y⁆ f = X (Y f) - Y (X f) :=
  rfl

instance : LieRing (LeftInvariantDerivation I G) where
  add_lie := fun X Y Z => by
    ext1
    simp only [← commutator_apply, ← coe_add, ← Pi.add_apply, ← LinearMap.map_add, ← LeftInvariantDerivation.map_add]
    ring
  lie_add := fun X Y Z => by
    ext1
    simp only [← commutator_apply, ← coe_add, ← Pi.add_apply, ← LinearMap.map_add, ← LeftInvariantDerivation.map_add]
    ring
  lie_self := fun X => by
    ext1
    simp only [← commutator_apply, ← sub_self]
    rfl
  leibniz_lie := fun X Y Z => by
    ext1
    simp only [← commutator_apply, ← coe_add, ← coe_sub, ← map_sub, ← Pi.add_apply]
    ring

instance :
    LieAlgebra 𝕜 (LeftInvariantDerivation I G) where lie_smul := fun r Y Z => by
    ext1
    simp only [← commutator_apply, ← map_smul, ← smul_sub, ← coe_smul, ← Pi.smul_apply]

end LeftInvariantDerivation

