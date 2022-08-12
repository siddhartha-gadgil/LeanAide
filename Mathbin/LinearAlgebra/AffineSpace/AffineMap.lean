/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Algebra.AddTorsor
import Mathbin.Data.Set.Intervals.UnorderedInterval
import Mathbin.LinearAlgebra.AffineSpace.Basic
import Mathbin.LinearAlgebra.BilinearMap
import Mathbin.LinearAlgebra.Pi
import Mathbin.LinearAlgebra.Prod
import Mathbin.Tactic.Abel

/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `affine_map` is the type of affine maps between two affine spaces with the same ring `k`.  Various
  basic examples of affine maps are defined, including `const`, `id`, `line_map` and `homothety`.

## Notations

* `P1 →ᵃ[k] P2` is a notation for `affine_map k P1 P2`;
* `affine_space V P`: a localized notation for `add_torsor V P` defined in
  `linear_algebra.affine_space.basic`.

## Implementation notes

`out_param` is used in the definition of `[add_torsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases; `include V` is needed in many cases for `V`, and type classes
using it, to be added as implicit arguments to individual lemmas.  As for modules, `k` is an
explicit argument rather than implied by `P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `analysis.normed_space.add_torsor` and
`topology.algebra.affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/


open Affine

/-- An `affine_map k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure AffineMap (k : Type _) {V1 : Type _} (P1 : Type _) {V2 : Type _} (P2 : Type _) [Ringₓ k] [AddCommGroupₓ V1]
  [Module k V1] [affine_space V1 P1] [AddCommGroupₓ V2] [Module k V2] [affine_space V2 P2] where
  toFun : P1 → P2
  linear : V1 →ₗ[k] V2
  map_vadd' : ∀ (p : P1) (v : V1), to_fun (v +ᵥ p) = linear v +ᵥ to_fun p

-- mathport name: «expr →ᵃ[ ] »
notation:25 P1 " →ᵃ[" k:25 "] " P2:0 => AffineMap k P1 P2

instance (k : Type _) {V1 : Type _} (P1 : Type _) {V2 : Type _} (P2 : Type _) [Ringₓ k] [AddCommGroupₓ V1] [Module k V1]
    [affine_space V1 P1] [AddCommGroupₓ V2] [Module k V2] [affine_space V2 P2] :
    CoeFun (P1 →ᵃ[k] P2) fun _ => P1 → P2 :=
  ⟨AffineMap.toFun⟩

namespace LinearMap

variable {k : Type _} {V₁ : Type _} {V₂ : Type _} [Ringₓ k] [AddCommGroupₓ V₁] [Module k V₁] [AddCommGroupₓ V₂]
  [Module k V₂] (f : V₁ →ₗ[k] V₂)

/-- Reinterpret a linear map as an affine map. -/
def toAffineMap : V₁ →ᵃ[k] V₂ where
  toFun := f
  linear := f
  map_vadd' := fun p v => f.map_add v p

@[simp]
theorem coe_to_affine_map : ⇑f.toAffineMap = f :=
  rfl

@[simp]
theorem to_affine_map_linear : f.toAffineMap.linear = f :=
  rfl

end LinearMap

namespace AffineMap

variable {k : Type _} {V1 : Type _} {P1 : Type _} {V2 : Type _} {P2 : Type _} {V3 : Type _} {P3 : Type _} {V4 : Type _}
  {P4 : Type _} [Ringₓ k] [AddCommGroupₓ V1] [Module k V1] [affine_space V1 P1] [AddCommGroupₓ V2] [Module k V2]
  [affine_space V2 P2] [AddCommGroupₓ V3] [Module k V3] [affine_space V3 P3] [AddCommGroupₓ V4] [Module k V4]
  [affine_space V4 P4]

include V1 V2

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp]
theorem coe_mk (f : P1 → P2) (linear add) : ((mk f linear add : P1 →ᵃ[k] P2) : P1 → P2) = f :=
  rfl

/-- `to_fun` is the same as the result of coercing to a function. -/
@[simp]
theorem to_fun_eq_coe (f : P1 →ᵃ[k] P2) : f.toFun = ⇑f :=
  rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp]
theorem map_vadd (f : P1 →ᵃ[k] P2) (p : P1) (v : V1) : f (v +ᵥ p) = f.linear v +ᵥ f p :=
  f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp]
theorem linear_map_vsub (f : P1 →ᵃ[k] P2) (p1 p2 : P1) : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 := by
  conv_rhs => rw [← vsub_vadd p1 p2, map_vadd, vadd_vsub]

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext]
theorem ext {f g : P1 →ᵃ[k] P2} (h : ∀ p, f p = g p) : f = g := by
  rcases f with ⟨f, f_linear, f_add⟩
  rcases g with ⟨g, g_linear, g_add⟩
  obtain rfl : f = g := funext h
  congr with v
  cases' (AddTorsor.nonempty : Nonempty P1) with p
  apply vadd_right_cancel (f p)
  erw [← f_add, ← g_add]

theorem ext_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ ∀ p, f p = g p :=
  ⟨fun h p => h ▸ rfl, ext⟩

theorem coe_fn_injective : @Function.Injective (P1 →ᵃ[k] P2) (P1 → P2) coeFn := fun f g H => ext <| congr_fun H

protected theorem congr_arg (f : P1 →ᵃ[k] P2) {x y : P1} (h : x = y) : f x = f y :=
  congr_arg _ h

protected theorem congr_fun {f g : P1 →ᵃ[k] P2} (h : f = g) (x : P1) : f x = g x :=
  h ▸ rfl

variable (k P1)

/-- Constant function as an `affine_map`. -/
def const (p : P2) : P1 →ᵃ[k] P2 where
  toFun := Function.const P1 p
  linear := 0
  map_vadd' := fun p v => by
    simp

@[simp]
theorem coe_const (p : P2) : ⇑(const k P1 p) = Function.const P1 p :=
  rfl

@[simp]
theorem const_linear (p : P2) : (const k P1 p).linear = 0 :=
  rfl

variable {k P1}

theorem linear_eq_zero_iff_exists_const (f : P1 →ᵃ[k] P2) : f.linear = 0 ↔ ∃ q, f = const k P1 q := by
  refine' ⟨fun h => _, fun h => _⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [coe_const, Function.const_applyₓ, ← @vsub_eq_zero_iff_eq V2, ← f.linear_map_vsub, h, LinearMap.zero_apply]
    
  · rcases h with ⟨q, rfl⟩
    exact const_linear k P1 q
    

instance nonempty : Nonempty (P1 →ᵃ[k] P2) :=
  (AddTorsor.nonempty : Nonempty P2).elim fun p => ⟨const k P1 p⟩

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) : P1 →ᵃ[k] P2 where
  toFun := f
  linear := f'
  map_vadd' := fun p' v => by
    rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]

@[simp]
theorem coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f :=
  rfl

@[simp]
theorem mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' :=
  rfl

section HasSmul

variable {R : Type _} [Monoidₓ R] [DistribMulAction R V2] [SmulCommClass k R V2]

/-- The space of affine maps to a module inherits an `R`-action from the action on its codomain. -/
instance : MulAction R (P1 →ᵃ[k] V2) where
  smul := fun c f =>
    ⟨c • f, c • f.linear, fun p v => by
      simp [← smul_add]⟩
  one_smul := fun f => ext fun p => one_smul _ _
  mul_smul := fun c₁ c₂ f => ext fun p => mul_smul _ _ _

@[simp, norm_cast]
theorem coe_smul (c : R) (f : P1 →ᵃ[k] V2) : ⇑(c • f) = c • f :=
  rfl

@[simp]
theorem smul_linear (t : R) (f : P1 →ᵃ[k] V2) : (t • f).linear = t • f.linear :=
  rfl

instance [DistribMulAction Rᵐᵒᵖ V2] [IsCentralScalar R V2] :
    IsCentralScalar R (P1 →ᵃ[k] V2) where op_smul_eq_smul := fun r x => ext fun _ => op_smul_eq_smul _ _

end HasSmul

instance : Zero (P1 →ᵃ[k] V2) where zero := ⟨0, 0, fun p v => (zero_vadd _ _).symm⟩

instance :
    Add (P1 →ᵃ[k] V2) where add := fun f g =>
    ⟨f + g, f.linear + g.linear, fun p v => by
      simp [← add_add_add_commₓ]⟩

instance :
    Sub (P1 →ᵃ[k] V2) where sub := fun f g =>
    ⟨f - g, f.linear - g.linear, fun p v => by
      simp [← sub_add_sub_comm]⟩

instance :
    Neg (P1 →ᵃ[k] V2) where neg := fun f =>
    ⟨-f, -f.linear, fun p v => by
      simp [← add_commₓ]⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : P1 →ᵃ[k] V2) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_add (f g : P1 →ᵃ[k] V2) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
theorem coe_neg (f : P1 →ᵃ[k] V2) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
theorem coe_sub (f g : P1 →ᵃ[k] V2) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem zero_linear : (0 : P1 →ᵃ[k] V2).linear = 0 :=
  rfl

@[simp]
theorem add_linear (f g : P1 →ᵃ[k] V2) : (f + g).linear = f.linear + g.linear :=
  rfl

@[simp]
theorem sub_linear (f g : P1 →ᵃ[k] V2) : (f - g).linear = f.linear - g.linear :=
  rfl

@[simp]
theorem neg_linear (f : P1 →ᵃ[k] V2) : (-f).linear = -f.linear :=
  rfl

/-- The set of affine maps to a vector space is an additive commutative group. -/
instance : AddCommGroupₓ (P1 →ᵃ[k] V2) :=
  coe_fn_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

/-- The space of affine maps from `P1` to `P2` is an affine space over the space of affine maps
from `P1` to the vector space `V2` corresponding to `P2`. -/
instance : affine_space (P1 →ᵃ[k] V2) (P1 →ᵃ[k] P2) where
  vadd := fun f g =>
    ⟨fun p => f p +ᵥ g p, f.linear + g.linear, fun p v => by
      simp [← vadd_vadd, ← add_right_commₓ]⟩
  zero_vadd := fun f => ext fun p => zero_vadd _ (f p)
  add_vadd := fun f₁ f₂ f₃ => ext fun p => add_vadd (f₁ p) (f₂ p) (f₃ p)
  vsub := fun f g =>
    ⟨fun p => f p -ᵥ g p, f.linear - g.linear, fun p v => by
      simp [← vsub_vadd_eq_vsub_sub, ← vadd_vsub_assoc, ← add_sub, ← sub_add_eq_add_sub]⟩
  vsub_vadd' := fun f g => ext fun p => vsub_vadd (f p) (g p)
  vadd_vsub' := fun f g => ext fun p => vadd_vsub (f p) (g p)

@[simp]
theorem vadd_apply (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) (p : P1) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl

@[simp]
theorem vsub_apply (f g : P1 →ᵃ[k] P2) (p : P1) : (f -ᵥ g : P1 →ᵃ[k] V2) p = f p -ᵥ g p :=
  rfl

/-- `prod.fst` as an `affine_map`. -/
def fst : P1 × P2 →ᵃ[k] P1 where
  toFun := Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' := fun _ _ => rfl

@[simp]
theorem coe_fst : ⇑(fst : P1 × P2 →ᵃ[k] P1) = Prod.fst :=
  rfl

@[simp]
theorem fst_linear : (fst : P1 × P2 →ᵃ[k] P1).linear = LinearMap.fst k V1 V2 :=
  rfl

/-- `prod.snd` as an `affine_map`. -/
def snd : P1 × P2 →ᵃ[k] P2 where
  toFun := Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' := fun _ _ => rfl

@[simp]
theorem coe_snd : ⇑(snd : P1 × P2 →ᵃ[k] P2) = Prod.snd :=
  rfl

@[simp]
theorem snd_linear : (snd : P1 × P2 →ᵃ[k] P2).linear = LinearMap.snd k V1 V2 :=
  rfl

variable (k P1)

omit V2

/-- Identity map as an affine map. -/
def id : P1 →ᵃ[k] P1 where
  toFun := id
  linear := LinearMap.id
  map_vadd' := fun p v => rfl

/-- The identity affine map acts as the identity. -/
@[simp]
theorem coe_id : ⇑(id k P1) = _root_.id :=
  rfl

@[simp]
theorem id_linear : (id k P1).linear = LinearMap.id :=
  rfl

variable {P1}

/-- The identity affine map acts as the identity. -/
theorem id_apply (p : P1) : id k P1 p = p :=
  rfl

variable {k P1}

instance : Inhabited (P1 →ᵃ[k] P1) :=
  ⟨id k P1⟩

include V2 V3

/-- Composition of affine maps. -/
def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 where
  toFun := f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_app, g.map_vadd, f.map_vadd]
    rfl

/-- Composition of affine maps acts as applying the two functions. -/
@[simp]
theorem coe_comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : ⇑(f.comp g) = f ∘ g :=
  rfl

/-- Composition of affine maps acts as applying the two functions. -/
theorem comp_apply (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) (p : P1) : f.comp g p = f (g p) :=
  rfl

omit V3

@[simp]
theorem comp_id (f : P1 →ᵃ[k] P2) : f.comp (id k P1) = f :=
  ext fun p => rfl

@[simp]
theorem id_comp (f : P1 →ᵃ[k] P2) : (id k P2).comp f = f :=
  ext fun p => rfl

include V3 V4

theorem comp_assoc (f₃₄ : P3 →ᵃ[k] P4) (f₂₃ : P2 →ᵃ[k] P3) (f₁₂ : P1 →ᵃ[k] P2) :
    (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
  rfl

omit V2 V3 V4

instance : Monoidₓ (P1 →ᵃ[k] P1) where
  one := id k P1
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp]
theorem coe_mul (f g : P1 →ᵃ[k] P1) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : P1 →ᵃ[k] P1) = _root_.id :=
  rfl

/-- `affine_map.linear` on endomorphisms is a `monoid_hom`. -/
@[simps]
def linearHom : (P1 →ᵃ[k] P1) →* V1 →ₗ[k] V1 where
  toFun := linear
  map_one' := rfl
  map_mul' := fun _ _ => rfl

include V2

@[simp]
theorem injective_iff_linear_injective (f : P1 →ᵃ[k] P2) : Function.Injective f.linear ↔ Function.Injective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equivₓ.vaddConst (f p)).symm ∘ f ∘ Equivₓ.vaddConst p := by
    ext v
    simp [← f.map_vadd, ← vadd_vsub_assoc]
  rw [h, Equivₓ.comp_injective, Equivₓ.injective_comp]

@[simp]
theorem surjective_iff_linear_surjective (f : P1 →ᵃ[k] P2) : Function.Surjective f.linear ↔ Function.Surjective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equivₓ.vaddConst (f p)).symm ∘ f ∘ Equivₓ.vaddConst p := by
    ext v
    simp [← f.map_vadd, ← vadd_vsub_assoc]
  rw [h, Equivₓ.comp_surjective, Equivₓ.surjective_comp]

theorem image_vsub_image {s t : Set P1} (f : P1 →ᵃ[k] P2) : f '' s -ᵥ f '' t = f.linear '' (s -ᵥ t) := by
  ext v
  simp only [← Set.mem_vsub, ← Set.mem_image, ← exists_exists_and_eq_and, ← exists_and_distrib_left, f.linear_map_vsub]
  constructor
  · rintro ⟨x, hx, y, hy, hv⟩
    exact ⟨x -ᵥ y, ⟨x, hx, y, hy, rfl⟩, hv⟩
    
  · rintro ⟨-, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
    

omit V2

/-! ### Definition of `affine_map.line_map` and lemmas about it -/


/-- The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`. -/
def lineMap (p₀ p₁ : P1) : k →ᵃ[k] P1 :=
  ((LinearMap.id : k →ₗ[k] k).smul_right (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀

theorem coe_line_map (p₀ p₁ : P1) : (lineMap p₀ p₁ : k → P1) = fun c => c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

theorem line_map_apply (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

theorem line_map_apply_module' (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = c • (p₁ - p₀) + p₀ :=
  rfl

theorem line_map_apply_module (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁ := by
  simp [← line_map_apply_module', ← smul_sub, ← sub_smul] <;> abel

omit V1

theorem line_map_apply_ring' (a b c : k) : lineMap a b c = c * (b - a) + a :=
  rfl

theorem line_map_apply_ring (a b c : k) : lineMap a b c = (1 - c) * a + c * b :=
  line_map_apply_module a b c

include V1

theorem line_map_vadd_apply (p : P1) (v : V1) (c : k) : lineMap p (v +ᵥ p) c = c • v +ᵥ p := by
  rw [line_map_apply, vadd_vsub]

@[simp]
theorem line_map_linear (p₀ p₁ : P1) : (lineMap p₀ p₁ : k →ᵃ[k] P1).linear = LinearMap.id.smul_right (p₁ -ᵥ p₀) :=
  add_zeroₓ _

theorem line_map_same_apply (p : P1) (c : k) : lineMap p p c = p := by
  simp [← line_map_apply]

@[simp]
theorem line_map_same (p : P1) : lineMap p p = const k k p :=
  ext <| line_map_same_apply p

@[simp]
theorem line_map_apply_zero (p₀ p₁ : P1) : lineMap p₀ p₁ (0 : k) = p₀ := by
  simp [← line_map_apply]

@[simp]
theorem line_map_apply_one (p₀ p₁ : P1) : lineMap p₀ p₁ (1 : k) = p₁ := by
  simp [← line_map_apply]

include V2

@[simp]
theorem apply_line_map (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c := by
  simp [← line_map_apply]

@[simp]
theorem comp_line_map (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) : f.comp (lineMap p₀ p₁) = lineMap (f p₀) (f p₁) :=
  ext <| f.apply_line_map p₀ p₁

@[simp]
theorem fst_line_map (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).1 = lineMap p₀.1 p₁.1 c :=
  fst.apply_line_map p₀ p₁ c

@[simp]
theorem snd_line_map (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).2 = lineMap p₀.2 p₁.2 c :=
  snd.apply_line_map p₀ p₁ c

omit V2

theorem line_map_symm (p₀ p₁ : P1) : lineMap p₀ p₁ = (lineMap p₁ p₀).comp (lineMap (1 : k) (0 : k)) := by
  rw [comp_line_map]
  simp

theorem line_map_apply_one_sub (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c := by
  rw [line_map_symm p₀, comp_apply]
  congr
  simp [← line_map_apply]

@[simp]
theorem line_map_vsub_left (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀) :=
  vadd_vsub _ _

@[simp]
theorem left_vsub_line_map (p₀ p₁ : P1) (c : k) : p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁) := by
  rw [← neg_vsub_eq_vsub_rev, line_map_vsub_left, ← smul_neg, neg_vsub_eq_vsub_rev]

@[simp]
theorem line_map_vsub_right (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁) := by
  rw [← line_map_apply_one_sub, line_map_vsub_left]

@[simp]
theorem right_vsub_line_map (p₀ p₁ : P1) (c : k) : p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀) := by
  rw [← line_map_apply_one_sub, left_vsub_line_map]

theorem line_map_vadd_line_map (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) :
    lineMap v₁ v₂ c +ᵥ lineMap p₁ p₂ c = lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c :=
  ((fst : V1 × P1 →ᵃ[k] V1) +ᵥ snd).apply_line_map (v₁, p₁) (v₂, p₂) c

theorem line_map_vsub_line_map (p₁ p₂ p₃ p₄ : P1) (c : k) :
    lineMap p₁ p₂ c -ᵥ lineMap p₃ p₄ c = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c := by
  -- Why Lean fails to find this instance without a hint?
    let this : affine_space (V1 × V1) (P1 × P1) := Prod.addTorsor <;>
    exact ((fst : P1 × P1 →ᵃ[k] P1) -ᵥ (snd : P1 × P1 →ᵃ[k] P1)).apply_line_map (_, _) (_, _) c

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp (f : V1 →ᵃ[k] V2) : (f : V1 → V2) = f.linear + fun z => f 0 := by
  ext x
  calc f x = f.linear x +ᵥ f 0 := by
      simp [f.map_vadd]_ = (f.linear.to_fun + fun z : V1 => f 0) x := by
      simp

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp' (f : V1 →ᵃ[k] V2) : (f.linear : V1 → V2) = f - fun z => f 0 := by
  rw [decomp] <;> simp only [← LinearMap.map_zero, ← Pi.add_apply, ← add_sub_cancel, ← zero_addₓ]

omit V1

theorem image_interval {k : Type _} [LinearOrderedField k] (f : k →ᵃ[k] k) (a b : k) :
    f '' Set.Interval a b = Set.Interval (f a) (f b) := by
  have : ⇑f = (fun x => x + f 0) ∘ fun x => x * (f 1 - f 0) := by
    ext x
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0
    rw [← f.linear_map_vsub, ← f.linear.map_smul, ← f.map_vadd]
    simp only [← vsub_eq_sub, ← add_zeroₓ, ← mul_oneₓ, ← vadd_eq_add, ← sub_zero, ← smul_eq_mul]
  rw [this, Set.image_comp]
  simp only [← Set.image_add_const_interval, ← Set.image_mul_const_interval]

section

variable {ι : Type _} {V : ∀ i : ι, Type _} {P : ∀ i : ι, Type _} [∀ i, AddCommGroupₓ (V i)] [∀ i, Module k (V i)]
  [∀ i, AddTorsor (V i) (P i)]

include V

/-- Evaluation at a point as an affine map. -/
def proj (i : ι) : (∀ i : ι, P i) →ᵃ[k] P i where
  toFun := fun f => f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' := fun p v => rfl

@[simp]
theorem proj_apply (i : ι) (f : ∀ i, P i) : @proj k _ ι V P _ _ _ i f = f i :=
  rfl

@[simp]
theorem proj_linear (i : ι) : (@proj k _ ι V P _ _ _ i).linear = @LinearMap.proj k ι _ V _ _ i :=
  rfl

theorem pi_line_map_apply (f g : ∀ i, P i) (c : k) (i : ι) : lineMap f g c i = lineMap (f i) (g i) c :=
  (proj i : (∀ i, P i) →ᵃ[k] P i).apply_line_map f g c

end

end AffineMap

namespace AffineMap

variable {R k V1 P1 V2 : Type _}

section Ringₓ

variable [Ringₓ k] [AddCommGroupₓ V1] [affine_space V1 P1] [AddCommGroupₓ V2]

variable [Module k V1] [Module k V2]

include V1

section DistribMulAction

variable [Monoidₓ R] [DistribMulAction R V2] [SmulCommClass k R V2]

/-- The space of affine maps to a module inherits an `R`-action from the action on its codomain. -/
instance : DistribMulAction R (P1 →ᵃ[k] V2) where
  smul_add := fun c f g => ext fun p => smul_add _ _ _
  smul_zero := fun c => ext fun p => smul_zero _

end DistribMulAction

section Module

variable [Semiringₓ R] [Module R V2] [SmulCommClass k R V2]

/-- The space of affine maps taking values in an `R`-module is an `R`-module. -/
instance : Module R (P1 →ᵃ[k] V2) :=
  { AffineMap.distribMulAction with smul := (· • ·), add_smul := fun c₁ c₂ f => ext fun p => add_smul _ _ _,
    zero_smul := fun f => ext fun p => zero_smul _ _ }

variable (R)

/-- The space of affine maps between two modules is linearly equivalent to the product of the
domain with the space of linear maps, by taking the value of the affine map at `(0 : V1)` and the
linear part.

See note [bundled maps over different rings]-/
@[simps]
def toConstProdLinearMap : (V1 →ᵃ[k] V2) ≃ₗ[R] V2 × (V1 →ₗ[k] V2) where
  toFun := fun f => ⟨f 0, f.linear⟩
  invFun := fun p => p.2.toAffineMap + const k V1 p.1
  left_inv := fun f => by
    ext
    rw [f.decomp]
    simp
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp
  map_add' := by
    simp
  map_smul' := by
    simp

end Module

end Ringₓ

section CommRingₓ

variable [CommRingₓ k] [AddCommGroupₓ V1] [affine_space V1 P1] [AddCommGroupₓ V2]

variable [Module k V1] [Module k V2]

include V1

/-- `homothety c r` is the homothety (also known as dilation) about `c` with scale factor `r`. -/
def homothety (c : P1) (r : k) : P1 →ᵃ[k] P1 :=
  r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c

theorem homothety_def (c : P1) (r : k) : homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
  rfl

theorem homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c : V1) +ᵥ c :=
  rfl

theorem homothety_eq_line_map (c : P1) (r : k) (p : P1) : homothety c r p = lineMap c p r :=
  rfl

@[simp]
theorem homothety_one (c : P1) : homothety c (1 : k) = id k P1 := by
  ext p
  simp [← homothety_apply]

@[simp]
theorem homothety_apply_same (c : P1) (r : k) : homothety c r c = c :=
  line_map_same_apply c r

theorem homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) :
    homothety c (r₁ * r₂) p = homothety c r₁ (homothety c r₂ p) := by
  simp [← homothety_apply, ← mul_smul]

theorem homothety_mul (c : P1) (r₁ r₂ : k) : homothety c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂) :=
  ext <| homothety_mul_apply c r₁ r₂

@[simp]
theorem homothety_zero (c : P1) : homothety c (0 : k) = const k P1 c := by
  ext p
  simp [← homothety_apply]

@[simp]
theorem homothety_add (c : P1) (r₁ r₂ : k) : homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ :=
  by
  simp only [← homothety_def, ← add_smul, ← vadd_vadd]

/-- `homothety` as a multiplicative monoid homomorphism. -/
def homothetyHom (c : P1) : k →* P1 →ᵃ[k] P1 :=
  ⟨homothety c, homothety_one c, homothety_mul c⟩

@[simp]
theorem coe_homothety_hom (c : P1) : ⇑(homothetyHom c : k →* _) = homothety c :=
  rfl

/-- `homothety` as an affine map. -/
def homothetyAffine (c : P1) : k →ᵃ[k] P1 →ᵃ[k] P1 :=
  ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c), Function.swap (homothety_add c)⟩

@[simp]
theorem coe_homothety_affine (c : P1) : ⇑(homothetyAffine c : k →ᵃ[k] _) = homothety c :=
  rfl

end CommRingₓ

end AffineMap

