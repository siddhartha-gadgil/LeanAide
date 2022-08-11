/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.LinearAlgebra.Basis

/-!
# (Semi-)linear isometries

In this file we define `linear_isometry σ₁₂ E E₂` (notation: `E →ₛₗᵢ[σ₁₂] E₂`) to be a semilinear
isometric embedding of `E` into `E₂` and `linear_isometry_equiv` (notation: `E ≃ₛₗᵢ[σ₁₂] E₂`) to be
a semilinear isometric equivalence between `E` and `E₂`.  The notation for the associated purely
linear concepts is `E →ₗᵢ[R] E₂`, `E ≃ₗᵢ[R] E₂`, and `E →ₗᵢ⋆[R] E₂`, `E ≃ₗᵢ⋆[R] E₂` for
the star-linear versions.

We also prove some trivial lemmas and provide convenience constructors.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory for `semi_normed_group` and we specialize to `normed_group` when needed.
-/


open Function Set

variable {R R₂ R₃ R₄ E E₂ E₃ E₄ F : Type _} [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ R₄] {σ₁₂ : R →+* R₂}
  {σ₂₁ : R₂ →+* R} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R} {σ₁₄ : R →+* R₄} {σ₄₁ : R₄ →+* R} {σ₂₃ : R₂ →+* R₃}
  {σ₃₂ : R₃ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₄₂ : R₄ →+* R₂} {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomInvPair σ₂₃ σ₃₂]
  [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄] [RingHomInvPair σ₂₄ σ₄₂]
  [RingHomInvPair σ₄₂ σ₂₄] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
  [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂]
  [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁] [SemiNormedGroup E] [SemiNormedGroup E₂] [SemiNormedGroup E₃] [SemiNormedGroup E₄]
  [Module R E] [Module R₂ E₂] [Module R₃ E₃] [Module R₄ E₄] [NormedGroup F] [Module R F]

/-- A `σ₁₂`-semilinear isometric embedding of a normed `R`-module into an `R₂`-module. -/
structure LinearIsometry (σ₁₂ : R →+* R₂) (E E₂ : Type _) [SemiNormedGroup E] [SemiNormedGroup E₂] [Module R E]
  [Module R₂ E₂] extends E →ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ∥to_linear_map x∥ = ∥x∥

-- mathport name: «expr →ₛₗᵢ[ ] »
notation:25 E " →ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometry σ₁₂ E E₂

-- mathport name: «expr →ₗᵢ[ ] »
notation:25 E " →ₗᵢ[" R:25 "] " E₂:0 => LinearIsometry (RingHom.id R) E E₂

-- mathport name: «expr →ₗᵢ⋆[ ] »
notation:25 E " →ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometry (starRingEnd R) E E₂

namespace LinearIsometry

variable (f : E →ₛₗᵢ[σ₁₂] E₂) (f₁ : F →ₛₗᵢ[σ₁₂] E₂)

theorem to_linear_map_injective : Injective (toLinearMap : (E →ₛₗᵢ[σ₁₂] E₂) → E →ₛₗ[σ₁₂] E₂)
  | ⟨f, _⟩, ⟨g, _⟩, rfl => rfl

@[simp]
theorem to_linear_map_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  to_linear_map_injective.eq_iff

instance : AddMonoidHomClass (E →ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe := fun e => e.toFun
  coe_injective' := fun f g h => to_linear_map_injective (FunLike.coe_injective h)
  map_add := fun f => map_add f.toLinearMap
  map_zero := fun f => map_zero f.toLinearMap

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : CoeFun (E →ₛₗᵢ[σ₁₂] E₂) fun _ => E → E₂ :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem coe_to_linear_map : ⇑f.toLinearMap = f :=
  rfl

@[simp]
theorem coe_mk (f : E →ₛₗ[σ₁₂] E₂) (hf) : ⇑(mk f hf) = f :=
  rfl

theorem coe_injective : @Injective (E →ₛₗᵢ[σ₁₂] E₂) (E → E₂) coeFn :=
  FunLike.coe_injective

@[ext]
theorem ext {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

protected theorem congr_arg {f : E →ₛₗᵢ[σ₁₂] E₂} : ∀ {x x' : E}, x = x' → f x = f x'
  | _, _, rfl => rfl

protected theorem congr_fun {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x :=
  h ▸ rfl

@[simp]
theorem map_zero : f 0 = 0 :=
  f.toLinearMap.map_zero

@[simp]
theorem map_add (x y : E) : f (x + y) = f x + f y :=
  f.toLinearMap.map_add x y

@[simp]
theorem map_neg (x : E) : f (-x) = -f x :=
  f.toLinearMap.map_neg x

@[simp]
theorem map_sub (x y : E) : f (x - y) = f x - f y :=
  f.toLinearMap.map_sub x y

@[simp]
theorem map_smulₛₗ (c : R) (x : E) : f (c • x) = σ₁₂ c • f x :=
  f.toLinearMap.map_smulₛₗ c x

@[simp]
theorem map_smul [Module R E₂] (f : E →ₗᵢ[R] E₂) (c : R) (x : E) : f (c • x) = c • f x :=
  f.toLinearMap.map_smul c x

@[simp]
theorem norm_map (x : E) : ∥f x∥ = ∥x∥ :=
  f.norm_map' x

@[simp]
theorem nnnorm_map (x : E) : ∥f x∥₊ = ∥x∥₊ :=
  Nnreal.eq <| f.norm_map x

protected theorem isometry : Isometry f :=
  AddMonoidHomClass.isometry_of_norm _ (norm_map _)

@[simp]
theorem is_complete_image_iff {s : Set E} : IsComplete (f '' s) ↔ IsComplete s :=
  is_complete_image_iff f.Isometry.UniformInducing

theorem is_complete_map_iff [RingHomSurjective σ₁₂] {p : Submodule R E} :
    IsComplete (p.map f.toLinearMap : Set E₂) ↔ IsComplete (p : Set E) :=
  f.is_complete_image_iff

instance complete_space_map [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map f.toLinearMap) :=
  (f.is_complete_map_iff.2 <| complete_space_coe_iff_is_complete.1 ‹_›).complete_space_coe

@[simp]
theorem dist_map (x y : E) : dist (f x) (f y) = dist x y :=
  f.Isometry.dist_eq x y

@[simp]
theorem edist_map (x y : E) : edist (f x) (f y) = edist x y :=
  f.Isometry.edist_eq x y

protected theorem injective : Injective f₁ :=
  f₁.Isometry.Injective

@[simp]
theorem map_eq_iff {x y : F} : f₁ x = f₁ y ↔ x = y :=
  f₁.Injective.eq_iff

theorem map_ne {x y : F} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.Injective.Ne h

protected theorem lipschitz : LipschitzWith 1 f :=
  f.Isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.Isometry.antilipschitz

@[continuity]
protected theorem continuous : Continuous f :=
  f.Isometry.Continuous

instance : ContinuousSemilinearMapClass (E →ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ :=
  { LinearIsometry.addMonoidHomClass with map_smulₛₗ := fun f => f.map_smulₛₗ, map_continuous := fun f => f.Continuous }

theorem ediam_image (s : Set E) : Emetric.diam (f '' s) = Emetric.diam s :=
  f.Isometry.ediam_image s

theorem ediam_range : Emetric.diam (Range f) = Emetric.diam (Univ : Set E) :=
  f.Isometry.ediam_range

theorem diam_image (s : Set E) : Metric.diam (f '' s) = Metric.diam s :=
  f.Isometry.diam_image s

theorem diam_range : Metric.diam (Range f) = Metric.diam (Univ : Set E) :=
  f.Isometry.diam_range

/-- Interpret a linear isometry as a continuous linear map. -/
def toContinuousLinearMap : E →SL[σ₁₂] E₂ :=
  ⟨f.toLinearMap, f.Continuous⟩

theorem to_continuous_linear_map_injective : Function.Injective (toContinuousLinearMap : _ → E →SL[σ₁₂] E₂) :=
  fun x y h => coe_injective (congr_arg _ h : ⇑x.toContinuousLinearMap = _)

@[simp]
theorem to_continuous_linear_map_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearMap = g.toContinuousLinearMap ↔ f = g :=
  to_continuous_linear_map_injective.eq_iff

@[simp]
theorem coe_to_continuous_linear_map : ⇑f.toContinuousLinearMap = f :=
  rfl

@[simp]
theorem comp_continuous_iff {α : Type _} [TopologicalSpace α] {g : α → E} : Continuous (f ∘ g) ↔ Continuous g :=
  f.Isometry.comp_continuous_iff

/-- The identity linear isometry. -/
def id : E →ₗᵢ[R] E :=
  ⟨LinearMap.id, fun x => rfl⟩

@[simp]
theorem coe_id : ((id : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl

@[simp]
theorem id_apply (x : E) : (id : E →ₗᵢ[R] E) x = x :=
  rfl

@[simp]
theorem id_to_linear_map : (id.toLinearMap : E →ₗ[R] E) = LinearMap.id :=
  rfl

@[simp]
theorem id_to_continuous_linear_map : id.toContinuousLinearMap = ContinuousLinearMap.id R E :=
  rfl

instance : Inhabited (E →ₗᵢ[R] E) :=
  ⟨id⟩

/-- Composition of linear isometries. -/
def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
  ⟨g.toLinearMap.comp f.toLinearMap, fun x => (g.norm_map _).trans (f.norm_map _)⟩

include σ₁₃

@[simp]
theorem coe_comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : ⇑(g.comp f) = g ∘ f :=
  rfl

omit σ₁₃

@[simp]
theorem id_comp : (id : E₂ →ₗᵢ[R₂] E₂).comp f = f :=
  ext fun x => rfl

@[simp]
theorem comp_id : f.comp id = f :=
  ext fun x => rfl

include σ₁₃ σ₂₄ σ₁₄

theorem comp_assoc (f : E₃ →ₛₗᵢ[σ₃₄] E₄) (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (h : E →ₛₗᵢ[σ₁₂] E₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

omit σ₁₃ σ₂₄ σ₁₄

instance : Monoidₓ (E →ₗᵢ[R] E) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl

@[simp]
theorem coe_mul (f g : E →ₗᵢ[R] E) : ⇑(f * g) = f ∘ g :=
  rfl

theorem one_def : (1 : E →ₗᵢ[R] E) = id :=
  rfl

theorem mul_def (f g : E →ₗᵢ[R] E) : (f * g : E →ₗᵢ[R] E) = f.comp g :=
  rfl

end LinearIsometry

/-- Construct a `linear_isometry` from a `linear_map` satisfying `isometry`. -/
def LinearMap.toLinearIsometry (f : E →ₛₗ[σ₁₂] E₂) (hf : Isometry f) : E →ₛₗᵢ[σ₁₂] E₂ :=
  { f with
    norm_map' := by
      simp_rw [← dist_zero_right, ← f.map_zero]
      exact fun x => hf.dist_eq x _ }

namespace Submodule

variable {R' : Type _} [Ringₓ R'] [Module R' E] (p : Submodule R' E)

/-- `submodule.subtype` as a `linear_isometry`. -/
def subtypeₗᵢ : p →ₗᵢ[R'] E :=
  ⟨p.Subtype, fun x => rfl⟩

@[simp]
theorem coe_subtypeₗᵢ : ⇑p.subtypeₗᵢ = p.Subtype :=
  rfl

@[simp]
theorem subtypeₗᵢ_to_linear_map : p.subtypeₗᵢ.toLinearMap = p.Subtype :=
  rfl

/-- `submodule.subtype` as a `continuous_linear_map`. -/
def subtypeL : p →L[R'] E :=
  p.subtypeₗᵢ.toContinuousLinearMap

@[simp]
theorem coe_subtypeL : (p.subtypeL : p →ₗ[R'] E) = p.Subtype :=
  rfl

@[simp]
theorem coe_subtypeL' : ⇑p.subtypeL = p.Subtype :=
  rfl

@[simp]
theorem range_subtypeL : p.subtypeL.range = p :=
  range_subtype _

@[simp]
theorem ker_subtypeL : p.subtypeL.ker = ⊥ :=
  ker_subtype _

end Submodule

/-- A semilinear isometric equivalence between two normed vector spaces. -/
structure LinearIsometryEquiv (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  (E E₂ : Type _) [SemiNormedGroup E] [SemiNormedGroup E₂] [Module R E] [Module R₂ E₂] extends E ≃ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ∥to_linear_equiv x∥ = ∥x∥

-- mathport name: «expr ≃ₛₗᵢ[ ] »
notation:25 E " ≃ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometryEquiv σ₁₂ E E₂

-- mathport name: «expr ≃ₗᵢ[ ] »
notation:25 E " ≃ₗᵢ[" R:25 "] " E₂:0 => LinearIsometryEquiv (RingHom.id R) E E₂

-- mathport name: «expr ≃ₗᵢ⋆[ ] »
notation:25 E " ≃ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometryEquiv (starRingEnd R) E E₂

namespace LinearIsometryEquiv

variable (e : E ≃ₛₗᵢ[σ₁₂] E₂)

include σ₂₁

theorem to_linear_equiv_injective : Injective (toLinearEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₛₗ[σ₁₂] E₂)
  | ⟨e, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
theorem to_linear_equiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearEquiv = g.toLinearEquiv ↔ f = g :=
  to_linear_equiv_injective.eq_iff

instance : AddMonoidHomClass (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe := fun e => e.toFun
  coe_injective' := fun f g h => to_linear_equiv_injective (FunLike.coe_injective h)
  map_add := fun f => map_add f.toLinearEquiv
  map_zero := fun f => map_zero f.toLinearEquiv

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ => E → E₂ :=
  ⟨fun f => f.toFun⟩

theorem coe_injective : @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E → E₂) coeFn :=
  FunLike.coe_injective

@[simp]
theorem coe_mk (e : E ≃ₛₗ[σ₁₂] E₂) (he : ∀ x, ∥e x∥ = ∥x∥) : ⇑(mk e he) = e :=
  rfl

@[simp]
theorem coe_to_linear_equiv (e : E ≃ₛₗᵢ[σ₁₂] E₂) : ⇑e.toLinearEquiv = e :=
  rfl

@[ext]
theorem ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, e x = e' x) : e = e' :=
  to_linear_equiv_injective <| LinearEquiv.ext h

protected theorem congr_arg {f : E ≃ₛₗᵢ[σ₁₂] E₂} : ∀ {x x' : E}, x = x' → f x = f x'
  | _, _, rfl => rfl

protected theorem congr_fun {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x :=
  h ▸ rfl

/-- Construct a `linear_isometry_equiv` from a `linear_equiv` and two inequalities:
`∀ x, ∥e x∥ ≤ ∥x∥` and `∀ y, ∥e.symm y∥ ≤ ∥y∥`. -/
def ofBounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : ∀ x, ∥e x∥ ≤ ∥x∥) (h₂ : ∀ y, ∥e.symm y∥ ≤ ∥y∥) : E ≃ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e, fun x =>
    le_antisymmₓ (h₁ x) <| by
      simpa only [← e.symm_apply_apply] using h₂ (e x)⟩

@[simp]
theorem norm_map (x : E) : ∥e x∥ = ∥x∥ :=
  e.norm_map' x

/-- Reinterpret a `linear_isometry_equiv` as a `linear_isometry`. -/
def toLinearIsometry : E →ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e.1, e.2⟩

theorem to_linear_isometry_injective : Function.Injective (toLinearIsometry : _ → E →ₛₗᵢ[σ₁₂] E₂) := fun x y h =>
  coe_injective (congr_arg _ h : ⇑x.toLinearIsometry = _)

@[simp]
theorem to_linear_isometry_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearIsometry = g.toLinearIsometry ↔ f = g :=
  to_linear_isometry_injective.eq_iff

@[simp]
theorem coe_to_linear_isometry : ⇑e.toLinearIsometry = e :=
  rfl

protected theorem isometry : Isometry e :=
  e.toLinearIsometry.Isometry

/-- Reinterpret a `linear_isometry_equiv` as an `isometric`. -/
def toIsometric : E ≃ᵢ E₂ :=
  ⟨e.toLinearEquiv.toEquiv, e.Isometry⟩

theorem to_isometric_injective : Function.Injective (toIsometric : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ᵢ E₂) := fun x y h =>
  coe_injective (congr_arg _ h : ⇑x.toIsometric = _)

@[simp]
theorem to_isometric_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toIsometric = g.toIsometric ↔ f = g :=
  to_isometric_injective.eq_iff

@[simp]
theorem coe_to_isometric : ⇑e.toIsometric = e :=
  rfl

theorem range_eq_univ (e : E ≃ₛₗᵢ[σ₁₂] E₂) : Set.Range e = Set.Univ := by
  rw [← coe_to_isometric]
  exact Isometric.range_eq_univ _

/-- Reinterpret a `linear_isometry_equiv` as an `homeomorph`. -/
def toHomeomorph : E ≃ₜ E₂ :=
  e.toIsometric.toHomeomorph

theorem to_homeomorph_injective : Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₜ E₂) := fun x y h =>
  coe_injective (congr_arg _ h : ⇑x.toHomeomorph = _)

@[simp]
theorem to_homeomorph_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toHomeomorph = g.toHomeomorph ↔ f = g :=
  to_homeomorph_injective.eq_iff

@[simp]
theorem coe_to_homeomorph : ⇑e.toHomeomorph = e :=
  rfl

protected theorem continuous : Continuous e :=
  e.Isometry.Continuous

protected theorem continuous_at {x} : ContinuousAt e x :=
  e.Continuous.ContinuousAt

protected theorem continuous_on {s} : ContinuousOn e s :=
  e.Continuous.ContinuousOn

protected theorem continuous_within_at {s x} : ContinuousWithinAt e s x :=
  e.Continuous.ContinuousWithinAt

/-- Interpret a `linear_isometry_equiv` as a continuous linear equiv. -/
def toContinuousLinearEquiv : E ≃SL[σ₁₂] E₂ :=
  { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }

theorem to_continuous_linear_equiv_injective : Function.Injective (toContinuousLinearEquiv : _ → E ≃SL[σ₁₂] E₂) :=
  fun x y h => coe_injective (congr_arg _ h : ⇑x.toContinuousLinearEquiv = _)

@[simp]
theorem to_continuous_linear_equiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearEquiv = g.toContinuousLinearEquiv ↔ f = g :=
  to_continuous_linear_equiv_injective.eq_iff

@[simp]
theorem coe_to_continuous_linear_equiv : ⇑e.toContinuousLinearEquiv = e :=
  rfl

omit σ₂₁

variable (R E)

/-- Identity map as a `linear_isometry_equiv`. -/
def refl : E ≃ₗᵢ[R] E :=
  ⟨LinearEquiv.refl R E, fun x => rfl⟩

variable {R E}

instance : Inhabited (E ≃ₗᵢ[R] E) :=
  ⟨refl R E⟩

@[simp]
theorem coe_refl : ⇑(refl R E) = id :=
  rfl

/-- The inverse `linear_isometry_equiv`. -/
def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
  ⟨e.toLinearEquiv.symm, fun x => (e.norm_map _).symm.trans <| congr_arg norm <| e.toLinearEquiv.apply_symm_apply x⟩

@[simp]
theorem apply_symm_apply (x : E₂) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp]
theorem map_eq_zero_iff {x : E} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

@[simp]
theorem symm_symm : e.symm.symm = e :=
  ext fun x => rfl

@[simp]
theorem to_linear_equiv_symm : e.toLinearEquiv.symm = e.symm.toLinearEquiv :=
  rfl

@[simp]
theorem to_isometric_symm : e.toIsometric.symm = e.symm.toIsometric :=
  rfl

@[simp]
theorem to_homeomorph_symm : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl

include σ₃₁ σ₃₂

/-- Composition of `linear_isometry_equiv`s as a `linear_isometry_equiv`. -/
def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
  ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun x => (e'.norm_map _).trans (e.norm_map _)⟩

include σ₁₃ σ₂₁

@[simp]
theorem coe_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) :
    (e₁.trans e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c) :=
  rfl

@[simp]
theorem to_linear_equiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toLinearEquiv = e.toLinearEquiv.trans e'.toLinearEquiv :=
  rfl

omit σ₁₃ σ₂₁ σ₃₁ σ₃₂

@[simp]
theorem trans_refl : e.trans (refl R₂ E₂) = e :=
  ext fun x => rfl

@[simp]
theorem refl_trans : (refl R E).trans e = e :=
  ext fun x => rfl

@[simp]
theorem self_trans_symm : e.trans e.symm = refl R E :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self : e.symm.trans e = refl R₂ E₂ :=
  ext e.apply_symm_apply

@[simp]
theorem symm_comp_self : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
theorem self_comp_symm : e ∘ e.symm = id :=
  e.symm.symm_comp_self

include σ₁₃ σ₂₁ σ₃₂ σ₃₁

@[simp]
theorem symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

theorem coe_symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl

include σ₁₄ σ₄₁ σ₄₂ σ₄₃ σ₂₄

theorem trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄) :
    eEE₂.trans (eE₂E₃.trans eE₃E₄) = (eEE₂.trans eE₂E₃).trans eE₃E₄ :=
  rfl

omit σ₂₁ σ₃₁ σ₄₁ σ₃₂ σ₄₂ σ₄₃ σ₁₃ σ₂₄ σ₁₄

instance : Groupₓ (E ≃ₗᵢ[R] E) where
  mul := fun e₁ e₂ => e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc := fun _ _ _ => trans_assoc _ _ _
  mul_left_inv := self_trans_symm

@[simp]
theorem coe_one : ⇑(1 : E ≃ₗᵢ[R] E) = id :=
  rfl

@[simp]
theorem coe_mul (e e' : E ≃ₗᵢ[R] E) : ⇑(e * e') = e ∘ e' :=
  rfl

@[simp]
theorem coe_inv (e : E ≃ₗᵢ[R] E) : ⇑e⁻¹ = e.symm :=
  rfl

theorem one_def : (1 : E ≃ₗᵢ[R] E) = refl _ _ :=
  rfl

theorem mul_def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e :=
  rfl

theorem inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm :=
  rfl

/-! Lemmas about mixing the group structure with definitions. Because we have multiple ways to
express `linear_isometry_equiv.refl`, `linear_isometry_equiv.symm`, and
`linear_isometry_equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it
after simp.

This copies the approach used by the lemmas near `equiv.perm.trans_one`. -/


@[simp]
theorem trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e :=
  trans_refl _

@[simp]
theorem one_trans : (1 : E ≃ₗᵢ[R] E).trans e = e :=
  refl_trans _

@[simp]
theorem refl_mul (e : E ≃ₗᵢ[R] E) : refl _ _ * e = e :=
  trans_refl _

@[simp]
theorem mul_refl (e : E ≃ₗᵢ[R] E) : e * refl _ _ = e :=
  refl_trans _

include σ₂₁

/-- Reinterpret a `linear_isometry_equiv` as a `continuous_linear_equiv`. -/
instance : CoeTₓ (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂) :=
  ⟨fun e => ⟨e.toLinearEquiv, e.Continuous, e.toIsometric.symm.Continuous⟩⟩

instance : CoeTₓ (E ≃ₛₗᵢ[σ₁₂] E₂) (E →SL[σ₁₂] E₂) :=
  ⟨fun e => ↑(e : E ≃SL[σ₁₂] E₂)⟩

@[simp]
theorem coe_coe : ⇑(e : E ≃SL[σ₁₂] E₂) = e :=
  rfl

@[simp]
theorem coe_coe' : ((e : E ≃SL[σ₁₂] E₂) : E →SL[σ₁₂] E₂) = e :=
  rfl

@[simp]
theorem coe_coe'' : ⇑(e : E →SL[σ₁₂] E₂) = e :=
  rfl

omit σ₂₁

@[simp]
theorem map_zero : e 0 = 0 :=
  e.1.map_zero

@[simp]
theorem map_add (x y : E) : e (x + y) = e x + e y :=
  e.1.map_add x y

@[simp]
theorem map_sub (x y : E) : e (x - y) = e x - e y :=
  e.1.map_sub x y

@[simp]
theorem map_smulₛₗ (c : R) (x : E) : e (c • x) = σ₁₂ c • e x :=
  e.1.map_smulₛₗ c x

@[simp]
theorem map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c • e x :=
  e.1.map_smul c x

@[simp]
theorem nnnorm_map (x : E) : ∥e x∥₊ = ∥x∥₊ :=
  e.toLinearIsometry.nnnorm_map x

@[simp]
theorem dist_map (x y : E) : dist (e x) (e y) = dist x y :=
  e.toLinearIsometry.dist_map x y

@[simp]
theorem edist_map (x y : E) : edist (e x) (e y) = edist x y :=
  e.toLinearIsometry.edist_map x y

protected theorem bijective : Bijective e :=
  e.1.Bijective

protected theorem injective : Injective e :=
  e.1.Injective

protected theorem surjective : Surjective e :=
  e.1.Surjective

@[simp]
theorem map_eq_iff {x y : E} : e x = e y ↔ x = y :=
  e.Injective.eq_iff

theorem map_ne {x y : E} (h : x ≠ y) : e x ≠ e y :=
  e.Injective.Ne h

protected theorem lipschitz : LipschitzWith 1 e :=
  e.Isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.Isometry.antilipschitz

@[simp]
theorem ediam_image (s : Set E) : Emetric.diam (e '' s) = Emetric.diam s :=
  e.Isometry.ediam_image s

@[simp]
theorem diam_image (s : Set E) : Metric.diam (e '' s) = Metric.diam s :=
  e.Isometry.diam_image s

variable {α : Type _} [TopologicalSpace α]

@[simp]
theorem comp_continuous_on_iff {f : α → E} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.Isometry.comp_continuous_on_iff

@[simp]
theorem comp_continuous_iff {f : α → E} : Continuous (e ∘ f) ↔ Continuous f :=
  e.Isometry.comp_continuous_iff

instance complete_space_map (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map (e.toLinearEquiv : E →ₛₗ[σ₁₂] E₂)) :=
  e.toLinearIsometry.complete_space_map p

include σ₂₁

/-- Construct a linear isometry equiv from a surjective linear isometry. -/
noncomputable def ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) : F ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofBijective f.toLinearMap f.Injective hfr with norm_map' := f.norm_map }

@[simp]
theorem coe_of_surjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    ⇑(LinearIsometryEquiv.ofSurjective f hfr) = f := by
  ext
  rfl

omit σ₂₁

variable (R)

/-- The negation operation on a normed space `E`, considered as a linear isometry equivalence. -/
def neg : E ≃ₗᵢ[R] E :=
  { LinearEquiv.neg R with norm_map' := norm_neg }

variable {R}

@[simp]
theorem coe_neg : (neg R : E → E) = fun x => -x :=
  rfl

@[simp]
theorem symm_neg : (neg R : E ≃ₗᵢ[R] E).symm = neg R :=
  rfl

variable (R E E₂ E₃)

/-- The natural equivalence `(E × E₂) × E₃ ≃ E × (E₂ × E₃)` is a linear isometry. -/
def prodAssoc [Module R E₂] [Module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃ :=
  { Equivₓ.prodAssoc E E₂ E₃ with toFun := Equivₓ.prodAssoc E E₂ E₃, invFun := (Equivₓ.prodAssoc E E₂ E₃).symm,
    map_add' := by
      simp ,
    map_smul' := by
      simp ,
    norm_map' := by
      rintro ⟨⟨e, f⟩, g⟩
      simp only [← LinearEquiv.coe_mk, ← Equivₓ.prod_assoc_apply, ← Prod.norm_def, ← max_assocₓ] }

@[simp]
theorem coe_prod_assoc [Module R E₂] [Module R E₃] :
    (prodAssoc R E E₂ E₃ : (E × E₂) × E₃ → E × E₂ × E₃) = Equivₓ.prodAssoc E E₂ E₃ :=
  rfl

@[simp]
theorem coe_prod_assoc_symm [Module R E₂] [Module R E₃] :
    ((prodAssoc R E E₂ E₃).symm : E × E₂ × E₃ → (E × E₂) × E₃) = (Equivₓ.prodAssoc E E₂ E₃).symm :=
  rfl

end LinearIsometryEquiv

/-- Two linear isometries are equal if they are equal on basis vectors. -/
theorem Basis.ext_linear_isometry {ι : Type _} (b : Basis ι R E) {f₁ f₂ : E →ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometry.to_linear_map_injective <| b.ext h

include σ₂₁

/-- Two linear isometric equivalences are equal if they are equal on basis vectors. -/
theorem Basis.ext_linear_isometry_equiv {ι : Type _} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometryEquiv.to_linear_equiv_injective <| b.ext' h

omit σ₂₁

