/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Patrick Massot, Floris van Doorn
-/
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.Topology.FiberBundle

/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`, one should
additionally have the following data:

* `F` should be a normed space over a normed field `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* There should be a distinguished set of bundle trivializations (which are continuous linear equivs
in the fibres), the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, and if moreover for any two trivializations `e`, `e'` in the
atlas the transition function considered as a map from `B` into `F →L[R] F` is continuous on
`e.base_set ∩ e'.base_set` with respect to the operator norm topology on `F →L[R] F`, we register
the typeclass `topological_vector_bundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.
Only the trivial bundle is defined in this file.

## Tags
Vector bundle
-/


noncomputable section

open Bundle Set

open Classical

variable (R 𝕜 : Type _) {B : Type _} (F : Type _) (E : B → Type _)

section TopologicalVectorSpace

variable [Semiringₓ R] [∀ x, AddCommMonoidₓ (E x)] [∀ x, Module R (E x)] [TopologicalSpace F] [AddCommMonoidₓ F]
  [Module R F] [TopologicalSpace B]

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- A pretrivialization for a (yet to be defined) topological vector bundle `total_space E` is a
local equiv between sets of the form `proj ⁻¹' base_set` and `base_set × F` which respects the
first coordinate, and is linear in each fiber. -/
@[ext, nolint has_inhabited_instance]
structure TopologicalVectorBundle.Pretrivialization extends
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure" where
  linear' : ∀, ∀ x ∈ base_set, ∀, IsLinearMap R fun y : E x => (to_fun (totalSpaceMk x y)).2

instance : CoeFun (TopologicalVectorBundle.Pretrivialization R F E) _ :=
  ⟨fun e => e.toFun⟩

instance :
    Coe (TopologicalVectorBundle.Pretrivialization R F E)
      (TopologicalFiberBundle.Pretrivialization F (@TotalSpace.proj B E)) :=
  ⟨TopologicalVectorBundle.Pretrivialization.toFiberBundlePretrivialization⟩

namespace TopologicalVectorBundle.Pretrivialization

open TopologicalVectorBundle

variable {R F E} (e : Pretrivialization R F E) {x : TotalSpace E} {b : B} {y : E b}

protected theorem linear (hb : b ∈ e.BaseSet) : IsLinearMap R fun y : E b => (e (totalSpaceMk b y)).2 :=
  e.linear' b hb

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toLocalEquiv = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.Source) : (e x).1 = x.proj :=
  e.proj_to_fun x ex

theorem mem_source : x ∈ e.Source ↔ x.proj ∈ e.BaseSet := by
  rw [e.source_eq, mem_preimage]

theorem coe_mem_source : ↑y ∈ e.Source ↔ b ∈ e.BaseSet :=
  e.mem_source

theorem coe_fst' (ex : x.proj ∈ e.BaseSet) : (e x).1 = x.proj :=
  e.coe_fst (e.mem_source.2 ex)

protected theorem eq_on : EqOn (Prod.fst ∘ e) TotalSpace.proj e.Source := fun x hx => e.coe_fst hx

theorem mk_proj_snd (ex : x ∈ e.Source) : (x.proj, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst ex).symm rfl

@[simp, mfld_simps]
theorem coe_coe_fst (hb : b ∈ e.BaseSet) : (e y).1 = b :=
  e.coe_fst (e.mem_source.2 hb)

theorem mk_proj_snd' (ex : x.proj ∈ e.BaseSet) : (x.proj, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst' ex).symm rfl

theorem mem_target {x : B × F} : x ∈ e.Target ↔ x.1 ∈ e.BaseSet :=
  e.toFiberBundlePretrivialization.mem_target

theorem mk_mem_target {x : B} {y : F} : (x, y) ∈ e.Target ↔ x ∈ e.BaseSet :=
  e.mem_target

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.Target) : (e.toLocalEquiv.symm x).proj = x.1 :=
  e.toFiberBundlePretrivialization.proj_symm_apply hx

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : (e.toLocalEquiv.symm (b, x)).proj = b :=
  e.proj_symm_apply (e.mem_target.2 hx)

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.Target) : e (e.toLocalEquiv.symm x) = x :=
  e.toLocalEquiv.right_inv hx

theorem symm_apply_apply {x : TotalSpace E} (hx : x ∈ e.Source) : e.toLocalEquiv.symm (e x) = x :=
  e.toLocalEquiv.left_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : e (e.toLocalEquiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps]
theorem symm_apply_mk_proj (ex : x ∈ e.Source) : e.toLocalEquiv.symm (x.proj, (e x).2) = x := by
  rw [← e.coe_fst ex, Prod.mk.eta, ← e.coe_coe, e.to_local_equiv.left_inv ex]

@[simp, mfld_simps]
theorem preimage_symm_proj_base_set : e.toLocalEquiv.symm ⁻¹' (total_space.proj ⁻¹' e.BaseSet) ∩ e.Target = e.Target :=
  e.toFiberBundlePretrivialization.preimage_symm_proj_base_set

theorem symm_coe_proj {x : B} {y : F} (e : Pretrivialization R F E) (h : x ∈ e.BaseSet) :
    (e.toLocalEquiv.symm (x, y)).1 = x :=
  e.proj_symm_apply' h

/-- A fiberwise inverse to `e`. This is the function `F → E b` that induces a local inverse
`B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (e : Pretrivialization R F E) (b : B) (y : F) : E b :=
  if hb : b ∈ e.BaseSet then cast (congr_arg E (e.proj_symm_apply' hb)) (e.toLocalEquiv.symm (b, y)).2 else 0

theorem symm_apply (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toLocalEquiv.symm (b, y)).2 :=
  dif_pos hb

theorem symm_apply_of_not_mem (e : Pretrivialization R F E) {b : B} (hb : b ∉ e.BaseSet) (y : F) : e.symm b y = 0 :=
  dif_neg hb

theorem coe_symm_of_not_mem (e : Pretrivialization R F E) {b : B} (hb : b ∉ e.BaseSet) : (e.symm b : F → E b) = 0 :=
  funext fun y => dif_neg hb

theorem mk_symm (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    totalSpaceMk b (e.symm b y) = e.toLocalEquiv.symm (b, y) := by
  rw [e.symm_apply hb, total_space.mk_cast, total_space.eta]

theorem symm_proj_apply (e : Pretrivialization R F E) (z : TotalSpace E) (hz : z.proj ∈ e.BaseSet) :
    e.symm z.proj (e z).2 = z.2 := by
  rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz, e.symm_apply_apply (e.mem_source.mpr hz)]

theorem symm_apply_apply_mk (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : E b) :
    e.symm b (e (totalSpaceMk b y)).2 = y :=
  e.symm_proj_apply (totalSpaceMk b y) hb

theorem apply_mk_symm (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    e (totalSpaceMk b (e.symm b y)) = (b, y) := by
  rw [e.mk_symm hb, e.apply_symm_apply (e.mk_mem_target.mpr hb)]

/-- A fiberwise linear inverse to `e`. -/
@[simps]
protected def symmₗ (e : Pretrivialization R F E) (b : B) : F →ₗ[R] E b := by
  refine' IsLinearMap.mk' (e.symm b) _
  by_cases' hb : b ∈ e.base_set
  · exact
      (((e.linear hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v =>
          congr_arg Prod.snd <| e.apply_mk_symm hb v).is_linear
    
  · rw [e.coe_symm_of_not_mem hb]
    exact (0 : F →ₗ[R] E b).is_linear
    

/-- A pretrivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps (config := { fullyApplied := false })]
def linearEquivAt (e : Pretrivialization R F E) (b : B) (hb : b ∈ e.BaseSet) : E b ≃ₗ[R] F where
  toFun := fun y => (e (totalSpaceMk b y)).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv := fun v => by
    simp_rw [e.apply_mk_symm hb v]
  map_add' := fun v w => (e.linear hb).map_add v w
  map_smul' := fun c v => (e.linear hb).map_smul c v

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linearMapAt (e : Pretrivialization R F E) (b : B) : E b →ₗ[R] F :=
  if hb : b ∈ e.BaseSet then e.linearEquivAt b hb else 0

theorem coe_linear_map_at (e : Pretrivialization R F E) (b : B) :
    ⇑(e.linearMapAt b) = fun y => if b ∈ e.BaseSet then (e (totalSpaceMk b y)).2 else 0 := by
  rw [pretrivialization.linear_map_at]
  split_ifs <;> rfl

theorem coe_linear_map_at_of_mem (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) :
    ⇑(e.linearMapAt b) = fun y => (e (totalSpaceMk b y)).2 := by
  simp_rw [coe_linear_map_at, if_pos hb]

theorem linear_map_at_apply (e : Pretrivialization R F E) {b : B} (y : E b) :
    e.linearMapAt b y = if b ∈ e.BaseSet then (e (totalSpaceMk b y)).2 else 0 := by
  rw [coe_linear_map_at]

theorem linear_map_at_def_of_mem (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) :
    e.linearMapAt b = e.linearEquivAt b hb :=
  dif_pos hb

theorem linear_map_at_def_of_not_mem (e : Pretrivialization R F E) {b : B} (hb : b ∉ e.BaseSet) : e.linearMapAt b = 0 :=
  dif_neg hb

theorem linear_map_at_eq_zero (e : Pretrivialization R F E) {b : B} (hb : b ∉ e.BaseSet) : e.linearMapAt b = 0 :=
  dif_neg hb

theorem symmₗ_linear_map_at (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : E b) :
    e.symmₗ b (e.linearMapAt b y) = y := by
  rw [e.linear_map_at_def_of_mem hb]
  exact (e.linear_equiv_at b hb).left_inv y

theorem linear_map_at_symmₗ (e : Pretrivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    e.linearMapAt b (e.symmₗ b y) = y := by
  rw [e.linear_map_at_def_of_mem hb]
  exact (e.linear_equiv_at b hb).right_inv y

end TopologicalVectorBundle.Pretrivialization

variable [TopologicalSpace (TotalSpace E)]

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- A structure extending local homeomorphisms, defining a local trivialization of the projection
`proj : total_space E → B` with fiber `F`, as a local homeomorphism between `total_space E`
and `B × F` defined between two sets of the form `proj ⁻¹' base_set` and `base_set × F`,
acting trivially on the first coordinate and linear in the fibers.
-/
@[ext, nolint has_inhabited_instance]
structure TopologicalVectorBundle.Trivialization extends
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure" where
  linear' : ∀, ∀ x ∈ base_set, ∀, IsLinearMap R fun y : E x => (to_fun (totalSpaceMk x y)).2

open TopologicalVectorBundle

instance : CoeFun (Trivialization R F E) fun _ => TotalSpace E → B × F :=
  ⟨fun e => e.toFun⟩

instance : Coe (Trivialization R F E) (TopologicalFiberBundle.Trivialization F (@TotalSpace.proj B E)) :=
  ⟨TopologicalVectorBundle.Trivialization.toFiberBundleTrivialization⟩

namespace TopologicalVectorBundle.Trivialization

variable {R F E} (e : Trivialization R F E) {x : TotalSpace E} {b : B} {y : E b}

/-- Natural identification as `topological_vector_bundle.pretrivialization`. -/
def toPretrivialization (e : Trivialization R F E) : TopologicalVectorBundle.Pretrivialization R F E :=
  { e with }

protected theorem linear (hb : b ∈ e.BaseSet) : IsLinearMap R fun y : E b => (e (totalSpaceMk b y)).2 :=
  e.linear' b hb

protected theorem continuous_on : ContinuousOn e e.Source :=
  e.continuous_to_fun

theorem to_pretrivialization_injective : Function.Injective fun e : Trivialization R F E => e.toPretrivialization := by
  intro e e'
  rw [pretrivialization.ext_iff, trivialization.ext_iff, ←
    topological_fiber_bundle.trivialization.to_pretrivialization_injective.eq_iff]
  exact id

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toLocalHomeomorph = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.Source) : (e x).1 = x.proj :=
  e.proj_to_fun x ex

theorem mem_source : x ∈ e.Source ↔ x.proj ∈ e.BaseSet := by
  rw [e.source_eq, mem_preimage]

theorem coe_mem_source : ↑y ∈ e.Source ↔ b ∈ e.BaseSet :=
  e.mem_source

theorem coe_fst' (ex : x.proj ∈ e.BaseSet) : (e x).1 = x.proj :=
  e.coe_fst (e.mem_source.2 ex)

protected theorem eq_on : EqOn (Prod.fst ∘ e) TotalSpace.proj e.Source := fun x hx => e.coe_fst hx

theorem mk_proj_snd (ex : x ∈ e.Source) : (x.proj, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst ex).symm rfl

theorem mk_proj_snd' (ex : x.proj ∈ e.BaseSet) : (x.proj, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst' ex).symm rfl

theorem open_target : IsOpen e.Target := by
  rw [e.target_eq]
  exact e.open_base_set.prod is_open_univ

@[simp, mfld_simps]
theorem coe_coe_fst (hb : b ∈ e.BaseSet) : (e y).1 = b :=
  e.coe_fst (e.mem_source.2 hb)

theorem source_inter_preimage_target_inter (s : Set (B × F)) : e.Source ∩ e ⁻¹' (e.Target ∩ s) = e.Source ∩ e ⁻¹' s :=
  e.toLocalHomeomorph.source_inter_preimage_target_inter s

theorem mem_target {x : B × F} : x ∈ e.Target ↔ x.1 ∈ e.BaseSet :=
  e.toPretrivialization.mem_target

theorem mk_mem_target {y : F} : (b, y) ∈ e.Target ↔ b ∈ e.BaseSet :=
  e.toPretrivialization.mem_target

theorem map_target {x : B × F} (hx : x ∈ e.Target) : e.toLocalHomeomorph.symm x ∈ e.Source :=
  e.toLocalHomeomorph.map_target hx

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.Target) : (e.toLocalHomeomorph.symm x).proj = x.1 :=
  e.toPretrivialization.proj_symm_apply hx

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : (e.toLocalHomeomorph.symm (b, x)).proj = b :=
  e.toPretrivialization.proj_symm_apply' hx

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.Target) : e (e.toLocalHomeomorph.symm x) = x :=
  e.toLocalHomeomorph.right_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : e (e.toLocalHomeomorph.symm (b, x)) = (b, x) :=
  e.toPretrivialization.apply_symm_apply' hx

theorem symm_apply_apply {x : TotalSpace E} (hx : x ∈ e.Source) : e.toLocalHomeomorph.symm (e x) = x :=
  e.toLocalEquiv.left_inv hx

@[simp, mfld_simps]
theorem symm_coe_proj {x : B} {y : F} (e : Trivialization R F E) (h : x ∈ e.BaseSet) :
    (e.toLocalHomeomorph.symm (x, y)).1 = x :=
  e.proj_symm_apply' h

/-- A fiberwise inverse to `e`. The function `F → E x` that induces a local inverse
  `B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (e : Trivialization R F E) (b : B) (y : F) : E b :=
  e.toPretrivialization.symm b y

theorem symm_apply (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toLocalHomeomorph.symm (b, y)).2 :=
  dif_pos hb

theorem symm_apply_of_not_mem (e : Trivialization R F E) {b : B} (hb : b ∉ e.BaseSet) (y : F) : e.symm b y = 0 :=
  dif_neg hb

theorem mk_symm (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    totalSpaceMk b (e.symm b y) = e.toLocalHomeomorph.symm (b, y) :=
  e.toPretrivialization.mk_symm hb y

theorem symm_proj_apply (e : Trivialization R F E) (z : TotalSpace E) (hz : z.proj ∈ e.BaseSet) :
    e.symm z.proj (e z).2 = z.2 :=
  e.toPretrivialization.symm_proj_apply z hz

theorem symm_apply_apply_mk (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : E b) :
    e.symm b (e (totalSpaceMk b y)).2 = y :=
  e.symm_proj_apply (totalSpaceMk b y) hb

theorem apply_mk_symm (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    e (totalSpaceMk b (e.symm b y)) = (b, y) :=
  e.toPretrivialization.apply_mk_symm hb y

theorem continuous_on_symm (e : Trivialization R F E) :
    ContinuousOn (fun z : B × F => totalSpaceMk z.1 (e.symm z.1 z.2)) (e.BaseSet ×ˢ (Univ : Set F)) := by
  have :
    ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : Set F)),
      total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z :=
    by
    rintro x ⟨hx : x.1 ∈ e.base_set, _⟩
    simp_rw [e.mk_symm hx, Prod.mk.eta]
  refine' ContinuousOn.congr _ this
  rw [← e.target_eq]
  exact e.to_local_homeomorph.continuous_on_symm

/-- A trivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
def linearEquivAt (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) : E b ≃ₗ[R] F :=
  e.toPretrivialization.linearEquivAt b hb

@[simp]
theorem linear_equiv_at_apply (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) (v : E b) :
    e.linearEquivAt b hb v = (e (totalSpaceMk b v)).2 :=
  rfl

@[simp]
theorem linear_equiv_at_symm_apply (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) (v : F) :
    (e.linearEquivAt b hb).symm v = e.symm b v :=
  rfl

/-- A fiberwise linear inverse to `e`. -/
protected def symmₗ (e : Trivialization R F E) (b : B) : F →ₗ[R] E b :=
  e.toPretrivialization.symmₗ b

theorem coe_symmₗ (e : Trivialization R F E) (b : B) : ⇑(e.symmₗ b) = e.symm b :=
  rfl

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linearMapAt (e : Trivialization R F E) (b : B) : E b →ₗ[R] F :=
  e.toPretrivialization.linearMapAt b

theorem coe_linear_map_at (e : Trivialization R F E) (b : B) :
    ⇑(e.linearMapAt b) = fun y => if b ∈ e.BaseSet then (e (totalSpaceMk b y)).2 else 0 :=
  e.toPretrivialization.coe_linear_map_at b

theorem coe_linear_map_at_of_mem (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) :
    ⇑(e.linearMapAt b) = fun y => (e (totalSpaceMk b y)).2 := by
  simp_rw [coe_linear_map_at, if_pos hb]

theorem linear_map_at_apply (e : Trivialization R F E) {b : B} (y : E b) :
    e.linearMapAt b y = if b ∈ e.BaseSet then (e (totalSpaceMk b y)).2 else 0 := by
  rw [coe_linear_map_at]

theorem linear_map_at_def_of_mem (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) :
    e.linearMapAt b = e.linearEquivAt b hb :=
  dif_pos hb

theorem linear_map_at_def_of_not_mem (e : Trivialization R F E) {b : B} (hb : b ∉ e.BaseSet) : e.linearMapAt b = 0 :=
  dif_neg hb

theorem symmₗ_linear_map_at (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : E b) :
    e.symmₗ b (e.linearMapAt b y) = y :=
  e.toPretrivialization.symmₗ_linear_map_at hb y

theorem linear_map_at_symmₗ (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    e.linearMapAt b (e.symmₗ b y) = y :=
  e.toPretrivialization.linear_map_at_symmₗ hb y

/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coordChange (e e' : Trivialization R F E) (b : B) : F ≃L[R] F :=
  { if hb : b ∈ e.BaseSet ∩ e'.BaseSet then (e.linearEquivAt b (hb.1 : _)).symm.trans (e'.linearEquivAt b hb.2)
    else LinearEquiv.refl R F with
    continuous_to_fun := by
      by_cases' hb : b ∈ e.base_set ∩ e'.base_set
      · simp_rw [dif_pos hb]
        refine' (e'.continuous_on.comp_continuous _ _).snd
        exact e.continuous_on_symm.comp_continuous (Continuous.Prod.mk b) fun y => mk_mem_prod hb.1 (mem_univ y)
        exact fun y => e'.mem_source.mpr hb.2
        
      · rw [dif_neg hb]
        exact continuous_id
        ,
    continuous_inv_fun := by
      by_cases' hb : b ∈ e.base_set ∩ e'.base_set
      · simp_rw [dif_pos hb]
        refine' (e.continuous_on.comp_continuous _ _).snd
        exact e'.continuous_on_symm.comp_continuous (Continuous.Prod.mk b) fun y => mk_mem_prod hb.2 (mem_univ y)
        exact fun y => e.mem_source.mpr hb.1
        
      · rw [dif_neg hb]
        exact continuous_id
         }

theorem coe_coord_change (e e' : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet) :
    ⇑(coordChange e e' b) = (e.linearEquivAt b hb.1).symm.trans (e'.linearEquivAt b hb.2) :=
  congr_arg LinearEquiv.toFun (dif_pos hb)

theorem coord_change_apply (e e' : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet) (y : F) :
    coordChange e e' b y = (e' (totalSpaceMk b (e.symm b y))).2 :=
  congr_arg (fun f => LinearEquiv.toFun f y) (dif_pos hb)

theorem mk_coord_change (e e' : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet) (y : F) :
    (b, coordChange e e' b y) = e' (totalSpaceMk b (e.symm b y)) := by
  ext
  · rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
    
  · exact e.coord_change_apply e' hb y
    

/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
theorem coord_change_apply' (e e' : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet) (y : F) :
    coordChange e e' b y = (e' (e.toLocalHomeomorph.symm (b, y))).2 := by
  rw [e.coord_change_apply e' hb, e.mk_symm hb.1]

theorem coord_change_symm_apply (e e' : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet) :
    ⇑(coordChange e e' b).symm = (e'.linearEquivAt b hb.2).symm.trans (e.linearEquivAt b hb.1) :=
  congr_arg LinearEquiv.invFun (dif_pos hb)

end TopologicalVectorBundle.Trivialization

end TopologicalVectorSpace

section

open TopologicalVectorBundle

variable (B)

variable [NondiscreteNormedField R] [∀ x, AddCommMonoidₓ (E x)] [∀ x, Module R (E x)] [NormedGroup F] [NormedSpace R F]
  [TopologicalSpace B] [TopologicalSpace (TotalSpace E)] [∀ x, TopologicalSpace (E x)]

/-- The valid transition functions for a topological vector bundle over `B` modelled on
a normed space `F`: a transition function must be a local homeomorphism of `B × F` with source and
target both `s ×ˢ univ`, which on this set is of the form `λ (b, v), (b, ε b v)` for some continuous
map `ε` from `s` to `F ≃L[R] F`. Here continuity is with respect to the operator norm on
`F →L[R] F`. -/
def ContinuousTransitions (e : LocalEquiv (B × F) (B × F)) : Prop :=
  ∃ s : Set B,
    e.Source = s ×ˢ (Univ : Set F) ∧
      e.Target = s ×ˢ (Univ : Set F) ∧
        ∃ ε : B → F ≃L[R] F, ContinuousOn (fun b => (ε b : F →L[R] F)) s ∧ ∀, ∀ b ∈ s, ∀, ∀ v : F, e (b, v) = (b, ε b v)

variable {B}

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`total_space_mk_inducing] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`TrivializationAtlas] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`trivializationAt] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`mem_base_set_trivialization_at] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`trivialization_mem_atlas] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`continuous_on_coord_change] []
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (e e' «expr ∈ » trivialization_atlas)
/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class TopologicalVectorBundle where
  total_space_mk_inducing : ∀ b : B, Inducing (@totalSpaceMk B E b)
  TrivializationAtlas : Set (Trivialization R F E)
  trivializationAt : B → Trivialization R F E
  mem_base_set_trivialization_at : ∀ b : B, b ∈ (trivialization_at b).BaseSet
  trivialization_mem_atlas : ∀ b : B, trivialization_at b ∈ trivialization_atlas
  continuous_on_coord_change :
    ∀ (e e') (_ : e ∈ trivialization_atlas) (_ : e' ∈ trivialization_atlas),
      ContinuousOn (fun b => Trivialization.coordChange e e' b : B → F →L[R] F) (e.BaseSet ∩ e'.BaseSet)

export
  TopologicalVectorBundle (TrivializationAtlas trivializationAt mem_base_set_trivialization_at trivialization_mem_atlas continuous_on_coord_change)

variable {R F E} [TopologicalVectorBundle R F E]

namespace TopologicalVectorBundle

namespace Trivialization

/-- Forward map of `continuous_linear_equiv_at` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps (config := { fullyApplied := false }) apply]
def continuousLinearMapAt (e : Trivialization R F E) (b : B) : E b →L[R] F :=
  { -- given explicitly to help `simps`
        e.linearMapAt
      b with
    toFun := e.linearMapAt b,
    cont := by
      dsimp'
      rw [e.coe_linear_map_at b]
      refine' continuous_if_const _ (fun hb => _) fun _ => continuous_zero
      exact
        continuous_snd.comp
          (e.to_local_homeomorph.continuous_on.comp_continuous (total_space_mk_inducing R F E b).Continuous fun x =>
            e.mem_source.mpr hb) }

/-- Backwards map of `continuous_linear_equiv_at`, defined everywhere. -/
@[simps (config := { fullyApplied := false }) apply]
def symmL (e : Trivialization R F E) (b : B) : F →L[R] E b :=
  { -- given explicitly to help `simps`
        e.symmₗ
      b with
    toFun := e.symm b,
    cont := by
      by_cases' hb : b ∈ e.base_set
      · rw [(TopologicalVectorBundle.total_space_mk_inducing R F E b).continuous_iff]
        exact
          e.continuous_on_symm.comp_continuous (continuous_const.prod_mk continuous_id) fun x =>
            mk_mem_prod hb (mem_univ x)
        
      · refine' continuous_zero.congr fun x => (e.symm_apply_of_not_mem hb x).symm
         }

theorem symmL_continuous_linear_map_at (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : E b) :
    e.symmL b (e.continuousLinearMapAt b y) = y :=
  e.symmₗ_linear_map_at hb y

theorem continuous_linear_map_at_symmL (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) (y : F) :
    e.continuousLinearMapAt b (e.symmL b y) = y :=
  e.linear_map_at_symmₗ hb y

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps (config := { fullyApplied := false }) apply symmApply]
def continuousLinearEquivAt (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) : E b ≃L[R] F :=
  { -- given explicitly to help `simps`
          -- given explicitly to help `simps`
          e.toPretrivialization.linearEquivAt
      b hb with
    toFun := fun y => (e (totalSpaceMk b y)).2, invFun := e.symm b,
    continuous_to_fun :=
      continuous_snd.comp
        (e.toLocalHomeomorph.ContinuousOn.comp_continuous (total_space_mk_inducing R F E b).Continuous fun x =>
          e.mem_source.mpr hb),
    continuous_inv_fun := (e.symmL b).Continuous }

theorem coe_continuous_linear_equiv_at_eq (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) :
    (e.continuousLinearEquivAt b hb : E b → F) = e.continuousLinearMapAt b :=
  (e.coe_linear_map_at_of_mem hb).symm

theorem symm_continuous_linear_equiv_at_eq (e : Trivialization R F E) {b : B} (hb : b ∈ e.BaseSet) :
    ((e.continuousLinearEquivAt b hb).symm : F → E b) = e.symmL b :=
  rfl

@[simp]
theorem continuous_linear_equiv_at_apply' (e : Trivialization R F E) (x : TotalSpace E) (hx : x ∈ e.Source) :
    e.continuousLinearEquivAt x.proj (e.mem_source.1 hx) x.2 = (e x).2 := by
  cases x
  rfl

theorem apply_eq_prod_continuous_linear_equiv_at (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) (z : E b) :
    e.toLocalHomeomorph ⟨b, z⟩ = (b, e.continuousLinearEquivAt b hb z) := by
  ext
  · refine' e.coe_fst _
    rw [e.source_eq]
    exact hb
    
  · simp only [← coe_coe, ← continuous_linear_equiv_at_apply]
    

theorem symm_apply_eq_mk_continuous_linear_equiv_at_symm (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet)
    (z : F) : e.toLocalHomeomorph.symm ⟨b, z⟩ = totalSpaceMk b ((e.continuousLinearEquivAt b hb).symm z) := by
  have h : (b, z) ∈ e.to_local_homeomorph.target := by
    rw [e.target_eq]
    exact ⟨hb, mem_univ _⟩
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h)
  · simp only [← e.source_eq, ← hb, ← mem_preimage]
    
  simp_rw [e.apply_eq_prod_continuous_linear_equiv_at b hb, e.to_local_homeomorph.right_inv h,
    ContinuousLinearEquiv.apply_symm_apply]

theorem comp_continuous_linear_equiv_at_eq_coord_change (e e' : Trivialization R F E) {b : B}
    (hb : b ∈ e.1.BaseSet ∩ e'.1.BaseSet) :
    (e.continuousLinearEquivAt b hb.1).symm.trans (e'.continuousLinearEquivAt b hb.2) = coordChange e e' b := by
  ext v
  rw [coord_change_apply e e' hb]
  rfl

end Trivialization

section

instance {B : Type _} {F : Type _} [AddCommMonoidₓ F] (b : B) : AddCommMonoidₓ (Bundle.Trivial B F b) :=
  ‹AddCommMonoidₓ F›

instance {B : Type _} {F : Type _} [AddCommGroupₓ F] (b : B) : AddCommGroupₓ (Bundle.Trivial B F b) :=
  ‹AddCommGroupₓ F›

instance {B : Type _} {F : Type _} [AddCommMonoidₓ F] [Module R F] (b : B) : Module R (Bundle.Trivial B F b) :=
  ‹Module R F›

end

namespace TrivialTopologicalVectorBundle

variable (R B F)

/-- Local trivialization for trivial bundle. -/
def trivialization : Trivialization R F (Bundle.Trivial B F) where
  toFun := fun x => (x.fst, x.snd)
  invFun := fun y => ⟨y.fst, y.snd⟩
  Source := Univ
  Target := Univ
  map_source' := fun x h => mem_univ (x.fst, x.snd)
  map_target' := fun y h => mem_univ ⟨y.fst, y.snd⟩
  left_inv' := fun x h => Sigma.eq rfl rfl
  right_inv' := fun x h => Prod.extₓ rfl rfl
  open_source := is_open_univ
  open_target := is_open_univ
  continuous_to_fun := by
    rw [← continuous_iff_continuous_on_univ, continuous_iff_le_induced]
    simp only [← Prod.topologicalSpace, ← induced_inf, ← induced_compose]
    exact le_rfl
  continuous_inv_fun := by
    rw [← continuous_iff_continuous_on_univ, continuous_iff_le_induced]
    simp only [← Bundle.TotalSpace.topologicalSpace, ← induced_inf, ← induced_compose]
    exact le_rfl
  BaseSet := Univ
  open_base_set := is_open_univ
  source_eq := rfl
  target_eq := by
    simp only [← univ_prod_univ]
  proj_to_fun := fun y hy => rfl
  linear' := fun x hx => ⟨fun y z => rfl, fun c y => rfl⟩

theorem trivialization.coord_change (b : B) :
    (trivialization R B F).coordChange (trivialization R B F) b = ContinuousLinearEquiv.refl R F := by
  ext v
  rw [trivialization.coord_change_apply']
  exacts[rfl, ⟨mem_univ _, mem_univ _⟩]

@[simp]
theorem trivialization_source : (trivialization R B F).Source = univ :=
  rfl

@[simp]
theorem trivialization_target : (trivialization R B F).Target = univ :=
  rfl

instance topologicalVectorBundle : TopologicalVectorBundle R F (Bundle.Trivial B F) where
  TrivializationAtlas := {TrivialTopologicalVectorBundle.trivialization R B F}
  trivializationAt := fun x => TrivialTopologicalVectorBundle.trivialization R B F
  mem_base_set_trivialization_at := mem_univ
  trivialization_mem_atlas := fun x => mem_singleton _
  total_space_mk_inducing := fun b =>
    ⟨by
      have : (fun x : trivialₓ B F b => x) = @id F := by
        ext x
        rfl
      simp only [← total_space.topological_space, ← induced_inf, ← induced_compose, ← Function.comp, ← total_space.proj,
        ← induced_const, ← top_inf_eq, ← trivial.proj_snd, ← id.def, ← trivial.topological_space, ← this, ← induced_id]⟩
  continuous_on_coord_change := by
    intro e he e' he'
    rw [mem_singleton_iff.mp he, mem_singleton_iff.mp he']
    simp_rw [trivial_topological_vector_bundle.trivialization.coord_change]
    exact continuous_const.continuous_on

end TrivialTopologicalVectorBundle

-- Not registered as an instance because of a metavariable.
theorem is_topological_vector_bundle_is_topological_fiber_bundle : IsTopologicalFiberBundle F (@TotalSpace.proj B E) :=
  fun x => ⟨(trivializationAt R F E x).toFiberBundleTrivialization, mem_base_set_trivialization_at R F E x⟩

include R F

theorem continuous_total_space_mk (x : B) : Continuous (@totalSpaceMk B E x) :=
  (TopologicalVectorBundle.total_space_mk_inducing R F E x).Continuous

variable (R B F)

@[continuity]
theorem continuous_proj : Continuous (@TotalSpace.proj B E) := by
  apply @IsTopologicalFiberBundle.continuous_proj B F
  apply @is_topological_vector_bundle_is_topological_fiber_bundle R

end TopologicalVectorBundle

/-! ### Constructing topological vector bundles -/


variable (R B F)

/-- Analogous construction of `topological_fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure TopologicalVectorBundleCore (ι : Type _) where
  BaseSet : ι → Set B
  is_open_base_set : ∀ i, IsOpen (base_set i)
  indexAt : B → ι
  mem_base_set_at : ∀ x, x ∈ base_set (index_at x)
  coordChange : ι → ι → B → F →L[R] F
  coord_change_self : ∀ i, ∀, ∀ x ∈ base_set i, ∀, ∀ v, coord_change i i x v = v
  coord_change_continuous : ∀ i j, ContinuousOn (coord_change i j) (base_set i ∩ base_set j)
  coord_change_comp :
    ∀ i j k,
      ∀,
        ∀ x ∈ base_set i ∩ base_set j ∩ base_set k,
          ∀, ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v

/-- The trivial topological vector bundle core, in which all the changes of coordinates are the
identity. -/
def trivialTopologicalVectorBundleCore (ι : Type _) [Inhabited ι] : TopologicalVectorBundleCore R B F ι where
  BaseSet := fun ι => Univ
  is_open_base_set := fun i => is_open_univ
  indexAt := default
  mem_base_set_at := fun x => mem_univ x
  coordChange := fun i j x => ContinuousLinearMap.id R F
  coord_change_self := fun i x hx v => rfl
  coord_change_comp := fun i j k x hx v => rfl
  coord_change_continuous := fun i j => continuous_on_const

instance (ι : Type _) [Inhabited ι] : Inhabited (TopologicalVectorBundleCore R B F ι) :=
  ⟨trivialTopologicalVectorBundleCore R B F ι⟩

namespace TopologicalVectorBundleCore

variable {R B F} {ι : Type _} (Z : TopologicalVectorBundleCore R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def toTopologicalFiberBundleCore : TopologicalFiberBundleCore ι B F :=
  { Z with coordChange := fun i j b => Z.coordChange i j b,
    coord_change_continuous := fun i j =>
      is_bounded_bilinear_map_apply.Continuous.comp_continuous_on
        ((Z.coord_change_continuous i j).prod_map continuous_on_id) }

instance toTopologicalFiberBundleCoreCoe :
    Coe (TopologicalVectorBundleCore R B F ι) (TopologicalFiberBundleCore ι B F) :=
  ⟨toTopologicalFiberBundleCore⟩

include Z

theorem coord_change_linear_comp (i j k : ι) :
    ∀,
      ∀ x ∈ Z.BaseSet i ∩ Z.BaseSet j ∩ Z.BaseSet k,
        ∀, (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x :=
  fun x hx => by
  ext v
  exact Z.coord_change_comp i j k x hx v

/-- The index set of a topological vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def Index :=
  ι

/-- The base space of a topological vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def Base :=
  B

/-- The fiber of a topological vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def Fiber (x : B) :=
  F

instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := by
  delta_instance topological_vector_bundle_core.fiber

instance addCommMonoidFiber : ∀ x : B, AddCommMonoidₓ (Z.Fiber x) := by
  delta_instance topological_vector_bundle_core.fiber

instance moduleFiber : ∀ x : B, Module R (Z.Fiber x) := by
  delta_instance topological_vector_bundle_core.fiber

instance addCommGroupFiber [AddCommGroupₓ F] : ∀ x : B, AddCommGroupₓ (Z.Fiber x) := by
  delta_instance topological_vector_bundle_core.fiber

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : TotalSpace Z.Fiber → B :=
  total_space.proj

/-- The total space of the topological vector bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def TotalSpace :=
  Bundle.TotalSpace Z.Fiber

/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : LocalHomeomorph (B × F) (B × F) :=
  TopologicalFiberBundleCore.trivChange (↑Z) i j

@[simp, mfld_simps]
theorem mem_triv_change_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).Source ↔ p.1 ∈ Z.BaseSet i ∩ Z.BaseSet j :=
  TopologicalFiberBundleCore.mem_triv_change_source (↑Z) i j p

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  TopologicalFiberBundleCore.toTopologicalSpace ι ↑Z

variable {ι} (b : B) (a : F)

@[simp, mfld_simps]
theorem coe_coord_change (i j : ι) : TopologicalFiberBundleCore.coordChange (↑Z) i j b = Z.coordChange i j b :=
  rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def localTriv (i : ι) : TopologicalVectorBundle.Trivialization R F Z.Fiber :=
  { TopologicalFiberBundleCore.localTriv (↑Z) i with
    linear' := fun x hx =>
      { map_add := fun v w => by
          simp' only [← ContinuousLinearMap.map_add] with mfld_simps,
        map_smul := fun r v => by
          simp' only [← ContinuousLinearMap.map_smul] with mfld_simps } }

variable (i j : ι)

@[simp, mfld_simps]
theorem mem_local_triv_source (p : Z.TotalSpace) : p ∈ (Z.localTriv i).Source ↔ p.1 ∈ Z.BaseSet i :=
  Iff.rfl

@[simp, mfld_simps]
theorem base_set_at : Z.BaseSet i = (Z.localTriv i).BaseSet :=
  rfl

@[simp, mfld_simps]
theorem local_triv_apply (p : Z.TotalSpace) : (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem mem_local_triv_target (p : B × F) : p ∈ (Z.localTriv i).Target ↔ p.1 ∈ (Z.localTriv i).BaseSet :=
  TopologicalFiberBundleCore.mem_local_triv_target Z i p

@[simp, mfld_simps]
theorem local_triv_symm_fst (p : B × F) :
    (Z.localTriv i).toLocalHomeomorph.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem local_triv_symm_apply {b : B} (hb : b ∈ Z.BaseSet i) (v : F) :
    (Z.localTriv i).symm b v = Z.coordChange i (Z.indexAt b) b v := by
  apply (Z.local_triv i).symmApply hb v

@[simp, mfld_simps]
theorem local_triv_coord_change_eq {b : B} (hb : b ∈ Z.BaseSet i ∩ Z.BaseSet j) (v : F) :
    (Z.localTriv i).coordChange (Z.localTriv j) b v = Z.coordChange i j b v := by
  rw [trivialization.coord_change_apply', local_triv_symm_fst, local_triv_apply, coord_change_comp]
  exacts[⟨⟨hb.1, Z.mem_base_set_at b⟩, hb.2⟩, hb]

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : TopologicalVectorBundle.Trivialization R F Z.Fiber :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
theorem local_triv_at_def : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

@[simp, mfld_simps]
theorem mem_source_at : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).Source := by
  rw [local_triv_at, mem_local_triv_source]
  exact Z.mem_base_set_at b

@[simp, mfld_simps]
theorem local_triv_at_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ :=
  TopologicalFiberBundleCore.local_triv_at_apply Z p

@[simp, mfld_simps]
theorem local_triv_at_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.local_triv_at_apply _

@[simp, mfld_simps]
theorem mem_local_triv_at_base_set : b ∈ (Z.localTrivAt b).BaseSet :=
  TopologicalFiberBundleCore.mem_local_triv_at_base_set Z b

instance : TopologicalVectorBundle R F Z.Fiber where
  total_space_mk_inducing := fun b =>
    ⟨by
      refine' le_antisymmₓ _ fun s h => _
      · rw [← continuous_iff_le_induced]
        exact TopologicalFiberBundleCore.continuous_total_space_mk (↑Z) b
        
      · refine'
          is_open_induced_iff.mpr
            ⟨(Z.local_triv_at b).Source ∩ Z.local_triv_at b ⁻¹' (Z.local_triv_at b).BaseSet ×ˢ s,
              (continuous_on_open_iff (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
                ((Z.local_triv_at b).open_base_set.Prod h),
              _⟩
        rw [preimage_inter, ← preimage_comp, Function.comp]
        simp only [← total_space_mk]
        refine' ext_iff.mpr fun a => ⟨fun ha => _, fun ha => ⟨Z.mem_base_set_at b, _⟩⟩
        · simp only [← mem_prod, ← mem_preimage, ← mem_inter_eq, ← local_triv_at_apply_mk] at ha
          exact ha.2.2
          
        · simp only [← mem_prod, ← mem_preimage, ← mem_inter_eq, ← local_triv_at_apply_mk]
          exact ⟨Z.mem_base_set_at b, ha⟩
          
        ⟩
  TrivializationAtlas := Set.Range Z.localTriv
  trivializationAt := Z.localTrivAt
  mem_base_set_trivialization_at := Z.mem_base_set_at
  trivialization_mem_atlas := fun b => ⟨Z.indexAt b, rfl⟩
  continuous_on_coord_change := by
    rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
    refine' (Z.coord_change_continuous i i').congr fun b hb => _
    ext v
    simp_rw [ContinuousLinearEquiv.coe_coe, Z.local_triv_coord_change_eq i i' hb]

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity]
theorem continuous_proj : Continuous Z.proj :=
  TopologicalFiberBundleCore.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
theorem is_open_map_proj : IsOpenMap Z.proj :=
  TopologicalFiberBundleCore.is_open_map_proj Z

end TopologicalVectorBundleCore

end

/-! ### Topological vector prebundle -/


section

variable [NondiscreteNormedField R] [∀ x, AddCommMonoidₓ (E x)] [∀ x, Module R (E x)] [NormedGroup F] [NormedSpace R F]
  [TopologicalSpace B]

open TopologicalSpace

open TopologicalVectorBundle

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (e e' «expr ∈ » pretrivialization_atlas)
/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bundle structure for
which the local equivalences are also local homeomorphisms and hence vector bundle trivializations.
The topology on the fibers is induced from the one on the total space.

The field `exists_coord_change` is stated as an existential statement (instead of 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivialization_atlas`).
This makes it inconvenient to explicitly define a `coord_change` function when constructing a
`topological_vector_prebundle`. -/
@[nolint has_inhabited_instance]
structure TopologicalVectorPrebundle where
  PretrivializationAtlas : Set (Pretrivialization R F E)
  pretrivializationAt : B → Pretrivialization R F E
  mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).BaseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas
  exists_coord_change :
    ∀ (e e') (_ : e ∈ pretrivialization_atlas) (_ : e' ∈ pretrivialization_atlas),
      ∃ f : B → F →L[R] F,
        ContinuousOn f (e.BaseSet ∩ e'.BaseSet) ∧
          ∀ (b : B) (hb : b ∈ e.BaseSet ∩ e'.BaseSet) (v : F), f b v = (e' (totalSpaceMk b (e.symm b v))).2

namespace TopologicalVectorPrebundle

variable {R E F}

/-- A randomly chosen coordinate change on a `topological_vector_prebundle`, given by
  the field `exists_coord_change`. -/
def coordChange (a : TopologicalVectorPrebundle R F E) {e e' : Pretrivialization R F E}
    (he : e ∈ a.PretrivializationAtlas) (he' : e' ∈ a.PretrivializationAtlas) (b : B) : F →L[R] F :=
  Classical.some (a.exists_coord_change e he e' he') b

theorem continuous_on_coord_change (a : TopologicalVectorPrebundle R F E) {e e' : Pretrivialization R F E}
    (he : e ∈ a.PretrivializationAtlas) (he' : e' ∈ a.PretrivializationAtlas) :
    ContinuousOn (a.coordChange he he') (e.BaseSet ∩ e'.BaseSet) :=
  (Classical.some_spec (a.exists_coord_change e he e' he')).1

theorem coord_change_apply (a : TopologicalVectorPrebundle R F E) {e e' : Pretrivialization R F E}
    (he : e ∈ a.PretrivializationAtlas) (he' : e' ∈ a.PretrivializationAtlas) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet)
    (v : F) : a.coordChange he he' b v = (e' (totalSpaceMk b (e.symm b v))).2 :=
  (Classical.some_spec (a.exists_coord_change e he e' he')).2 b hb v

theorem mk_coord_change (a : TopologicalVectorPrebundle R F E) {e e' : Pretrivialization R F E}
    (he : e ∈ a.PretrivializationAtlas) (he' : e' ∈ a.PretrivializationAtlas) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet)
    (v : F) : (b, a.coordChange he he' b v) = e' (totalSpaceMk b (e.symm b v)) := by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
    
  · exact a.coord_change_apply he he' hb v
    

/-- Natural identification of `topological_vector_prebundle` as a `topological_fiber_prebundle`. -/
def toTopologicalFiberPrebundle (a : TopologicalVectorPrebundle R F E) :
    TopologicalFiberPrebundle F (@TotalSpace.proj B E) :=
  { a with PretrivializationAtlas := pretrivialization.to_fiber_bundle_pretrivialization '' a.PretrivializationAtlas,
    pretrivializationAt := fun x => (a.pretrivializationAt x).toFiberBundlePretrivialization,
    pretrivialization_mem_atlas := fun x => ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
    continuous_triv_change := by
      rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
      have :=
        is_bounded_bilinear_map_apply.continuous.comp_continuous_on
          ((a.continuous_on_coord_change he' he).prod_map continuous_on_id)
      have H :
        e'.to_fiber_bundle_pretrivialization.to_local_equiv.target ∩
            e'.to_fiber_bundle_pretrivialization.to_local_equiv.symm ⁻¹'
              e.to_fiber_bundle_pretrivialization.to_local_equiv.source =
          (e'.base_set ∩ e.base_set) ×ˢ (univ : Set F) :=
        by
        rw [e'.target_eq, e.source_eq]
        ext ⟨b, f⟩
        simp'(config := { contextual := true }) only [-total_space.proj, ← And.congr_right_iff, ← e'.proj_symm_apply', ←
          iff_selfₓ, ← implies_true_iff] with mfld_simps
      rw [H]
      refine' (continuous_on_fst.prod this).congr _
      rintro ⟨b, f⟩ ⟨hb, -⟩
      dsimp' only [← Function.comp, ← Prod.map]
      rw [a.mk_coord_change _ _ hb, e'.mk_symm hb.1]
      rfl }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def totalSpaceTopology (a : TopologicalVectorPrebundle R F E) : TopologicalSpace (TotalSpace E) :=
  a.toTopologicalFiberPrebundle.totalSpaceTopology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivializationOfMemPretrivializationAtlas (a : TopologicalVectorPrebundle R F E)
    {e : TopologicalVectorBundle.Pretrivialization R F E} (he : e ∈ a.PretrivializationAtlas) :
    @TopologicalVectorBundle.Trivialization R _ F E _ _ _ _ _ _ _ a.totalSpaceTopology := by
  let this := a.total_space_topology
  exact
    { a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas ⟨e, he, rfl⟩ with
      linear' := fun b => e.linear }

variable (a : TopologicalVectorPrebundle R F E)

theorem mem_trivialization_at_source (b : B) (x : E b) : totalSpaceMk b x ∈ (a.pretrivializationAt b).Source := by
  simp only [← (a.pretrivialization_at b).source_eq, ← mem_preimage, ← total_space.proj]
  exact a.mem_base_pretrivialization_at b

@[simp]
theorem total_space_mk_preimage_source (b : B) : totalSpaceMk b ⁻¹' (a.pretrivializationAt b).Source = univ := by
  apply eq_univ_of_univ_subset
  rw [(a.pretrivialization_at b).source_eq, ← preimage_comp, Function.comp]
  simp only [← total_space.proj]
  rw [preimage_const_of_mem _]
  exact a.mem_base_pretrivialization_at b

/-- Topology on the fibers `E b` induced by the map `E b → E.total_space`. -/
def fiberTopology (b : B) : TopologicalSpace (E b) :=
  TopologicalSpace.induced (totalSpaceMk b) a.totalSpaceTopology

@[continuity]
theorem inducing_total_space_mk (b : B) : @Inducing _ _ (a.fiberTopology b) a.totalSpaceTopology (totalSpaceMk b) := by
  let this := a.total_space_topology
  let this := a.fiber_topology b
  exact ⟨rfl⟩

@[continuity]
theorem continuous_total_space_mk (b : B) : @Continuous _ _ (a.fiberTopology b) a.totalSpaceTopology (totalSpaceMk b) :=
  by
  let this := a.total_space_topology
  let this := a.fiber_topology b
  exact (a.inducing_total_space_mk b).Continuous

/-- Make a `topological_vector_bundle` from a `topological_vector_prebundle`.  Concretely this means
that, given a `topological_vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`topological_vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def toTopologicalVectorBundle : @TopologicalVectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology a.fiberTopology where
  total_space_mk_inducing := a.inducing_total_space_mk
  TrivializationAtlas :=
    { e | ∃ (e₀ : _)(he₀ : e₀ ∈ a.PretrivializationAtlas), e = a.trivializationOfMemPretrivializationAtlas he₀ }
  trivializationAt := fun x => a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x)
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at
  trivialization_mem_atlas := fun x => ⟨_, a.pretrivialization_mem_atlas x, rfl⟩
  continuous_on_coord_change := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    refine' (a.continuous_on_coord_change he he').congr _
    intro b hb
    ext v
    rw [a.coord_change_apply he he' hb v, ContinuousLinearEquiv.coe_coe, trivialization.coord_change_apply]
    exacts[rfl, hb]

end TopologicalVectorPrebundle

end

