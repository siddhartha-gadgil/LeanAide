/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathbin.Topology.Sheaves.Forget
import Mathbin.CategoryTheory.Limits.Shapes.Types
import Mathbin.Topology.Sheaves.Sheaf
import Mathbin.CategoryTheory.Types

/-!
# The sheaf condition in terms of unique gluings

We provide an alternative formulation of the sheaf condition in terms of unique gluings.

We work with sheaves valued in a concrete category `C` admitting all limits, whose forgetful
functor `C ⥤ Type` preserves limits and reflects isomorphisms. The usual categories of algebraic
structures, such as `Mon`, `AddCommGroup`, `Ring`, `CommRing` etc. are all examples of this kind of
category.

A presheaf `F : presheaf C X` satisfies the sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
`s : F.obj (op (supr U))`.

Here, the family `sf` is called compatible, if for all `i j : ι`, the restrictions of `sf i`
and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (supr U))` is a gluing for the
family `sf`, if `s` restricts to `sf i` on `U i` for all `i : ι`

We show that the sheaf condition in terms of unique gluings is equivalent to the definition
in terms of equalizers. Our approach is as follows: First, we show them to be equivalent for
`Type`-valued presheaves. Then we use that composing a presheaf with a limit-preserving and
isomorphism-reflecting functor leaves the sheaf condition invariant, as shown in
`topology/sheaves/forget.lean`.

-/


noncomputable section

open Top

open Top.Presheaf

open Top.Presheaf.SheafConditionEqualizerProducts

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open TopologicalSpace.Opens

open Opposite

universe u v

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]

namespace Top

namespace Presheaf

section

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable {X : Top.{v}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

/-- A family of sections `sf` is compatible, if the restrictions of `sf i` and `sf j` to `U i ⊓ U j`
agree, for all `i` and `j`
-/
def IsCompatible (sf : ∀ i : ι, F.obj (op (U i))) : Prop :=
  ∀ i j : ι, F.map (inf_le_left (U i) (U j)).op (sf i) = F.map (inf_le_right (U i) (U j)).op (sf j)

/-- A section `s` is a gluing for a family of sections `sf` if it restricts to `sf i` on `U i`,
for all `i`
-/
def IsGluing (sf : ∀ i : ι, F.obj (op (U i))) (s : F.obj (op (supr U))) : Prop :=
  ∀ i : ι, F.map (Opens.leSupr U i).op s = sf i

/-- The sheaf condition in terms of unique gluings. A presheaf `F : presheaf C X` satisfies this sheaf
condition if and only if, for every compatible family of sections `sf : Π i : ι, F.obj (op (U i))`,
there exists a unique gluing `s : F.obj (op (supr U))`.

We prove this to be equivalent to the usual one below in
`is_sheaf_iff_is_sheaf_unique_gluing`
-/
def IsSheafUniqueGluing : Prop :=
  ∀ ⦃ι : Type v⦄ (U : ι → Opens X) (sf : ∀ i : ι, F.obj (op (U i))),
    IsCompatible F U sf → ∃! s : F.obj (op (supr U)), IsGluing F U sf s

end

section TypeValued

variable {X : Top.{v}} (F : Presheaf (Type v) X) {ι : Type v} (U : ι → Opens X)

/-- For presheaves of types, terms of `pi_opens F U` are just families of sections.
-/
def piOpensIsoSectionsFamily : piOpens F U ≅ ∀ i : ι, F.obj (op (U i)) :=
  Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor fun i : ι => F.obj (op (U i))))
    (Types.productLimitCone fun i : ι => F.obj (op (U i))).IsLimit

/-- Under the isomorphism `pi_opens_iso_sections_family`, compatibility of sections is the same
as being equalized by the arrows `left_res` and `right_res` of the equalizer diagram.
-/
theorem compatible_iff_left_res_eq_right_res (sf : piOpens F U) :
    IsCompatible F U ((piOpensIsoSectionsFamily F U).Hom sf) ↔ leftRes F U sf = rightRes F U sf := by
  constructor <;> intro h
  · ext ⟨i, j⟩
    rw [left_res, types.limit.lift_π_apply', fan.mk_π_app, right_res, types.limit.lift_π_apply', fan.mk_π_app]
    exact h i j
    
  · intro i j
    convert congr_arg (limits.pi.π (fun p : ι × ι => F.obj (op (U p.1⊓U p.2))) (i, j)) h
    · rw [left_res, types.pi_lift_π_apply]
      rfl
      
    · rw [right_res, types.pi_lift_π_apply]
      rfl
      
    

/-- Under the isomorphism `pi_opens_iso_sections_family`, being a gluing of a family of
sections `sf` is the same as lying in the preimage of `res` (the leftmost arrow of the
equalizer diagram).
-/
@[simp]
theorem is_gluing_iff_eq_res (sf : piOpens F U) (s : F.obj (op (supr U))) :
    IsGluing F U ((piOpensIsoSectionsFamily F U).Hom sf) s ↔ res F U s = sf := by
  constructor <;> intro h
  · ext ⟨i⟩
    rw [res, types.limit.lift_π_apply', fan.mk_π_app]
    exact h i
    
  · intro i
    convert congr_arg (limits.pi.π (fun i : ι => F.obj (op (U i))) i) h
    rw [res, types.pi_lift_π_apply]
    rfl
    

/-- The "equalizer" sheaf condition can be obtained from the sheaf condition
in terms of unique gluings.
-/
theorem is_sheaf_of_is_sheaf_unique_gluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf := by
  intro ι U
  refine' ⟨fork.is_limit.mk' _ _⟩
  intro s
  have h_compatible : ∀ x : s.X, F.is_compatible U ((F.pi_opens_iso_sections_family U).Hom (s.ι x)) := by
    intro x
    rw [compatible_iff_left_res_eq_right_res]
    convert congr_fun s.condition x
  choose m m_spec m_uniq using fun x : s.X => Fsh U ((pi_opens_iso_sections_family F U).Hom (s.ι x)) (h_compatible x)
  refine' ⟨m, _, _⟩
  · ext ⟨i⟩ x
    simp [← res]
    exact m_spec x i
    
  · intro l hl
    ext x
    apply m_uniq
    rw [is_gluing_iff_eq_res]
    exact congr_fun hl x
    

/-- The sheaf condition in terms of unique gluings can be obtained from the usual
"equalizer" sheaf condition.
-/
theorem is_sheaf_unique_gluing_of_is_sheaf_types (Fsh : F.IsSheaf) : F.IsSheafUniqueGluing := by
  intro ι U sf hsf
  let sf' := (pi_opens_iso_sections_family F U).inv sf
  have hsf' : left_res F U sf' = right_res F U sf' := by
    rwa [← compatible_iff_left_res_eq_right_res F U sf', inv_hom_id_apply]
  choose s s_spec s_uniq using types.unique_of_type_equalizer _ _ (Fsh U).some sf' hsf'
  use s
  dsimp'
  constructor
  · convert (is_gluing_iff_eq_res F U sf' _).mpr s_spec
    rw [inv_hom_id_apply]
    
  · intro y hy
    apply s_uniq
    rw [← is_gluing_iff_eq_res F U]
    convert hy
    rw [inv_hom_id_apply]
    

/-- For type-valued presheaves, the sheaf condition in terms of unique gluings is equivalent to the
usual sheaf condition in terms of equalizer diagrams.
-/
theorem is_sheaf_iff_is_sheaf_unique_gluing_types : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
  Iff.intro (is_sheaf_unique_gluing_of_is_sheaf_types F) (is_sheaf_of_is_sheaf_unique_gluing_types F)

end TypeValued

section

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable [HasLimits C] [ReflectsIsomorphisms (forget C)] [PreservesLimits (forget C)]

variable {X : Top.{v}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

/-- For presheaves valued in a concrete category, whose forgetful functor reflects isomorphisms and
preserves limits, the sheaf condition in terms of unique gluings is equivalent to the usual one
in terms of equalizer diagrams.
-/
theorem is_sheaf_iff_is_sheaf_unique_gluing : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
  Iff.trans (is_sheaf_iff_is_sheaf_comp (forget C) F) (is_sheaf_iff_is_sheaf_unique_gluing_types (F ⋙ forget C))

end

end Presheaf

namespace Sheaf

open Presheaf

open CategoryTheory

section

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable [HasLimits C] [ReflectsIsomorphisms (ConcreteCategory.forget C)]

variable [PreservesLimits (ConcreteCategory.forget C)]

variable {X : Top.{v}} (F : Sheaf C X) {ι : Type v} (U : ι → Opens X)

/-- A more convenient way of obtaining a unique gluing of sections for a sheaf.
-/
theorem exists_unique_gluing (sf : ∀ i : ι, F.1.obj (op (U i))) (h : IsCompatible F.1 U sf) :
    ∃! s : F.1.obj (op (supr U)), IsGluing F.1 U sf s :=
  (is_sheaf_iff_is_sheaf_unique_gluing F.1).mp F.property U sf h

/-- In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
theorem exists_unique_gluing' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ supr U)
    (sf : ∀ i : ι, F.1.obj (op (U i))) (h : IsCompatible F.1 U sf) :
    ∃! s : F.1.obj (op V), ∀ i : ι, F.1.map (iUV i).op s = sf i := by
  have V_eq_supr_U : V = supr U := le_antisymmₓ hcover (supr_le fun i => (iUV i).le)
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.exists_unique_gluing U sf h
  refine' ⟨F.1.map (eq_to_hom V_eq_supr_U).op gl, _, _⟩
  · intro i
    rw [← comp_apply, ← F.1.map_comp]
    exact gl_spec i
    
  · intro gl' gl'_spec
    convert congr_arg _ (gl_uniq (F.1.map (eq_to_hom V_eq_supr_U.symm).op gl') fun i => _) <;>
      rw [← comp_apply, ← F.1.map_comp]
    · rw [eq_to_hom_op, eq_to_hom_op, eq_to_hom_trans, eq_to_hom_refl, F.1.map_id, id_apply]
      
    · convert gl'_spec i
      
    

@[ext]
theorem eq_of_locally_eq (s t : F.1.obj (op (supr U)))
    (h : ∀ i, F.1.map (Opens.leSupr U i).op s = F.1.map (Opens.leSupr U i).op t) : s = t := by
  let sf : ∀ i : ι, F.1.obj (op (U i)) := fun i => F.1.map (opens.le_supr U i).op s
  have sf_compatible : is_compatible _ U sf := by
    intro i j
    simp_rw [← comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨gl, -, gl_uniq⟩ := F.exists_unique_gluing U sf sf_compatible
  trans gl
  · apply gl_uniq
    intro i
    rfl
    
  · symm
    apply gl_uniq
    intro i
    rw [← h]
    

/-- In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
theorem eq_of_locally_eq' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ supr U) (s t : F.1.obj (op V))
    (h : ∀ i, F.1.map (iUV i).op s = F.1.map (iUV i).op t) : s = t := by
  have V_eq_supr_U : V = supr U := le_antisymmₓ hcover (supr_le fun i => (iUV i).le)
  suffices F.1.map (eq_to_hom V_eq_supr_U.symm).op s = F.1.map (eq_to_hom V_eq_supr_U.symm).op t by
    convert congr_arg (F.1.map (eq_to_hom V_eq_supr_U).op) this <;>
      rw [← comp_apply, ← F.1.map_comp, eq_to_hom_op, eq_to_hom_op, eq_to_hom_trans, eq_to_hom_refl, F.1.map_id,
        id_apply]
  apply eq_of_locally_eq
  intro i
  rw [← comp_apply, ← comp_apply, ← F.1.map_comp]
  convert h i

end

end Sheaf

end Top

