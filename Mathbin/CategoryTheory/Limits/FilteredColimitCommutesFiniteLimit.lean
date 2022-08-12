/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.ColimitLimit
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathbin.CategoryTheory.Limits.Preserves.Filtered
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# Filtered colimits commute with finite limits.

We show that for a functor `F : J × K ⥤ Type v`, when `J` is finite and `K` is filtered,
the universal morphism `colimit_limit_to_limit_colimit F` comparing the
colimit (over `K`) of the limits (over `J`) with the limit of the colimits is an isomorphism.

(In fact, to prove that it is injective only requires that `J` has finitely many objects.)

## References
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/


universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits.Types

open CategoryTheory.Limits.Types.FilteredColimit

namespace CategoryTheory.Limits

variable {J K : Type v} [SmallCategory J] [SmallCategory K]

variable (F : J × K ⥤ Type v)

open CategoryTheory.prod

variable [IsFiltered K]

section

/-!
Injectivity doesn't need that we have finitely many morphisms in `J`,
only that there are finitely many objects.
-/


variable [Fintype J]

/-- This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
-/
theorem colimit_limit_to_limit_colimit_injective : Function.Injective (colimitLimitToLimitColimit F) := by
  classical
  -- Suppose we have two terms `x y` in the colimit (over `K`) of the limits (over `J`),
  -- and that these have the same image under `colimit_limit_to_limit_colimit F`.
  intro x y h
  -- These elements of the colimit have representatives somewhere:
  obtain ⟨kx, x, rfl⟩ := jointly_surjective'.{v, v} x
  obtain ⟨ky, y, rfl⟩ := jointly_surjective'.{v, v} y
  dsimp'  at x y
  -- Since the images of `x` and `y` are equal in a limit, they are equal componentwise
  -- (indexed by `j : J`),
  replace h := fun j => congr_arg (limit.π (curry.obj F ⋙ colim) j) h
  -- and they are equations in a filtered colimit,
  -- so for each `j` we have some place `k j` to the right of both `kx` and `ky`
  simp [← colimit_eq_iff.{v, v}] at h
  let k := fun j => (h j).some
  let f : ∀ j, kx ⟶ k j := fun j => (h j).some_spec.some
  let g : ∀ j, ky ⟶ k j := fun j => (h j).some_spec.some_spec.some
  -- where the images of the components of the representatives become equal:
  have w :
    ∀ j,
      F.map ((𝟙 j, f j) : (j, kx) ⟶ (j, k j)) (limit.π ((curry.obj (swap K J ⋙ F)).obj kx) j x) =
        F.map ((𝟙 j, g j) : (j, ky) ⟶ (j, k j)) (limit.π ((curry.obj (swap K J ⋙ F)).obj ky) j y) :=
    fun j => (h j).some_spec.some_spec.some_spec
  -- We now use that `K` is filtered, picking some point to the right of all these
  -- morphisms `f j` and `g j`.
  let O : Finset K := Finset.univ.Image k ∪ {kx, ky}
  have kxO : kx ∈ O :=
    finset.mem_union.mpr
      (Or.inr
        (by
          simp ))
  have kyO : ky ∈ O :=
    finset.mem_union.mpr
      (Or.inr
        (by
          simp ))
  have kjO : ∀ j, k j ∈ O := fun j =>
    finset.mem_union.mpr
      (Or.inl
        (by
          simp ))
  let H : Finset (Σ'(X Y : K)(mX : X ∈ O)(mY : Y ∈ O), X ⟶ Y) :=
    (Finset.univ.Image fun j : J =>
        ⟨kx, k j, kxO,
          finset.mem_union.mpr
            (Or.inl
              (by
                simp )),
          f j⟩) ∪
      Finset.univ.Image fun j : J =>
        ⟨ky, k j, kyO,
          finset.mem_union.mpr
            (Or.inl
              (by
                simp )),
          g j⟩
  obtain ⟨S, T, W⟩ := is_filtered.sup_exists O H
  have fH : ∀ j, (⟨kx, k j, kxO, kjO j, f j⟩ : Σ'(X Y : K)(mX : X ∈ O)(mY : Y ∈ O), X ⟶ Y) ∈ H := fun j =>
    finset.mem_union.mpr
      (Or.inl
        (by
          simp only [← true_andₓ, ← Finset.mem_univ, ← eq_self_iff_true, ← exists_prop_of_true, ← Finset.mem_image, ←
            heq_iff_eq]
          refine' ⟨j, rfl, _⟩
          simp only [← heq_iff_eq]
          exact ⟨rfl, rfl, rfl⟩))
  have gH : ∀ j, (⟨ky, k j, kyO, kjO j, g j⟩ : Σ'(X Y : K)(mX : X ∈ O)(mY : Y ∈ O), X ⟶ Y) ∈ H := fun j =>
    finset.mem_union.mpr
      (Or.inr
        (by
          simp only [← true_andₓ, ← Finset.mem_univ, ← eq_self_iff_true, ← exists_prop_of_true, ← Finset.mem_image, ←
            heq_iff_eq]
          refine' ⟨j, rfl, _⟩
          simp only [← heq_iff_eq]
          exact ⟨rfl, rfl, rfl⟩))
  -- Our goal is now an equation between equivalence classes of representatives of a colimit,
  -- and so it suffices to show those representative become equal somewhere, in particular at `S`.
  apply colimit_sound'.{v, v} (T kxO) (T kyO)
  -- We can check if two elements of a limit (in `Type`) are equal by comparing them componentwise.
  ext
  -- Now it's just a calculation using `W` and `w`.
  simp only [← functor.comp_map, ← limit.map_π_apply, ← curry.obj_map_app, ← swap_map]
  rw [← W _ _ (fH j)]
  rw [← W _ _ (gH j)]
  simp [← w]

end

variable [FinCategory J]

/-- This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
although with different names.
-/
theorem colimit_limit_to_limit_colimit_surjective : Function.Surjective (colimitLimitToLimitColimit F) := by
  classical
  -- We begin with some element `x` in the limit (over J) over the colimits (over K),
  intro x
  -- This consists of some coherent family of elements in the various colimits,
  -- and so our first task is to pick representatives of these elements.
  have z := fun j => jointly_surjective'.{v, v} (limit.π (curry.obj F ⋙ limits.colim) j x)
  -- `k : J ⟶ K` records where the representative of the element in the `j`-th element of `x` lives
  let k : J → K := fun j => (z j).some
  -- `y j : F.obj (j, k j)` is the representative
  let y : ∀ j, F.obj (j, k j) := fun j => (z j).some_spec.some
  -- and we record that these representatives, when mapped back into the relevant colimits,
  -- are actually the components of `x`.
  have e : ∀ j, colimit.ι ((curry.obj F).obj j) (k j) (y j) = limit.π (curry.obj F ⋙ limits.colim) j x := fun j =>
    (z j).some_spec.some_spec
  clear_value k y
  -- A little tidying up of things we no longer need.
  clear z
  -- As a first step, we use that `K` is filtered to pick some point `k' : K` above all the `k j`
  let k' : K := is_filtered.sup (finset.univ.image k) ∅
  -- and name the morphisms as `g j : k j ⟶ k'`.
  have g : ∀ j, k j ⟶ k' := fun j =>
    is_filtered.to_sup (finset.univ.image k) ∅
      (by
        simp )
  clear_value k'
  -- Recalling that the components of `x`, which are indexed by `j : J`, are "coherent",
  -- in other words preserved by morphisms in the `J` direction,
  -- we see that for any morphism `f : j ⟶ j'` in `J`,
  -- the images of `y j` and `y j'`, when mapped to `F.obj (j', k')` respectively by
  -- `(f, g j)` and `(𝟙 j', g j')`, both represent the same element in the colimit.
  have w :
    ∀ {j j' : J} (f : j ⟶ j'),
      colimit.ι ((curry.obj F).obj j') k' (F.map ((𝟙 j', g j') : (j', k j') ⟶ (j', k')) (y j')) =
        colimit.ι ((curry.obj F).obj j') k' (F.map ((f, g j) : (j, k j) ⟶ (j', k')) (y j)) :=
    by
    intro j j' f
    have t : (f, g j) = (((f, 𝟙 (k j)) : (j, k j) ⟶ (j', k j)) ≫ (𝟙 j', g j) : (j, k j) ⟶ (j', k')) := by
      simp only [← id_comp, ← comp_id, ← prod_comp]
    erw [colimit.w_apply', t, functor_to_types.map_comp_apply, colimit.w_apply', e, ← limit.w_apply' f, ← e]
    simp
  -- Because `K` is filtered, we can restate this as saying that
  -- for each such `f`, there is some place to the right of `k'`
  -- where these images of `y j` and `y j'` become equal.
  simp_rw [colimit_eq_iff.{v, v}] at w
  -- We take a moment to restate `w` more conveniently.
  let kf : ∀ {j j'} (f : j ⟶ j'), K := fun _ _ f => (w f).some
  let gf : ∀ {j j'} (f : j ⟶ j'), k' ⟶ kf f := fun _ _ f => (w f).some_spec.some
  let hf : ∀ {j j'} (f : j ⟶ j'), k' ⟶ kf f := fun _ _ f => (w f).some_spec.some_spec.some
  have wf :
    ∀ {j j'} (f : j ⟶ j'),
      F.map ((𝟙 j', g j' ≫ gf f) : (j', k j') ⟶ (j', kf f)) (y j') =
        F.map ((f, g j ≫ hf f) : (j, k j) ⟶ (j', kf f)) (y j) :=
    fun j j' f => by
    have q : ((curry.obj F).obj j').map (gf f) (F.map _ (y j')) = ((curry.obj F).obj j').map (hf f) (F.map _ (y j)) :=
      (w f).some_spec.some_spec.some_spec
    dsimp'  at q
    simp_rw [← functor_to_types.map_comp_apply] at q
    convert q <;> simp only [← comp_id]
  clear_value kf gf hf
  -- and clean up some things that are no longer needed.
  clear w
  -- We're now ready to use the fact that `K` is filtered a second time,
  -- picking some place to the right of all of
  -- the morphisms `gf f : k' ⟶ kh f` and `hf f : k' ⟶ kf f`.
  -- At this point we're relying on there being only finitely morphisms in `J`.
  let O := (finset.univ.bUnion fun j => finset.univ.bUnion fun j' => finset.univ.image (@kf j j')) ∪ {k'}
  have kfO : ∀ {j j'} (f : j ⟶ j'), kf f ∈ O := fun j j' f =>
    finset.mem_union.mpr
      (Or.inl
        (by
          rw [Finset.mem_bUnion]
          refine' ⟨j, Finset.mem_univ j, _⟩
          rw [Finset.mem_bUnion]
          refine' ⟨j', Finset.mem_univ j', _⟩
          rw [Finset.mem_image]
          refine' ⟨f, Finset.mem_univ _, _⟩
          rfl))
  have k'O : k' ∈ O := finset.mem_union.mpr (Or.inr (finset.mem_singleton.mpr rfl))
  let H : Finset (Σ'(X Y : K)(mX : X ∈ O)(mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bUnion fun j : J =>
      finset.univ.bUnion fun j' : J =>
        finset.univ.bUnion fun f : j ⟶ j' => {⟨k', kf f, k'O, kfO f, gf f⟩, ⟨k', kf f, k'O, kfO f, hf f⟩}
  obtain ⟨k'', i', s'⟩ := is_filtered.sup_exists O H
  -- We then restate this slightly more conveniently, as a family of morphism `i f : kf f ⟶ k''`,
  -- satisfying `gf f ≫ i f = hf f' ≫ i f'`.
  let i : ∀ {j j'} (f : j ⟶ j'), kf f ⟶ k'' := fun j j' f => i' (kfO f)
  have s : ∀ {j₁ j₂ j₃ j₄} (f : j₁ ⟶ j₂) (f' : j₃ ⟶ j₄), gf f ≫ i f = hf f' ≫ i f' := by
    intros
    rw [s', s']
    swap
    exact k'O
    swap
    · rw [Finset.mem_bUnion]
      refine' ⟨j₁, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨j₂, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨f, Finset.mem_univ _, _⟩
      simp only [← true_orₓ, ← eq_self_iff_true, ← and_selfₓ, ← Finset.mem_insert, ← heq_iff_eq]
      
    · rw [Finset.mem_bUnion]
      refine' ⟨j₃, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨j₄, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨f', Finset.mem_univ _, _⟩
      simp only [← eq_self_iff_true, ← or_trueₓ, ← and_selfₓ, ← Finset.mem_insert, ← Finset.mem_singleton, ← heq_iff_eq]
      
  clear_value i
  clear s' i' H kfO k'O O
  -- We're finally ready to construct the pre-image, and verify it really maps to `x`.
  fconstructor
  · -- We construct the pre-image (which, recall is meant to be a point
    -- in the colimit (over `K`) of the limits (over `J`)) via a representative at `k''`.
    apply colimit.ι (curry.obj (swap K J ⋙ F) ⋙ limits.lim) k'' _
    dsimp'
    -- This representative is meant to be an element of a limit,
    -- so we need to construct a family of elements in `F.obj (j, k'')` for varying `j`,
    -- then show that are coherent with respect to morphisms in the `j` direction.
    apply Limit.mk.{v, v}
    swap
    · -- We construct the elements as the images of the `y j`.
      exact fun j => F.map (⟨𝟙 j, g j ≫ gf (𝟙 j) ≫ i (𝟙 j)⟩ : (j, k j) ⟶ (j, k'')) (y j)
      
    · -- After which it's just a calculation, using `s` and `wf`, to see they are coherent.
      dsimp'
      intro j j' f
      simp only [functor_to_types.map_comp_apply, ← prod_comp, ← id_comp, ← comp_id]
      calc
        F.map ((f, g j ≫ gf (𝟙 j) ≫ i (𝟙 j)) : (j, k j) ⟶ (j', k'')) (y j) =
            F.map ((f, g j ≫ hf f ≫ i f) : (j, k j) ⟶ (j', k'')) (y j) :=
          by
          rw
            [s (𝟙 j)
              f]_ =
            F.map ((𝟙 j', i f) : (j', kf f) ⟶ (j', k'')) (F.map ((f, g j ≫ hf f) : (j, k j) ⟶ (j', kf f)) (y j)) :=
          by
          rw [← functor_to_types.map_comp_apply, prod_comp, comp_id,
            assoc]_ =
            F.map ((𝟙 j', i f) : (j', kf f) ⟶ (j', k''))
              (F.map ((𝟙 j', g j' ≫ gf f) : (j', k j') ⟶ (j', kf f)) (y j')) :=
          by
          rw [← wf f]_ = F.map ((𝟙 j', g j' ≫ gf f ≫ i f) : (j', k j') ⟶ (j', k'')) (y j') := by
          rw [← functor_to_types.map_comp_apply, prod_comp, id_comp,
            assoc]_ = F.map ((𝟙 j', g j' ≫ gf (𝟙 j') ≫ i (𝟙 j')) : (j', k j') ⟶ (j', k'')) (y j') :=
          by
          rw [s f (𝟙 j'), ← s (𝟙 j') (𝟙 j')]
      
    
  -- Finally we check that this maps to `x`.
  · -- We can do this componentwise:
    apply limit_ext'
    intro j
    -- and as each component is an equation in a colimit, we can verify it by
    -- pointing out the morphism which carries one representative to the other:
    simp only [e, ← colimit_eq_iff.{v, v}, ← curry.obj_obj_map, ← limit.π_mk', ← bifunctor.map_id_comp, ← id.def, ←
      types_comp_apply, ← limits.ι_colimit_limit_to_limit_colimit_π_apply]
    refine' ⟨k'', 𝟙 k'', g j ≫ gf (𝟙 j) ≫ i (𝟙 j), _⟩
    simp only [← bifunctor.map_id_comp, ← types_comp_apply, ← bifunctor.map_id, ← types_id_apply]
    

instance colimit_limit_to_limit_colimit_is_iso : IsIso (colimitLimitToLimitColimit F) :=
  (is_iso_iff_bijective _).mpr ⟨colimit_limit_to_limit_colimit_injective F, colimit_limit_to_limit_colimit_surjective F⟩

instance colimit_limit_to_limit_colimit_cone_iso (F : J ⥤ K ⥤ Type v) : IsIso (colimitLimitToLimitColimitCone F) := by
  have : is_iso (colimit_limit_to_limit_colimit_cone F).Hom := by
    dsimp' only [← colimit_limit_to_limit_colimit_cone]
    infer_instance
  apply cones.cone_iso_of_hom_iso

noncomputable instance filteredColimPreservesFiniteLimitsOfTypes : PreservesFiniteLimits (colim : (K ⥤ Type v) ⥤ _) :=
  by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{v}
  intro J _ _
  skip
  constructor
  intro F
  constructor
  intro c hc
  apply is_limit.of_iso_limit (limit.is_limit _)
  symm
  trans colim.map_cone (limit.cone F)
  exact functor.map_iso _ (hc.unique_up_to_iso (limit.is_limit F))
  exact as_iso (colimitLimitToLimitColimitCone.{v, v + 1} F)

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]

variable [ReflectsLimitsOfShape J (forget C)] [PreservesColimitsOfShape K (forget C)]

variable [PreservesLimitsOfShape J (forget C)]

noncomputable instance filteredColimPreservesFiniteLimits : PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _) := by
  have : preserves_limits_of_shape J ((colim : (K ⥤ C) ⥤ _) ⋙ forget C) :=
    preserves_limits_of_shape_of_nat_iso (preserves_colimit_nat_iso _).symm
  exact preserves_limits_of_shape_of_reflects_of_preserves _ (forget C)

end

attribute [local instance] reflects_limits_of_shape_of_reflects_isomorphisms

noncomputable instance [PreservesFiniteLimits (forget C)] [PreservesFilteredColimits (forget C)] [HasFiniteLimits C]
    [HasColimitsOfShape K C] [ReflectsIsomorphisms (forget C)] : PreservesFiniteLimits (colim : (K ⥤ C) ⥤ _) := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{v}
  intro J _ _
  skip
  infer_instance

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]

variable [ReflectsLimitsOfShape J (forget C)] [PreservesColimitsOfShape K (forget C)]

variable [PreservesLimitsOfShape J (forget C)]

/-- A curried version of the fact that filtered colimits commute with finite limits. -/
noncomputable def colimitLimitIso (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.flip) :=
  (isLimitOfPreserves colim (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (colimitFlipIsoCompColim _).symm

@[simp, reassoc]
theorem ι_colimit_limit_iso_limit_π (F : J ⥤ K ⥤ C) (a) (b) :
    colimit.ι (limit F) a ≫ (colimitLimitIso F).Hom ≫ limit.π (colimit F.flip) b =
      (limit.π F b).app a ≫ (colimit.ι F.flip a).app b :=
  by
  dsimp' [← colimit_limit_iso]
  simp only [← functor.map_cone_π_app, ← iso.symm_hom, ← limits.limit.cone_point_unique_up_to_iso_hom_comp_assoc, ←
    limits.limit.cone_π, ← limits.colimit.ι_map_assoc, ← limits.colimit_flip_iso_comp_colim_inv_app, ← assoc, ←
    limits.has_limit.iso_of_nat_iso_hom_π]
  congr 1
  simp only [category.assoc, ← iso.comp_inv_eq, ← limits.colimit_obj_iso_colimit_comp_evaluation_ι_app_hom, ←
    limits.has_colimit.iso_of_nat_iso_ι_hom, ← nat_iso.of_components.hom_app]
  dsimp'
  simp

end

end CategoryTheory.Limits

