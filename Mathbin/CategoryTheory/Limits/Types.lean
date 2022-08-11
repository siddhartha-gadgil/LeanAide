/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.Filtered
import Mathbin.Tactic.EquivRw

/-!
# Limits in the category of types.

We show that the category of types has all (co)limits, by providing the usual concrete models.

We also give a characterisation of filtered colimits in `Type`, via
`colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj`.

Finally, we prove the category of types has categorical images,
and that these agree with the range of a function.
-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.Types

variable {J : Type v} [SmallCategory J]

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
def limitCone (F : J ⥤ Type max v u) : Cone F where
  x := F.sections
  π := { app := fun j u => u.val j }

attribute [local elabWithoutExpectedType] congr_fun

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
def limitConeIsLimit (F : J ⥤ Type max v u) : IsLimit (limitCone F) where
  lift := fun s v => ⟨fun j => s.π.app j v, fun j j' f => congr_fun (Cone.w s f) _⟩
  uniq' := by
    intros
    ext x j
    exact congr_fun (w j) x

/-- The category of types has all limits.

See <https://stacks.math.columbia.edu/tag/002U>.
-/
instance has_limits_of_size :
    HasLimitsOfSize.{v}
      (Type
        max v
          u) where HasLimitsOfShape := fun J 𝒥 =>
    { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } }

instance : HasLimits (Type u) :=
  types.has_limits_of_size.{u, u}

/-- The equivalence between a limiting cone of `F` in `Type u` and the "concrete" definition as the
sections of `F`.
-/
def isLimitEquivSections {F : J ⥤ Type max v u} {c : Cone F} (t : IsLimit c) : c.x ≃ F.sections :=
  (IsLimit.conePointUniqueUpToIso t (limitConeIsLimit F)).toEquiv

@[simp]
theorem is_limit_equiv_sections_apply {F : J ⥤ Type max v u} {c : Cone F} (t : IsLimit c) (j : J) (x : c.x) :
    ((isLimitEquivSections t) x : ∀ j, F.obj j) j = c.π.app j x :=
  rfl

@[simp]
theorem is_limit_equiv_sections_symm_apply {F : J ⥤ Type max v u} {c : Cone F} (t : IsLimit c) (x : F.sections)
    (j : J) : c.π.app j ((isLimitEquivSections t).symm x) = (x : ∀ j, F.obj j) j := by
  equiv_rw(is_limit_equiv_sections t).symm  at x
  simp

/-- The equivalence between the abstract limit of `F` in `Type u`
and the "concrete" definition as the sections of `F`.
-/
noncomputable def limitEquivSections (F : J ⥤ Type max v u) : (limit F : Type max v u) ≃ F.sections :=
  isLimitEquivSections (limit.isLimit _)

@[simp]
theorem limit_equiv_sections_apply (F : J ⥤ Type max v u) (x : limit F) (j : J) :
    ((limitEquivSections F) x : ∀ j, F.obj j) j = limit.π F j x :=
  rfl

@[simp]
theorem limit_equiv_sections_symm_apply (F : J ⥤ Type max v u) (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections F).symm x) = (x : ∀ j, F.obj j) j :=
  is_limit_equiv_sections_symm_apply _ _ _

@[simp]
theorem limit_equiv_sections_symm_apply' (F : J ⥤ Type v) (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections.{v, v} F).symm x) = (x : ∀ j, F.obj j) j :=
  is_limit_equiv_sections_symm_apply _ _ _

/-- Construct a term of `limit F : Type u` from a family of terms `x : Π j, F.obj j`
which are "coherent": `∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j'`.
-/
@[ext]
noncomputable def Limit.mk (F : J ⥤ Type max v u) (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') :
    (limit F : Type max v u) :=
  (limitEquivSections F).symm ⟨x, h⟩

@[simp]
theorem Limit.π_mk (F : J ⥤ Type max v u) (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
    limit.π F j (Limit.mk F x h) = x j := by
  dsimp' [← limit.mk]
  simp

@[simp]
theorem Limit.π_mk' (F : J ⥤ Type v) (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
    limit.π F j (Limit.mk.{v, v} F x h) = x j := by
  dsimp' [← limit.mk]
  simp

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits
@[ext]
theorem limit_ext (F : J ⥤ Type max v u) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) : x = y := by
  apply (limit_equiv_sections F).Injective
  ext j
  simp [← w j]

@[ext]
theorem limit_ext' (F : J ⥤ Type v) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) : x = y := by
  apply (limitEquivSections.{v, v} F).Injective
  ext j
  simp [← w j]

theorem limit_ext_iff (F : J ⥤ Type max v u) (x y : limit F) : x = y ↔ ∀ j, limit.π F j x = limit.π F j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext _ _ _⟩

theorem limit_ext_iff' (F : J ⥤ Type v) (x y : limit F) : x = y ↔ ∀ j, limit.π F j x = limit.π F j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext _ _ _⟩

-- TODO: are there other limits lemmas that should have `_apply` versions?
-- Can we generate these like with `@[reassoc]`?
-- PROJECT: prove these for any concrete category where the forgetful functor preserves limits?
@[simp]
theorem Limit.w_apply {F : J ⥤ Type max v u} {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x

@[simp]
theorem Limit.lift_π_apply (F : J ⥤ Type max v u) (s : Cone F) (j : J) (x : s.x) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x

@[simp]
theorem Limit.map_π_apply {F G : J ⥤ Type max v u} (α : F ⟶ G) (j : J) (x) :
    limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (lim_map_π α j) x

@[simp]
theorem Limit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x

@[simp]
theorem Limit.lift_π_apply' (F : J ⥤ Type v) (s : Cone F) (j : J) (x : s.x) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x

@[simp]
theorem Limit.map_π_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x) :
    limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (lim_map_π α j) x

/-- The relation defining the quotient type which implements the colimit of a functor `F : J ⥤ Type u`.
See `category_theory.limits.types.quot`.
-/
def Quot.Rel (F : J ⥤ Type max v u) : (Σj, F.obj j) → (Σj, F.obj j) → Prop := fun p p' =>
  ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

/-- A quotient type implementing the colimit of a functor `F : J ⥤ Type u`,
as pairs `⟨j, x⟩` where `x : F.obj j`, modulo the equivalence relation generated by
`⟨j, x⟩ ~ ⟨j', x'⟩` whenever there is a morphism `f : j ⟶ j'` so `F.map f x = x'`.
-/
@[nolint has_inhabited_instance]
def Quot (F : J ⥤ Type max v u) : Type max v u :=
  @Quot (Σj, F.obj j) (Quot.Rel F)

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
def colimitCocone (F : J ⥤ Type max v u) : Cocone F where
  x := Quot F
  ι :=
    { app := fun j x => Quot.mk _ ⟨j, x⟩, naturality' := fun j j' f => funext fun x => Eq.symm (Quot.sound ⟨f, rfl⟩) }

attribute [local elab_with_expected_type] Quot.lift

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
def colimitCoconeIsColimit (F : J ⥤ Type max v u) :
    IsColimit
      (colimitCocone
        F) where desc := fun s =>
    Quot.lift (fun p : Σj, F.obj j => s.ι.app p.1 p.2) fun ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩ => by
      rw [hf] <;> exact (congr_fun (cocone.w s f) x).symm

/-- The category of types has all colimits.

See <https://stacks.math.columbia.edu/tag/002U>.
-/
instance has_colimits_of_size :
    HasColimitsOfSize.{v}
      (Type
        max v
          u) where HasColimitsOfShape := fun J 𝒥 =>
    { HasColimit := fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } }

instance : HasColimits (Type u) :=
  types.has_colimits_of_size.{u, u}

/-- The equivalence between the abstract colimit of `F` in `Type u`
and the "concrete" definition as a quotient.
-/
noncomputable def colimitEquivQuot (F : J ⥤ Type max v u) : (colimit F : Type max v u) ≃ Quot F :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv

@[simp]
theorem colimit_equiv_quot_symm_apply (F : J ⥤ Type max v u) (j : J) (x : F.obj j) :
    (colimitEquivQuot F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  rfl

@[simp]
theorem colimit_equiv_quot_apply (F : J ⥤ Type max v u) (j : J) (x : F.obj j) :
    (colimitEquivQuot F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (colimit_equiv_quot F).symm.Injective
  simp

@[simp]
theorem Colimit.w_apply {F : J ⥤ Type max v u} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x

@[simp]
theorem Colimit.ι_desc_apply (F : J ⥤ Type max v u) (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_fun (colimit.ι_desc s j) x

@[simp]
theorem Colimit.ι_map_apply {F G : J ⥤ Type max v u} (α : F ⟶ G) (j : J) (x) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x

@[simp]
theorem Colimit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x

@[simp]
theorem Colimit.ι_desc_apply' (F : J ⥤ Type v) (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_fun (colimit.ι_desc s j) x

@[simp]
theorem Colimit.ι_map_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x

theorem colimit_sound {F : J ⥤ Type max v u} {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w]
  simp

theorem colimit_sound' {F : J ⥤ Type max v u} {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J} (f : j ⟶ j'')
    (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w _ f, ← colimit.w _ f']
  rw [types_comp_apply, types_comp_apply, w]

theorem colimit_eq {F : J ⥤ Type max v u} {j j' : J} {x : F.obj j} {x' : F.obj j'}
    (w : colimit.ι F j x = colimit.ι F j' x') : EqvGen (Quot.Rel F) ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using congr_arg (colimit_equiv_quot F) w

theorem jointly_surjective (F : J ⥤ Type max v u) {t : Cocone F} (h : IsColimit t) (x : t.x) : ∃ j y, t.ι.app j y = x :=
  by
  suffices (fun x : t.X => ULift.up (∃ j y, t.ι.app j y = x)) = fun _ => ULift.up True by
    have := congr_fun this x
    have H := congr_arg ULift.down this
    dsimp'  at H
    rwa [eq_trueₓ] at H
  refine' h.hom_ext _
  intro j
  ext y
  erw [iff_trueₓ]
  exact ⟨j, y, rfl⟩

/-- A variant of `jointly_surjective` for `x : colimit F`. -/
theorem jointly_surjective' {F : J ⥤ Type max v u} (x : colimit F) : ∃ j y, colimit.ι F j y = x :=
  jointly_surjective F (colimit.isColimit _) x

namespace FilteredColimit

/- For filtered colimits of types, we can give an explicit description
  of the equivalence relation generated by the relation used to form
  the colimit.  -/
variable (F : J ⥤ Type max v u)

/-- An alternative relation on `Σ j, F.obj j`,
which generates the same equivalence relation as we use to define the colimit in `Type` above,
but that is more convenient when working with filtered colimits.

Elements in `F.obj j` and `F.obj j'` are equivalent if there is some `k : J` to the right
where their images are equal.
-/
protected def Rel (x y : Σj, F.obj j) : Prop :=
  ∃ (k : _)(f : x.1 ⟶ k)(g : y.1 ⟶ k), F.map f x.2 = F.map g y.2

theorem rel_of_quot_rel (x y : Σj, F.obj j) : Quot.Rel F x y → FilteredColimit.Rel F x y := fun ⟨f, h⟩ =>
  ⟨y.1, f, 𝟙 y.1, by
    rw [← h, functor_to_types.map_id_apply]⟩

theorem eqv_gen_quot_rel_of_rel (x y : Σj, F.obj j) : FilteredColimit.Rel F x y → EqvGen (Quot.Rel F) x y :=
  fun ⟨k, f, g, h⟩ =>
  EqvGen.trans _ ⟨k, F.map f x.2⟩ _ (EqvGen.rel _ _ ⟨f, rfl⟩) (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨g, h⟩))

attribute [local elabWithoutExpectedType] nat_trans.app

/-- Recognizing filtered colimits of types. -/
noncomputable def isColimitOf (t : Cocone F) (hsurj : ∀ x : t.x, ∃ i xi, x = t.ι.app i xi)
    (hinj : ∀ i j xi xj, t.ι.app i xi = t.ι.app j xj → ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f xi = F.map g xj) :
    IsColimit t := by
  -- Strategy: Prove that the map from "the" colimit of F (defined above) to t.X
  -- is a bijection.
  apply is_colimit.of_iso_colimit (colimit.is_colimit F)
  refine' cocones.ext (Equivₓ.toIso (Equivₓ.ofBijective _ _)) _
  · exact colimit.desc F t
    
  · constructor
    · show Function.Injective _
      intro a b h
      rcases jointly_surjective F (colimit.is_colimit F) a with ⟨i, xi, rfl⟩
      rcases jointly_surjective F (colimit.is_colimit F) b with ⟨j, xj, rfl⟩
      change (colimit.ι F i ≫ colimit.desc F t) xi = (colimit.ι F j ≫ colimit.desc F t) xj at h
      rw [colimit.ι_desc, colimit.ι_desc] at h
      rcases hinj i j xi xj h with ⟨k, f, g, h'⟩
      change colimit.ι F i xi = colimit.ι F j xj
      rw [← colimit.w F f, ← colimit.w F g]
      change colimit.ι F k (F.map f xi) = colimit.ι F k (F.map g xj)
      rw [h']
      
    · show Function.Surjective _
      intro x
      rcases hsurj x with ⟨i, xi, rfl⟩
      use colimit.ι F i xi
      simp
      
    
  · intro j
    apply colimit.ι_desc
    

variable [IsFilteredOrEmpty J]

protected theorem rel_equiv : Equivalenceₓ (FilteredColimit.Rel F) :=
  ⟨fun x => ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩, fun x y ⟨k, f, g, h⟩ => ⟨k, g, f, h.symm⟩,
    fun x y z ⟨k, f, g, h⟩ ⟨k', f', g', h'⟩ =>
    let ⟨l, fl, gl, _⟩ := IsFilteredOrEmpty.cocone_objs k k'
    let ⟨m, n, hn⟩ := IsFilteredOrEmpty.cocone_maps (g ≫ fl) (f' ≫ gl)
    ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n,
      calc
        F.map (f ≫ fl ≫ n) x.2 = F.map (fl ≫ n) (F.map f x.2) := by
          simp
        _ = F.map (fl ≫ n) (F.map g y.2) := by
          rw [h]
        _ = F.map ((g ≫ fl) ≫ n) y.2 := by
          simp
        _ = F.map ((f' ≫ gl) ≫ n) y.2 := by
          rw [hn]
        _ = F.map (gl ≫ n) (F.map f' y.2) := by
          simp
        _ = F.map (gl ≫ n) (F.map g' z.2) := by
          rw [h']
        _ = F.map (g' ≫ gl ≫ n) z.2 := by
          simp
        ⟩⟩

protected theorem rel_eq_eqv_gen_quot_rel : FilteredColimit.Rel F = EqvGen (Quot.Rel F) := by
  ext ⟨j, x⟩ ⟨j', y⟩
  constructor
  · apply eqv_gen_quot_rel_of_rel
    
  · rw [← (filtered_colimit.rel_equiv F).eqv_gen_iff]
    exact EqvGen.mono (rel_of_quot_rel F)
    

theorem colimit_eq_iff_aux {i j : J} {xi : F.obj i} {xj : F.obj j} :
    (colimitCocone F).ι.app i xi = (colimitCocone F).ι.app j xj ↔ FilteredColimit.Rel F ⟨i, xi⟩ ⟨j, xj⟩ := by
  change Quot.mk _ _ = Quot.mk _ _ ↔ _
  rw [Quot.eq, filtered_colimit.rel_eq_eqv_gen_quot_rel]

theorem is_colimit_eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j} :
    t.ι.app i xi = t.ι.app j xj ↔ ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f xi = F.map g xj := by
  let t' := colimitCocone F
  let e : t' ≅ t := IsColimit.uniqueUpToIso (colimitCoconeIsColimit F) ht
  let e' : t'.x ≅ t.x := (Cocones.forget _).mapIso e
  refine' Iff.trans _ (colimit_eq_iff_aux F)
  convert e'.to_equiv.apply_eq_iff_eq <;> rw [← e.hom.w] <;> rfl

theorem colimit_eq_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔ ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f xi = F.map g xj :=
  is_colimit_eq_iff _ (colimit.isColimit F)

end FilteredColimit

variable {α β : Type u} (f : α ⟶ β)

section

/-- the image of a morphism in Type is just `set.range f` -/
-- implementation of `has_image`
def Image : Type u :=
  Set.Range f

instance [Inhabited α] : Inhabited (Image f) where default := ⟨f default, ⟨_, rfl⟩⟩

/-- the inclusion of `image f` into the target -/
def Image.ι : Image f ⟶ β :=
  Subtype.val

instance : Mono (Image.ι f) :=
  (mono_iff_injective _).2 Subtype.val_injective

variable {f}

/-- the universal property for the image factorisation -/
noncomputable def Image.lift (F' : MonoFactorisation f) : Image f ⟶ F'.i :=
  (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : Image f → F'.i)

theorem Image.lift_fac (F' : MonoFactorisation f) : Image.lift F' ≫ F'.m = Image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

/-- the factorisation of any morphism in Type through a mono. -/
def monoFactorisation : MonoFactorisation f where
  i := Image f
  m := Image.ι f
  e := Set.rangeFactorization f

/-- the facorisation through a mono has the universal property of the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := Image.lift
  lift_fac' := Image.lift_fac

instance : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩

instance :
    HasImages (Type u) where HasImage := by
    infer_instance

instance :
    HasImageMaps
      (Type
        u) where HasImageMap := fun f g st =>
    HasImageMap.transport st (monoFactorisation f.Hom) (isImage g.Hom)
      (fun x =>
        ⟨st.right x.1,
          ⟨st.left (Classical.some x.2), by
            have p := st.w
            replace p := congr_fun p (Classical.some x.2)
            simp only [← functor.id_map, ← types_comp_apply, ← Subtype.val_eq_coe] at p
            erw [p, Classical.some_spec x.2]⟩⟩)
      rfl

end CategoryTheory.Limits.Types

