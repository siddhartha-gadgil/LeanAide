/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.AffineScheme
import Mathbin.RingTheory.Nilpotent
import Mathbin.Topology.Sheaves.SheafCondition.Sites
import Mathbin.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathbin.Algebra.Category.Ring.Constructions
import Mathbin.RingTheory.IntegralDomain
import Mathbin.RingTheory.LocalProperties

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `algebraic_geometry.is_integral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `algebraic_geometry.is_reduced`: A scheme is reduced if all the components of the structure sheaf
  is reduced.
-/


open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits Top

namespace AlgebraicGeometry

variable (X : Scheme)

instance : T0Space X.Carrier := by
  rw [t0_space_iff_inseparable]
  intro x y h
  obtain ⟨U, R, ⟨e⟩⟩ := X.local_affine x
  have hy : y ∈ U.val := (h.mem_open_iff U.1.2).1 U.2
  erw [← subtype_inseparable_iff (⟨x, U.2⟩ : U.1.1) (⟨y, hy⟩ : U.1.1)] at h
  let e' : U.1 ≃ₜ PrimeSpectrum R :=
    homeo_of_iso ((LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _).mapIso e)
  have := t0_space_of_injective_of_continuous e'.injective e'.continuous
  rw [t0_space_iff_inseparable] at this
  · simpa only [← Subtype.mk_eq_mk] using this ⟨x, U.2⟩ ⟨y, hy⟩ h
    

instance : QuasiSober X.Carrier := by
  apply quasi_sober_of_open_cover (Set.Range fun x => Set.Range <| (X.affine_cover.map x).1.base) with
    { instances := false }
  · rintro ⟨_, i, rfl⟩
    exact (X.affine_cover.is_open i).base_open.open_range
    
  · rintro ⟨_, i, rfl⟩
    exact
      @OpenEmbedding.quasi_sober _ _ _
        (Homeomorph.ofEmbedding _ (X.affine_cover.is_open i).base_open.toEmbedding).symm.OpenEmbedding
        PrimeSpectrum.quasi_sober
    
  · rw [Set.top_eq_univ, Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x
    exact ⟨_, ⟨_, rfl⟩, X.affine_cover.covers x⟩
    

/-- A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced. -/
class IsReduced : Prop where
  component_reduced : ∀ U, IsReduced (X.Presheaf.obj (op U)) := by
    run_tac
      tactic.apply_instance

attribute [instance] is_reduced.component_reduced

theorem is_reduced_of_stalk_is_reduced [∀ x : X.Carrier, IsReduced (X.Presheaf.stalk x)] : IsReduced X := by
  refine' ⟨fun U => ⟨fun s hs => _⟩⟩
  apply presheaf.section_ext X.sheaf U s 0
  intro x
  rw [RingHom.map_zero]
  change X.presheaf.germ x s = 0
  exact (hs.map _).eq_zero

instance stalk_is_reduced_of_reduced [IsReduced X] (x : X.Carrier) : IsReduced (X.Presheaf.stalk x) := by
  constructor
  rintro g ⟨n, e⟩
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.germ_exist x g
  rw [← map_pow, ← map_zero (X.presheaf.germ ⟨x, hxU⟩)] at e
  obtain ⟨V, hxV, iU, iV, e'⟩ := X.presheaf.germ_eq x hxU hxU _ 0 e
  rw [map_pow, map_zero] at e'
  replace e' := (IsNilpotent.mk _ _ e').eq_zero
  erw [← concrete_category.congr_hom (X.presheaf.germ_res iU ⟨x, hxV⟩) s]
  rw [comp_apply, e', map_zero]

theorem is_reduced_of_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] [IsReduced Y] : IsReduced X :=
  by
  constructor
  intro U
  have : U = (opens.map f.1.base).obj (H.base_open.is_open_map.functor.obj U) := by
    ext1
    exact (Set.preimage_image_eq _ H.base_open.inj).symm
  rw [this]
  exact
    is_reduced_of_injective (inv <| f.1.c.app (op <| H.base_open.is_open_map.functor.obj U))
      (as_iso <| f.1.c.app (op <| H.base_open.is_open_map.functor.obj U) :
              Y.presheaf.obj _ ≅ _).symm.commRingIsoToRingEquiv.Injective

instance {R : CommRingₓₓ} [H : IsReduced R] : IsReduced (Scheme.spec.obj <| op R) := by
  apply is_reduced_of_stalk_is_reduced with { instances := false }
  intro x
  dsimp'
  have : _root_.is_reduced (CommRingₓₓ.of <| Localization.AtPrime (PrimeSpectrum.asIdeal x)) := by
    dsimp'
    infer_instance
  exact
    is_reduced_of_injective (structure_sheaf.stalk_iso R x).Hom
      (structure_sheaf.stalk_iso R x).commRingIsoToRingEquiv.Injective

theorem affine_is_reduced_iff (R : CommRingₓₓ) : IsReduced (Scheme.spec.obj <| op R) ↔ IsReduced R := by
  refine' ⟨_, fun h => inferInstance⟩
  intro h
  skip
  have : _root_.is_reduced (LocallyRingedSpace.Γ.obj (op <| Spec.to_LocallyRingedSpace.obj <| op R)) := by
    change _root_.is_reduced ((Scheme.Spec.obj <| op R).Presheaf.obj <| op ⊤)
    infer_instance
  exact is_reduced_of_injective (to_Spec_Γ R) (as_iso <| to_Spec_Γ R).commRingIsoToRingEquiv.Injective

theorem is_reduced_of_is_affine_is_reduced [IsAffine X] [h : IsReduced (X.Presheaf.obj (op ⊤))] : IsReduced X := by
  have : IsReduced (Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))) := by
    rw [affine_is_reduced_iff]
    exact h
  exact is_reduced_of_open_immersion X.iso_Spec.hom

/-- To show that a statement `P` holds for all open subsets of all schemes, it suffices to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for `U`.
2. For an open immerison `f : X ⟶ Y`, if `P` holds for the entire space of `X`, then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
theorem reduce_to_affine_global (P : ∀ (X : Scheme) (U : Opens X.Carrier), Prop)
    (h₁ : ∀ (X : Scheme) (U : Opens X.Carrier), (∀ x : U, ∃ (V : _)(h : x.1 ∈ V)(i : V ⟶ U), P X V) → P X U)
    (h₂ :
      ∀ {X Y} (f : X ⟶ Y) [hf : IsOpenImmersion f],
        ∃ (U : Set X.Carrier)(V : Set Y.Carrier)(hU : U = ⊤)(hV : V = Set.Range f.1.base),
          P X ⟨U, hU.symm ▸ is_open_univ⟩ → P Y ⟨V, hV.symm ▸ hf.base_open.open_range⟩)
    (h₃ : ∀ R : CommRingₓₓ, P (Scheme.spec.obj <| op R) ⊤) : ∀ (X : Scheme) (U : Opens X.Carrier), P X U := by
  intro X U
  apply h₁
  intro x
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open x.prop U.2
  let U' : opens _ := ⟨_, (X.affine_basis_cover.is_open j).base_open.open_range⟩
  let i' : U' ⟶ U := hom_of_le i
  refine' ⟨U', hx, i', _⟩
  obtain ⟨_, _, rfl, rfl, h₂'⟩ := h₂ (X.affine_basis_cover.map j)
  apply h₂'
  apply h₃

theorem reduce_to_affine_nbhd (P : ∀ (X : Scheme) (x : X.Carrier), Prop)
    (h₁ : ∀ (R : CommRingₓₓ) (x : PrimeSpectrum R), P (Scheme.spec.obj <| op R) x)
    (h₂ : ∀ {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X.Carrier), P X x → P Y (f.1.base x)) :
    ∀ (X : Scheme) (x : X.Carrier), P X x := by
  intro X x
  obtain ⟨y, e⟩ := X.affine_cover.covers x
  convert h₂ (X.affine_cover.map (X.affine_cover.f x)) y _
  · rw [e]
    
  apply h₁

theorem eq_zero_of_basic_open_empty {X : Scheme} [hX : IsReduced X] {U : Opens X.Carrier} (s : X.Presheaf.obj (op U))
    (hs : X.basicOpen s = ∅) : s = 0 := by
  apply Top.Presheaf.section_ext X.sheaf U
  simp_rw [RingHom.map_zero]
  revert X U hX s
  refine' reduce_to_affine_global _ _ _ _
  · intro X U hx hX s hs x
    obtain ⟨V, hx, i, H⟩ := hx x
    specialize H (X.presheaf.map i.op s)
    erw [Scheme.basic_open_res] at H
    rw [hs, ← subtype.coe_injective.eq_iff, opens.empty_eq, opens.inter_eq, inf_bot_eq] at H
    specialize H rfl ⟨x, hx⟩
    erw [Top.Presheaf.germ_res_apply] at H
    exact H
    
  · rintro X Y f hf
    have e : f.val.base ⁻¹' Set.Range ⇑f.val.base = ⊤ := by
      rw [← Set.image_univ, Set.preimage_image_eq _ hf.base_open.inj, Set.top_eq_univ]
    refine' ⟨_, _, e, rfl, _⟩
    rintro H hX s hs ⟨_, x, rfl⟩
    have := is_reduced_of_open_immersion f
    specialize
      H (f.1.c.app _ s) _
        ⟨x, by
          change x ∈ f.val.base ⁻¹' _
          rw [e]
          trivial⟩
    · rw [← Scheme.preimage_basic_open, hs]
      ext1
      simp [← opens.map]
      
    · erw [← PresheafedSpace.stalk_map_germ_apply f.1 ⟨_, _⟩ ⟨x, _⟩] at H
      apply_fun inv <| PresheafedSpace.stalk_map f.val x  at H
      erw [CategoryTheory.IsIso.hom_inv_id_apply, map_zero] at H
      exact H
      
    
  · intro R hX s hs x
    erw [basic_open_eq_of_affine', PrimeSpectrum.basic_open_eq_bot_iff] at hs
    replace hs := hs.map (Spec_Γ_identity.app R).inv
    -- what the hell?!
    replace hs := @IsNilpotent.eq_zero _ _ _ _ (show _ from _) hs
    rw [iso.hom_inv_id_apply] at hs
    rw [hs, map_zero]
    exact @is_reduced.component_reduced hX ⊤
    

@[simp]
theorem basic_open_eq_bot_iff {X : Scheme} [IsReduced X] {U : Opens X.Carrier} (s : X.Presheaf.obj <| op U) :
    X.basicOpen s = ⊥ ↔ s = 0 := by
  refine' ⟨eq_zero_of_basic_open_empty s, _⟩
  rintro rfl
  simp

/-- A scheme `X` is integral if its carrier is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
class IsIntegral : Prop where
  Nonempty : Nonempty X.Carrier := by
    run_tac
      tactic.apply_instance
  component_integral : ∀ (U : Opens X.Carrier) [Nonempty U], IsDomain (X.Presheaf.obj (op U)) := by
    run_tac
      tactic.apply_instance

attribute [instance] is_integral.component_integral is_integral.nonempty

instance [h : IsIntegral X] : IsDomain (X.Presheaf.obj (op ⊤)) :=
  @IsIntegral.component_integral _ _
    (by
      simp )

instance (priority := 900) is_reduced_of_is_integral [IsIntegral X] : IsReduced X := by
  constructor
  intro U
  cases U.1.eq_empty_or_nonempty
  · have : U = ∅ := Subtype.eq h
    have := CommRingₓₓ.subsingleton_of_is_terminal (X.sheaf.is_terminal_of_eq_empty this)
    change _root_.is_reduced (X.sheaf.val.obj (op U))
    infer_instance
    
  · have : Nonempty U := by
      simpa
    infer_instance
    

instance is_irreducible_of_is_integral [IsIntegral X] : IrreducibleSpace X.Carrier := by
  by_contra H
  replace H : ¬IsPreirreducible (⊤ : Set X.carrier) := fun h =>
    H { to_preirreducible_space := ⟨h⟩, to_nonempty := inferInstance }
  simp_rw [is_preirreducible_iff_closed_union_closed, not_forall, not_or_distrib] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  erw [not_forall] at h₂ h₃
  simp_rw [not_forall] at h₂ h₃
  have : Nonempty (⟨Sᶜ, hS.1⟩ : opens X.carrier) := ⟨⟨_, h₂.some_spec.some_spec⟩⟩
  have : Nonempty (⟨Tᶜ, hT.1⟩ : opens X.carrier) := ⟨⟨_, h₃.some_spec.some_spec⟩⟩
  have : Nonempty (⟨Sᶜ, hS.1⟩⊔⟨Tᶜ, hT.1⟩ : opens X.carrier) := ⟨⟨_, Or.inl h₂.some_spec.some_spec⟩⟩
  let e : X.presheaf.obj _ ≅ CommRingₓₓ.of _ :=
    (X.sheaf.is_product_of_disjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ _).conePointUniqueUpToIso (CommRingₓₓ.prodFanIsLimit _ _)
  apply false_of_nontrivial_of_product_domain with { instances := false }
  · exact e.symm.CommRing_iso_to_ring_equiv.is_domain _
    
  · apply X.to_LocallyRingedSpace.component_nontrivial
    
  · apply X.to_LocallyRingedSpace.component_nontrivial
    
  · ext x
    constructor
    · rintro ⟨hS, hT⟩
      cases
        h₁
          (show x ∈ ⊤ by
            trivial)
      exacts[hS h, hT h]
      
    · intro x
      exact x.rec _
      
    

theorem is_integral_of_is_irreducible_is_reduced [IsReduced X] [H : IrreducibleSpace X.Carrier] : IsIntegral X := by
  constructor
  refine' fun U hU => ⟨fun a b e => _, (@LocallyRingedSpace.component_nontrivial X.to_LocallyRingedSpace U hU).1⟩
  simp_rw [← basic_open_eq_bot_iff, ← opens.not_nonempty_iff_eq_bot]
  by_contra' h
  obtain ⟨_, ⟨x, hx₁, rfl⟩, ⟨x, hx₂, e'⟩⟩ :=
    @nonempty_preirreducible_inter _ H.1 (X.basic_open a).2 (X.basic_open b).2 h.1 h.2
  replace e' := Subtype.eq e'
  subst e'
  replace e := congr_arg (X.presheaf.germ x) e
  rw [RingHom.map_mul, RingHom.map_zero] at e
  refine' @zero_ne_one (X.presheaf.stalk x.1) _ _ (is_unit_zero_iff.1 _)
  convert hx₁.mul hx₂
  exact e.symm

theorem is_integral_iff_is_irreducible_and_is_reduced : IsIntegral X ↔ IrreducibleSpace X.Carrier ∧ IsReduced X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => is_integral_of_is_irreducible_is_reduced X⟩

theorem is_integral_of_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] [IsIntegral Y]
    [Nonempty X.Carrier] : IsIntegral X := by
  constructor
  intro U hU
  have : U = (opens.map f.1.base).obj (H.base_open.is_open_map.functor.obj U) := by
    ext1
    exact (Set.preimage_image_eq _ H.base_open.inj).symm
  rw [this]
  have : IsDomain (Y.presheaf.obj (op (H.base_open.is_open_map.functor.obj U))) := by
    apply is_integral.component_integral with { instances := false }
    infer_instance
    refine' ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact
    (as_iso <| f.1.c.app (op <| H.base_open.is_open_map.functor.obj U) :
              Y.presheaf.obj _ ≅ _).symm.commRingIsoToRingEquiv.IsDomain
      _

instance {R : CommRingₓₓ} [H : IsDomain R] : IsIntegral (Scheme.spec.obj <| op R) := by
  apply is_integral_of_is_irreducible_is_reduced with { instances := false }
  · infer_instance
    
  · dsimp' [← Spec.Top_obj]
    infer_instance
    

theorem affine_is_integral_iff (R : CommRingₓₓ) : IsIntegral (Scheme.spec.obj <| op R) ↔ IsDomain R :=
  ⟨fun h =>
    RingEquiv.is_domain ((Scheme.Spec.obj <| op R).Presheaf.obj _) (as_iso <| to_Spec_Γ R).commRingIsoToRingEquiv,
    fun h => inferInstance⟩

theorem is_integral_of_is_affine_is_domain [IsAffine X] [Nonempty X.Carrier] [h : IsDomain (X.Presheaf.obj (op ⊤))] :
    IsIntegral X := by
  have : IsIntegral (Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))) := by
    rw [affine_is_integral_iff]
    exact h
  exact is_integral_of_open_immersion X.iso_Spec.hom

theorem map_injective_of_is_integral [IsIntegral X] {U V : Opens X.Carrier} (i : U ⟶ V) [H : Nonempty U] :
    Function.Injective (X.Presheaf.map i.op) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← basic_open_eq_bot_iff] at hx⊢
  rw [Scheme.basic_open_res] at hx
  revert hx
  contrapose!
  simp_rw [← opens.not_nonempty_iff_eq_bot, not_not]
  apply nonempty_preirreducible_inter U.prop (RingedSpace.basic_open _ _).Prop
  simpa using H

end AlgebraicGeometry

