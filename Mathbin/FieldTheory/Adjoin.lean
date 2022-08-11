/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathbin.FieldTheory.IntermediateField
import Mathbin.FieldTheory.Separable
import Mathbin.RingTheory.TensorProduct

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining `S ∪ T`.
- `bot_eq_top_of_dim_adjoin_eq_one`: if `F⟮x⟯` has dimension `1` over `F` for every `x`
  in `E` then `F = E`

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/


open FiniteDimensional Polynomial

open Classical Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type _) [Field F] {E : Type _} [Field E] [Algebra F E] (S : Set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.Range (algebraMap F E) ∪ S) with
    algebra_map_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

end AdjoinDef

section Lattice

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

@[simp]
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ≤ T :=
  ⟨fun H => le_transₓ (le_transₓ (Set.subset_union_right _ _) Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.Range (algebraMap F E) ∪ S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E) coe := fun _ _ => adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E) coe where
  choice := fun s hs => (adjoin F s).copy s <| le_antisymmₓ (gc.le_u_l s) hs
  gc := IntermediateField.gc
  le_l_u := fun S => (IntermediateField.gc (S : Set E) (adjoin F S)).1 <| le_rfl
  choice_eq := fun _ _ => copy_eq _ _ _

instance : CompleteLattice (IntermediateField F E) :=
  GaloisInsertion.liftCompleteLattice IntermediateField.gi

instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

theorem coe_bot : ↑(⊥ : IntermediateField F E) = Set.Range (algebraMap F E) := by
  change ↑(Subfield.closure (Set.Range (algebraMap F E) ∪ ∅)) = Set.Range (algebraMap F E)
  simp [Set.image_univ, RingHom.map_field_closure]

theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.Range (algebraMap F E) :=
  Set.ext_iff.mp coe_bot x

@[simp]
theorem bot_to_subalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := by
  ext
  rw [mem_to_subalgebra, Algebra.mem_bot, mem_bot]

@[simp]
theorem coe_top : ↑(⊤ : IntermediateField F E) = (Set.Univ : Set E) :=
  rfl

@[simp]
theorem mem_top {x : E} : x ∈ (⊤ : IntermediateField F E) :=
  trivialₓ

@[simp]
theorem top_to_subalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ :=
  rfl

@[simp]
theorem top_to_subfield : (⊤ : IntermediateField F E).toSubfield = ⊤ :=
  rfl

@[simp, norm_cast]
theorem coe_inf (S T : IntermediateField F E) : (↑(S⊓T) : Set E) = S ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : IntermediateField F E} {x : E} : x ∈ S⊓T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_to_subalgebra (S T : IntermediateField F E) : (S⊓T).toSubalgebra = S.toSubalgebra⊓T.toSubalgebra :=
  rfl

@[simp]
theorem inf_to_subfield (S T : IntermediateField F E) : (S⊓T).toSubfield = S.toSubfield⊓T.toSubfield :=
  rfl

@[simp, norm_cast]
theorem coe_Inf (S : Set (IntermediateField F E)) : (↑(inf S) : Set E) = inf (coe '' S) :=
  rfl

@[simp]
theorem Inf_to_subalgebra (S : Set (IntermediateField F E)) : (inf S).toSubalgebra = inf (to_subalgebra '' S) :=
  SetLike.coe_injective <| by
    simp [← Set.sUnion_image]

@[simp]
theorem Inf_to_subfield (S : Set (IntermediateField F E)) : (inf S).toSubfield = inf (to_subfield '' S) :=
  SetLike.coe_injective <| by
    simp [← Set.sUnion_image]

@[simp, norm_cast]
theorem coe_infi {ι : Sort _} (S : ι → IntermediateField F E) : (↑(infi S) : Set E) = ⋂ i, S i := by
  simp [← infi]

@[simp]
theorem infi_to_subalgebra {ι : Sort _} (S : ι → IntermediateField F E) :
    (infi S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by
    simp [← infi]

@[simp]
theorem infi_to_subfield {ι : Sort _} (S : ι → IntermediateField F E) : (infi S).toSubfield = ⨅ i, (S i).toSubfield :=
  SetLike.coe_injective <| by
    simp [← infi]

/-- Construct an algebra isomorphism from an equality of intermediate fields -/
@[simps apply]
def equivOfEq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T := by
  refine' { toFun := fun x => ⟨x, _⟩, invFun := fun x => ⟨x, _⟩.. } <;> tidy

@[simp]
theorem equiv_of_eq_symm {S T : IntermediateField F E} (h : S = T) : (equivOfEq h).symm = equivOfEq h.symm :=
  rfl

@[simp]
theorem equiv_of_eq_rfl (S : IntermediateField F E) : equivOfEq (rfl : S = S) = AlgEquiv.refl := by
  ext
  rfl

@[simp]
theorem equiv_of_eq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U) :
    (equivOfEq hST).trans (equivOfEq hTU) = equivOfEq (trans hST hTU) :=
  rfl

variable (F E)

/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_to_subalgebra).trans (Algebra.botEquiv F E)

variable {F E}

@[simp]
theorem bot_equiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x :=
  AlgEquiv.commutes (botEquiv F E) x

@[simp]
theorem bot_equiv_symm (x : F) : (botEquiv F E).symm x = algebraMap F _ x :=
  rfl

noncomputable instance algebraOverBot : Algebra (⊥ : IntermediateField F E) F :=
  (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra

theorem coe_algebra_map_over_bot :
    (algebraMap (⊥ : IntermediateField F E) F : (⊥ : IntermediateField F E) → F) = IntermediateField.botEquiv F E :=
  rfl

instance is_scalar_tower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E :=
  IsScalarTower.of_algebra_map_eq
    (by
      intro x
      obtain ⟨y, rfl⟩ := (bot_equiv F E).symm.Surjective x
      rw [coe_algebra_map_over_bot, (bot_equiv F E).apply_symm_apply, bot_equiv_symm,
        IsScalarTower.algebra_map_apply F (⊥ : IntermediateField F E) E])

/-- The top intermediate_field is isomorphic to the field.

This is the intermediate field version of `subalgebra.top_equiv`. -/
@[simps apply]
def topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  (Subalgebra.equivOfEq _ _ top_to_subalgebra).trans Subalgebra.topEquiv

@[simp]
theorem top_equiv_symm_apply_coe (a : E) : ↑(topEquiv.symm a : (⊤ : IntermediateField F E)) = a :=
  rfl

@[simp]
theorem restrict_scalars_bot_eq_self (K : IntermediateField F E) : (⊥ : IntermediateField K E).restrictScalars _ = K :=
  by
  ext
  rw [mem_restrict_scalars, mem_bot]
  exact set.ext_iff.mp Subtype.range_coe x

@[simp]
theorem restrict_scalars_top {K : Type _} [Field K] [Algebra K E] [Algebra K F] [IsScalarTower K F E] :
    (⊤ : IntermediateField F E).restrictScalars K = ⊤ :=
  rfl

end Lattice

section AdjoinDef

variable (F : Type _) [Field F] {E : Type _} [Field E] [Algebra F E] (S : Set E)

theorem adjoin_eq_range_algebra_map_adjoin : (adjoin F S : Set E) = Set.Range (algebraMap (adjoin F S) E) :=
  Subtype.range_coe.symm

theorem adjoin.algebra_map_mem (x : F) : algebraMap F E x ∈ adjoin F S :=
  IntermediateField.algebra_map_mem (adjoin F S) x

theorem adjoin.range_algebra_map_subset : Set.Range (algebraMap F E) ⊆ adjoin F S := by
  intro x hx
  cases' hx with f hf
  rw [← hf]
  exact adjoin.algebra_map_mem F S f

instance adjoin.fieldCoe : CoeTₓ F (adjoin F S) where coe := fun x => ⟨algebraMap F E x, adjoin.algebra_map_mem F S x⟩

theorem subset_adjoin : S ⊆ adjoin F S := fun x hx => Subfield.subset_closure (Or.inr hx)

instance adjoin.setCoe : CoeTₓ S (adjoin F S) where coe := fun x => ⟨x, subset_adjoin F S (Subtype.mem x)⟩

@[mono]
theorem adjoin.mono (T : Set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
  GaloisConnection.monotone_l gc h

theorem adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) ⊆ adjoin F S := fun x hx =>
  adjoin.algebra_map_mem F S ⟨x, hx⟩

theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T ⊆ F) : T ⊆ adjoin F S := fun x hx =>
  (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

theorem subset_adjoin_of_subset_right {T : Set E} (H : T ⊆ S) : T ⊆ adjoin F S := fun x hx => subset_adjoin F S (H hx)

@[simp]
theorem adjoin_empty (F E : Type _) [Field F] [Field E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥ :=
  eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

@[simp]
theorem adjoin_univ (F E : Type _) [Field F] [Field E] [Algebra F E] : adjoin F (Set.Univ : Set E) = ⊤ :=
  eq_top_iff.mpr <| subset_adjoin _ _

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.Range (algebraMap F E) ⊆ K) (HS : S ⊆ K) :
    (adjoin F S).toSubfield ≤ K := by
  apply subfield.closure_le.mpr
  rw [Set.union_subset_iff]
  exact ⟨HF, HS⟩

theorem adjoin_subset_adjoin_iff {F' : Type _} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) ⊆ adjoin F' S' ↔ Set.Range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
  ⟨fun h => ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩, fun ⟨hF, hS⟩ =>
    Subfield.closure_le.mpr (Set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
theorem adjoin_adjoin_left (T : Set E) : (adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S ∪ T) := by
  rw [SetLike.ext'_iff]
  change ↑(adjoin (adjoin F S) T) = _
  apply Set.eq_of_subset_of_subset <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact adjoin.mono _ _ _ (Set.subset_union_left _ _) hx
    
  · exact subset_adjoin_of_subset_right _ _ (Set.subset_union_right _ _)
    
  · exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _)
    
  · exact Set.union_subset (subset_adjoin_of_subset_left _ (subset_adjoin _ _)) (subset_adjoin _ _)
    

@[simp]
theorem adjoin_insert_adjoin (x : E) : adjoin F (insert x (adjoin F S : Set E)) = adjoin F (insert x S) :=
  le_antisymmₓ
    (adjoin_le_iff.mpr
      (Set.insert_subset.mpr
        ⟨subset_adjoin _ _ (Set.mem_insert _ _),
          adjoin_le_iff.mpr (subset_adjoin_of_subset_right _ _ (Set.subset_insert _ _))⟩))
    (adjoin.mono _ _ _ (Set.insert_subset_insert (subset_adjoin _ _)))

/-- `F[S][T] = F[T][S]` -/
theorem adjoin_adjoin_comm (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars F = (adjoin (adjoin F T) S).restrictScalars F := by
  rw [adjoin_adjoin_left, adjoin_adjoin_left, Set.union_comm]

theorem adjoin_map {E' : Type _} [Field E'] [Algebra F E'] (f : E →ₐ[F] E') : (adjoin F S).map f = adjoin F (f '' S) :=
  by
  ext x
  show
    x ∈ (Subfield.closure (Set.Range (algebraMap F E) ∪ S)).map (f : E →+* E') ↔
      x ∈ Subfield.closure (Set.Range (algebraMap F E') ∪ f '' S)
  rw [RingHom.map_field_closure, Set.image_union, ← Set.range_comp, ← RingHom.coe_comp, f.comp_algebra_map]
  rfl

theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S ≤ (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)

theorem adjoin_eq_algebra_adjoin (inv_mem : ∀, ∀ x ∈ Algebra.adjoin F S, ∀, x⁻¹ ∈ Algebra.adjoin F S) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  le_antisymmₓ
    (show
      adjoin F S ≤ { Algebra.adjoin F S with neg_mem' := fun x => (Algebra.adjoin F S).neg_mem, inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E) (h : K.toSubalgebra = Algebra.adjoin F S) :
    K = adjoin F S := by
  apply to_subalgebra_injective
  rw [h]
  refine' (adjoin_eq_algebra_adjoin _ _ _).symm
  intro x
  convert K.inv_mem
  rw [← h]
  rfl

@[elab_as_eliminator]
theorem adjoin_induction {s : Set E} {p : E → Prop} {x} (h : x ∈ adjoin F s) (Hs : ∀, ∀ x ∈ s, ∀, p x)
    (Hmap : ∀ x, p (algebraMap F E x)) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x, p x → p (-x))
    (Hinv : ∀ x, p x → p x⁻¹) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  Subfield.closure_induction h (fun x hx => Or.cases_on hx (fun ⟨x, hx⟩ => hx ▸ Hmap x) (Hs x))
    ((algebraMap F E).map_one ▸ Hmap 1) Hadd Hneg Hinv Hmul

/-- Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
--this definition of notation is courtesy of Kyle Miller on zulip
class Insert {α : Type _} (s : Set α) where
  insert : α → Set α

instance (priority := 1000) insertEmpty {α : Type _} :
    Insert (∅ : Set α) where insert := fun x => @singleton _ _ Set.hasSingleton x

instance (priority := 900) insertNonempty {α : Type _} (s : Set α) :
    Insert s where insert := fun x => HasInsert.insert x s

-- mathport name: «expr ⟮ ,⟯»
notation3:max K"⟮"(l", "* => foldr (h t => Insert.Insert t h) ∅)"⟯" => adjoin K l

section AdjoinSimple

variable (α : E)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem mem_adjoin_simple_self : α ∈ F⟮⟯ :=
  subset_adjoin F {α} (Set.mem_singleton α)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- generator of `F⟮α⟯` -/
def AdjoinSimple.gen : F⟮⟯ :=
  ⟨α, mem_adjoin_simple_self F α⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem AdjoinSimple.algebra_map_gen : algebraMap F⟮⟯ E (AdjoinSimple.gen F α) = α :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem AdjoinSimple.is_integral_gen : IsIntegral F (AdjoinSimple.gen F α) ↔ IsIntegral F α := by
  conv_rhs => rw [← adjoin_simple.algebra_map_gen F α]
  rw [is_integral_algebra_map_iff (algebraMap F⟮⟯ E).Injective]
  infer_instance

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem adjoin_simple_adjoin_simple (β : E) : F⟮⟯⟮⟯.restrictScalars F = F⟮⟯ :=
  adjoin_adjoin_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem adjoin_simple_comm (β : E) : F⟮⟯⟮⟯.restrictScalars F = F⟮⟯⟮⟯.restrictScalars F :=
  adjoin_adjoin_comm _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- TODO: develop the API for `subalgebra.is_field_of_algebraic` so it can be used here
theorem adjoin_simple_to_subalgebra_of_integral (hα : IsIntegral F α) : F⟮⟯.toSubalgebra = Algebra.adjoin F {α} := by
  apply adjoin_eq_algebra_adjoin
  intro x hx
  by_cases' x = 0
  · rw [h, inv_zero]
    exact Subalgebra.zero_mem (Algebra.adjoin F {α})
    
  let ϕ := AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly F α
  have := Fact.mk (minpoly.irreducible hα)
  suffices ϕ ⟨x, hx⟩ * (ϕ ⟨x, hx⟩)⁻¹ = 1 by
    convert Subtype.mem (ϕ.symm (ϕ ⟨x, hx⟩)⁻¹)
    refine' inv_eq_of_mul_eq_one_right _
    apply_fun ϕ.symm  at this
    rw [AlgEquiv.map_one, AlgEquiv.map_mul, AlgEquiv.symm_apply_apply] at this
    rw [← Subsemiring.coe_one, ← this, Subsemiring.coe_mul, Subtype.coe_mk]
  rw [mul_inv_cancel (mt (fun key => _) h)]
  rw [← ϕ.map_zero] at key
  change ↑(⟨x, hx⟩ : Algebra.adjoin F {α}) = _
  rw [ϕ.injective key, Subalgebra.coe_zero]

variable {F} {α}

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮⟯ ≤ K ↔ α ∈ K :=
  adjoin_le_iff.trans Set.singleton_subset_iff

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff, adjoin_le_iff]
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem adjoin_simple_eq_bot_iff : F⟮⟯ = ⊥ ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [adjoin_eq_bot_iff]
  exact Set.singleton_subset_iff

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem adjoin_zero : F⟮⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem adjoin_one : F⟮⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem adjoin_int (n : ℤ) : F⟮⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (coe_int_mem ⊥ n)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
@[simp]
theorem adjoin_nat (n : ℕ) : F⟮⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (coe_nat_mem ⊥ n)

section AdjoinDim

open FiniteDimensional Module

variable {K L : IntermediateField F E}

@[simp]
theorem dim_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ := by
  rw [← to_subalgebra_eq_iff, ← dim_eq_dim_subalgebra, Subalgebra.dim_eq_one_iff, bot_to_subalgebra]

@[simp]
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
  rw [← to_subalgebra_eq_iff, ← finrank_eq_finrank_subalgebra, Subalgebra.finrank_eq_one_iff, bot_to_subalgebra]

@[simp]
theorem dim_bot : Module.rank F (⊥ : IntermediateField F E) = 1 := by
  rw [dim_eq_one_iff]

@[simp]
theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by
  rw [finrank_eq_one_iff]

theorem dim_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans dim_eq_one_iff adjoin_eq_bot_iff

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem dim_adjoin_simple_eq_one_iff : Module.rank F F⟮⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [dim_adjoin_eq_one_iff]
  exact Set.singleton_subset_iff

theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem finrank_adjoin_simple_eq_one_iff : finrank F F⟮⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [finrank_adjoin_eq_one_iff]
  exact Set.singleton_subset_iff

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_dim_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮⟯ = 1) : (⊥ : IntermediateField F E) = ⊤ := by
  ext
  rw [iff_true_right IntermediateField.mem_top]
  exact dim_adjoin_simple_eq_one_iff.mp (h x)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem bot_eq_top_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮⟯ = 1) : (⊥ : IntermediateField F E) = ⊤ := by
  ext
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h x)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem subsingleton_of_dim_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮⟯ = 1) : Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_dim_adjoin_eq_one h)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem subsingleton_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮⟯ = 1) : Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_finrank_adjoin_le_one [FiniteDimensional F E] (h : ∀ x : E, finrank F F⟮⟯ ≤ 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by
    linarith [h x, show 0 < finrank F F⟮⟯ from finrank_pos]

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E] (h : ∀ x : E, finrank F F⟮⟯ ≤ 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

end AdjoinDim

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] {α : E}

variable {K : Type _} [Field K] [Algebra F K]

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem minpoly_gen {α : E} (h : IsIntegral F α) : minpoly F (AdjoinSimple.gen F α) = minpoly F α := by
  rw [← adjoin_simple.algebra_map_gen F α] at h
  have inj := (algebraMap F⟮⟯ E).Injective
  exact
    minpoly.eq_of_algebra_map_eq inj ((is_integral_algebra_map_iff inj).mp h) (adjoin_simple.algebra_map_gen _ _).symm

variable (F)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem aeval_gen_minpoly (α : E) : aeval (AdjoinSimple.gen F α) (minpoly F α) = 0 := by
  ext
  convert minpoly.aeval F α
  conv in aeval α => rw [← adjoin_simple.algebra_map_gen F α]
  exact IsScalarTower.algebra_map_aeval F F⟮⟯ E _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/
noncomputable def adjoinRootEquivAdjoin (h : IsIntegral F α) : AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮⟯ :=
  AlgEquiv.ofBijective (AdjoinRoot.liftHom (minpoly F α) (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α : _)
      have := Fact.mk (minpoly.irreducible h)
      constructor
      · exact RingHom.injective f
        
      · suffices F⟮⟯.toSubfield ≤ RingHom.fieldRange (F⟮⟯.toSubfield.Subtype.comp f) by
          exact fun x => Exists.cases_on (this (Subtype.mem x)) fun y hy => ⟨y, Subtype.ext hy⟩
        exact
          subfield.closure_le.mpr
            (Set.union_subset
              (fun x hx =>
                Exists.cases_on hx fun y hy =>
                  ⟨y, by
                    rw [RingHom.comp_apply, AdjoinRoot.lift_of]
                    exact hy⟩)
              (set.singleton_subset_iff.mpr
                ⟨AdjoinRoot.root (minpoly F α), by
                  rw [RingHom.comp_apply, AdjoinRoot.lift_root]
                  rfl⟩))
        )

theorem adjoin_root_equiv_adjoin_apply_root (h : IsIntegral F α) :
    adjoinRootEquivAdjoin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)

section PowerBasis

variable {L : Type _} [Field L] [Algebra K L]

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def powerBasisAux {x : L} (hx : IsIntegral K x) : Basis (Finₓ (minpoly K x).natDegree) K K⟮⟯ :=
  (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).Basis.map (adjoinRootEquivAdjoin K hx).toLinearEquiv

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
noncomputable def adjoin.powerBasis {x : L} (hx : IsIntegral K x) : PowerBasis K K⟮⟯ where
  gen := AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  Basis := powerBasisAux hx
  basis_eq_pow := fun i => by
    rw [power_basis_aux, Basis.map_apply, PowerBasis.basis_eq_pow, AlgEquiv.to_linear_equiv_apply, AlgEquiv.map_pow,
      AdjoinRoot.power_basis_gen, adjoin_root_equiv_adjoin_apply_root]

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem adjoin.finite_dimensional {x : L} (hx : IsIntegral K x) : FiniteDimensional K K⟮⟯ :=
  PowerBasis.finite_dimensional (adjoin.powerBasis hx)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem adjoin.finrank {x : L} (hx : IsIntegral K x) : FiniteDimensional.finrank K K⟮⟯ = (minpoly K x).natDegree := by
  rw [PowerBasis.finrank (adjoin.power_basis hx : _)]
  rfl

end PowerBasis

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable def algHomAdjoinIntegralEquiv (h : IsIntegral F α) :
    (F⟮⟯ →ₐ[F] K) ≃ { x // x ∈ ((minpoly F α).map (algebraMap F K)).roots } :=
  (adjoin.powerBasis h).liftEquiv'.trans
    ((Equivₓ.refl _).subtypeEquiv fun x => by
      rw [adjoin.power_basis_gen, minpoly_gen h, Equivₓ.refl_apply])

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable def fintypeOfAlgHomAdjoinIntegral (h : IsIntegral F α) : Fintype (F⟮⟯ →ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (adjoin.powerBasis h)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem card_alg_hom_adjoin_integral (h : IsIntegral F α) (h_sep : (minpoly F α).Separable)
    (h_splits : (minpoly F α).Splits (algebraMap F K)) :
    @Fintype.card (F⟮⟯ →ₐ[F] K) (fintypeOfAlgHomAdjoinIntegral F h) = (minpoly F α).natDegree := by
  rw [AlgHom.card_of_power_basis] <;>
    simp only [← adjoin.power_basis_dim, ← adjoin.power_basis_gen, ← minpoly_gen h, ← h_sep, ← h_splits]

end AdjoinIntegralElement

section Induction

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : finset E` such that
`intermediate_field.adjoin F t = S`. -/
def Fg (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F ↑t = S

theorem fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).Fg :=
  ⟨t, rfl⟩

theorem fg_def {S : IntermediateField F E} : S.Fg ↔ ∃ t : Set E, Set.Finite t ∧ adjoin F t = S :=
  Iff.symm Set.exists_finite_iff_finset

theorem fg_bot : (⊥ : IntermediateField F E).Fg :=
  ⟨∅, adjoin_empty F E⟩

theorem fg_of_fg_to_subalgebra (S : IntermediateField F E) (h : S.toSubalgebra.Fg) : S.Fg := by
  cases' h with t ht
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.Fg :=
  S.fg_of_fg_to_subalgebra S.toSubalgebra.fg_of_noetherian

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E), ∀ x ∈ S, ∀, P K → P (K⟮⟯.restrictScalars F)) : P (adjoin F ↑S) := by
  apply Finset.induction_on' S
  · exact base
    
  · intro a s h1 _ _ h4
    rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F s) a h1 h4
    

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem induction_on_adjoin_fg (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮⟯.restrictScalars F)) (K : IntermediateField F E)
    (hK : K.Fg) : P K := by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem induction_on_adjoin [fd : FiniteDimensional F E] (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮⟯.restrictScalars F)) (K : IntermediateField F E) : P K :=
  by
  let this : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  exact induction_on_adjoin_fg P base ih K K.fg_of_noetherian

end Induction

section AlgHomMkAdjoinSplits

variable (F E K : Type _) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

/-- Lifts `L → K` of `F → K` -/
def Lifts :=
  ΣL : IntermediateField F E, L →ₐ[F] K

variable {F E K}

instance : PartialOrderₓ (Lifts F E K) where
  le := fun x y => x.1 ≤ y.1 ∧ ∀ (s : x.1) (t : y.1), (s : E) = t → x.2 s = y.2 t
  le_refl := fun x => ⟨le_reflₓ x.1, fun s t hst => congr_arg x.2 (Subtype.ext hst)⟩
  le_trans := fun x y z hxy hyz =>
    ⟨le_transₓ hxy.1 hyz.1, fun s u hsu => Eq.trans (hxy.2 s ⟨s, hxy.1 s.Mem⟩ rfl) (hyz.2 ⟨s, hxy.1 s.Mem⟩ u hsu)⟩
  le_antisymm := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨hxy1, hxy2⟩ ⟨hyx1, hyx2⟩
    obtain rfl : x1 = y1 := le_antisymmₓ hxy1 hyx1
    congr
    exact AlgHom.ext fun s => hxy2 s s rfl

noncomputable instance : OrderBot (Lifts F E K) where
  bot := ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E).toAlgHom⟩
  bot_le := fun x =>
    ⟨bot_le, fun s t hst => by
      cases' intermediate_field.mem_bot.mp s.mem with u hu
      rw [show s = (algebraMap F _) u from Subtype.ext hu.symm, AlgHom.commutes]
      rw [show t = (algebraMap F _) u from Subtype.ext (Eq.trans hu hst).symm, AlgHom.commutes]⟩

noncomputable instance : Inhabited (Lifts F E K) :=
  ⟨⊥⟩

theorem Lifts.eq_of_le {x y : Lifts F E K} (hxy : x ≤ y) (s : x.1) : x.2 s = y.2 ⟨s, hxy.1 s.Mem⟩ :=
  hxy.2 s ⟨s, hxy.1 s.Mem⟩ rfl

theorem Lifts.exists_max_two {c : Set (Lifts F E K)} {x y : Lifts F E K} (hc : IsChain (· ≤ ·) c)
    (hx : x ∈ HasInsert.insert ⊥ c) (hy : y ∈ HasInsert.insert ⊥ c) :
    ∃ z : Lifts F E K, z ∈ HasInsert.insert ⊥ c ∧ x ≤ z ∧ y ≤ z := by
  cases' (hc.insert fun _ _ _ => Or.inl bot_le).Total hx hy with hxy hyx
  · exact ⟨y, hy, hxy, le_reflₓ y⟩
    
  · exact ⟨x, hx, le_reflₓ x, hyx⟩
    

theorem Lifts.exists_max_three {c : Set (Lifts F E K)} {x y z : Lifts F E K} (hc : IsChain (· ≤ ·) c)
    (hx : x ∈ HasInsert.insert ⊥ c) (hy : y ∈ HasInsert.insert ⊥ c) (hz : z ∈ HasInsert.insert ⊥ c) :
    ∃ w : Lifts F E K, w ∈ HasInsert.insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w := by
  obtain ⟨v, hv, hxv, hyv⟩ := lifts.exists_max_two hc hx hy
  obtain ⟨w, hw, hzw, hvw⟩ := lifts.exists_max_two hc hz hv
  exact ⟨w, hw, le_transₓ hxv hvw, le_transₓ hyv hvw, hzw⟩

/-- An upper bound on a chain of lifts -/
def Lifts.upperBoundIntermediateField {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) : IntermediateField F E where
  Carrier := fun s => ∃ x : Lifts F E K, x ∈ HasInsert.insert ⊥ c ∧ (s ∈ x.1 : Prop)
  zero_mem' := ⟨⊥, Set.mem_insert ⊥ c, zero_mem ⊥⟩
  one_mem' := ⟨⊥, Set.mem_insert ⊥ c, one_mem ⊥⟩
  neg_mem' := by
    rintro _ ⟨x, y, h⟩
    exact ⟨x, ⟨y, x.1.neg_mem h⟩⟩
  inv_mem' := by
    rintro _ ⟨x, y, h⟩
    exact ⟨x, ⟨y, x.1.inv_mem h⟩⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy
    exact ⟨z, hz, z.1.add_mem (hxz.1 ha) (hyz.1 hb)⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy
    exact ⟨z, hz, z.1.mul_mem (hxz.1 ha) (hyz.1 hb)⟩
  algebra_map_mem' := fun s => ⟨⊥, Set.mem_insert ⊥ c, algebra_map_mem ⊥ s⟩

/-- The lift on the upper bound on a chain of lifts -/
noncomputable def Lifts.upperBoundAlgHom {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) :
    Lifts.upperBoundIntermediateField hc →ₐ[F] K where
  toFun := fun s => (Classical.some s.Mem).2 ⟨s, (Classical.some_spec s.Mem).2⟩
  map_zero' := AlgHom.map_zero _
  map_one' := AlgHom.map_one _
  map_add' := fun s t => by
    obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
      lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
        (Classical.some_spec (s + t).Mem).1
    rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ← w.2.map_add]
    rfl
  map_mul' := fun s t => by
    obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
      lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
        (Classical.some_spec (s * t).Mem).1
    rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ← w.2.map_mul]
    rfl
  commutes' := fun _ => AlgHom.commutes _ _

/-- An upper bound on a chain of lifts -/
noncomputable def Lifts.upperBound {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) : Lifts F E K :=
  ⟨Lifts.upperBoundIntermediateField hc, Lifts.upperBoundAlgHom hc⟩

theorem Lifts.exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c) : ∃ ub, ∀, ∀ a ∈ c, ∀, a ≤ ub :=
  ⟨Lifts.upperBound hc, by
    intro x hx
    constructor
    · exact fun s hs => ⟨x, Set.mem_insert_of_mem ⊥ hx, hs⟩
      
    · intro s t hst
      change x.2 s = (Classical.some t.mem).2 ⟨t, (Classical.some_spec t.mem).2⟩
      obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc (Set.mem_insert_of_mem ⊥ hx) (Classical.some_spec t.mem).1
      rw [lifts.eq_of_le hxz, lifts.eq_of_le hyz]
      exact congr_arg z.2 (Subtype.ext hst)
      ⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- Extend a lift `x : lifts F E K` to an element `s : E` whose conjugates are all in `K` -/
noncomputable def Lifts.liftOfSplits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : Lifts F E K :=
  let h3 : IsIntegral x.1 s := is_integral_of_is_scalar_tower s h1
  let key : (minpoly x.1 s).Splits x.2.toRingHom :=
    splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero h1))
      ((splits_map_iff _ _).mpr
        (by
          convert h2
          exact RingHom.ext fun y => x.2.commutes y))
      (minpoly.dvd_map_of_is_scalar_tower _ _ _)
  ⟨x.1⟮⟯.restrictScalars F,
    (@algHomEquivSigma F x.1 (x.1⟮⟯.restrictScalars F) K _ _ _ _ _ _ _ (IntermediateField.algebra x.1⟮⟯)
          (IsScalarTower.of_algebra_map_eq fun _ => rfl)).invFun
      ⟨x.2,
        (@algHomAdjoinIntegralEquiv x.1 _ E _ _ s K _ x.2.toRingHom.toAlgebra h3).invFun
          ⟨rootOfSplits x.2.toRingHom key (ne_of_gtₓ (minpoly.degree_pos h3)), by
            simp_rw [mem_roots (map_ne_zero (minpoly.ne_zero h3)), is_root, ← eval₂_eq_eval_map]
            exact map_root_of_splits x.2.toRingHom key (ne_of_gtₓ (minpoly.degree_pos h3))⟩⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem Lifts.le_lifts_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : x ≤ x.lift_of_splits h1 h2 :=
  ⟨fun z hz => algebra_map_mem x.1⟮⟯ ⟨z, hz⟩, fun t u htu =>
    Eq.symm
      (by
        rw [← show algebraMap x.1 x.1⟮⟯ t = u from Subtype.ext htu]
        let this : Algebra x.1 K := x.2.toRingHom.toAlgebra
        exact AlgHom.commutes _ t)⟩

theorem Lifts.mem_lifts_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : s ∈ (x.lift_of_splits h1 h2).1 :=
  mem_adjoin_simple_self x.1 s

theorem Lifts.exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : ∃ y, x ≤ y ∧ s ∈ y.1 :=
  ⟨x.lift_of_splits h1 h2, x.le_lifts_of_splits h1 h2, x.mem_lifts_of_splits h1 h2⟩

theorem alg_hom_mk_adjoin_splits (hK : ∀, ∀ s ∈ S, ∀, IsIntegral F (s : E) ∧ (minpoly F s).Splits (algebraMap F K)) :
    Nonempty (adjoin F S →ₐ[F] K) := by
  obtain ⟨x : lifts F E K, hx⟩ := zorn_partial_order lifts.exists_upper_bound
  refine'
    ⟨AlgHom.mk (fun s => x.2 ⟨s, adjoin_le_iff.mpr (fun s hs => _) s.Mem⟩) x.2.map_one
        (fun s t => x.2.map_mul ⟨s, _⟩ ⟨t, _⟩) x.2.map_zero (fun s t => x.2.map_add ⟨s, _⟩ ⟨t, _⟩) x.2.commutes⟩
  rcases x.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
  rwa [hx y h1] at h2

theorem alg_hom_mk_adjoin_splits' (hS : adjoin F S = ⊤)
    (hK : ∀, ∀ x ∈ S, ∀, IsIntegral F (x : E) ∧ (minpoly F x).Splits (algebraMap F K)) : Nonempty (E →ₐ[F] K) := by
  cases' alg_hom_mk_adjoin_splits hK with ϕ
  rw [hS] at ϕ
  exact ⟨ϕ.comp top_equiv.symm.to_alg_hom⟩

end AlgHomMkAdjoinSplits

section Supremum

variable {K L : Type _} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

theorem le_sup_to_subalgebra : E1.toSubalgebra⊔E2.toSubalgebra ≤ (E1⊔E2).toSubalgebra :=
  sup_le (show E1 ≤ E1⊔E2 from le_sup_left) (show E2 ≤ E1⊔E2 from le_sup_right)

theorem sup_to_subalgebra [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] :
    (E1⊔E2).toSubalgebra = E1.toSubalgebra⊔E2.toSubalgebra := by
  let S1 := E1.to_subalgebra
  let S2 := E2.to_subalgebra
  refine'
    le_antisymmₓ
      (show _ ≤ (S1⊔S2).toIntermediateField _ from
        sup_le (show S1 ≤ _ from le_sup_left) (show S2 ≤ _ from le_sup_right))
      (le_sup_to_subalgebra E1 E2)
  suffices IsField ↥(S1⊔S2) by
    intro x hx
    by_cases' hx' : (⟨x, hx⟩ : S1⊔S2) = 0
    · rw [← Subtype.coe_mk x hx, hx', Subalgebra.coe_zero, inv_zero]
      exact (S1⊔S2).zero_mem
      
    · obtain ⟨y, h⟩ := this.mul_inv_cancel hx'
      exact (congr_arg (· ∈ S1⊔S2) <| eq_inv_of_mul_eq_one_right <| subtype.ext_iff.mp h).mp y.2
      
  exact
    is_field_of_is_integral_of_is_field'
      (is_integral_sup.mpr ⟨Algebra.is_integral_of_finite K E1, Algebra.is_integral_of_finite K E2⟩)
      (Field.to_is_field K)

instance finite_dimensional_sup [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] :
    FiniteDimensional K ↥(E1⊔E2) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1⊔E2).toSubalgebra by
    have h : FiniteDimensional K g.range.to_submodule := g.to_linear_map.finite_dimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.product_map_range, E1.range_val, E2.range_val, sup_to_subalgebra]

instance IntermediateField.finite_dimensional_supr_of_finite {ι : Type _} {t : ι → IntermediateField K L} [h : Finite ι]
    [∀ i, FiniteDimensional K (t i)] : FiniteDimensional K (⨆ i, t i : IntermediateField K L) := by
  rw [← supr_univ]
  let P : Set ι → Prop := fun s => FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L)
  change P Set.Univ
  apply Set.Finite.induction_on
  · exact Set.finite_univ
    
  all_goals
    dsimp' only [← P]
  · rw [supr_emptyset]
    exact (IntermediateField.botEquiv K L).symm.toLinearEquiv.FiniteDimensional
    
  · intro _ s _ _ hs
    rw [supr_insert]
    exact IntermediateField.finite_dimensional_sup _ _
    

end Supremum

end IntermediateField

section PowerBasis

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

namespace PowerBasis

open IntermediateField

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- `pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable def equivAdjoinSimple (pb : PowerBasis K L) : K⟮⟯ ≃ₐ[K] L :=
  (adjoin.powerBasis pb.is_integral_gen).equivOfMinpoly pb
    (minpoly.eq_of_algebra_map_eq (algebraMap K⟮⟯ L).Injective (adjoin.powerBasis pb.is_integral_gen).is_integral_gen
      (by
        rw [adjoin.power_basis_gen, adjoin_simple.algebra_map_gen]))

@[simp]
theorem equiv_adjoin_simple_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple (aeval (AdjoinSimple.gen K pb.gen) f) = aeval pb.gen f :=
  equiv_of_minpoly_aeval _ pb _ f

@[simp]
theorem equiv_adjoin_simple_gen (pb : PowerBasis K L) : pb.equivAdjoinSimple (AdjoinSimple.gen K pb.gen) = pb.gen :=
  equiv_of_minpoly_gen _ pb _

@[simp]
theorem equiv_adjoin_simple_symm_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple.symm (aeval pb.gen f) = aeval (AdjoinSimple.gen K pb.gen) f := by
  rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_aeval, adjoin.power_basis_gen]

@[simp]
theorem equiv_adjoin_simple_symm_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple.symm pb.gen = AdjoinSimple.gen K pb.gen := by
  rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_gen, adjoin.power_basis_gen]

end PowerBasis

end PowerBasis

