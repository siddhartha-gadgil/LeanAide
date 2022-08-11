/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.FieldTheory.Subfield
import Mathbin.FieldTheory.Tower
import Mathbin.RingTheory.Algebraic

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `algebra K L`.
This file defines the type of fields in between `K` and `L`, `intermediate_field K L`.
An `intermediate_field K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `subfield L` and a `subalgebra K L`.

## Main definitions

* `intermediate_field K L` : the type of intermediate fields between `K` and `L`.
* `subalgebra.to_intermediate_field`: turns a subalgebra closed under `⁻¹`
  into an intermediate field
* `subfield.to_intermediate_field`: turns a subfield containing the image of `K`
  into an intermediate field
* `intermediate_field.map`: map an intermediate field along an `alg_hom`
* `intermediate_field.restrict_scalars`: restrict the scalars of an intermediate field to a smaller
  field in a tower of fields.

## Implementation notes

Intermediate fields are defined with a structure extending `subfield` and `subalgebra`.
A `subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/


open FiniteDimensional Polynomial

open BigOperators Polynomial

variable (K L : Type _) [Field K] [Field L] [Algebra K L]

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure IntermediateField extends Subalgebra K L where
  neg_mem' : ∀, ∀ x ∈ carrier, ∀, -x ∈ carrier
  inv_mem' : ∀, ∀ x ∈ carrier, ∀, x⁻¹ ∈ carrier

/-- Reinterpret an `intermediate_field` as a `subalgebra`. -/
add_decl_doc IntermediateField.toSubalgebra

variable {K L} (S : IntermediateField K L)

namespace IntermediateField

/-- Reinterpret an `intermediate_field` as a `subfield`. -/
def toSubfield : Subfield L :=
  { S.toSubalgebra, S with }

instance : SetLike (IntermediateField K L) L :=
  ⟨fun S => S.toSubalgebra.Carrier, by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨h⟩
    congr⟩

instance : SubfieldClass (IntermediateField K L) L where
  add_mem := fun s => s.add_mem'
  zero_mem := fun s => s.zero_mem'
  neg_mem := neg_mem'
  mul_mem := fun s => s.mul_mem'
  one_mem := fun s => s.one_mem'
  inv_mem := inv_mem'

@[simp]
theorem mem_carrier {s : IntermediateField K L} {x : L} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext]
theorem ext {S T : IntermediateField K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem coe_to_subalgebra : (S.toSubalgebra : Set L) = S :=
  rfl

@[simp]
theorem coe_to_subfield : (S.toSubfield : Set L) = S :=
  rfl

@[simp]
theorem mem_mk (s : Set L) (hK : ∀ x, algebraMap K L x ∈ s) (ho hm hz ha hn hi) (x : L) :
    x ∈ IntermediateField.mk (Subalgebra.mk s ho hm hz ha hK) hn hi ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_to_subalgebra (s : IntermediateField K L) (x : L) : x ∈ s.toSubalgebra ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_to_subfield (s : IntermediateField K L) (x : L) : x ∈ s.toSubfield ↔ x ∈ s :=
  Iff.rfl

/-- Copy of an intermediate field with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : IntermediateField K L where
  toSubalgebra := S.toSubalgebra.copy s (hs : s = S.toSubalgebra.Carrier)
  neg_mem' :=
    have hs' : (S.toSubalgebra.copy s hs).Carrier = S.toSubalgebra.Carrier := hs
    hs'.symm ▸ S.neg_mem'
  inv_mem' :=
    have hs' : (S.toSubalgebra.copy s hs).Carrier = S.toSubalgebra.Carrier := hs
    hs'.symm ▸ S.inv_mem'

@[simp]
theorem coe_copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : (S.copy s hs : Set L) = s :=
  rfl

theorem copy_eq (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section InheritedLemmas

/-! ### Lemmas inherited from more general structures

The declarations in this section derive from the fact that an `intermediate_field` is also a
subalgebra or subfield. Their use should be replaceable with the corresponding lemma from a
subobject class.
-/


/-- An intermediate field contains the image of the smaller field. -/
theorem algebra_map_mem (x : K) : algebraMap K L x ∈ S :=
  S.algebra_map_mem' x

/-- An intermediate field is closed under scalar multiplication. -/
theorem smul_mem {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S :=
  S.toSubalgebra.smul_mem

/-- An intermediate field contains the ring's 1. -/
protected theorem one_mem : (1 : L) ∈ S :=
  one_mem S

/-- An intermediate field contains the ring's 0. -/
protected theorem zero_mem : (0 : L) ∈ S :=
  zero_mem S

/-- An intermediate field is closed under multiplication. -/
protected theorem mul_mem {x y : L} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem

/-- An intermediate field is closed under addition. -/
protected theorem add_mem {x y : L} : x ∈ S → y ∈ S → x + y ∈ S :=
  add_mem

/-- An intermediate field is closed under subtraction -/
protected theorem sub_mem {x y : L} : x ∈ S → y ∈ S → x - y ∈ S :=
  sub_mem

/-- An intermediate field is closed under negation. -/
protected theorem neg_mem {x : L} : x ∈ S → -x ∈ S :=
  neg_mem

/-- An intermediate field is closed under inverses. -/
protected theorem inv_mem {x : L} : x ∈ S → x⁻¹ ∈ S :=
  inv_mem

/-- An intermediate field is closed under division. -/
protected theorem div_mem {x y : L} : x ∈ S → y ∈ S → x / y ∈ S :=
  div_mem

/-- Product of a list of elements in an intermediate_field is in the intermediate_field. -/
protected theorem list_prod_mem {l : List L} : (∀, ∀ x ∈ l, ∀, x ∈ S) → l.Prod ∈ S :=
  list_prod_mem

/-- Sum of a list of elements in an intermediate field is in the intermediate_field. -/
protected theorem list_sum_mem {l : List L} : (∀, ∀ x ∈ l, ∀, x ∈ S) → l.Sum ∈ S :=
  list_sum_mem

/-- Product of a multiset of elements in an intermediate field is in the intermediate_field. -/
protected theorem multiset_prod_mem (m : Multiset L) : (∀, ∀ a ∈ m, ∀, a ∈ S) → m.Prod ∈ S :=
  multiset_prod_mem m

/-- Sum of a multiset of elements in a `intermediate_field` is in the `intermediate_field`. -/
protected theorem multiset_sum_mem (m : Multiset L) : (∀, ∀ a ∈ m, ∀, a ∈ S) → m.Sum ∈ S :=
  multiset_sum_mem m

/-- Product of elements of an intermediate field indexed by a `finset` is in the intermediate_field.
-/
protected theorem prod_mem {ι : Type _} {t : Finset ι} {f : ι → L} (h : ∀, ∀ c ∈ t, ∀, f c ∈ S) : (∏ i in t, f i) ∈ S :=
  prod_mem h

/-- Sum of elements in a `intermediate_field` indexed by a `finset` is in the `intermediate_field`.
-/
protected theorem sum_mem {ι : Type _} {t : Finset ι} {f : ι → L} (h : ∀, ∀ c ∈ t, ∀, f c ∈ S) : (∑ i in t, f i) ∈ S :=
  sum_mem h

protected theorem pow_mem {x : L} (hx : x ∈ S) (n : ℤ) : x ^ n ∈ S :=
  zpow_mem hx n

protected theorem zsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n

protected theorem coe_int_mem (n : ℤ) : (n : L) ∈ S :=
  coe_int_mem S n

protected theorem coe_add (x y : S) : (↑(x + y) : L) = ↑x + ↑y :=
  rfl

protected theorem coe_neg (x : S) : (↑(-x) : L) = -↑x :=
  rfl

protected theorem coe_mul (x y : S) : (↑(x * y) : L) = ↑x * ↑y :=
  rfl

protected theorem coe_inv (x : S) : (↑x⁻¹ : L) = (↑x)⁻¹ :=
  rfl

protected theorem coe_zero : ((0 : S) : L) = 0 :=
  rfl

protected theorem coe_one : ((1 : S) : L) = 1 :=
  rfl

protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : L) = ↑x ^ n :=
  SubmonoidClass.coe_pow x n

end InheritedLemmas

theorem coe_nat_mem (n : ℕ) : (n : L) ∈ S := by
  simpa using coe_int_mem S n

end IntermediateField

/-- Turn a subalgebra closed under inverses into an intermediate field -/
def Subalgebra.toIntermediateField (S : Subalgebra K L) (inv_mem : ∀, ∀ x ∈ S, ∀, x⁻¹ ∈ S) : IntermediateField K L :=
  { S with neg_mem' := fun x => S.neg_mem, inv_mem' := inv_mem }

@[simp]
theorem to_subalgebra_to_intermediate_field (S : Subalgebra K L) (inv_mem : ∀, ∀ x ∈ S, ∀, x⁻¹ ∈ S) :
    (S.toIntermediateField inv_mem).toSubalgebra = S := by
  ext
  rfl

@[simp]
theorem to_intermediate_field_to_subalgebra (S : IntermediateField K L)
    (inv_mem : ∀, ∀ x ∈ S.toSubalgebra, ∀, x⁻¹ ∈ S) : S.toSubalgebra.toIntermediateField inv_mem = S := by
  ext
  rfl

/-- Turn a subfield of `L` containing the image of `K` into an intermediate field -/
def Subfield.toIntermediateField (S : Subfield L) (algebra_map_mem : ∀ x, algebraMap K L x ∈ S) :
    IntermediateField K L :=
  { S with algebra_map_mem' := algebra_map_mem }

namespace IntermediateField

/-- An intermediate field inherits a field structure -/
instance toField : Field S :=
  S.toSubfield.toField

@[simp, norm_cast]
theorem coe_sum {ι : Type _} [Fintype ι] (f : ι → S) : (↑(∑ i, f i) : L) = ∑ i, (f i : L) := by
  classical
  induction' Finset.univ using Finset.induction_on with i s hi H
  · simp
    
  · rw [Finset.sum_insert hi, AddMemClass.coe_add, H, Finset.sum_insert hi]
    

@[simp, norm_cast]
theorem coe_prod {ι : Type _} [Fintype ι] (f : ι → S) : (↑(∏ i, f i) : L) = ∏ i, (f i : L) := by
  classical
  induction' Finset.univ using Finset.induction_on with i s hi H
  · simp
    
  · rw [Finset.prod_insert hi, MulMemClass.coe_mul, H, Finset.prod_insert hi]
    

/-! `intermediate_field`s inherit structure from their `subalgebra` coercions. -/


instance module' {R} [Semiringₓ R] [HasSmul R K] [Module R L] [IsScalarTower R K L] : Module R S :=
  S.toSubalgebra.module'

instance module : Module K S :=
  S.toSubalgebra.Module

instance is_scalar_tower {R} [Semiringₓ R] [HasSmul R K] [Module R L] [IsScalarTower R K L] : IsScalarTower R K S :=
  S.toSubalgebra.IsScalarTower

@[simp]
theorem coe_smul {R} [Semiringₓ R] [HasSmul R K] [Module R L] [IsScalarTower R K L] (r : R) (x : S) :
    ↑(r • x) = (r • x : L) :=
  rfl

instance algebra' {K'} [CommSemiringₓ K'] [HasSmul K' K] [Algebra K' L] [IsScalarTower K' K L] : Algebra K' S :=
  S.toSubalgebra.algebra'

instance algebra : Algebra K S :=
  S.toSubalgebra.Algebra

instance toAlgebra {R : Type _} [Semiringₓ R] [Algebra L R] : Algebra S R :=
  S.toSubalgebra.toAlgebra

instance is_scalar_tower_bot {R : Type _} [Semiringₓ R] [Algebra L R] : IsScalarTower S L R :=
  IsScalarTower.subalgebra _ _ _ S.toSubalgebra

instance is_scalar_tower_mid {R : Type _} [Semiringₓ R] [Algebra L R] [Algebra K R] [IsScalarTower K L R] :
    IsScalarTower K S R :=
  IsScalarTower.subalgebra' _ _ _ S.toSubalgebra

/-- Specialize `is_scalar_tower_mid` to the common case where the top field is `L` -/
instance is_scalar_tower_mid' : IsScalarTower K S L :=
  S.is_scalar_tower_mid

variable {L' : Type _} [Field L'] [Algebra K L']

/-- If `f : L →+* L'` fixes `K`, `S.map f` is the intermediate field between `L'` and `K`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map (f : L →ₐ[K] L') : IntermediateField K L' :=
  { S.toSubalgebra.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, S.inv_mem hx, f.map_inv x⟩,
    neg_mem' := fun x hx => (S.toSubalgebra.map f).neg_mem hx }

theorem map_map {K L₁ L₂ L₃ : Type _} [Field K] [Field L₁] [Algebra K L₁] [Field L₂] [Algebra K L₂] [Field L₃]
    [Algebra K L₃] (E : IntermediateField K L₁) (f : L₁ →ₐ[K] L₂) (g : L₂ →ₐ[K] L₃) :
    (E.map f).map g = E.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

/-- Given an equivalence `e : L ≃ₐ[K] L'` of `K`-field extensions and an intermediate
field `E` of `L/K`, `intermediate_field_equiv_map e E` is the induced equivalence
between `E` and `E.map e` -/
def intermediateFieldMap (e : L ≃ₐ[K] L') (E : IntermediateField K L) : E ≃ₐ[K] E.map e.toAlgHom :=
  e.subalgebraMap E.toSubalgebra

/- We manually add these two simp lemmas because `@[simps]` before `intermediate_field_map`
  led to a timeout. -/
@[simp]
theorem intermediate_field_map_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L) (a : E) :
    ↑(intermediateFieldMap e E a) = e a :=
  rfl

@[simp]
theorem intermediate_field_map_symm_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L) (a : E.map e.toAlgHom) :
    ↑((intermediateFieldMap e E).symm a) = e.symm a :=
  rfl

/-- The embedding from an intermediate field of `L / K` to `L`. -/
def val : S →ₐ[K] L :=
  S.toSubalgebra.val

@[simp]
theorem coe_val : ⇑S.val = coe :=
  rfl

@[simp]
theorem val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x :=
  rfl

theorem range_val : S.val.range = S.toSubalgebra :=
  S.toSubalgebra.range_val

theorem aeval_coe {R : Type _} [CommRingₓ R] [Algebra R K] [Algebra R L] [IsScalarTower R K L] (x : S) (P : R[X]) :
    aeval (x : L) P = aeval x P := by
  refine' Polynomial.induction_on' P (fun f g hf hg => _) fun n r => _
  · rw [aeval_add, aeval_add, AddMemClass.coe_add, hf, hg]
    
  · simp only [← MulMemClass.coe_mul, ← aeval_monomial, ← SubmonoidClass.coe_pow, ← mul_eq_mul_right_iff]
    left
    rfl
    

theorem coe_is_integral_iff {R : Type _} [CommRingₓ R] [Algebra R K] [Algebra R L] [IsScalarTower R K L] {x : S} :
    IsIntegral R (x : L) ↔ IsIntegral R x := by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨P, hPmo, hProot⟩ := h
    refine' ⟨P, hPmo, (injective_iff_map_eq_zero _).1 (algebraMap (↥S) L).Injective _ _⟩
    let this : IsScalarTower R S L := IsScalarTower.of_algebra_map_eq (congr_fun rfl)
    rwa [eval₂_eq_eval_map, ← eval₂_at_apply, eval₂_eq_eval_map, Polynomial.map_map, ← IsScalarTower.algebra_map_eq, ←
      eval₂_eq_eval_map]
    
  · obtain ⟨P, hPmo, hProot⟩ := h
    refine' ⟨P, hPmo, _⟩
    rw [← aeval_def, aeval_coe, aeval_def, hProot, AddSubmonoidClass.coe_zero]
    

/-- The map `E → F` when `E` is an intermediate field contained in the intermediate field `F`.

This is the intermediate field version of `subalgebra.inclusion`. -/
def inclusion {E F : IntermediateField K L} (hEF : E ≤ F) : E →ₐ[K] F :=
  Subalgebra.inclusion hEF

theorem inclusion_injective {E F : IntermediateField K L} (hEF : E ≤ F) : Function.Injective (inclusion hEF) :=
  Subalgebra.inclusion_injective hEF

@[simp]
theorem inclusion_self {E : IntermediateField K L} : inclusion (le_reflₓ E) = AlgHom.id K E :=
  Subalgebra.inclusion_self

@[simp]
theorem inclusion_inclusion {E F G : IntermediateField K L} (hEF : E ≤ F) (hFG : F ≤ G) (x : E) :
    inclusion hFG (inclusion hEF x) = inclusion (le_transₓ hEF hFG) x :=
  Subalgebra.inclusion_inclusion hEF hFG x

@[simp]
theorem coe_inclusion {E F : IntermediateField K L} (hEF : E ≤ F) (e : E) : (inclusion hEF e : L) = e :=
  rfl

variable {S}

theorem to_subalgebra_injective {S S' : IntermediateField K L} (h : S.toSubalgebra = S'.toSubalgebra) : S = S' := by
  ext
  rw [← mem_to_subalgebra, ← mem_to_subalgebra, h]

variable (S)

theorem set_range_subset : Set.Range (algebraMap K L) ⊆ S :=
  S.toSubalgebra.range_subset

theorem field_range_le : (algebraMap K L).fieldRange ≤ S.toSubfield := fun x hx =>
  S.toSubalgebra.range_subset
    (by
      rwa [Set.mem_range, ← RingHom.mem_field_range])

@[simp]
theorem to_subalgebra_le_to_subalgebra {S S' : IntermediateField K L} : S.toSubalgebra ≤ S'.toSubalgebra ↔ S ≤ S' :=
  Iff.rfl

@[simp]
theorem to_subalgebra_lt_to_subalgebra {S S' : IntermediateField K L} : S.toSubalgebra < S'.toSubalgebra ↔ S < S' :=
  Iff.rfl

variable {S}

section Tower

/-- Lift an intermediate_field of an intermediate_field -/
def lift {F : IntermediateField K L} (E : IntermediateField K F) : IntermediateField K L :=
  map E (val F)

instance hasLift {F : IntermediateField K L} : HasLiftT (IntermediateField K F) (IntermediateField K L) :=
  ⟨lift⟩

section RestrictScalars

variable (K) [Algebra L' L] [IsScalarTower K L' L]

/-- Given a tower `L / ↥E / L' / K` of field extensions, where `E` is an `L'`-intermediate field of
`L`, reinterpret `E` as a `K`-intermediate field of `L`. -/
def restrictScalars (E : IntermediateField L' L) : IntermediateField K L :=
  { E.toSubfield, E.toSubalgebra.restrictScalars K with Carrier := E.Carrier }

@[simp]
theorem coe_restrict_scalars {E : IntermediateField L' L} : (restrictScalars K E : Set L) = (E : Set L) :=
  rfl

@[simp]
theorem restrict_scalars_to_subalgebra {E : IntermediateField L' L} :
    (E.restrictScalars K).toSubalgebra = E.toSubalgebra.restrictScalars K :=
  SetLike.coe_injective rfl

@[simp]
theorem restrict_scalars_to_subfield {E : IntermediateField L' L} : (E.restrictScalars K).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl

@[simp]
theorem mem_restrict_scalars {E : IntermediateField L' L} {x : L} : x ∈ restrictScalars K E ↔ x ∈ E :=
  Iff.rfl

theorem restrict_scalars_injective :
    Function.Injective (restrictScalars K : IntermediateField L' L → IntermediateField K L) := fun U V H =>
  ext fun x => by
    rw [← mem_restrict_scalars K, H, mem_restrict_scalars]

end RestrictScalars

/-- This was formerly an instance called `lift2_alg`, but an instance above already provides it. -/
example {F : IntermediateField K L} {E : IntermediateField F L} : Algebra K E := by
  infer_instance

end Tower

section FiniteDimensional

variable (F E : IntermediateField K L)

instance finite_dimensional_left [FiniteDimensional K L] : FiniteDimensional K F :=
  left K F L

instance finite_dimensional_right [FiniteDimensional K L] : FiniteDimensional F L :=
  right K F L

@[simp]
theorem dim_eq_dim_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F :=
  rfl

@[simp]
theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
  rfl

variable {F} {E}

@[simp]
theorem to_subalgebra_eq_iff : F.toSubalgebra = E.toSubalgebra ↔ F = E := by
  rw [SetLike.ext_iff, SetLike.ext'_iff, Set.ext_iff]
  rfl

theorem eq_of_le_of_finrank_le [FiniteDimensional K L] (h_le : F ≤ E) (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  to_subalgebra_injective <| Subalgebra.to_submodule_injective <| eq_of_le_of_finrank_le h_le h_finrank

theorem eq_of_le_of_finrank_eq [FiniteDimensional K L] (h_le : F ≤ E) (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.Ge

theorem eq_of_le_of_finrank_le' [FiniteDimensional K L] (h_le : F ≤ E) (h_finrank : finrank F L ≤ finrank E L) :
    F = E := by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith

theorem eq_of_le_of_finrank_eq' [FiniteDimensional K L] (h_le : F ≤ E) (h_finrank : finrank F L = finrank E L) :
    F = E :=
  eq_of_le_of_finrank_le' h_le h_finrank.le

end FiniteDimensional

end IntermediateField

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.  -/
def subalgebraEquivIntermediateField (alg : Algebra.IsAlgebraic K L) : Subalgebra K L ≃o IntermediateField K L where
  toFun := fun S => S.toIntermediateField fun x hx => S.inv_mem_of_algebraic (alg (⟨x, hx⟩ : S))
  invFun := fun S => S.toSubalgebra
  left_inv := fun S => to_subalgebra_to_intermediate_field _ _
  right_inv := fun S => to_intermediate_field_to_subalgebra _ _
  map_rel_iff' := fun S S' => Iff.rfl

@[simp]
theorem mem_subalgebra_equiv_intermediate_field (alg : Algebra.IsAlgebraic K L) {S : Subalgebra K L} {x : L} :
    x ∈ subalgebraEquivIntermediateField alg S ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_subalgebra_equiv_intermediate_field_symm (alg : Algebra.IsAlgebraic K L) {S : IntermediateField K L}
    {x : L} : x ∈ (subalgebraEquivIntermediateField alg).symm S ↔ x ∈ S :=
  Iff.rfl

