/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.LinearAlgebra.Prod
import Mathbin.SetTheory.Cardinal.Basic

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `linear_independent R v` as `ker (finsupp.total ι M R v) = ⊥`. Here `finsupp.total` is the
linear map sending a function `f : ι →₀ R` with finite support to the linear combination of vectors
from `v` with these coefficients. Then we prove that several other statements are equivalent to this
one, including injectivity of `finsupp.total ι M R v` and some versions with explicitly written
linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `linear_independent R v` states that the elements of the family `v` are linearly independent.

* `linear_independent.repr hv x` returns the linear combination representing `x : span R (range v)`
on the linearly independent vectors `v`, given `hv : linear_independent R v`
(using classical choice). `linear_independent.repr hv` is provided as a linear map.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `fintype.linear_independent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : finset ι`;
* `linear_independent_empty_type`: a family indexed by an empty type is linearly independent;
* `linear_independent_unique_iff`: if `ι` is a singleton, then `linear_independent K v` is
  equivalent to `v default ≠ 0`;
* linear_independent_option`, `linear_independent_sum`, `linear_independent_fin_cons`,
  `linear_independent_fin_succ`: type-specific tests for linear independence of families of vector
  fields;
* `linear_independent_insert`, `linear_independent_union`, `linear_independent_pair`,
  `linear_independent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `linear_independent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent.

If you want to use sets, use the family `(λ x, x : s → M)` given a set `s : set M`. The lemmas
`linear_independent.to_subtype_range` and `linear_independent.of_subtype_range` connect those two
worlds.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/


noncomputable section

open Function Set Submodule

open Classical BigOperators Cardinal

universe u

variable {ι : Type _} {ι' : Type _} {R : Type _} {K : Type _}

variable {M : Type _} {M' M'' : Type _} {V : Type u} {V' : Type _}

section Module

variable {v : ι → M}

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M'] [AddCommMonoidₓ M'']

variable [Module R M] [Module R M'] [Module R M'']

variable {a b : R} {x y : M}

variable (R) (v)

/-- `linear_independent R v` states the family of vectors `v` is linearly independent over `R`. -/
def LinearIndependent : Prop :=
  (Finsupp.total ι M R v).ker = ⊥

variable {R} {v}

theorem linear_independent_iff : LinearIndependent R v ↔ ∀ l, Finsupp.total ι M R v l = 0 → l = 0 := by
  simp [← LinearIndependent, ← LinearMap.ker_eq_bot']

theorem linear_independent_iff' :
    LinearIndependent R v ↔ ∀ s : Finset ι, ∀ g : ι → R, (∑ i in s, g i • v i) = 0 → ∀, ∀ i ∈ s, ∀, g i = 0 :=
  linear_independent_iff.trans
    ⟨fun hf s g hg i his =>
      have h :=
        hf (∑ i in s, Finsupp.single i (g i)) <| by
          simpa only [← LinearMap.map_sum, ← Finsupp.total_single] using hg
      calc
        g i = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (g i)) := by
          rw [Finsupp.lapply_apply, Finsupp.single_eq_same]
        _ = ∑ j in s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (g j)) :=
          Eq.symm <|
            Finset.sum_eq_single i
              (fun j hjs hji => by
                rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hji])
              fun hnis => hnis.elim his
        _ = (∑ j in s, Finsupp.single j (g j)) i := (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R).map_sum.symm
        _ = 0 := Finsupp.ext_iff.1 h i
        ,
      fun hf l hl =>
      Finsupp.ext fun i => Classical.by_contradiction fun hni => hni <| hf _ _ hl _ <| Finsupp.mem_support_iff.2 hni⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » s)
theorem linear_independent_iff'' :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (g : ι → R) (hg : ∀ (i) (_ : i ∉ s), g i = 0), (∑ i in s, g i • v i) = 0 → ∀ i, g i = 0 :=
  linear_independent_iff'.trans
    ⟨fun H s g hg hv i => if his : i ∈ s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert
        H s (fun j => if j ∈ s then g j else 0) (fun j hj => if_neg hj)
          (by
            simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg])
          i
      exact (if_pos hi).symm⟩

theorem not_linear_independent_iff :
    ¬LinearIndependent R v ↔ ∃ s : Finset ι, ∃ g : ι → R, (∑ i in s, g i • v i) = 0 ∧ ∃ i ∈ s, g i ≠ 0 := by
  rw [linear_independent_iff']
  simp only [← exists_prop, ← not_forall]

theorem Fintype.linear_independent_iff [Fintype ι] :
    LinearIndependent R v ↔ ∀ g : ι → R, (∑ i, g i • v i) = 0 → ∀ i, g i = 0 := by
  refine'
    ⟨fun H g => by
      simpa using linear_independent_iff'.1 H Finset.univ g, fun H =>
      linear_independent_iff''.2 fun s g hg hs i => H _ _ _⟩
  rw [← hs]
  refine' (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => _).symm
  rw [hg i hi, zero_smul]

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel. -/
theorem Fintype.linear_independent_iff' [Fintype ι] :
    LinearIndependent R v ↔ (LinearMap.lsum R (fun i : ι => R) ℕ fun i => LinearMap.id.smul_right (v i)).ker = ⊥ := by
  simp [← Fintype.linear_independent_iff, ← LinearMap.ker_eq_bot', ← funext_iff] <;> skip

theorem Fintype.not_linear_independent_iff [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ g : ι → R, (∑ i, g i • v i) = 0 ∧ ∃ i, g i ≠ 0 := by
  simpa using not_iff_not.2 Fintype.linear_independent_iff

theorem linear_independent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  linear_independent_iff.mpr fun v hv => Subsingleton.elimₓ v 0

theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) : v i ≠ 0 := fun h =>
  @zero_ne_one R _ _ <|
    Eq.symm
      (by
        suffices (Finsupp.single i 1 : ι →₀ R) i = 0 by
          simpa
        rw [linear_independent_iff.1 hv (Finsupp.single i 1)]
        · simp
          
        · simp [← h]
          )

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' → ι) (hf : Injective f) :
    LinearIndependent R (v ∘ f) := by
  rw [linear_independent_iff, Finsupp.total_comp]
  intro l hl
  have h_map_domain : ∀ x, (Finsupp.mapDomain f l) (f x) = 0 := by
    rw [linear_independent_iff.1 h (Finsupp.mapDomain f l) hl] <;> simp
  ext x
  convert h_map_domain x
  rw [Finsupp.map_domain_apply hf]

theorem LinearIndependent.coe_range (i : LinearIndependent R v) : LinearIndependent R (coe : Range v → M) := by
  simpa using i.comp _ (range_splitting_injective v)

/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `linear_independent.map'` for a special case assuming `ker f = ⊥`. -/
theorem LinearIndependent.map (hv : LinearIndependent R v) {f : M →ₗ[R] M'}
    (hf_inj : Disjoint (span R (Range v)) f.ker) : LinearIndependent R (f ∘ v) := by
  rw [Disjoint, ← Set.image_univ, Finsupp.span_image_eq_map_total, map_inf_eq_map_inf_comap, map_le_iff_le_comap,
    comap_bot, Finsupp.supported_univ, top_inf_eq] at hf_inj
  unfold LinearIndependent  at hv⊢
  rw [hv, le_bot_iff] at hf_inj
  have : Inhabited M := ⟨0⟩
  rw [Finsupp.total_comp, @Finsupp.lmap_domain_total _ _ R _ _ _ _ _ _ _ _ _ _ f, LinearMap.ker_comp, hf_inj]
  exact fun _ => rfl

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `linear_independent.map` for a more general statement. -/
theorem LinearIndependent.map' (hv : LinearIndependent R v) (f : M →ₗ[R] M') (hf_inj : f.ker = ⊥) :
    LinearIndependent R (f ∘ v) :=
  hv.map <| by
    simp [← hf_inj]

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
theorem LinearIndependent.of_comp (f : M →ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v :=
  linear_independent_iff'.2 fun s g hg i his =>
    have : (∑ i : ι in s, g i • f (v i)) = 0 := by
      simp_rw [← f.map_smul, ← f.map_sum, hg, f.map_zero]
    linear_independent_iff'.1 hfv s g this i his

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected theorem LinearMap.linear_independent_iff (f : M →ₗ[R] M') (hf_inj : f.ker = ⊥) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  ⟨fun h => h.of_comp f, fun h =>
    h.map <| by
      simp only [← hf_inj, ← disjoint_bot_right]⟩

@[nontriviality]
theorem linear_independent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linear_independent_iff.2 fun l hl => Subsingleton.elimₓ _ _

theorem linear_independent_equiv (e : ι ≃ ι') {f : ι' → M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h => Function.comp.right_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.Injective, fun h => h.comp _ e.Injective⟩

theorem linear_independent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
    LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linear_independent_equiv e

theorem linear_independent_subtype_range {ι} {f : ι → M} (hf : Injective f) :
    LinearIndependent R (coe : Range f → M) ↔ LinearIndependent R f :=
  Iff.symm <| linear_independent_equiv' (Equivₓ.ofInjective f hf) rfl

alias linear_independent_subtype_range ↔ LinearIndependent.of_subtype_range _

theorem linear_independent_image {ι} {s : Set ι} {f : ι → M} (hf : Set.InjOn f s) :
    (LinearIndependent R fun x : s => f x) ↔ LinearIndependent R fun x : f '' s => (x : M) :=
  linear_independent_equiv' (Equivₓ.Set.imageOfInjOn _ _ hf) rfl

theorem linear_independent_span (hs : LinearIndependent R v) :
    @LinearIndependent ι R (span R (Range v)) (fun i : ι => ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ :=
  LinearIndependent.of_comp (span R (Range v)).Subtype hs

/-- See `linear_independent.fin_cons` for a family of elements in a vector space. -/
theorem LinearIndependent.fin_cons' {m : ℕ} (x : M) (v : Finₓ m → M) (hli : LinearIndependent R v)
    (x_ortho : ∀ (c : R) (y : Submodule.span R (Set.Range v)), c • x + y = (0 : M) → c = 0) :
    LinearIndependent R (Finₓ.cons x v : Finₓ m.succ → M) := by
  rw [Fintype.linear_independent_iff] at hli⊢
  rintro g total_eq j
  simp_rw [Finₓ.sum_univ_succ, Finₓ.cons_zero, Finₓ.cons_succ] at total_eq
  have : g 0 = 0 := by
    refine' x_ortho (g 0) ⟨∑ i : Finₓ m, g i.succ • v i, _⟩ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this, zero_smul, zero_addₓ] at total_eq
  exact Finₓ.cases this (hli _ total_eq) j

/-- A set of linearly independent vectors in a module `M` over a semiring `K` is also linearly
independent over a subring `R` of `K`.
The implementation uses minimal assumptions about the relationship between `R`, `K` and `M`.
The version where `K` is an `R`-algebra is `linear_independent.restrict_scalars_algebras`.
 -/
theorem LinearIndependent.restrict_scalars [Semiringₓ K] [SmulWithZero R K] [Module K M] [IsScalarTower R K M]
    (hinj : Function.Injective fun r : R => r • (1 : K)) (li : LinearIndependent K v) : LinearIndependent R v := by
  refine' linear_independent_iff'.mpr fun s g hg i hi => hinj (Eq.trans _ (zero_smul _ _).symm)
  refine' (linear_independent_iff'.mp li : _) _ _ _ i hi
  simp_rw [smul_assoc, one_smul]
  exact hg

/-- Every finite subset of a linearly independent set is linearly independent. -/
theorem linear_independent_finset_map_embedding_subtype (s : Set M) (li : LinearIndependent R (coe : s → M))
    (t : Finset s) : LinearIndependent R (coe : Finset.map (Embedding.subtype s) t → M) := by
  let f : t.map (embedding.subtype s) → s := fun x =>
    ⟨x.1, by
      obtain ⟨x, h⟩ := x
      rw [Finset.mem_map] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp only [← Subtype.coe_prop, ← embedding.coe_subtype]⟩
  convert LinearIndependent.comp li f _
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [Finset.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  simp only [← imp_self, ← Subtype.mk_eq_mk]

/-- If every finite set of linearly independent vectors has cardinality at most `n`,
then the same is true for arbitrary sets of linearly independent vectors.
-/
theorem linear_independent_bounded_of_finset_linear_independent_bounded {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    ∀ s : Set M, LinearIndependent R (coe : s → M) → # s ≤ n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (embedding.subtype s)]
  apply H
  apply linear_independent_finset_map_embedding_subtype _ li

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/


theorem linear_independent_comp_subtype {s : Set ι} :
    LinearIndependent R (v ∘ coe : s → M) ↔
      ∀, ∀ l ∈ Finsupp.supported R R s, ∀, (Finsupp.total ι M R v) l = 0 → l = 0 :=
  by
  simp only [← linear_independent_iff, ← (· ∘ ·), ← Finsupp.mem_supported, ← Finsupp.total_apply, ← Set.subset_def, ←
    Finset.mem_coe]
  constructor
  · intro h l hl₁ hl₂
    have := h (l.subtype_domain s) ((Finsupp.sum_subtype_domain_index hl₁).trans hl₂)
    exact (Finsupp.subtype_domain_eq_zero_iff hl₁).1 this
    
  · intro h l hl
    refine' Finsupp.emb_domain_eq_zero.1 (h (l.emb_domain <| Function.Embedding.subtype s) _ _)
    · suffices ∀ i hi, ¬l ⟨i, hi⟩ = 0 → i ∈ s by
        simpa
      intros
      assumption
      
    · rwa [Finsupp.emb_domain_eq_map_domain, Finsupp.sum_map_domain_index]
      exacts[fun _ => zero_smul _ _, fun _ _ _ => add_smul _ _ _]
      
    

theorem linear_dependent_comp_subtype' {s : Set ι} :
    ¬LinearIndependent R (v ∘ coe : s → M) ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ Finsupp.total ι M R v f = 0 ∧ f ≠ 0 :=
  by
  simp [← linear_independent_comp_subtype]

/-- A version of `linear_dependent_comp_subtype'` with `finsupp.total` unfolded. -/
theorem linear_dependent_comp_subtype {s : Set ι} :
    ¬LinearIndependent R (v ∘ coe : s → M) ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ (∑ i in f.Support, f i • v i) = 0 ∧ f ≠ 0 :=
  linear_dependent_comp_subtype'

theorem linear_independent_subtype {s : Set M} :
    LinearIndependent R (fun x => x : s → M) ↔
      ∀, ∀ l ∈ Finsupp.supported R R s, ∀, (Finsupp.total M M R id) l = 0 → l = 0 :=
  by
  apply @linear_independent_comp_subtype _ _ _ id

theorem linear_independent_comp_subtype_disjoint {s : Set ι} :
    LinearIndependent R (v ∘ coe : s → M) ↔ Disjoint (Finsupp.supported R R s) (Finsupp.total ι M R v).ker := by
  rw [linear_independent_comp_subtype, LinearMap.disjoint_ker]

theorem linear_independent_subtype_disjoint {s : Set M} :
    LinearIndependent R (fun x => x : s → M) ↔ Disjoint (Finsupp.supported R R s) (Finsupp.total M M R id).ker := by
  apply @linear_independent_comp_subtype_disjoint _ _ _ id

theorem linear_independent_iff_total_on {s : Set M} :
    LinearIndependent R (fun x => x : s → M) ↔ (Finsupp.totalOn M M R id s).ker = ⊥ := by
  rw [Finsupp.totalOn, LinearMap.ker, LinearMap.comap_cod_restrict, map_bot, comap_bot, LinearMap.ker_comp,
    linear_independent_subtype_disjoint, Disjoint, ← map_comap_subtype, map_le_iff_le_comap, comap_bot, ker_subtype,
    le_bot_iff]

theorem LinearIndependent.restrict_of_comp_subtype {s : Set ι} (hs : LinearIndependent R (v ∘ coe : s → M)) :
    LinearIndependent R (s.restrict v) :=
  hs

variable (R M)

theorem linear_independent_empty : LinearIndependent R (fun x => x : (∅ : Set M) → M) := by
  simp [← linear_independent_subtype_disjoint]

variable {R M}

theorem LinearIndependent.mono {t s : Set M} (h : t ⊆ s) :
    LinearIndependent R (fun x => x : s → M) → LinearIndependent R (fun x => x : t → M) := by
  simp only [← linear_independent_subtype_disjoint]
  exact Disjoint.mono_left (Finsupp.supported_mono h)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem linear_independent_of_finite (s : Set M)
    (H : ∀ (t) (_ : t ⊆ s), Set.Finite t → LinearIndependent R (fun x => x : t → M)) :
    LinearIndependent R (fun x => x : s → M) :=
  linear_independent_subtype.2 fun l hl =>
    linear_independent_subtype.1 (H _ hl (Finset.finite_to_set _)) l (Subset.refl _)

theorem linear_independent_Union_of_directed {η : Type _} {s : η → Set M} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, LinearIndependent R (fun x => x : s i → M)) : LinearIndependent R (fun x => x : (⋃ i, s i) → M) := by
  by_cases' hη : Nonempty η
  · skip
    refine' linear_independent_of_finite (⋃ i, s i) fun t ht ft => _
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.to_finset with ⟨i, hi⟩
    exact (h i).mono (subset.trans hI <| Union₂_subset fun j hj => hi j (fi.mem_to_finset.2 hj))
    
  · refine' (linear_independent_empty _ _).mono _
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩
    

theorem linear_independent_sUnion_of_directed {s : Set (Set M)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀, ∀ a ∈ s, ∀, LinearIndependent R (fun x => x : (a : Set M) → M)) :
    LinearIndependent R (fun x => x : ⋃₀s → M) := by
  rw [sUnion_eq_Union] <;>
    exact
      linear_independent_Union_of_directed hs.directed_coe
        (by
          simpa using h)

theorem linear_independent_bUnion_of_directed {η} {s : Set η} {t : η → Set M} (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s)
    (h : ∀, ∀ a ∈ s, ∀, LinearIndependent R (fun x => x : t a → M)) :
    LinearIndependent R (fun x => x : (⋃ a ∈ s, t a) → M) := by
  rw [bUnion_eq_Union] <;>
    exact
      linear_independent_Union_of_directed (directed_comp.2 <| hs.directed_coe)
        (by
          simpa using h)

end Subtype

end Module

/-! ### Properties which require `ring R` -/


section Module

variable {v : ι → M}

variable [Ringₓ R] [AddCommGroupₓ M] [AddCommGroupₓ M'] [AddCommGroupₓ M'']

variable [Module R M] [Module R M'] [Module R M'']

variable {a b : R} {x y : M}

theorem linear_independent_iff_injective_total : LinearIndependent R v ↔ Function.Injective (Finsupp.total ι M R v) :=
  linear_independent_iff.trans (injective_iff_map_eq_zero (Finsupp.total ι M R v).toAddMonoidHom).symm

alias linear_independent_iff_injective_total ↔ LinearIndependent.injective_total _

theorem LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : Injective v := by
  intro i j hij
  let l : ι →₀ R := Finsupp.single i (1 : R) - Finsupp.single j 1
  have h_total : Finsupp.total ι M R v l = 0 := by
    simp_rw [LinearMap.map_sub, Finsupp.total_apply]
    simp [← hij]
  have h_single_eq : Finsupp.single i (1 : R) = Finsupp.single j 1 := by
    rw [linear_independent_iff] at hv
    simp [← eq_add_of_sub_eq' (hv l h_total)]
  simpa [← Finsupp.single_eq_single_iff] using h_single_eq

theorem LinearIndependent.to_subtype_range {ι} {f : ι → M} (hf : LinearIndependent R f) :
    LinearIndependent R (coe : Range f → M) := by
  nontriviality R
  exact (linear_independent_subtype_range hf.injective).2 hf

theorem LinearIndependent.to_subtype_range' {ι} {f : ι → M} (hf : LinearIndependent R f) {t} (ht : Range f = t) :
    LinearIndependent R (coe : t → M) :=
  ht ▸ hf.to_subtype_range

theorem LinearIndependent.image_of_comp {ι ι'} (s : Set ι) (f : ι → ι') (g : ι' → M)
    (hs : LinearIndependent R fun x : s => g (f x)) : LinearIndependent R fun x : f '' s => g x := by
  nontriviality R
  have : inj_on f s := inj_on_iff_injective.2 hs.injective.of_comp
  exact (linear_independent_equiv' (Equivₓ.Set.imageOfInjOn f s this) rfl).1 hs

theorem LinearIndependent.image {ι} {s : Set ι} {f : ι → M} (hs : LinearIndependent R fun x : s => f x) :
    LinearIndependent R fun x : f '' s => (x : M) := by
  convert LinearIndependent.image_of_comp s f id hs

theorem LinearIndependent.group_smul {G : Type _} [hG : Groupₓ G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SmulCommClass G R M] {v : ι → M} (hv : LinearIndependent R v) (w : ι → G) :
    LinearIndependent R (w • v) := by
  rw [linear_independent_iff''] at hv⊢
  intro s g hgs hsum i
  refine' (smul_eq_zero_iff_eq (w i)).1 _
  refine' hv s (fun i => w i • g i) (fun i hi => _) _ i
  · dsimp' only
    exact (hgs i hi).symm ▸ smul_zero _
    
  · rw [← hsum, Finset.sum_congr rfl _]
    intros
    erw [Pi.smul_apply, smul_assoc, smul_comm]
    

-- This lemma cannot be proved with `linear_independent.group_smul` since the action of
-- `Rˣ` on `R` is not commutative.
theorem LinearIndependent.units_smul {v : ι → M} (hv : LinearIndependent R v) (w : ι → Rˣ) :
    LinearIndependent R (w • v) := by
  rw [linear_independent_iff''] at hv⊢
  intro s g hgs hsum i
  rw [← (w i).mul_left_eq_zero]
  refine' hv s (fun i => g i • w i) (fun i hi => _) _ i
  · dsimp' only
    exact (hgs i hi).symm ▸ zero_smul _ _
    
  · rw [← hsum, Finset.sum_congr rfl _]
    intros
    erw [Pi.smul_apply, smul_assoc]
    rfl
    

section Maximal

universe v w

/-- A linearly independent family is maximal if there is no strictly larger linearly independent family.
-/
@[nolint unused_arguments]
def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiringₓ R] {M : Type v} [AddCommMonoidₓ M] [Module R M]
    {v : ι → M} (i : LinearIndependent R v) : Prop :=
  ∀ (s : Set M) (i' : LinearIndependent R (coe : s → M)) (h : Range v ≤ s), Range v = s

/-- An alternative characterization of a maximal linearly independent family,
quantifying over types (in the same universe as `M`) into which the indexing family injects.
-/
theorem LinearIndependent.maximal_iff {ι : Type w} {R : Type u} [Ringₓ R] [Nontrivial R] {M : Type v} [AddCommGroupₓ M]
    [Module R M] {v : ι → M} (i : LinearIndependent R v) :
    i.Maximal ↔ ∀ (κ : Type v) (w : κ → M) (i' : LinearIndependent R w) (j : ι → κ) (h : w ∘ j = v), Surjective j := by
  fconstructor
  · rintro p κ w i' j rfl
    specialize p (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp, ← @image_univ _ _ w] at p
    exact range_iff_surjective.mp (image_injective.mpr i'.injective p)
    
  · intro p w i' h
    specialize
      p w (coe : w → M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp )
    have q := congr_arg (fun s => (coe : w → M) '' s) p.range_eq
    dsimp'  at q
    rw [← image_univ, image_image] at q
    simpa using q
    

end Maximal

/-- Linear independent families are injective, even if you multiply either side. -/
theorem LinearIndependent.eq_of_smul_apply_eq_smul_apply {M : Type _} [AddCommGroupₓ M] [Module R M] {v : ι → M}
    (li : LinearIndependent R v) (c d : R) (i j : ι) (hc : c ≠ 0) (h : c • v i = d • v j) : i = j := by
  let l : ι →₀ R := Finsupp.single i c - Finsupp.single j d
  have h_total : Finsupp.total ι M R v l = 0 := by
    simp_rw [LinearMap.map_sub, Finsupp.total_apply]
    simp [← h]
  have h_single_eq : Finsupp.single i c = Finsupp.single j d := by
    rw [linear_independent_iff] at li
    simp [← eq_add_of_sub_eq' (li l h_total)]
  rcases(Finsupp.single_eq_single_iff _ _ _ _).mp h_single_eq with (⟨this, _⟩ | ⟨hc, _⟩)
  · exact this
    
  · contradiction
    

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/


theorem LinearIndependent.disjoint_span_image (hv : LinearIndependent R v) {s t : Set ι} (hs : Disjoint s t) :
    Disjoint (Submodule.span R <| v '' s) (Submodule.span R <| v '' t) := by
  simp only [← disjoint_def, ← Finsupp.mem_span_image_iff_total]
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  rw [hv.injective_total.eq_iff] at H
  subst l₂
  have : l₁ = 0 := Finsupp.disjoint_supported_supported hs (Submodule.mem_inf.2 ⟨hl₁, hl₂⟩)
  simp [← this]

theorem LinearIndependent.not_mem_span_image [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι} {x : ι}
    (h : x ∉ s) : v x ∉ Submodule.span R (v '' s) := by
  have h' : v x ∈ Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  apply LinearIndependent.ne_zero x hv
  refine' disjoint_def.1 (hv.disjoint_span_image _) (v x) h' w
  simpa using h

theorem LinearIndependent.total_ne_of_not_mem_support [Nontrivial R] (hv : LinearIndependent R v) {x : ι} (f : ι →₀ R)
    (h : x ∉ f.Support) : Finsupp.total ι M R v f ≠ v x := by
  replace h : x ∉ (f.support : Set ι) := h
  have p := hv.not_mem_span_image h
  intro w
  rw [← w] at p
  rw [Finsupp.span_image_eq_map_total] at p
  simp only [← not_exists, ← not_and, ← mem_map] at p
  exact p f (f.mem_supported_support R) rfl

theorem linear_independent_sum {v : Sum ι ι' → M} :
    LinearIndependent R v ↔
      LinearIndependent R (v ∘ Sum.inl) ∧
        LinearIndependent R (v ∘ Sum.inr) ∧
          Disjoint (Submodule.span R (Range (v ∘ Sum.inl))) (Submodule.span R (Range (v ∘ Sum.inr))) :=
  by
  rw [range_comp v, range_comp v]
  refine'
    ⟨fun h =>
      ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, h.disjoint_span_image is_compl_range_inl_range_inr.1⟩, _⟩
  rintro ⟨hl, hr, hlr⟩
  rw [linear_independent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i in s.preimage Sum.inl (sum.inl_injective.inj_on _), (fun x => g x • v x) (Sum.inl i)) +
        ∑ i in s.preimage Sum.inr (sum.inr_injective.inj_on _), (fun x => g x • v x) (Sum.inr i)) =
      0 :=
    by
    rw [Finset.sum_preimage', Finset.sum_preimage', ← Finset.sum_union, ← Finset.filter_or]
    · simpa only [mem_union, ← range_inl_union_range_inr, ← mem_univ, ← Finset.filter_true]
      
    · exact Finset.disjoint_filter.2 fun x _ hx => disjoint_left.1 is_compl_range_inl_range_inr.1 hx
      
  · rw [← eq_neg_iff_add_eq_zero] at this
    rw [disjoint_def'] at hlr
    have A := hlr _ (sum_mem fun i hi => _) _ (neg_mem <| sum_mem fun i hi => _) this
    · cases' i with i i
      · exact hl _ _ A i (Finset.mem_preimage.2 hi)
        
      · rw [this, neg_eq_zero] at A
        exact hr _ _ A i (Finset.mem_preimage.2 hi)
        
      
    · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
      
    · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
      
    

theorem LinearIndependent.sum_type {v' : ι' → M} (hv : LinearIndependent R v) (hv' : LinearIndependent R v')
    (h : Disjoint (Submodule.span R (Range v)) (Submodule.span R (Range v'))) : LinearIndependent R (Sum.elim v v') :=
  linear_independent_sum.2 ⟨hv, hv', h⟩

theorem LinearIndependent.union {s t : Set M} (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M)) (hst : Disjoint (span R s) (span R t)) :
    LinearIndependent R (fun x => x : s ∪ t → M) :=
  (hs.sum_type ht <| by
        simpa).to_subtype_range' <|
    by
    simp

theorem linear_independent_Union_finite_subtype {ι : Type _} {f : ι → Set M}
    (hl : ∀ i, LinearIndependent R (fun x => x : f i → M))
    (hd : ∀ i, ∀ t : Set ι, t.Finite → i ∉ t → Disjoint (span R (f i)) (⨆ i ∈ t, span R (f i))) :
    LinearIndependent R (fun x => x : (⋃ i, f i) → M) := by
  rw [Union_eq_Union_finset f]
  apply linear_independent_Union_of_directed
  · apply directed_of_sup
    exact fun t₁ t₂ ht => Union_mono fun i => Union_subset_Union_const fun h => ht h
    
  intro t
  induction' t using Finset.induction_on with i s his ih
  · refine' (linear_independent_empty _ _).mono _
    simp
    
  · rw [Finset.set_bUnion_insert]
    refine' (hl _).union ih _
    rw [span_Union₂]
    exact hd i s s.finite_to_set his
    

theorem linear_independent_Union_finite {η : Type _} {ιs : η → Type _} {f : ∀ j : η, ιs j → M}
    (hindep : ∀ j, LinearIndependent R (f j))
    (hd : ∀ i, ∀ t : Set η, t.Finite → i ∉ t → Disjoint (span R (Range (f i))) (⨆ i ∈ t, span R (Range (f i)))) :
    LinearIndependent R fun ji : Σj, ιs j => f ji.1 ji.2 := by
  nontriviality R
  apply LinearIndependent.of_subtype_range
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    by_cases' h_cases : x₁ = y₁
    subst h_cases
    · apply Sigma.eq
      rw [LinearIndependent.injective (hindep _) hxy]
      rfl
      
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h)) (f x₁ x₂)
            (subset_span (mem_range_self _))
        rw [supr_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
      
    
  rw [range_sigma_eq_Union_range]
  apply linear_independent_Union_finite_subtype (fun j => (hindep j).to_subtype_range) hd

end Subtype

section reprₓ

variable (hv : LinearIndependent R v)

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps (config := { rhsMd := semireducible })]
def LinearIndependent.totalEquiv (hv : LinearIndependent R v) : (ι →₀ R) ≃ₗ[R] span R (Range v) := by
  apply LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v)) (Finsupp.total ι M R v) _)
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_cod_restrict]
    apply hv
    
  · rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_cod_restrict, ← LinearMap.range_le_iff_comap,
      range_subtype, map_top]
    rw [Finsupp.range_total]
    exact le_rfl
    
  · intro l
    rw [← Finsupp.range_total]
    rw [LinearMap.mem_range]
    apply mem_range_self l
    

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `linear_independent.total_equiv`. -/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (Range v) →ₗ[R] ι →₀ R :=
  hv.totalEquiv.symm

@[simp]
theorem LinearIndependent.total_repr (x) : Finsupp.total ι M R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.totalEquiv x)

theorem LinearIndependent.total_comp_repr : (Finsupp.total ι M R v).comp hv.repr = Submodule.subtype _ :=
  LinearMap.ext <| hv.total_repr

theorem LinearIndependent.repr_ker : hv.repr.ker = ⊥ := by
  rw [LinearIndependent.repr, LinearEquiv.ker]

theorem LinearIndependent.repr_range : hv.repr.range = ⊤ := by
  rw [LinearIndependent.repr, LinearEquiv.range]

theorem LinearIndependent.repr_eq {l : ι →₀ R} {x} (eq : Finsupp.total ι M R v l = ↑x) : hv.repr x = l := by
  have : ↑((LinearIndependent.totalEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l) = Finsupp.total ι M R v l := rfl
  have : (LinearIndependent.totalEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x := by
    rw [Eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.total_equiv l]
  rw [← this]
  rfl

theorem LinearIndependent.repr_eq_single (i) (x) (hx : ↑x = v i) : hv.repr x = Finsupp.single i 1 := by
  apply hv.repr_eq
  simp [← Finsupp.total_single, ← hx]

theorem LinearIndependent.span_repr_eq [Nontrivial R] (x) :
    Span.repr R (Set.Range v) x = (hv.repr x).equivMapDomain (Equivₓ.ofInjective _ hv.Injective) := by
  have p : (Span.repr R (Set.Range v) x).equivMapDomain (Equivₓ.ofInjective _ hv.injective).symm = hv.repr x := by
    apply (LinearIndependent.totalEquiv hv).Injective
    ext
    simp only [← LinearIndependent.total_equiv_apply_coe, ← Equivₓ.self_comp_of_injective_symm, ←
      LinearIndependent.total_repr, ← Finsupp.total_equiv_map_domain, ← Span.finsupp_total_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  simp [p]

-- TODO: why is this so slow?
theorem linear_independent_iff_not_smul_mem_span :
    LinearIndependent R v ↔ ∀ (i : ι) (a : R), a • v i ∈ span R (v '' (univ \ {i})) → a = 0 :=
  ⟨fun hv i a ha => by
    rw [Finsupp.span_image_eq_map_total, mem_map] at ha
    rcases ha with ⟨l, hl, e⟩
    rw
      [sub_eq_zero.1
        (linear_independent_iff.1 hv (l - Finsupp.single i a)
          (by
            simp [← e]))] at
      hl
    by_contra hn
    exact
      (not_mem_of_mem_diff
          (hl <| by
            simp [← hn]))
        (mem_singleton _),
    fun H =>
    linear_independent_iff.2 fun l hl => by
      ext i
      simp only [← Finsupp.zero_apply]
      by_contra hn
      refine' hn (H i _ _)
      refine' (Finsupp.mem_span_image_iff_total _).2 ⟨Finsupp.single i (l i) - l, _, _⟩
      · rw [Finsupp.mem_supported']
        intro j hj
        have hij : j = i :=
          not_not.1 fun hij : j ≠ i => hj ((mem_diff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [← hij]
        
      · simp [← hl]
        ⟩

/-- See also `complete_lattice.independent_iff_linear_independent_of_ne_zero`. -/
theorem LinearIndependent.independent_span_singleton (hv : LinearIndependent R v) :
    CompleteLattice.Independent fun i => R∙v i := by
  refine' complete_lattice.independent_def.mp fun i m hm => (mem_bot R).mpr _
  simp only [← mem_inf, ← mem_span_singleton, ← supr_subtype', span_range_eq_supr] at hm
  obtain ⟨⟨r, rfl⟩, hm⟩ := hm
  suffices r = 0 by
    simp [← this]
  apply linear_independent_iff_not_smul_mem_span.mp hv i
  convert hm
  ext
  simp

variable (R)

theorem exists_maximal_independent' (s : ι → M) :
    ∃ I : Set ι,
      (LinearIndependent R fun x : I => s x) ∧ ∀ J : Set ι, I ⊆ J → (LinearIndependent R fun x : J => s x) → I = J :=
  by
  let indep : Set ι → Prop := fun I => LinearIndependent R (s ∘ coe : I → M)
  let X := { I : Set ι // indep I }
  let r : X → X → Prop := fun I J => I.1 ⊆ J.1
  have key : ∀ c : Set X, IsChain r c → indep (⋃ (I : X) (H : I ∈ c), I) := by
    intro c hc
    dsimp' [← indep]
    rw [linear_independent_comp_subtype]
    intro f hsupport hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · simpa using hsupport
      
    have : IsRefl X r := ⟨fun _ => Set.Subset.refl _⟩
    obtain ⟨I, I_mem, hI⟩ : ∃ I ∈ c, (f.support : Set ι) ⊆ I :=
      hc.directed_on.exists_mem_subset_of_finset_subset_bUnion hn hsupport
    exact linear_independent_comp_subtype.mp I.2 f hI hsum
  have trans : Transitive r := fun I J K => Set.Subset.trans
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    @exists_maximal_of_chains_bounded _ r
      (fun c hc => ⟨⟨⋃ I ∈ c, (I : Set ι), key c hc⟩, fun I => Set.subset_bUnion_of_mem⟩) trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » I)
theorem exists_maximal_independent (s : ι → M) :
    ∃ I : Set ι,
      (LinearIndependent R fun x : I => s x) ∧ ∀ (i) (_ : i ∉ I), ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I) :=
  by
  classical
  rcases exists_maximal_independent' R s with ⟨I, hIlinind, hImaximal⟩
  use I, hIlinind
  intro i hi
  specialize
    hImaximal (I ∪ {i})
      (by
        simp )
  set J := I ∪ {i} with hJ
  have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I := by
    simp [← hJ]
  have hiJ : i ∈ J := by
    simp
  have h := mt hImaximal _
  swap
  · intro h2
    rw [h2] at hi
    exact absurd hiJ hi
    
  obtain ⟨f, supp_f, sum_f, f_ne⟩ := linear_dependent_comp_subtype.mp h
  have hfi : f i ≠ 0 := by
    contrapose hIlinind
    refine' linear_dependent_comp_subtype.mpr ⟨f, _, sum_f, f_ne⟩
    simp only [← Finsupp.mem_supported, ← hJ] at supp_f⊢
    rintro x hx
    refine' (memJ.mp (supp_f hx)).resolve_left _
    rintro rfl
    exact hIlinind (finsupp.mem_support_iff.mp hx)
  use f i, hfi
  have hfi' : i ∈ f.support := finsupp.mem_support_iff.mpr hfi
  rw [← Finset.insert_erase hfi', Finset.sum_insert (Finset.not_mem_erase _ _), add_eq_zero_iff_eq_neg] at sum_f
  rw [sum_f]
  refine' neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, _, rfl⟩))
  exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)

end reprₓ

theorem surjective_of_linear_independent_of_span [Nontrivial R] (hv : LinearIndependent R v) (f : ι' ↪ ι)
    (hss : Range v ⊆ span R (Range (v ∘ f))) : Surjective f := by
  intro i
  let repr : (span R (range (v ∘ f)) : Type _) → ι' →₀ R := (hv.comp f f.injective).repr
  let l := (reprₓ ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  have h_total_l : Finsupp.total ι M R v l = v i := by
    dsimp' only [← l]
    rw [Finsupp.total_map_domain]
    rw [(hv.comp f f.injective).total_repr]
    · rfl
      
    · exact f.injective
      
  have h_total_eq : (Finsupp.total ι M R v) l = (Finsupp.total ι M R v) (Finsupp.single i 1) := by
    rw [h_total_l, Finsupp.total_single, one_smul]
  have l_eq : l = _ := LinearMap.ker_eq_bot.1 hv h_total_eq
  dsimp' only [← l]  at l_eq
  rw [← Finsupp.emb_domain_eq_map_domain] at l_eq
  rcases Finsupp.single_of_emb_domain_single (reprₓ ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with ⟨i', hi'⟩
  use i'
  exact hi'.2

theorem eq_of_linear_independent_of_span_subtype [Nontrivial R] {s t : Set M}
    (hs : LinearIndependent R (fun x => x : s → M)) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t := by
  let f : t ↪ s := ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.injₓ hab)⟩
  have h_surj : surjective f := by
    apply surjective_of_linear_independent_of_span hs f _
    convert hst <;> simp [← f, ← comp]
  show s = t
  · apply subset.antisymm _ h
    intro x hx
    rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
    convert y.mem
    rw [← Subtype.mk.injₓ hy]
    rfl
    

open LinearMap

theorem LinearIndependent.image_subtype {s : Set M} {f : M →ₗ[R] M'} (hs : LinearIndependent R (fun x => x : s → M))
    (hf_inj : Disjoint (span R s) f.ker) : LinearIndependent R (fun x => x : f '' s → M') := by
  rw [← @Subtype.range_coe _ s] at hf_inj
  refine' (hs.map hf_inj).to_subtype_range' _
  simp [← Set.range_comp f]

theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'} (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M')) :
    LinearIndependent R (fun x => x : inl R M M' '' s ∪ inr R M M' '' t → M × M') := by
  refine' (hs.image_subtype _).union (ht.image_subtype _) _ <;> [simp , simp , skip]
  simp only [← span_image]
  simp [← disjoint_iff, ← prod_inf_prod]

theorem linear_independent_inl_union_inr' {v : ι → M} {v' : ι' → M'} (hv : LinearIndependent R v)
    (hv' : LinearIndependent R v') : LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
  (hv.map' (inl R M M') ker_inl).sum_type (hv'.map' (inr R M M') ker_inr) <| by
    refine' is_compl_range_inl_inr.disjoint.mono _ _ <;> simp only [← span_le, ← range_coe, ← range_comp_subset_range]

/-- Dedekind's linear independence of characters -/
-- See, for example, Keith Conrad's note
--  <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
theorem linear_independent_monoid_hom (G : Type _) [Monoidₓ G] (L : Type _) [CommRingₓ L] [NoZeroDivisors L] :
    @LinearIndependent _ L (G → L) (fun f => f : (G →* L) → G → L) _ _ _ := by
  let this := Classical.decEq (G →* L) <;>
    let this : MulAction L L :=
        DistribMulAction.toMulAction <;>-- We prove linear independence by showing that only the trivial linear combination vanishes.
      exact
        linear_independent_iff'.2-- To do this, we use `finset` induction,
        fun s =>
          (Finset.induction_on s fun g hg i => False.elim) fun a s has ih g hg =>
            -- Here
            -- * `a` is a new character we will insert into the `finset` of characters `s`,
            -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
            -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
            -- and it remains to prove that `g` vanishes on `insert a s`.
            -- We now make the key calculation:
            -- For any character `i` in the original `finset`, we have `g i • i = g i • a` as functions on the
            -- monoid `G`.
            have h1 : ∀, ∀ i ∈ s, ∀, (g i • i : G → L) = g i • a := fun i his =>
              funext fun x : G =>
                -- We prove these expressions are equal by showing
                  -- the differences of their values on each monoid element `x` is zero
                  eq_of_sub_eq_zero <|
                  ih (fun j => g j * j x - g j * a x)
                    (funext fun y : G =>
                      calc
                        (-- After that, it's just a chase scene.
                              ∑ i in s, ((g i * i x - g i * a x) • i : G → L))
                              y =
                            ∑ i in s, (g i * i x - g i * a x) * i y :=
                          Finset.sum_apply _ _ _
                        _ = ∑ i in s, g i * i x * i y - g i * a x * i y := Finset.sum_congr rfl fun _ _ => sub_mul _ _ _
                        _ = (∑ i in s, g i * i x * i y) - ∑ i in s, g i * a x * i y := Finset.sum_sub_distrib
                        _ =
                            (g a * a x * a y + ∑ i in s, g i * i x * i y) -
                              (g a * a x * a y + ∑ i in s, g i * a x * i y) :=
                          by
                          rw [add_sub_add_left_eq_sub]
                        _ = (∑ i in insert a s, g i * i x * i y) - ∑ i in insert a s, g i * a x * i y := by
                          rw [Finset.sum_insert has, Finset.sum_insert has]
                        _ = (∑ i in insert a s, g i * i (x * y)) - ∑ i in insert a s, a x * (g i * i y) :=
                          congr
                            (congr_arg Sub.sub
                              ((Finset.sum_congr rfl) fun i _ => by
                                rw [i.map_mul, mul_assoc]))
                            ((Finset.sum_congr rfl) fun _ _ => by
                              rw [mul_assoc, mul_left_commₓ])
                        _ =
                            (∑ i in insert a s, (g i • i : G → L)) (x * y) -
                              a x * (∑ i in insert a s, (g i • i : G → L)) y :=
                          by
                          rw [Finset.sum_apply, Finset.sum_apply, Finset.mul_sum] <;> rfl
                        _ = 0 - a x * 0 := by
                          rw [hg] <;> rfl
                        _ = 0 := by
                          rw [mul_zero, sub_zero]
                        )
                    i his
            -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
            -- there is some element of the monoid on which it differs from `a`.
            have h2 : ∀ i : G →* L, i ∈ s → ∃ y, i y ≠ a y := fun i his =>
              Classical.by_contradiction fun h =>
                have hia : i = a := MonoidHom.ext fun y => Classical.by_contradiction fun hy => h ⟨y, hy⟩
                has <| hia ▸ his
            -- From these two facts we deduce that `g` actually vanishes on `s`,
            have h3 : ∀, ∀ i ∈ s, ∀, g i = 0 := fun i his =>
              let ⟨y, hy⟩ := h2 i his
              have h : g i • i y = g i • a y := congr_fun (h1 i his) y
              Or.resolve_right
                (mul_eq_zero.1 <| by
                  rw [mul_sub, sub_eq_zero] <;> exact h)
                (sub_ne_zero_of_ne hy)
            -- And so, using the fact that the linear combination over `s` and over `insert a s` both vanish,
            -- we deduce that `g a = 0`.
            have h4 : g a = 0 :=
              calc
                g a = g a * 1 := (mul_oneₓ _).symm
                _ = (g a • a : G → L) 1 := by
                  rw [← a.map_one] <;> rfl
                _ = (∑ i in insert a s, (g i • i : G → L)) 1 := by
                  rw [Finset.sum_eq_single a]
                  · intro i his hia
                    rw [Finset.mem_insert] at his
                    rw [h3 i (his.resolve_left hia), zero_smul]
                    
                  · intro haas
                    exfalso
                    apply haas
                    exact Finset.mem_insert_self a s
                    
                _ = 0 := by
                  rw [hg] <;> rfl
                
            (-- Now we're done; the last two facts together imply that `g` vanishes on every element
                  -- of `insert a s`.
                  Finset.forall_mem_insert
                  _ _ _).2
              ⟨h4, h3⟩

theorem le_of_span_le_span [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R (coe : u → M)) (hsu : s ⊆ u)
    (htu : t ⊆ u) (hst : span R s ≤ span R t) : s ⊆ t := by
  have :=
    eq_of_linear_independent_of_span_subtype (hl.mono (Set.union_subset hsu htu)) (Set.subset_union_right _ _)
      (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]
  apply Set.subset_union_left

theorem span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R (coe : u → M)) (hsu : s ⊆ u)
    (htu : t ⊆ u) : span R s ≤ span R t ↔ s ⊆ t :=
  ⟨le_of_span_le_span hl hsu htu, span_mono⟩

end Module

section Nontrivial

variable [Ringₓ R] [Nontrivial R] [AddCommGroupₓ M] [AddCommGroupₓ M']

variable [Module R M] [NoZeroSmulDivisors R M] [Module R M']

variable {v : ι → M} {s t : Set M} {x y z : M}

theorem linear_independent_unique_iff (v : ι → M) [Unique ι] : LinearIndependent R v ↔ v default ≠ 0 := by
  simp only [← linear_independent_iff, ← Finsupp.total_unique, ← smul_eq_zero]
  refine' ⟨fun h hv => _, fun hv l hl => Finsupp.unique_ext <| hl.resolve_right hv⟩
  have := h (Finsupp.single default 1) (Or.inr hv)
  exact one_ne_zero (Finsupp.single_eq_zero.1 this)

alias linear_independent_unique_iff ↔ _ linear_independent_unique

theorem linear_independent_singleton {x : M} (hx : x ≠ 0) : LinearIndependent R (fun x => x : ({x} : Set M) → M) :=
  linear_independent_unique coe hx

end Nontrivial

/-!
### Properties which require `division_ring K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroupₓ V] [AddCommGroupₓ V']

variable [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

open Submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/
theorem mem_span_insert_exchange : x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) := by
  simp [← mem_span_insert]
  rintro a z hz rfl h
  refine' ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩
  have a0 : a ≠ 0 := by
    rintro rfl
    simp_all
  simp [← a0, ← smul_add, ← smul_smul]

theorem linear_independent_iff_not_mem_span : LinearIndependent K v ↔ ∀ i, v i ∉ span K (v '' (univ \ {i})) := by
  apply linear_independent_iff_not_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply
      one_ne_zero
        (h i 1
          (by
            simp [← h_in_span]))
    
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))
    

theorem LinearIndependent.insert (hs : LinearIndependent K (fun b => b : s → V)) (hx : x ∉ span K s) :
    LinearIndependent K (fun b => b : insert x s → V) := by
  rw [← union_singleton]
  have x0 : x ≠ 0 :=
    mt
      (by
        rintro rfl <;> apply zero_mem (span K s))
      hx
  apply hs.union (linear_independent_singleton x0)
  rwa [disjoint_span_singleton' x0]

theorem linear_independent_option' :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (Range v) :=
  by
  rw [← linear_independent_equiv (Equivₓ.optionEquivSumPunit ι).symm, linear_independent_sum, @range_unique _ PUnit,
    @linear_independent_unique_iff PUnit, disjoint_span_singleton]
  dsimp' [← (· ∘ ·)]
  refine' ⟨fun h => ⟨h.1, fun hx => h.2.1 <| h.2.2 hx⟩, fun h => ⟨h.1, _, fun hx => (h.2 hx).elim⟩⟩
  rintro rfl
  exact h.2 (zero_mem _)

theorem LinearIndependent.option (hv : LinearIndependent K v) (hx : x ∉ Submodule.span K (Range v)) :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) :=
  linear_independent_option'.2 ⟨hv, hx⟩

theorem linear_independent_option {v : Option ι → V} :
    LinearIndependent K v ↔
      LinearIndependent K (v ∘ coe : ι → V) ∧ v none ∉ Submodule.span K (Range (v ∘ coe : ι → V)) :=
  by
  simp only [linear_independent_option', ← Option.cases_on'_none_coe]

theorem linear_independent_insert' {ι} {s : Set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
    (LinearIndependent K fun x : insert a s => f x) ↔
      (LinearIndependent K fun x : s => f x) ∧ f a ∉ Submodule.span K (f '' s) :=
  by
  rw [← linear_independent_equiv ((Equivₓ.optionEquivSumPunit _).trans (Equivₓ.Set.insert has).symm),
    linear_independent_option]
  simp [← (· ∘ ·), ← range_comp f]

theorem linear_independent_insert (hxs : x ∉ s) :
    (LinearIndependent K fun b : insert x s => (b : V)) ↔
      (LinearIndependent K fun b : s => (b : V)) ∧ x ∉ Submodule.span K s :=
  (@linear_independent_insert' _ _ _ _ _ _ _ _ id hxs).trans <| by
    simp

theorem linear_independent_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
    LinearIndependent K (coe : ({x, y} : Set V) → V) :=
  pair_comm y x ▸ (linear_independent_singleton hx).insert <| mt mem_span_singleton.1 (not_exists.2 hy)

theorem linear_independent_fin_cons {n} {v : Finₓ n → V} :
    LinearIndependent K (Finₓ.cons x v : Finₓ (n + 1) → V) ↔ LinearIndependent K v ∧ x ∉ Submodule.span K (Range v) :=
  by
  rw [← linear_independent_equiv (finSuccEquiv n).symm, linear_independent_option]
  convert Iff.rfl
  · ext
    -- TODO: why doesn't simp use `fin_succ_equiv_symm_coe` here?
    rw [comp_app, comp_app, fin_succ_equiv_symm_coe, Finₓ.cons_succ]
    
  · ext
    rw [comp_app, comp_app, fin_succ_equiv_symm_coe, Finₓ.cons_succ]
    

theorem linear_independent_fin_snoc {n} {v : Finₓ n → V} :
    LinearIndependent K (Finₓ.snoc v x : Finₓ (n + 1) → V) ↔ LinearIndependent K v ∧ x ∉ Submodule.span K (Range v) :=
  by
  rw [Finₓ.snoc_eq_cons_rotate, linear_independent_equiv, linear_independent_fin_cons]

/-- See `linear_independent.fin_cons'` for an uglier version that works if you
only have a module over a semiring. -/
theorem LinearIndependent.fin_cons {n} {v : Finₓ n → V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (Range v)) : LinearIndependent K (Finₓ.cons x v : Finₓ (n + 1) → V) :=
  linear_independent_fin_cons.2 ⟨hv, hx⟩

theorem linear_independent_fin_succ {n} {v : Finₓ (n + 1) → V} :
    LinearIndependent K v ↔ LinearIndependent K (Finₓ.tail v) ∧ v 0 ∉ Submodule.span K (range <| Finₓ.tail v) := by
  rw [← linear_independent_fin_cons, Finₓ.cons_self_tail]

theorem linear_independent_fin_succ' {n} {v : Finₓ (n + 1) → V} :
    LinearIndependent K v ↔
      LinearIndependent K (Finₓ.init v) ∧ v (Finₓ.last _) ∉ Submodule.span K (range <| Finₓ.init v) :=
  by
  rw [← linear_independent_fin_snoc, Finₓ.snoc_init_self]

theorem linear_independent_fin2 {f : Finₓ 2 → V} : LinearIndependent K f ↔ f 1 ≠ 0 ∧ ∀ a : K, a • f 1 ≠ f 0 := by
  rw [linear_independent_fin_succ, linear_independent_unique_iff, range_unique, mem_span_singleton, not_exists,
    show Finₓ.tail f default = f 1 by
      rw [← Finₓ.succ_zero_eq_one] <;> rfl]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ⊆ » t)
theorem exists_linear_independent_extension (hs : LinearIndependent K (coe : s → V)) (hst : s ⊆ t) :
    ∃ (b : _)(_ : b ⊆ t), s ⊆ b ∧ t ⊆ span K b ∧ LinearIndependent K (coe : b → V) := by
  rcases zorn_subset_nonempty { b | b ⊆ t ∧ LinearIndependent K (coe : b → V) } _ _ ⟨hst, hs⟩ with ⟨b, ⟨bt, bi⟩, sb, h⟩
  · refine' ⟨b, bt, sb, fun x xt => _, bi⟩
    by_contra hn
    apply hn
    rw [← h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _)]
    exact subset_span (mem_insert _ _)
    
  · refine' fun c hc cc c0 => ⟨⋃₀c, ⟨_, _⟩, fun x => _⟩
    · exact sUnion_subset fun x xc => (hc xc).1
      
    · exact linear_independent_sUnion_of_directed cc.directed_on fun x xc => (hc xc).2
      
    · exact subset_sUnion_of_mem
      
    

variable (K t)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ⊆ » t)
theorem exists_linear_independent : ∃ (b : _)(_ : b ⊆ t), span K b = span K t ∧ LinearIndependent K (coe : b → V) := by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linear_independent_extension (linear_independent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

variable {K t}

/-- `linear_independent.extend` adds vectors to a linear independent set `s ⊆ t` until it spans
all elements of `t`. -/
noncomputable def LinearIndependent.Extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) : Set V :=
  Classical.some (exists_linear_independent_extension hs hst)

theorem LinearIndependent.extend_subset (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
    hs.extend hst ⊆ t :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  hbt

theorem LinearIndependent.subset_extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
    s ⊆ hs.extend hst :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  hsb

theorem LinearIndependent.subset_span_extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
    t ⊆ span K (hs.extend hst) :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  htb

theorem LinearIndependent.linear_independent_extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
    LinearIndependent K (coe : hs.extend hst → V) :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  hli

variable {K V}

-- TODO(Mario): rewrite?
theorem exists_of_linear_independent_of_finite_span {t : Finset V} (hs : LinearIndependent K (fun x => x : s → V))
    (hst : s ⊆ (span K ↑t : Submodule K V)) : ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card := by
  have :
    ∀ t,
      ∀ s' : Finset V,
        ↑s' ⊆ s →
          s ∩ ↑t = ∅ →
            s ⊆ (span K ↑(s' ∪ t) : Submodule K V) →
              ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
        have : s = ↑s' :=
          eq_of_linear_independent_of_span_subtype hs hs' <| by
            simpa using hss'
        ⟨s', by
          simp [← this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ ∈ s ∩ ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
      have hb₁s' : b₁ ∉ s' := fun h => hb₁s <| hs' h
      have hst : s ∩ ↑t = ∅ :=
        eq_empty_of_subset_empty <|
          Subset.trans
            (by
              simp [← inter_subset_inter, ← subset.refl])
            (le_of_eqₓ hst)
      Classical.by_cases
        (fun this : s ⊆ (span K ↑(s' ∪ t) : Submodule K V) =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by
            simp [← insert_subset_insert hust],
            Subset.trans hsu
              (by
                simp ),
            by
            simp [← Eq, ← hb₁t, ← hb₁s', ← hb₁u]⟩)
        fun this : ¬s ⊆ (span K ↑(s' ∪ t) : Submodule K V) =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
        have hb₂t' : b₂ ∉ s' ∪ t := fun h => hb₂t <| subset_span h
        have : s ⊆ (span K ↑(insert b₂ s' ∪ t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : Set V) := by
            simp [← insert_eq, -singleton_union, -union_singleton, ← union_subset_union, ← subset.refl, ←
              subset_union_right]
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : Set V)) := span_mono this (hss' hb₃)
          have : s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : Submodule K V) := by
            simpa [← insert_eq, -singleton_union, -union_singleton] using hss'
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)) := mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃ <;> simpa using hb₃
        let ⟨u, hust, hsu, Eq⟩ :=
          ih _
            (by
              simp [← insert_subset, ← hb₂s, ← hs'])
            hst this
        ⟨u,
          Subset.trans hust <|
            union_subset_union (Subset.refl _)
              (by
                simp [← subset_insert]),
          hsu, by
          simp [← Eq, ← hb₂t', ← hb₁t, ← hb₁s']⟩
  have eq : ((t.filter fun x => x ∈ s) ∪ t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases' x ∈ s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x ∈ s)
        (by
          simp [← Set.subset_def])
        (by
          simp (config := { contextual := true })[← Set.ext_iff])
        (by
          rwa [Eq]))
  intro u h
  exact
    ⟨u,
      subset.trans h.1
        (by
          simp (config := { contextual := true })[← subset_def, ← and_imp, ← or_imp_distrib]),
      h.2.1, by
      simp only [← h.2.2, ← Eq]⟩

theorem exists_finite_card_le_of_finite_of_linear_independent_of_span (ht : t.Finite)
    (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ span K t) :
    ∃ h : s.Finite, h.toFinset.card ≤ ht.toFinset.card :=
  have : s ⊆ (span K ↑ht.toFinset : Submodule K V) := by
    simp <;> assumption
  let ⟨u, hust, hsu, Eq⟩ := exists_of_linear_independent_of_finite_span hs this
  have : s.Finite := u.finite_to_set.Subset hsu
  ⟨this, by
    rw [← Eq] <;>
      exact
        Finset.card_le_of_subset <|
          finset.coe_subset.mp <| by
            simp [← hsu]⟩

end Module

