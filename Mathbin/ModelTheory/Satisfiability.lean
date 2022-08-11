/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.Ultraproducts
import Mathbin.ModelTheory.Bundled
import Mathbin.ModelTheory.Skolem

/-!
# First-Order Satisfiability
This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions
* `first_order.language.Theory.is_satisfiable`: `T.is_satisfiable` indicates that `T` has a nonempty
model.
* `first_order.language.Theory.is_finitely_satisfiable`: `T.is_finitely_satisfiable` indicates that
every finite subset of `T` is satisfiable.
* `first_order.language.Theory.is_complete`: `T.is_complete` indicates that `T` is satisfiable and
models each sentence or its negation.
* `first_order.language.Theory.semantically_equivalent`: `T.semantically_equivalent φ ψ` indicates
that `φ` and `ψ` are equivalent formulas or sentences in models of `T`.
* `cardinal.categorical`: A theory is `κ`-categorical if all models of size `κ` are isomorphic.

## Main Results
* The Compactness Theorem, `first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable`,
shows that a theory is satisfiable iff it is finitely satisfiable.
* `first_order.language.complete_theory.is_complete`: The complete theory of a structure is
complete.
* `first_order.language.Theory.exists_large_model_of_infinite_model` shows that any theory with an
infinite model has arbitrarily large models.
* `first_order.language.Theory.exists_elementary_embedding_card_eq`: The Upward Löwenheim–Skolem
Theorem: If `κ` is a cardinal greater than the cardinalities of `L` and an infinite `L`-structure
`M`, then `M` has an elementary extension of cardinality `κ`.

## Implementation Details
* Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.

-/


universe u v w w'

open Cardinal CategoryTheory

open Cardinal FirstOrder

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

namespace Theory

variable (T)

/-- A theory is satisfiable if a structure models it. -/
def IsSatisfiable : Prop :=
  Nonempty (ModelCat.{u, v, max u v} T)

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def IsFinitelySatisfiable : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → (T0 : L.Theory).IsSatisfiable

variable {T} {T' : L.Theory}

theorem Model.is_satisfiable (M : Type w) [n : Nonempty M] [S : L.Structure M] [M ⊨ T] : T.IsSatisfiable :=
  ⟨((⊥ : Substructure _ (ModelCat.of T M)).elementarySkolem₁Reduct.toModel T).Shrink⟩

theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨(Theory.Model.mono (ModelCat.is_model h.some) hs).Bundled⟩

theorem IsSatisfiable.is_finitely_satisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable := fun _ => h.mono

/-- The Compactness Theorem of first-order logic: A theory is satisfiable if and only if it is
finitely satisfiable. -/
theorem is_satisfiable_iff_is_finitely_satisfiable {T : L.Theory} : T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  ⟨Theory.IsSatisfiable.is_finitely_satisfiable, fun h => by
    classical
    set M : ∀ T0 : Finset T, Type max u v := fun T0 =>
      (h (T0.map (Function.Embedding.subtype fun x => x ∈ T)) T0.map_subtype_subset).some with hM
    let M' := Filter.Product (↑(Ultrafilter.of (Filter.atTop : Filter (Finset T)))) M
    have h' : M' ⊨ T := by
      refine' ⟨fun φ hφ => _⟩
      rw [ultraproduct.sentence_realize]
      refine'
        Filter.Eventually.filter_mono (Ultrafilter.of_le _)
          (Filter.eventually_at_top.2
            ⟨{⟨φ, hφ⟩}, fun s h' =>
              Theory.realize_sentence_of_mem (s.map (Function.Embedding.subtype fun x => x ∈ T)) _⟩)
      simp only [← Finset.coe_map, ← Function.Embedding.coe_subtype, ← Set.mem_image, ← Finset.mem_coe, ←
        Subtype.exists, ← Subtype.coe_mk, ← exists_and_distrib_right, ← exists_eq_right]
      exact ⟨hφ, h' (Finset.mem_singleton_self _)⟩
    exact ⟨Model.of T M'⟩⟩

theorem is_satisfiable_directed_union_iff {ι : Type _} [Nonempty ι] {T : ι → L.Theory} (h : Directed (· ⊆ ·) T) :
    Theory.IsSatisfiable (⋃ i, T i) ↔ ∀ i, (T i).IsSatisfiable := by
  refine' ⟨fun h' i => h'.mono (Set.subset_Union _ _), fun h' => _⟩
  rw [is_satisfiable_iff_is_finitely_satisfiable, is_finitely_satisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_bUnion hT0
  exact (h' i).mono hi

theorem is_satisfiable_union_distinct_constants_theory_of_card_le (T : L.Theory) (s : Set α) (M : Type w') [Nonempty M]
    [L.Structure M] [M ⊨ T] (h : Cardinal.lift.{w'} (# s) ≤ Cardinal.lift.{w} (# M)) :
    ((L.lhomWithConstants α).OnTheory T ∪ L.DistinctConstantsTheory s).IsSatisfiable := by
  have : Inhabited M := Classical.inhabitedOfNonempty inferInstance
  rw [Cardinal.lift_mk_le'] at h
  let this : (constants_on α).Structure M := constants_on.Structure (Function.extendₓ coe h.some default)
  have : M ⊨ (L.Lhom_with_constants α).OnTheory T ∪ L.distinct_constants_theory s := by
    refine' ((Lhom.on_Theory_model _ _).2 inferInstance).union _
    rw [model_distinct_constants_theory]
    refine' fun a as b bs ab => _
    rw [← Subtype.coe_mk a as, ← Subtype.coe_mk b bs, ← Subtype.ext_iff]
    exact
      h.some.injective
        ((Function.extend_applyₓ Subtype.coe_injective h.some default ⟨a, as⟩).symm.trans
          (ab.trans (Function.extend_applyₓ Subtype.coe_injective h.some default ⟨b, bs⟩)))
  exact model.is_satisfiable M

theorem is_satisfiable_union_distinct_constants_theory_of_infinite (T : L.Theory) (s : Set α) (M : Type w')
    [L.Structure M] [M ⊨ T] [Infinite M] :
    ((L.lhomWithConstants α).OnTheory T ∪ L.DistinctConstantsTheory s).IsSatisfiable := by
  classical
  rw [distinct_constants_theory_eq_Union, Set.union_Union, is_satisfiable_directed_union_iff]
  · exact fun t =>
      is_satisfiable_union_distinct_constants_theory_of_card_le T _ M
        ((lift_le_aleph_0.2 (finset_card_lt_aleph_0 _).le).trans (aleph_0_le_lift.2 (aleph_0_le_mk M)))
    
  · refine' (monotone_const.union (monotone_distinct_constants_theory.comp _)).directed_le
    simp only [← Finset.coe_map, ← Function.Embedding.coe_subtype]
    exact set.monotone_image.comp fun _ _ => Finset.coe_subset.2
    

/-- Any theory with an infinite model has arbitrarily large models. -/
theorem exists_large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M : Type w') [L.Structure M] [M ⊨ T]
    [Infinite M] : ∃ N : ModelCat.{_, _, max u v w} T, Cardinal.lift.{max u v w} κ ≤ # N := by
  obtain ⟨N⟩ := is_satisfiable_union_distinct_constants_theory_of_infinite T (Set.Univ : Set κ.out) M
  refine' ⟨(N.is_model.mono (Set.subset_union_left _ _)).Bundled.reduct _, _⟩
  have : N ⊨ distinct_constants_theory _ _ := N.is_model.mono (Set.subset_union_right _ _)
  simp only [← Model.reduct_carrier, ← coe_of, ← Model.carrier_eq_coe]
  refine' trans (lift_le.2 (le_of_eqₓ (Cardinal.mk_out κ).symm)) _
  rw [← mk_univ]
  refine' (card_le_of_model_distinct_constants_theory L Set.Univ N).trans (lift_le.1 _)
  rw [lift_lift]

end Theory

variable (L)

/-- A version of The Downward Löwenheim–Skolem theorem where the structure `N` elementarily embeds
into `M`, but is not by type a substructure of `M`, and thus can be chosen to belong to the universe
of the cardinal `κ`.
 -/
theorem exists_elementary_embedding_card_eq_of_le (M : Type w') [L.Structure M] [Nonempty M] (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) (h3 : lift.{w'} κ ≤ Cardinal.lift.{w} (# M)) :
    ∃ N : Bundled L.Structure, Nonempty (N ↪ₑ[L] M) ∧ # N = κ := by
  obtain ⟨S, _, hS⟩ :=
    exists_elementary_substructure_card_eq L ∅ κ h1
      (by
        simp )
      h2 h3
  have : Small.{w} S := by
    rw [← lift_inj.{_, w + 1}, lift_lift, lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  refine'
    ⟨(equivShrink S).bundledInduced L, ⟨S.subtype.comp (Equivₓ.bundledInducedEquiv L _).symm.toElementaryEmbedding⟩,
      lift_inj.1 (trans _ hS)⟩
  simp only [← Equivₓ.bundled_induced_α, ← lift_mk_shrink']

/-- The Upward Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the cardinalities of `L`
and an infinite `L`-structure `M`, then `M` has an elementary extension of cardinality `κ`. -/
theorem exists_elementary_embedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM : Infinite M] (κ : Cardinal.{w})
    (h1 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) (h2 : Cardinal.lift.{w} (# M) ≤ Cardinal.lift.{w'} κ) :
    ∃ N : Bundled L.Structure, Nonempty (M ↪ₑ[L] N) ∧ # N = κ := by
  obtain ⟨N0, hN0⟩ := (L.elementary_diagram M).exists_large_model_of_infinite_model κ M
  let f0 := elementary_embedding.of_models_elementary_diagram L M N0
  rw [← lift_le.{max w w', max u v}, lift_lift, lift_lift] at h2
  obtain ⟨N, ⟨NN0⟩, hN⟩ :=
    exists_elementary_embedding_card_eq_of_le (L[[M]]) N0 κ
      (aleph_0_le_lift.1 ((aleph_0_le_lift.2 (aleph_0_le_mk M)).trans h2)) _ (hN0.trans _)
  · let this := (Lhom_with_constants L M).reduct N
    have h : N ⊨ L.elementary_diagram M := (NN0.Theory_model_iff (L.elementary_diagram M)).2 inferInstance
    refine' ⟨bundled.of N, ⟨_⟩, hN⟩
    apply elementary_embedding.of_models_elementary_diagram L M N
    
  · simp only [← card_with_constants, ← lift_add, ← lift_lift]
    rw [add_commₓ, add_eq_max (aleph_0_le_lift.2 (infinite_iff.1 iM)), max_le_iff]
    rw [← lift_le.{_, w'}, lift_lift, lift_lift] at h1
    exact ⟨h2, h1⟩
    
  · rw [← lift_umax', lift_id]
    

/-- The Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the cardinalities of `L`
and an infinite `L`-structure `M`, then there is an elementary embedding in the appropriate
direction between then `M` and a structure of cardinality `κ`. -/
theorem exists_elementary_embedding_card_eq (M : Type w') [L.Structure M] [iM : Infinite M] (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : Bundled L.Structure, (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧ # N = κ := by
  cases le_or_gtₓ (lift.{w'} κ) (Cardinal.lift.{w} (# M))
  · obtain ⟨N, hN1, hN2⟩ := exists_elementary_embedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, Or.inl hN1, hN2⟩
    
  · obtain ⟨N, hN1, hN2⟩ := exists_elementary_embedding_card_eq_of_ge L M κ h2 (le_of_ltₓ h)
    exact ⟨N, Or.inr hN1, hN2⟩
    

/-- A consequence of the Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the
cardinalities of `L` and an infinite `L`-structure `M`, then there is a structure of cardinality `κ`
elementarily equivalent to `M`. -/
theorem exists_elementarily_equivalent_card_eq (M : Type w') [L.Structure M] [Infinite M] (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : CategoryTheory.Bundled L.Structure, (M ≅[L] N) ∧ # N = κ := by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementary_embedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarily_equivalent.symm, hNκ⟩
    
  · exact ⟨N, MN.some.elementarily_equivalent, hNκ⟩
    

variable {L}

namespace Theory

theorem exists_model_card_eq (h : ∃ M : ModelCat.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) : ∃ N : ModelCat.{u, v, w} T, # N = κ := by
  cases' h with M MI
  obtain ⟨N, hN, rfl⟩ := exists_elementarily_equivalent_card_eq L M κ h1 h2
  have : Nonempty N := hN.nonempty
  exact ⟨hN.Theory_model.bundled, rfl⟩

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  ∀ (M : ModelCat.{u, v, max u v} T) (v : α → M) (xs : Finₓ n → M), φ.realize v xs

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => ModelsBoundedFormula

-- input using \|= or \vDash, but not using \models
variable {T}

theorem models_formula_iff {φ : L.Formula α} : T ⊨ φ ↔ ∀ (M : ModelCat.{u, v, max u v} T) (v : α → M), φ.realize v :=
  forall_congrₓ fun M => forall_congrₓ fun v => Unique.forall_iff

theorem models_sentence_iff {φ : L.Sentence} : T ⊨ φ ↔ ∀ M : ModelCat.{u, v, max u v} T, M ⊨ φ :=
  models_formula_iff.trans (forall_congrₓ fun M => Unique.forall_iff)

theorem models_sentence_of_mem {φ : L.Sentence} (h : φ ∈ T) : T ⊨ φ :=
  models_sentence_iff.2 fun _ => realize_sentence_of_mem T h

/-- A theory is complete when it is satisfiable and models each sentence or its negation. -/
def IsComplete (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, T ⊨ φ ∨ T ⊨ φ.Not

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def SemanticallyEquivalent (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ φ.Iff ψ

@[refl]
theorem SemanticallyEquivalent.refl (φ : L.BoundedFormula α n) : T.SemanticallyEquivalent φ φ := fun M v xs => by
  rw [bounded_formula.realize_iff]

instance : IsRefl (L.BoundedFormula α n) T.SemanticallyEquivalent :=
  ⟨SemanticallyEquivalent.refl⟩

@[symm]
theorem SemanticallyEquivalent.symm {φ ψ : L.BoundedFormula α n} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent ψ φ := fun M v xs => by
  rw [bounded_formula.realize_iff, Iff.comm, ← bounded_formula.realize_iff]
  exact h M v xs

@[trans]
theorem SemanticallyEquivalent.trans {φ ψ θ : L.BoundedFormula α n} (h1 : T.SemanticallyEquivalent φ ψ)
    (h2 : T.SemanticallyEquivalent ψ θ) : T.SemanticallyEquivalent φ θ := fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [bounded_formula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩

theorem SemanticallyEquivalent.realize_bd_iff {φ ψ : L.BoundedFormula α n} {M : Type max u v} [ne : Nonempty M]
    [str : L.Structure M] [hM : T.Model M] (h : T.SemanticallyEquivalent φ ψ) {v : α → M} {xs : Finₓ n → M} :
    φ.realize v xs ↔ ψ.realize v xs :=
  BoundedFormula.realize_iff.1 (h (ModelCat.of T M) v xs)

theorem SemanticallyEquivalent.realize_iff {φ ψ : L.Formula α} {M : Type max u v} [ne : Nonempty M]
    [str : L.Structure M] (hM : T.Model M) (h : T.SemanticallyEquivalent φ ψ) {v : α → M} : φ.realize v ↔ ψ.realize v :=
  h.realize_bd_iff

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semanticallyEquivalentSetoid (T : L.Theory) : Setoidₓ (L.BoundedFormula α n) where
  R := SemanticallyEquivalent T
  iseqv := ⟨fun _ => refl _, fun a b h => h.symm, fun _ _ _ h1 h2 => h1.trans h2⟩

protected theorem SemanticallyEquivalent.all {φ ψ : L.BoundedFormula α (n + 1)} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent φ.all ψ.all := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_all]
  exact fun M v xs => forall_congrₓ fun a => h.realize_bd_iff

protected theorem SemanticallyEquivalent.ex {φ ψ : L.BoundedFormula α (n + 1)} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent φ.ex ψ.ex := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff

protected theorem SemanticallyEquivalent.not {φ ψ : L.BoundedFormula α n} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent φ.Not ψ.Not := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff

protected theorem SemanticallyEquivalent.imp {φ ψ φ' ψ' : L.BoundedFormula α n} (h : T.SemanticallyEquivalent φ ψ)
    (h' : T.SemanticallyEquivalent φ' ψ') : T.SemanticallyEquivalent (φ.imp φ') (ψ.imp ψ') := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff

end Theory

namespace CompleteTheory

variable (L) (M : Type w) [L.Structure M]

theorem is_satisfiable [Nonempty M] : (L.CompleteTheory M).IsSatisfiable :=
  Theory.Model.is_satisfiable M

theorem mem_or_not_mem (φ : L.Sentence) : φ ∈ L.CompleteTheory M ∨ φ.Not ∈ L.CompleteTheory M := by
  simp_rw [complete_theory, Set.mem_set_of_eq, sentence.realize, formula.realize_not, or_not]

theorem is_complete [Nonempty M] : (L.CompleteTheory M).IsComplete :=
  ⟨is_satisfiable L M, fun φ => (mem_or_not_mem L M φ).imp Theory.models_sentence_of_mem Theory.models_sentence_of_mem⟩

end CompleteTheory

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula α n)

theorem semantically_equivalent_not_not : T.SemanticallyEquivalent φ φ.Not.Not := fun M v xs => by
  simp

theorem imp_semantically_equivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.Not⊔ψ) := fun M v xs => by
  simp [← imp_iff_not_or]

theorem sup_semantically_equivalent_not_inf_not : T.SemanticallyEquivalent (φ⊔ψ) (φ.Not⊓ψ.Not).Not := fun M v xs => by
  simp [← imp_iff_not_or]

theorem inf_semantically_equivalent_not_sup_not : T.SemanticallyEquivalent (φ⊓ψ) (φ.Not⊔ψ.Not).Not := fun M v xs => by
  simp [← and_iff_not_or_not]

theorem all_semantically_equivalent_not_ex_not (φ : L.BoundedFormula α (n + 1)) :
    T.SemanticallyEquivalent φ.all φ.Not.ex.Not := fun M v xs => by
  simp

theorem ex_semantically_equivalent_not_all_not (φ : L.BoundedFormula α (n + 1)) :
    T.SemanticallyEquivalent φ.ex φ.Not.all.Not := fun M v xs => by
  simp

theorem semantically_equivalent_all_lift_at : T.SemanticallyEquivalent φ (φ.liftAt 1 n).all := fun M v xs => by
  skip
  rw [realize_iff, realize_all_lift_at_one_self]

end BoundedFormula

namespace Formula

variable (φ ψ : L.Formula α)

theorem semantically_equivalent_not_not : T.SemanticallyEquivalent φ φ.Not.Not :=
  φ.semantically_equivalent_not_not

theorem imp_semantically_equivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.Not⊔ψ) :=
  φ.imp_semantically_equivalent_not_sup ψ

theorem sup_semantically_equivalent_not_inf_not : T.SemanticallyEquivalent (φ⊔ψ) (φ.Not⊓ψ.Not).Not :=
  φ.sup_semantically_equivalent_not_inf_not ψ

theorem inf_semantically_equivalent_not_sup_not : T.SemanticallyEquivalent (φ⊓ψ) (φ.Not⊔ψ.Not).Not :=
  φ.inf_semantically_equivalent_not_sup_not ψ

end Formula

namespace BoundedFormula

theorem IsQf.induction_on_sup_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} (h : IsQf φ)
    (hf : P (⊥ : L.BoundedFormula α n)) (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hsup : ∀ {φ₁ φ₂} (h₁ : P φ₁) (h₂ : P φ₂), P (φ₁⊔φ₂)) (hnot : ∀ {φ} (h : P φ), P φ.Not)
    (hse : ∀ {φ₁ φ₂ : L.BoundedFormula α n} (h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) : P φ :=
  IsQf.rec_on h hf ha fun φ₁ φ₂ _ _ h1 h2 => (hse (φ₁.imp_semantically_equivalent_not_sup φ₂)).2 (hsup (hnot h1) h2)

theorem IsQf.induction_on_inf_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} (h : IsQf φ)
    (hf : P (⊥ : L.BoundedFormula α n)) (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hinf : ∀ {φ₁ φ₂} (h₁ : P φ₁) (h₂ : P φ₂), P (φ₁⊓φ₂)) (hnot : ∀ {φ} (h : P φ), P φ.Not)
    (hse : ∀ {φ₁ φ₂ : L.BoundedFormula α n} (h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) : P φ :=
  h.induction_on_sup_not hf ha
    (fun φ₁ φ₂ h1 h2 => (hse (φ₁.sup_semantically_equivalent_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun _ => hnot) fun _ _ => hse

theorem semantically_equivalent_to_prenex (φ : L.BoundedFormula α n) :
    (∅ : L.Theory).SemanticallyEquivalent φ φ.toPrenex := fun M v xs => by
  rw [realize_iff, realize_to_prenex]

theorem induction_on_all_ex {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQf ψ → P ψ)
    (hall : ∀ {m} {ψ : L.BoundedFormula α (m + 1)} (h : P ψ), P ψ.all)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)} (h : P φ), P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m} (h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) : P φ := by
  suffices h' : ∀ {m} {φ : L.bounded_formula α m}, φ.IsPrenex → P φ
  · exact (hse φ.semantically_equivalent_to_prenex).2 (h' φ.to_prenex_is_prenex)
    
  intro m φ hφ
  induction' hφ with _ _ hφ _ _ _ hφ _ _ _ hφ
  · exact hqf hφ
    
  · exact hall hφ
    
  · exact hex hφ
    

theorem induction_on_exists_not {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQf ψ → P ψ) (hnot : ∀ {m} {φ : L.BoundedFormula α m} (h : P φ), P φ.Not)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)} (h : P φ), P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m} (h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) : P φ :=
  φ.induction_on_all_ex (fun _ _ => hqf)
    (fun _ φ hφ => (hse φ.all_semantically_equivalent_not_ex_not).2 (hnot (hex (hnot hφ)))) (fun _ _ => hex)
    fun _ _ _ => hse

end BoundedFormula

end Language

end FirstOrder

namespace Cardinal

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} (κ : Cardinal.{w}) (T : L.Theory)

/-- A theory is `κ`-categorical if all models of size `κ` are isomorphic. -/
def Categorical : Prop :=
  ∀ M N : T.Model, # M = κ → # N = κ → Nonempty (M ≃[L] N)

/-- The Łoś–Vaught Test : a criterion for categorical theories to be complete. -/
theorem Categorical.is_complete (h : κ.Categorical T) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) (hS : T.IsSatisfiable)
    (hT : ∀ M : Theory.ModelCat.{u, v, max u v} T, Infinite M) : T.IsComplete :=
  ⟨hS, fun φ => by
    obtain ⟨N, hN⟩ := Theory.exists_model_card_eq ⟨hS.some, hT hS.some⟩ κ h1 h2
    rw [Theory.models_sentence_iff, Theory.models_sentence_iff]
    by_contra con
    push_neg  at con
    obtain ⟨⟨MF, hMF⟩, MT, hMT⟩ := con
    rw [sentence.realize_not, not_not] at hMT
    refine' hMF _
    have := hT MT
    have := hT MF
    obtain ⟨NT, MNT, hNT⟩ := exists_elementarily_equivalent_card_eq L MT κ h1 h2
    obtain ⟨NF, MNF, hNF⟩ := exists_elementarily_equivalent_card_eq L MF κ h1 h2
    obtain ⟨TF⟩ := h (MNT.to_Model T) (MNF.to_Model T) hNT hNF
    exact ((MNT.realize_sentence φ).trans ((TF.realize_sentence φ).trans (MNF.realize_sentence φ).symm)).1 hMT⟩

theorem empty_Theory_categorical (T : Language.empty.Theory) : κ.Categorical T := fun M N hM hN => by
  rw [empty.nonempty_equiv_iff, hM, hN]

theorem empty_infinite_Theory_is_complete : Language.empty.InfiniteTheory.IsComplete :=
  (empty_Theory_categorical ℵ₀ _).IsComplete ℵ₀ _ le_rfl
    (by
      simp )
    ⟨Theory.Model.bundled ((model_infinite_theory_iff Language.empty).2 Nat.infinite)⟩ fun M =>
    (model_infinite_theory_iff Language.empty).1 M.is_model

end Cardinal

