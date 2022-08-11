/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.ModelTheory.Substructures

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions
* A `first_order.language.elementary_embedding` is an embedding that commutes with the
  realizations of formulas.
* A `first_order.language.elementary_substructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.
* The `first_order.language.elementary_diagram` of a structure is the set of all sentences with
  parameters that the structure satisfies.
* `first_order.language.elementary_embedding.of_models_elementary_diagram` is the canonical
elementary embedding of any structure into a model of its elementary diagram.

## Main Results
* The Tarski-Vaught Test for embeddings: `first_order.language.embedding.is_elementary_of_exists`
gives a simple criterion for an embedding to be elementary.
* The Tarski-Vaught Test for substructures: `first_order.language.embedding.is_elementary_of_exists`
gives a simple criterion for a substructure to be elementary.
 -/


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable (L : Language) (M : Type _) (N : Type _) {P : Type _} {Q : Type _}

variable [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/-- An elementary embedding of first-order structures is an embedding that commutes with the
  realizations of formulas. -/
structure ElementaryEmbedding where
  toFun : M → N
  map_formula' : ∀ {n} (φ : L.Formula (Finₓ n)) (x : Finₓ n → M), φ.realize (to_fun ∘ x) ↔ φ.realize x := by
    run_tac
      obviously

-- mathport name: «expr ↪ₑ[ ] »
localized [FirstOrder] notation:25 A " ↪ₑ[" L "] " B => FirstOrder.Language.ElementaryEmbedding L A B

variable {L} {M} {N}

namespace ElementaryEmbedding

instance funLike : FunLike (M ↪ₑ[L] N) M fun _ => N where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iffₓ.1 h x

instance : CoeFun (M ↪ₑ[L] N) fun _ => M → N :=
  FunLike.hasCoeToFun

@[simp]
theorem map_bounded_formula (f : M ↪ₑ[L] N) {α : Type} {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M)
    (xs : Finₓ n → M) : φ.realize (f ∘ v) (f ∘ xs) ↔ φ.realize v xs := by
  classical
  rw [← bounded_formula.realize_restrict_free_var Set.Subset.rfl, Set.inclusion_eq_id, iff_eq_eq]
  swap
  · infer_instance
    
  have h :=
    f.map_formula' ((φ.restrict_free_var id).toFormula.relabel (Fintype.equivFin _))
      (Sum.elim (v ∘ coe) xs ∘ (Fintype.equivFin _).symm)
  simp only [← formula.realize_relabel, ← bounded_formula.realize_to_formula, ← iff_eq_eq] at h
  rw [← Function.comp.assoc _ _ (Fintype.equivFin _).symm,
    Function.comp.assoc _ (Fintype.equivFin _).symm (Fintype.equivFin _), Equivₓ.symm_comp_self, Function.comp.right_id,
    Function.comp.assoc, Sum.elim_comp_inl, Function.comp.assoc _ _ Sum.inr, Sum.elim_comp_inr, ←
    Function.comp.assoc] at h
  refine' h.trans _
  rw [Function.comp.assoc _ _ (Fintype.equivFin _), Equivₓ.symm_comp_self, Function.comp.right_id, Sum.elim_comp_inl,
    Sum.elim_comp_inr, ← Set.inclusion_eq_id, bounded_formula.realize_restrict_free_var Set.Subset.rfl]

@[simp]
theorem map_formula (f : M ↪ₑ[L] N) {α : Type} (φ : L.Formula α) (x : α → M) : φ.realize (f ∘ x) ↔ φ.realize x := by
  rw [formula.realize, formula.realize, ← f.map_bounded_formula, Unique.eq_default (f ∘ default)]

theorem map_sentence (f : M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [sentence.realize, sentence.realize, ← f.map_formula, Unique.eq_default (f ∘ default)]

theorem Theory_model_iff (f : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T := by
  simp only [← Theory.model_iff, ← f.map_sentence]

theorem elementarily_equivalent (f : M ↪ₑ[L] N) : M ≅[L] N :=
  elementarily_equivalent_iff.2 f.map_sentence

@[simp]
theorem injective (φ : M ↪ₑ[L] N) : Function.Injective φ := by
  intro x y
  have h := φ.map_formula ((var 0).equal (var 1) : L.formula (Finₓ 2)) fun i => if i = 0 then x else y
  rw [formula.realize_equal, formula.realize_equal] at h
  simp only [← Nat.one_ne_zero, ← term.realize, ← Finₓ.one_eq_zero_iff, ← if_true, ← eq_self_iff_true, ←
    Function.comp_app, ← if_false] at h
  exact h.1

instance embeddingLike : EmbeddingLike (M ↪ₑ[L] N) M N where injective' := injective

@[simp]
theorem map_fun (φ : M ↪ₑ[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) := by
  have h := φ.map_formula (formula.graph f) (Finₓ.cons (fun_map f x) x)
  rw [formula.realize_graph, Finₓ.comp_cons, formula.realize_graph] at h
  rw [eq_comm, h]

@[simp]
theorem map_rel (φ : M ↪ₑ[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r (φ ∘ x) ↔ RelMap r x := by
  have h := φ.map_formula (r.formula var) x
  exact h

instance strongHomClass : StrongHomClass L (M ↪ₑ[L] N) M N where
  map_fun := map_fun
  map_rel := map_rel

@[simp]
theorem map_constants (φ : M ↪ₑ[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

/-- An elementary embedding is also a first-order embedding. -/
def toEmbedding (f : M ↪ₑ[L] N) : M ↪[L] N where
  toFun := f
  inj' := f.Injective

/-- An elementary embedding is also a first-order homomorphism. -/
def toHom (f : M ↪ₑ[L] N) : M →[L] N where toFun := f

@[simp]
theorem to_embedding_to_hom (f : M ↪ₑ[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
theorem coe_to_hom {f : M ↪ₑ[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl

@[simp]
theorem coe_to_embedding (f : M ↪ₑ[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl

theorem coe_injective : @Function.Injective (M ↪ₑ[L] N) (M → N) coeFn :=
  FunLike.coe_injective

@[ext]
theorem ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

theorem ext_iff {f g : M ↪ₑ[L] N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

variable (L) (M)

/-- The identity elementary embedding from a structure to itself -/
@[refl]
def refl : M ↪ₑ[L] M where toFun := id

variable {L} {M}

instance : Inhabited (M ↪ₑ[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of elementary embeddings -/
@[trans]
def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where toFun := hnp ∘ hmn

@[simp]
theorem comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of elementary embeddings is associative. -/
theorem comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end ElementaryEmbedding

variable (L) (M)

/-- The elementary diagram of an `L`-structure is the set of all sentences with parameters it
  satisfies. -/
abbrev ElementaryDiagram : L[[M]].Theory :=
  L[[M]].CompleteTheory M

/-- The canonical elementary embedding of an `L`-structure into any model of its elementary diagram
-/
@[simps]
def ElementaryEmbedding.ofModelsElementaryDiagram (N : Type _) [L.Structure N] [L[[M]].Structure N]
    [(lhomWithConstants L M).IsExpansionOn N] [N ⊨ L.ElementaryDiagram M] : M ↪ₑ[L] N :=
  ⟨(coe : L[[M]].Constants → N) ∘ Sum.inr, fun n φ x => by
    refine'
      trans _
        ((realize_iff_of_model_complete_theory M N
              (((L.Lhom_with_constants M).onBoundedFormula φ).subst (constants.term ∘ Sum.inr ∘ x)).alls).trans
          _)
    · simp_rw [sentence.realize, bounded_formula.realize_alls, bounded_formula.realize_subst,
        Lhom.realize_on_bounded_formula, formula.realize, Unique.forall_iff, realize_constants]
      
    · simp_rw [sentence.realize, bounded_formula.realize_alls, bounded_formula.realize_subst,
        Lhom.realize_on_bounded_formula, formula.realize, Unique.forall_iff]
      rfl
      ⟩

variable {L M}

namespace Embedding

/-- The Tarski-Vaught test for elementarity of an embedding. -/
theorem is_elementary_of_exists (f : M ↪[L] N)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Finₓ n → M) (a : N),
        φ.realize default (Finₓ.snoc (f ∘ x) a : _ → N) →
          ∃ b : M, φ.realize default (Finₓ.snoc (f ∘ x) (f b) : _ → N)) :
    ∀ {n} (φ : L.Formula (Finₓ n)) (x : Finₓ n → M), φ.realize (f ∘ x) ↔ φ.realize x := by
  suffices h :
    ∀ (n : ℕ) (φ : L.bounded_formula Empty n) (xs : Finₓ n → M), φ.realize (f ∘ default) (f ∘ xs) ↔ φ.realize default xs
  · intro n φ x
    refine' φ.realize_relabel_sum_inr.symm.trans (trans (h n _ _) φ.realize_relabel_sum_inr)
    
  refine' fun n φ => φ.recOn _ _ _ _ _
  · exact fun _ _ => Iff.rfl
    
  · intros
    simp [← bounded_formula.realize, Sum.comp_elim, ← embedding.realize_term]
    
  · intros
    simp [← bounded_formula.realize, Sum.comp_elim, ← embedding.realize_term]
    
  · intro _ _ _ ih1 ih2 _
    simp [← ih1, ← ih2]
    
  · intro n φ ih xs
    simp only [← bounded_formula.realize_all]
    refine' ⟨fun h a => _, _⟩
    · rw [← ih, Finₓ.comp_snoc]
      exact h (f a)
      
    · contrapose!
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := htv n φ.not xs a _
      · refine' ⟨b, fun h => hb (Eq.mp _ ((ih _).2 h))⟩
        rw [Unique.eq_default (f ∘ default), Finₓ.comp_snoc]
        
      · rw [bounded_formula.realize_not, ← Unique.eq_default (f ∘ default)]
        exact ha
        
      
    

/-- Bundles an embedding satisfying the Tarski-Vaught test as an elementary embedding. -/
@[simps]
def toElementaryEmbedding (f : M ↪[L] N)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Finₓ n → M) (a : N),
        φ.realize default (Finₓ.snoc (f ∘ x) a : _ → N) →
          ∃ b : M, φ.realize default (Finₓ.snoc (f ∘ x) (f b) : _ → N)) :
    M ↪ₑ[L] N :=
  ⟨f, fun _ => f.is_elementary_of_exists htv⟩

end Embedding

namespace Equivₓ

/-- A first-order equivalence is also an elementary embedding. -/
def toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N where toFun := f

@[simp]
theorem to_elementary_embedding_to_embedding (f : M ≃[L] N) : f.toElementaryEmbedding.toEmbedding = f.toEmbedding :=
  rfl

@[simp]
theorem coe_to_elementary_embedding (f : M ≃[L] N) : (f.toElementaryEmbedding : M → N) = (f : M → N) :=
  rfl

end Equivₓ

@[simp]
theorem realize_term_substructure {α : Type _} {S : L.Substructure M} (v : α → S) (t : L.Term α) :
    t.realize (coe ∘ v) = (↑(t.realize v) : M) :=
  S.Subtype.realize_term t

namespace Substructure

@[simp]
theorem realize_bounded_formula_top {α : Type _} {n : ℕ} {φ : L.BoundedFormula α n} {v : α → (⊤ : L.Substructure M)}
    {xs : Finₓ n → (⊤ : L.Substructure M)} : φ.realize v xs ↔ φ.realize ((coe : _ → M) ∘ v) (coe ∘ xs) := by
  rw [← substructure.top_equiv.realize_bounded_formula φ]
  simp

@[simp]
theorem realize_formula_top {α : Type _} {φ : L.Formula α} {v : α → (⊤ : L.Substructure M)} :
    φ.realize v ↔ φ.realize ((coe : (⊤ : L.Substructure M) → M) ∘ v) := by
  rw [← substructure.top_equiv.realize_formula φ]
  simp

/-- A substructure is elementary when every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
def IsElementary (S : L.Substructure M) : Prop :=
  ∀ {n} (φ : L.Formula (Finₓ n)) (x : Finₓ n → S), φ.realize ((coe : _ → M) ∘ x) ↔ φ.realize x

end Substructure

variable (L) (M)

/-- An elementary substructure is one in which every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
structure ElementarySubstructure where
  toSubstructure : L.Substructure M
  is_elementary' : to_substructure.IsElementary

variable {L} {M}

namespace ElementarySubstructure

instance : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩

instance : SetLike (L.ElementarySubstructure M) M :=
  ⟨fun x => x.toSubstructure.Carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, ht2⟩ h => by
    congr
    exact h⟩

@[simp]
theorem is_elementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.is_elementary'

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := coe
  map_formula' := fun n => S.IsElementary

@[simp]
theorem coe_subtype {S : L.ElementarySubstructure M} : ⇑S.Subtype = coe :=
  rfl

/-- The substructure `M` of the structure `M` is elementary. -/
instance : HasTop (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun n φ x => Substructure.realize_formula_top.symm⟩⟩

instance : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.ElementarySubstructure M) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.Univ :=
  rfl

@[simp]
theorem realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) : S ⊨ φ ↔ M ⊨ φ :=
  S.Subtype.map_sentence φ

@[simp]
theorem Theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔ M ⊨ T := by
  simp only [← Theory.model_iff, ← realize_sentence]

instance Theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} : S ⊨ T :=
  (Theory_model_iff S T).2 h

instance [h : Nonempty M] {S : L.ElementarySubstructure M} : Nonempty S :=
  (model_nonempty_theory_iff L).1 inferInstance

theorem elementarily_equivalent (S : L.ElementarySubstructure M) : S ≅[L] M :=
  S.Subtype.ElementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/-- The Tarski-Vaught test for elementarity of a substructure. -/
theorem is_elementary_of_exists (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Finₓ n → S) (a : M),
        φ.realize default (Finₓ.snoc (coe ∘ x) a : _ → M) →
          ∃ b : S, φ.realize default (Finₓ.snoc (coe ∘ x) b : _ → M)) :
    S.IsElementary := fun n => S.Subtype.is_elementary_of_exists htv

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps]
def toElementarySubstructure (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Finₓ n → S) (a : M),
        φ.realize default (Finₓ.snoc (coe ∘ x) a : _ → M) →
          ∃ b : S, φ.realize default (Finₓ.snoc (coe ∘ x) b : _ → M)) :
    L.ElementarySubstructure M :=
  ⟨S, fun _ => S.is_elementary_of_exists htv⟩

end Substructure

end Language

end FirstOrder

