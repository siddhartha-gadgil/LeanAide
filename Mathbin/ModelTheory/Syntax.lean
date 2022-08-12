/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.Data.List.ProdSigma
import Mathbin.Data.Set.Prod
import Mathbin.Logic.Equiv.Fin
import Mathbin.ModelTheory.LanguageMap

/-!
# Basics on First-Order Syntax
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.Theory` is a set of sentences.
* The variables of terms and formulas can be relabelled with `first_order.language.term.relabel`,
`first_order.language.bounded_formula.relabel`, and `first_order.language.formula.relabel`.
* Given an operation on terms and an operation on relations,
  `first_order.language.bounded_formula.map_term_rel` gives an operation on formulas.
* `first_order.language.bounded_formula.cast_le` adds more `fin`-indexed variables.
* `first_order.language.bounded_formula.lift_at` raises the indexes of the `fin`-indexed variables
above a particular index.
* `first_order.language.term.subst` and `first_order.language.bounded_formula.subst` substitute
variables with given terms.
* Language maps can act on syntactic objects with functions such as
`first_order.language.Lhom.on_formula`.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.bounded_formula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `fin n`, which can. For any `φ : L.bounded_formula α (n + 1)`, we define the formula
`∀' φ : L.bounded_formula α n` by universally quantifying over the variable indexed by
`n : fin (n + 1)`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {L' : Language}

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'} {γ : Type _}

open FirstOrder

open Structure Finₓ

-- ./././Mathport/Syntax/Translate/Basic.lean:1422:30: infer kinds are unsupported in Lean 4: var {}
-- ./././Mathport/Syntax/Translate/Basic.lean:1422:30: infer kinds are unsupported in Lean 4: func {}
/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term (α : Type u') : Type max u u'
  | var : ∀ a : α, term
  | func : ∀ {l : ℕ} (f : L.Functions l) (ts : Finₓ l → term), term

export Term ()

variable {L}

namespace Term

open Finset

/-- The `finset` of variables used in a given term. -/
@[simp]
def varFinsetₓ [DecidableEq α] : L.Term α → Finset α
  | var i => {i}
  | func f ts => univ.bUnion fun i => (ts i).varFinset

/-- The `finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeftₓ [DecidableEq α] : L.Term (Sum α β) → Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr i) => ∅
  | func f ts => univ.bUnion fun i => (ts i).varFinsetLeft

/-- Relabels a term's variables along a particular function. -/
@[simp]
def relabelₓ (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun i => (ts i).relabel

theorem relabel_id (t : L.Term α) : t.relabel id = t := by
  induction' t with _ _ _ _ ih
  · rfl
    
  · simp [← ih]
    

@[simp]
theorem relabel_id_eq_id : (Term.relabelₓ id : L.Term α → L.Term α) = id :=
  funext relabel_id

@[simp]
theorem relabel_relabel (f : α → β) (g : β → γ) (t : L.Term α) : (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction' t with _ _ _ _ ih
  · rfl
    
  · simp [← ih]
    

@[simp]
theorem relabel_comp_relabel (f : α → β) (g : β → γ) :
    (Term.relabelₓ g ∘ Term.relabelₓ f : L.Term α → L.Term γ) = Term.relabelₓ (g ∘ f) :=
  funext (relabel_relabel f g)

/-- Restricts a term to use only a set of the given variables. -/
def restrictVarₓ [DecidableEq α] : ∀ (t : L.Term α) (f : t.varFinset → β), L.Term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f => func F fun i => (ts i).restrictVar (f ∘ Set.inclusion (subset_bUnion_of_mem _ (mem_univ i)))

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeftₓ [DecidableEq α] {γ : Type _} : ∀ (t : L.Term (Sum α γ)) (f : t.varFinsetLeft → β), L.Term (Sum β γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), f => var (Sum.inr a)
  | func F ts, f => func F fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_bUnion_of_mem _ (mem_univ i)))

end Term

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants) : L.Term α :=
  func c default

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]

/-- Applies a binary function to two terms. -/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]

namespace Term

instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩

instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).Term⟩

/-- Raises all of the `fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (Sum α (Finₓ n)) → L.Term (Sum α (Finₓ (n + n'))) :=
  relabelₓ (Sum.map id fun i => if ↑i < m then Finₓ.castAdd n' i else Finₓ.addNat n' i)

/-- Substitutes the variables in a given term with terms. -/
@[simp]
def substₓ : L.Term α → (α → L.Term β) → L.Term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf

end Term

-- mathport name: «expr& »
localized [FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

namespace Lhom

/-- Maps a term's symbols along a language map. -/
@[simp]
def onTermₓ (φ : L →ᴸ L') : L.Term α → L'.Term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => on_term (ts i)

@[simp]
theorem id_on_term : ((Lhom.id L).onTerm : L.Term α → L.Term α) = id := by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
    
  · simp_rw [on_term, ih]
    rfl
    

@[simp]
theorem comp_on_term {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α → L''.Term α) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
    
  · simp_rw [on_term, ih]
    rfl
    

end Lhom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def Lequiv.onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLhom.onTerm
  invFun := φ.invLhom.onTerm
  left_inv := by
    rw [Function.left_inverse_iff_comp, ← Lhom.comp_on_term, φ.left_inv, Lhom.id_on_term]
  right_inv := by
    rw [Function.right_inverse_iff_comp, ← Lhom.comp_on_term, φ.right_inv, Lhom.id_on_term]

variable (L) (α)

-- ./././Mathport/Syntax/Translate/Basic.lean:1422:30: infer kinds are unsupported in Lean 4: falsum {}
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : bounded_formula n
  | equal {n} (t₁ t₂ : L.Term (Sum α (Finₓ n))) : bounded_formula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Finₓ l → L.Term (Sum α (Finₓ n))) : bounded_formula n
  | imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
  | all {n} (f : bounded_formula (n + 1)) : bounded_formula n

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible]
def Formula :=
  L.BoundedFormula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible]
def Sentence :=
  L.Formula Empty

/-- A theory is a set of sentences. -/
@[reducible]
def Theory :=
  Set L.Sentence

variable {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Finₓ n → L.Term (Sum α (Finₓ l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  r.BoundedFormula ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  r.BoundedFormula ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a bounded formula. -/
def Relations.formula (R : L.Relations n) (ts : Finₓ n → L.Term α) : L.Formula α :=
  R.BoundedFormula fun i => (ts i).relabel Sum.inl

/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.Formula ![t]

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.Formula ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

instance : HasBot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[matchPattern]
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[matchPattern]
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.Not.all.Not

instance : HasTop (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩

instance : HasInf (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.Not).Not⟩

instance : HasSup (L.BoundedFormula α n) :=
  ⟨fun f g => f.Not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ⊓ψ.imp φ

open Finset

/-- The `finset` of variables used in a given formula. -/
@[simp]
def freeVarFinsetₓ [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | n, falsum => ∅
  | n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | n, rel R ts => univ.bUnion fun i => (ts i).varFinsetLeft
  | n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | n, all f => f.freeVarFinset

/-- Casts `L.bounded_formula α m` as `L.bounded_formula α n`, where `m ≤ n`. -/
@[simp]
def castLeₓ : ∀ {m n : ℕ} (h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | m, n, h, falsum => falsum
  | m, n, h, equal t₁ t₂ => equal (t₁.relabel (Sum.map id (Finₓ.castLe h))) (t₂.relabel (Sum.map id (Finₓ.castLe h)))
  | m, n, h, rel R ts => rel R (Term.relabelₓ (Sum.map id (Finₓ.castLe h)) ∘ ts)
  | m, n, h, imp f₁ f₂ => (f₁.cast_le h).imp (f₂.cast_le h)
  | m, n, h, all f => (f.cast_le (add_le_add_right h 1)).all

@[simp]
theorem cast_le_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.cast_le h = φ := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp [← Finₓ.cast_le_of_eq]
    
  · simp [← Finₓ.cast_le_of_eq]
    
  · simp [← Finₓ.cast_le_of_eq, ← ih1, ← ih2]
    
  · simp [← Finₓ.cast_le_of_eq, ← ih3]
    

@[simp]
theorem cast_le_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.cast_le km).cast_le mn = φ.cast_le (km.trans mn) := by
  revert m n
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 <;> intro m n km mn
  · rfl
    
  · simp
    
  · simp only [← cast_le, ← eq_self_iff_true, ← heq_iff_eq, ← true_andₓ]
    rw [← Function.comp.assoc, relabel_comp_relabel]
    simp
    
  · simp [← ih1, ← ih2]
    
  · simp only [← cast_le, ← ih3]
    

@[simp]
theorem cast_le_comp_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLeₓ mn ∘ BoundedFormula.castLeₓ km : L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLeₓ (km.trans mn) :=
  funext (cast_le_cast_le km mn)

/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVarₓ [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (f : φ.freeVarFinset → β), L.BoundedFormula β n
  | n, falsum, f => falsum
  | n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion (subset_union_left _ _)))
      (t₂.restrictVarLeft (f ∘ Set.inclusion (subset_union_right _ _)))
  | n, rel R ts, f => rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_bUnion_of_mem _ (mem_univ i)))
  | n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion (subset_union_left _ _))).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion (subset_union_right _ _)))
  | n, all φ, f => (φ.restrictFreeVar f).all

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def allsₓ : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | n + 1, φ => φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exsₓ : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | n + 1, φ => φ.ex.exs

/-- Maps bounded formulas along a map of terms and a map of relations. -/
def mapTermRelₓ {g : ℕ → ℕ} (ft : ∀ n, L.Term (Sum α (Finₓ n)) → L'.Term (Sum β (Finₓ (g n))))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) :
    ∀ {n}, L.BoundedFormula α n → L'.BoundedFormula β (g n)
  | n, falsum => falsum
  | n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | n, rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | n, imp φ₁ φ₂ => φ₁.mapTermRel.imp φ₂.mapTermRel
  | n, all φ => (h n φ.mapTermRel).all

/-- Raises all of the `fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def liftAt : ∀ {n : ℕ} (n' m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') := fun n n' m φ =>
  φ.mapTermRel (fun k t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLeₓ
      (by
        rw [add_assocₓ, add_commₓ 1, add_assocₓ])

@[simp]
theorem map_term_rel_map_term_rel {L'' : Language} (ft : ∀ n, L.Term (Sum α (Finₓ n)) → L'.Term (Sum β (Finₓ n)))
    (fr : ∀ n, L.Relations n → L'.Relations n) (ft' : ∀ n, L'.Term (Sum β (Finₓ n)) → L''.Term (Sum γ (Finₓ n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp [← map_term_rel]
    
  · simp [← map_term_rel]
    
  · simp [← map_term_rel, ← ih1, ← ih2]
    
  · simp [← map_term_rel, ← ih3]
    

@[simp]
theorem map_term_rel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp [← map_term_rel]
    
  · simp [← map_term_rel]
    
  · simp [← map_term_rel, ← ih1, ← ih2]
    
  · simp [← map_term_rel, ← ih3]
    

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
def mapTermRelEquiv (ft : ∀ n, L.Term (Sum α (Finₓ n)) ≃ L'.Term (Sum β (Finₓ n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRelₓ (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRelₓ (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by
    simp , fun φ => by
    simp ⟩

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → Sum β (Finₓ n)) (k : ℕ) : Sum α (Finₓ k) → Sum β (Finₓ (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equivₓ.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
theorem sum_elim_comp_relabel_aux {m : ℕ} {g : α → Sum β (Finₓ n)} {v : β → M} {xs : Finₓ (n + m) → M} :
    Sum.elim v xs ∘ relabelAux g m = Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  cases x
  · simp only [← bounded_formula.relabel_aux, ← Function.comp_app, ← Sum.map_inl, ← Sum.elim_inl]
    cases' g x with l r <;> simp
    
  · simp [← bounded_formula.relabel_aux]
    

@[simp]
theorem relabel_aux_sum_inl (k : ℕ) : relabelAux (Sum.inl : α → Sum α (Finₓ n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;>
    · simp [← relabel_aux]
      

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → Sum β (Finₓ n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ => castLeₓ (ge_of_eq (add_assocₓ _ _ _))

@[simp]
theorem relabel_falsum (g : α → Sum β (Finₓ n)) {k} : (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl

@[simp]
theorem relabel_bot (g : α → Sum β (Finₓ n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl

@[simp]
theorem relabel_imp (g : α → Sum β (Finₓ n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl

@[simp]
theorem relabel_not (g : α → Sum β (Finₓ n)) {k} (φ : L.BoundedFormula α k) : φ.Not.relabel g = (φ.relabel g).Not := by
  simp [← bounded_formula.not]

@[simp]
theorem relabel_all (g : α → Sum β (Finₓ n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel, map_term_rel, relabel]
  simp

@[simp]
theorem relabel_ex (g : α → Sum β (Finₓ n)) {k} (φ : L.BoundedFormula α (k + 1)) : φ.ex.relabel g = (φ.relabel g).ex :=
  by
  simp [← bounded_formula.ex]

@[simp]
theorem relabel_sum_inl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.cast_le (ge_of_eq (zero_addₓ n)) := by
  simp only [← relabel, ← relabel_aux_sum_inl]
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp [← Finₓ.nat_add_zero, ← cast_le_of_eq, ← map_term_rel]
    
  · simp [← Finₓ.nat_add_zero, ← cast_le_of_eq, ← map_term_rel]
    
  · simp [← map_term_rel, ← ih1, ← ih2]
    
  · simp [← map_term_rel, ← ih3, ← cast_le]
    

/-- Substitutes the variables in a given formula with terms. -/
@[simp]
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabelₓ Sum.inl ∘ f) (var ∘ Sum.inr))) (fun _ => id) fun _ => id

/-- Turns the extra variables of a bounded formula into free variables. -/
@[simp]
def toFormulaₓ : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (Sum α (Finₓ n))
  | n, falsum => falsum
  | n, equal t₁ t₂ => t₁.equal t₂
  | n, rel R ts => R.Formula ts
  | n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | n, all φ => (φ.toFormula.relabel (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}

variable {v : α → M} {xs : Finₓ l → M}

/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive IsAtomic : L.BoundedFormula α n → Prop
  | equal (t₁ t₂ : L.Term (Sum α (Finₓ n))) : is_atomic (bdEqual t₁ t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Finₓ l → L.Term (Sum α (Finₓ n))) : is_atomic (R.BoundedFormula ts)

theorem not_all_is_atomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases con

theorem not_ex_is_atomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by
  cases con

theorem IsAtomic.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic) (f : α → Sum β (Finₓ n)) :
    (φ.relabel f).IsAtomic :=
  IsAtomic.rec_on h (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _

theorem IsAtomic.lift_at {k m : ℕ} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.rec_on h (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _

theorem IsAtomic.cast_le {h : l ≤ n} (hφ : IsAtomic φ) : (φ.cast_le h).IsAtomic :=
  IsAtomic.rec_on hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive IsQf : L.BoundedFormula α n → Prop
  | falsum : is_qf falsum
  | of_is_atomic {φ} (h : IsAtomic φ) : is_qf φ
  | imp {φ₁ φ₂} (h₁ : is_qf φ₁) (h₂ : is_qf φ₂) : is_qf (φ₁.imp φ₂)

theorem IsAtomic.is_qf {φ : L.BoundedFormula α n} : IsAtomic φ → IsQf φ :=
  is_qf.of_is_atomic

theorem is_qf_bot : IsQf (⊥ : L.BoundedFormula α n) :=
  is_qf.falsum

theorem IsQf.not {φ : L.BoundedFormula α n} (h : IsQf φ) : IsQf φ.Not :=
  h.imp is_qf_bot

theorem IsQf.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQf) (f : α → Sum β (Finₓ n)) : (φ.relabel f).IsQf :=
  IsQf.rec_on h is_qf_bot (fun _ h => (h.relabel f).IsQf) fun _ _ _ _ h1 h2 => h1.imp h2

theorem IsQf.lift_at {k m : ℕ} (h : IsQf φ) : (φ.liftAt k m).IsQf :=
  IsQf.rec_on h is_qf_bot (fun _ ih => ih.liftAt.IsQf) fun _ _ _ _ ih1 ih2 => ih1.imp ih2

theorem IsQf.cast_le {h : l ≤ n} (hφ : IsQf φ) : (φ.cast_le h).IsQf :=
  IsQf.rec_on hφ is_qf_bot (fun _ ih => ih.cast_le.IsQf) fun _ _ _ _ ih1 ih2 => ih1.imp ih2

theorem not_all_is_qf (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQf := fun con => by
  cases' con with _ con
  exact φ.not_all_is_atomic con

theorem not_ex_is_qf (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQf := fun con => by
  cases' con with _ con _ _ con
  · exact φ.not_ex_is_atomic con
    
  · exact not_all_is_qf _ con
    

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive IsPrenex : ∀ {n}, L.BoundedFormula α n → Prop
  | of_is_qf {n} {φ : L.BoundedFormula α n} (h : IsQf φ) : is_prenex φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : is_prenex φ) : is_prenex φ.all
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (h : is_prenex φ) : is_prenex φ.ex

theorem IsQf.is_prenex {φ : L.BoundedFormula α n} : IsQf φ → IsPrenex φ :=
  is_prenex.of_is_qf

theorem IsAtomic.is_prenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.IsQf.IsPrenex

theorem IsPrenex.induction_on_all_not {P : ∀ {n}, L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsPrenex φ) (hq : ∀ {m} {ψ : L.BoundedFormula α m}, ψ.IsQf → P ψ)
    (ha : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hn : ∀ {m} {ψ : L.BoundedFormula α m}, P ψ → P ψ.Not) : P φ :=
  IsPrenex.rec_on h (fun _ _ => hq) (fun _ _ _ => ha) fun _ _ _ ih => hn (ha (hn ih))

theorem IsPrenex.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsPrenex) (f : α → Sum β (Finₓ n)) :
    (φ.relabel f).IsPrenex :=
  IsPrenex.rec_on h (fun _ _ h => (h.relabel f).IsPrenex)
    (fun _ _ _ h => by
      simp [← h.all])
    fun _ _ _ h => by
    simp [← h.ex]

theorem IsPrenex.cast_le (hφ : IsPrenex φ) : ∀ {n} {h : l ≤ n}, (φ.cast_le h).IsPrenex :=
  IsPrenex.rec_on hφ (fun _ _ ih _ _ => ih.cast_le.IsPrenex) (fun _ _ _ ih _ _ => ih.all) fun _ _ _ ih _ _ => ih.ex

theorem IsPrenex.lift_at {k m : ℕ} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.rec_on h (fun _ _ ih => ih.liftAt.IsPrenex) (fun _ _ _ ih => ih.cast_le.all) fun _ _ _ ih => ih.cast_le.ex

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.to_prenex_imp_right ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpRightₓ : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, φ, bounded_formula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | n, φ, ψ => φ.imp ψ

theorem IsQf.to_prenex_imp_right {φ : L.BoundedFormula α n} :
    ∀ {ψ : L.BoundedFormula α n}, IsQf ψ → φ.toPrenexImpRight ψ = φ.imp ψ
  | _, is_qf.falsum => rfl
  | _, is_qf.of_is_atomic (is_atomic.equal _ _) => rfl
  | _, is_qf.of_is_atomic (is_atomic.rel _ _) => rfl
  | _, is_qf.imp is_qf.falsum _ => rfl
  | _, is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _ => rfl
  | _, is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _ => rfl
  | _, is_qf.imp (is_qf.imp _ _) _ => rfl

theorem is_prenex_to_prenex_imp_right {φ ψ : L.BoundedFormula α n} (hφ : IsQf φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) := by
  induction' hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2
  · rw [hψ.to_prenex_imp_right]
    exact (hφ.imp hψ).IsPrenex
    
  · exact (ih1 hφ.lift_at).all
    
  · exact (ih2 hφ.lift_at).ex
    

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.to_prenex_imp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpₓ : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, bounded_formula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ

theorem IsQf.to_prenex_imp : ∀ {φ ψ : L.BoundedFormula α n}, φ.IsQf → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, is_qf.falsum => rfl
  | _, _, is_qf.of_is_atomic (is_atomic.equal _ _) => rfl
  | _, _, is_qf.of_is_atomic (is_atomic.rel _ _) => rfl
  | _, _, is_qf.imp is_qf.falsum _ => rfl
  | _, _, is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _ => rfl
  | _, _, is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _ => rfl
  | _, _, is_qf.imp (is_qf.imp _ _) _ => rfl

theorem is_prenex_to_prenex_imp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) := by
  induction' hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2
  · rw [hφ.to_prenex_imp]
    exact is_prenex_to_prenex_imp_right hφ hψ
    
  · exact (ih1 hψ.lift_at).ex
    
  · exact (ih2 hψ.lift_at).all
    

/-- For any bounded formula `φ`, `φ.to_prenex` is a semantically-equivalent formula in prenex normal
  form. -/
def toPrenexₓ : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all

theorem to_prenex_is_prenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ (fun _ => is_qf_bot.IsPrenex) (fun _ _ _ => (IsAtomic.equal _ _).IsPrenex)
    (fun _ _ _ _ => (IsAtomic.rel _ _).IsPrenex) (fun _ _ _ h1 h2 => is_prenex_to_prenex_imp h1 h2) fun _ _ =>
    IsPrenex.all

end BoundedFormula

namespace Lhom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormulaₓ (g : L →ᴸ L') : ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | k, falsum => falsum
  | k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | k, rel R ts => (g.onRelation R).BoundedFormula (g.onTerm ∘ ts)
  | k, imp f₁ f₂ => (on_bounded_formula f₁).imp (on_bounded_formula f₂)
  | k, all f => (on_bounded_formula f).all

@[simp]
theorem id_on_bounded_formula : ((Lhom.id L).onBoundedFormula : L.BoundedFormula α n → L.BoundedFormula α n) = id := by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · rw [on_bounded_formula, Lhom.id_on_term, id.def, id.def, id.def, bd_equal]
    
  · rw [on_bounded_formula, Lhom.id_on_term]
    rfl
    
  · rw [on_bounded_formula, ih1, ih2, id.def, id.def, id.def]
    
  · rw [on_bounded_formula, ih3, id.def, id.def]
    

@[simp]
theorem comp_on_bounded_formula {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n → L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula :=
  by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp only [← on_bounded_formula, ← comp_on_term, ← Function.comp_app]
    rfl
    
  · simp only [← on_bounded_formula, ← comp_on_relation, ← comp_on_term, ← Function.comp_app]
    rfl
    
  · simp only [← on_bounded_formula, ← Function.comp_app, ← ih1, ← ih2, ← eq_self_iff_true, ← and_selfₓ]
    
  · simp only [← ih3, ← on_bounded_formula, ← Function.comp_app]
    

/-- Maps a formula's symbols along a language map. -/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula

/-- Maps a sentence's symbols along a language map. -/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula

/-- Maps a theory's symbols along a language map. -/
def OnTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T

@[simp]
theorem mem_on_Theory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.OnTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _

end Lhom

namespace Lequiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n where
  toFun := φ.toLhom.onBoundedFormula
  invFun := φ.invLhom.onBoundedFormula
  left_inv := by
    rw [Function.left_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.left_inv, Lhom.id_on_bounded_formula]
  right_inv := by
    rw [Function.right_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.right_inv, Lhom.id_on_bounded_formula]

theorem on_bounded_formula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) = φ.symm.onBoundedFormula :=
  rfl

/-- Maps a formula's symbols along a language equivalence. -/
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula

@[simp]
theorem on_formula_apply (φ : L ≃ᴸ L') : (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLhom.onFormula :=
  rfl

@[simp]
theorem on_formula_symm (φ : L ≃ᴸ L') : (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps]
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula

end Lequiv

-- mathport name: «expr =' »
localized [FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual

-- mathport name: «expr ⟹ »
-- input \~- or \simeq
localized [FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp

-- mathport name: «expr∀' »
-- input \==>
localized [FirstOrder] prefix:110 "∀'" => FirstOrder.Language.BoundedFormula.all

-- mathport name: «expr∼ »
localized [FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not

-- mathport name: «expr ⇔ »
-- input \~, the ASCII character ~ has too low precedence
localized [FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff

-- mathport name: «expr∃' »
-- input \<=>
localized [FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex

-- input \ex
namespace Formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Finₓ (n + 1)) :=
  equal (var 0) (func f fun i => var i.succ)

/-- The negation of a formula. -/
protected def not (φ : L.Formula α) : L.Formula α :=
  φ.Not

/-- The implication between formulas, as a formula. -/
protected def imp : L.Formula α → L.Formula α → L.Formula α :=
  bounded_formula.imp

/-- The biimplication between formulas, as a formula. -/
protected def iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.Iff ψ

theorem is_atomic_graph (f : L.Functions n) : (graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _

end Formula

namespace Relations

variable (r : L.Relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀'r.boundedFormula₂ (&0) &0

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀'∼(r.boundedFormula₂ (&0) &0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀'∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1⊔r.boundedFormula₂ (&1) &0)

end Relations

section Cardinality

variable (L)

/-- A sentence indicating that a structure has `n` distinct elements. -/
protected def Sentence.cardGe (n) : L.Sentence :=
  (((((List.finRange n).product (List.finRange n)).filter fun ij : _ × _ => ij.1 ≠ ij.2).map fun ij : _ × _ =>
          ∼((&ij.1).bdEqual &ij.2)).foldr
      (·⊓·) ⊤).exs

/-- A theory indicating that a structure is infinite. -/
def InfiniteTheory : L.Theory :=
  Set.Range (Sentence.cardGe L)

/-- A theory that indicates a structure is nonempty. -/
def NonemptyTheory : L.Theory :=
  {Sentence.cardGe L 1}

/-- A theory indicating that each of a set of constants is distinct. -/
def DistinctConstantsTheory (s : Set α) : L[[α]].Theory :=
  (fun ab : α × α => ((L.con ab.1).Term.equal (L.con ab.2).Term).Not) '' (s ×ˢ s ∩ Set.Diagonal αᶜ)

variable {L} {α}

open Set

theorem monotone_distinct_constants_theory : Monotone (L.DistinctConstantsTheory : Set α → L[[α]].Theory) :=
  fun s t st => image_subset _ (inter_subset_inter_left _ (prod_mono st st))

theorem directed_distinct_constants_theory : Directed (· ⊆ ·) (L.DistinctConstantsTheory : Set α → L[[α]].Theory) :=
  Monotone.directed_le monotone_distinct_constants_theory

theorem distinct_constants_theory_eq_Union (s : Set α) :
    L.DistinctConstantsTheory s =
      ⋃ t : Finset s, L.DistinctConstantsTheory (t.map (Function.Embedding.subtype fun x => x ∈ s)) :=
  by
  classical
  simp only [← distinct_constants_theory]
  rw [← image_Union, ← Union_inter]
  refine' congr rfl (congr (congr rfl _) rfl)
  ext ⟨i, j⟩
  simp only [← prod_mk_mem_set_prod_eq, ← Finset.coe_map, ← Function.Embedding.coe_subtype, ← mem_Union, ← mem_image, ←
    Finset.mem_coe, ← Subtype.exists, ← Subtype.coe_mk, ← exists_and_distrib_right, ← exists_eq_right]
  refine' ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, _⟩, ⟨h.2, _⟩⟩, _⟩
  · simp
    
  · simp
    
  · rintro ⟨t, ⟨is, _⟩, ⟨js, _⟩⟩
    exact ⟨is, js⟩
    

end Cardinality

end Language

end FirstOrder

