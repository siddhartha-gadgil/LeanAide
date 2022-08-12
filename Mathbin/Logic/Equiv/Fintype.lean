/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.GroupTheory.Perm.Sign
import Mathbin.Logic.Equiv.Basic

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `fintype`s.

# Main definitions

 - `function.embedding.to_equiv_range`: computably turn an embedding of a
   fintype into an `equiv` of the domain to its range
 - `equiv.perm.via_fintype_embedding : perm α → (α ↪ β) → perm β` extends the domain of
   a permutation, fixing everything outside the range of the embedding

# Implementation details

 - `function.embedding.to_equiv_range` uses a computable inverse, but one that has poor
   computational performance, since it operates by exhaustive search over the input `fintype`s.
-/


variable {α β : Type _} [Fintype α] [DecidableEq β] (e : Equivₓ.Perm α) (f : α ↪ β)

/-- Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ set.range f`,
if `α` is a `fintype`. Has poor computational performance, due to exhaustive searching in
constructed inverse. When a better inverse is known, use `equiv.of_left_inverse'` or
`equiv.of_left_inverse` instead. This is the computable version of `equiv.of_injective`.
-/
def Function.Embedding.toEquivRange : α ≃ Set.Range f :=
  ⟨fun a => ⟨f a, Set.mem_range_self a⟩, f.invOfMemRange, fun _ => by
    simp , fun _ => by
    simp ⟩

@[simp]
theorem Function.Embedding.to_equiv_range_apply (a : α) : f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩ :=
  rfl

@[simp]
theorem Function.Embedding.to_equiv_range_symm_apply_self (a : α) :
    f.toEquivRange.symm ⟨f a, Set.mem_range_self a⟩ = a := by
  simp [← Equivₓ.symm_apply_eq]

theorem Function.Embedding.to_equiv_range_eq_of_injective : f.toEquivRange = Equivₓ.ofInjective f f.Injective := by
  ext
  simp

/-- Extend the domain of `e : equiv.perm α`, mapping it through `f : α ↪ β`.
Everything outside of `set.range f` is kept fixed. Has poor computational performance,
due to exhaustive searching in constructed inverse due to using `function.embedding.to_equiv_range`.
When a better `α ≃ set.range f` is known, use `equiv.perm.via_set_range`.
When `[fintype α]` is not available, a noncomputable version is available as
`equiv.perm.via_embedding`.
-/
def Equivₓ.Perm.viaFintypeEmbedding : Equivₓ.Perm β :=
  e.extendDomain f.toEquivRange

@[simp]
theorem Equivₓ.Perm.via_fintype_embedding_apply_image (a : α) : e.viaFintypeEmbedding f (f a) = f (e a) := by
  rw [Equivₓ.Perm.viaFintypeEmbedding]
  convert Equivₓ.Perm.extend_domain_apply_image e _ _

theorem Equivₓ.Perm.via_fintype_embedding_apply_mem_range {b : β} (h : b ∈ Set.Range f) :
    e.viaFintypeEmbedding f b = f (e (f.invOfMemRange ⟨b, h⟩)) := by
  simpa [← Equivₓ.Perm.viaFintypeEmbedding, ← Equivₓ.Perm.extend_domain_apply_subtype, ← h]

theorem Equivₓ.Perm.via_fintype_embedding_apply_not_mem_range {b : β} (h : b ∉ Set.Range f) :
    e.viaFintypeEmbedding f b = b := by
  rwa [Equivₓ.Perm.viaFintypeEmbedding, Equivₓ.Perm.extend_domain_apply_not_subtype]

@[simp]
theorem Equivₓ.Perm.via_fintype_embedding_sign [DecidableEq α] [Fintype β] :
    Equivₓ.Perm.sign (e.viaFintypeEmbedding f) = Equivₓ.Perm.sign e := by
  simp [← Equivₓ.Perm.viaFintypeEmbedding]

namespace Equivₓ

variable {p q : α → Prop} [DecidablePred p] [DecidablePred q]

/-- If `e` is an equivalence between two subtypes of a fintype `α`, `e.to_compl`
is an equivalence between the complement of those subtypes.

See also `equiv.compl`, for a computable version when a term of type
`{e' : α ≃ α // ∀ x : {x // p x}, e' x = e x}` is known. -/
noncomputable def toCompl (e : { x // p x } ≃ { x // q x }) : { x // ¬p x } ≃ { x // ¬q x } :=
  Classical.choice (Fintype.card_eq.mp (Fintype.card_compl_eq_card_compl _ _ (Fintype.card_congr e)))

/-- If `e` is an equivalence between two subtypes of a fintype `α`, `e.extend_subtype`
is a permutation of `α` acting like `e` on the subtypes and doing something arbitrary outside.

Note that when `p = q`, `equiv.perm.subtype_congr e (equiv.refl _)` can be used instead. -/
noncomputable abbrev extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α :=
  subtypeCongr e e.toCompl

theorem extend_subtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) : e.extendSubtype x = e ⟨x, hx⟩ :=
  by
  dunfold extend_subtype
  simp only [← subtype_congr, ← Equivₓ.trans_apply, ← Equivₓ.sum_congr_apply]
  rw [sum_compl_apply_symm_of_pos _ _ hx, Sum.map_inl, sum_compl_apply_inl]

theorem extend_subtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) : q (e.extendSubtype x) := by
  convert (e ⟨x, hx⟩).2
  rw [e.extend_subtype_apply_of_mem _ hx, Subtype.val_eq_coe]

theorem extend_subtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    e.extendSubtype x = e.toCompl ⟨x, hx⟩ := by
  dunfold extend_subtype
  simp only [← subtype_congr, ← Equivₓ.trans_apply, ← Equivₓ.sum_congr_apply]
  rw [sum_compl_apply_symm_of_neg _ _ hx, Sum.map_inr, sum_compl_apply_inr]

theorem extend_subtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) : ¬q (e.extendSubtype x) := by
  convert (e.to_compl ⟨x, hx⟩).2
  rw [e.extend_subtype_apply_of_not_mem _ hx, Subtype.val_eq_coe]

end Equivₓ

