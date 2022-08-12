/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Topology.Constructions
import Mathbin.Topology.Algebra.Monoid

/-!
# Topology on lists and vectors

-/


open TopologicalSpace Set Filter

open TopologicalSpace Filter

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

instance : TopologicalSpace (List α) :=
  TopologicalSpace.mkOfNhds (traverse nhds)

theorem nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as := by
  refine' nhds_mk_of_nhds _ _ _ _
  · intro l
    induction l
    case list.nil =>
      exact le_rfl
    case list.cons a l ih =>
      suffices List.cons <$> pure a <*> pure l ≤ List.cons <$> 𝓝 a <*> traverse 𝓝 l by
        simpa only with functor_norm using this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_nhds a) ih
    
  · intro l s hs
    rcases(mem_traverse_iff _ _).1 hs with ⟨u, hu, hus⟩
    clear as hs
    have : ∃ v : List (Set α), l.forall₂ (fun a s => IsOpen s ∧ a ∈ s) v ∧ sequence v ⊆ s := by
      induction hu generalizing s
      case list.forall₂.nil hs this =>
        exists
        simpa only [← List.forall₂_nil_left_iff, ← exists_eq_left]
      case list.forall₂.cons a s as ss ht h ih t hts =>
        rcases mem_nhds_iff.1 ht with ⟨u, hut, hu⟩
        rcases ih (subset.refl _) with ⟨v, hv, hvss⟩
        exact ⟨u :: v, List.Forall₂.cons hu hv, subset.trans (Set.seq_mono (Set.image_subset _ hut) hvss) hts⟩
    rcases this with ⟨v, hv, hvs⟩
    refine' ⟨sequence v, mem_traverse _ _ _, hvs, _⟩
    · exact hv.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha
      
    · intro u hu
      have hu := (List.mem_traverse _ _).1 hu
      have : List.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) u v := by
        refine' List.Forall₂.flip _
        replace hv := hv.flip
        simp only [← List.forall₂_and_left, ← flip] at hv⊢
        exact ⟨hv.1, hu.flip⟩
      refine' mem_of_superset _ hvs
      exact mem_traverse _ _ (this.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha)
      
    

@[simp]
theorem nhds_nil : 𝓝 ([] : List α) = pure [] := by
  rw [nhds_list, List.traverse_nil _] <;> infer_instance

theorem nhds_cons (a : α) (l : List α) : 𝓝 (a :: l) = List.cons <$> 𝓝 a <*> 𝓝 l := by
  rw [nhds_list, List.traverse_cons _, ← nhds_list] <;> infer_instance

theorem List.tendsto_cons {a : α} {l : List α} :
    Tendsto (fun p : α × List α => List.cons p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a :: l)) := by
  rw [nhds_cons, tendsto, Filter.map_prod] <;> exact le_rfl

theorem Filter.Tendsto.cons {α : Type _} {f : α → β} {g : α → List β} {a : Filter α} {b : β} {l : List β}
    (hf : Tendsto f a (𝓝 b)) (hg : Tendsto g a (𝓝 l)) : Tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b :: l)) :=
  List.tendsto_cons.comp (Tendsto.prod_mk hf hg)

namespace List

theorem tendsto_cons_iff {β : Type _} {f : List α → β} {b : Filter β} {a : α} {l : List α} :
    Tendsto f (𝓝 (a :: l)) b ↔ Tendsto (fun p : α × List α => f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) b := by
  have : 𝓝 (a :: l) = (𝓝 a ×ᶠ 𝓝 l).map fun p : α × List α => p.1 :: p.2 := by
    simp only [← nhds_cons, ← Filter.prod_eq, ← (Filter.map_def _ _).symm, ← (Filter.seq_eq_filter_seq _ _).symm]
    simp' [-Filter.seq_eq_filter_seq, -Filter.map_def, ← (· ∘ ·)] with functor_norm
  rw [this, Filter.tendsto_map'_iff]

theorem continuous_cons : Continuous fun x : α × List α => (x.1 :: x.2 : List α) :=
  continuous_iff_continuous_at.mpr fun ⟨x, y⟩ => continuous_at_fst.cons continuous_at_snd

theorem tendsto_nhds {β : Type _} {f : List α → β} {r : List α → Filter β} (h_nil : Tendsto f (pure []) (r []))
    (h_cons : ∀ l a, Tendsto f (𝓝 l) (r l) → Tendsto (fun p : α × List α => f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) (r (a :: l))) :
    ∀ l, Tendsto f (𝓝 l) (r l)
  | [] => by
    rwa [nhds_nil]
  | a :: l => by
    rw [tendsto_cons_iff] <;> exact h_cons l a (tendsto_nhds l)

theorem continuous_at_length : ∀ l : List α, ContinuousAt List.length l := by
  simp only [← ContinuousAt, ← nhds_discrete]
  refine' tendsto_nhds _ _
  · exact tendsto_pure_pure _ _
    
  · intro l a ih
    dsimp' only [← List.length]
    refine' tendsto.comp (tendsto_pure_pure (fun x => x + 1) _) _
    refine' tendsto.comp ih tendsto_snd
    

theorem tendsto_insert_nth' {a : α} :
    ∀ {n : ℕ} {l : List α}, Tendsto (fun p : α × List α => insertNthₓ n p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insertNthₓ n a l))
  | 0, l => tendsto_cons
  | n + 1, [] => by
    simp
  | n + 1, a' :: l => by
    have : 𝓝 a ×ᶠ 𝓝 (a' :: l) = (𝓝 a ×ᶠ (𝓝 a' ×ᶠ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1 :: p.2.2) := by
      simp only [← nhds_cons, ← Filter.prod_eq, Filter.map_def, Filter.seq_eq_filter_seq]
      simp' [-Filter.seq_eq_filter_seq, -Filter.map_def, ← (· ∘ ·)] with functor_norm
    rw [this, tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insert_nth' n l).comp <| tendsto_fst.prod_mk <| tendsto_snd.comp tendsto_snd)

theorem tendsto_insert_nth {β} {n : ℕ} {a : α} {l : List α} {f : β → α} {g : β → List α} {b : Filter β}
    (hf : Tendsto f b (𝓝 a)) (hg : Tendsto g b (𝓝 l)) :
    Tendsto (fun b : β => insertNthₓ n (f b) (g b)) b (𝓝 (insertNthₓ n a l)) :=
  tendsto_insert_nth'.comp (Tendsto.prod_mk hf hg)

theorem continuous_insert_nth {n : ℕ} : Continuous fun p : α × List α => insertNthₓ n p.1 p.2 :=
  continuous_iff_continuous_at.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth'

theorem tendsto_remove_nth : ∀ {n : ℕ} {l : List α}, Tendsto (fun l => removeNthₓ l n) (𝓝 l) (𝓝 (removeNthₓ l n))
  | _, [] => by
    rw [nhds_nil] <;> exact tendsto_pure_nhds _ _
  | 0, a :: l => by
    rw [tendsto_cons_iff] <;> exact tendsto_snd
  | n + 1, a :: l => by
    rw [tendsto_cons_iff]
    dsimp' [← remove_nth]
    exact tendsto_fst.cons ((@tendsto_remove_nth n l).comp tendsto_snd)

theorem continuous_remove_nth {n : ℕ} : Continuous fun l : List α => removeNthₓ l n :=
  continuous_iff_continuous_at.mpr fun a => tendsto_remove_nth

@[to_additive]
theorem tendsto_prod [Monoidₓ α] [HasContinuousMul α] {l : List α} : Tendsto List.prod (𝓝 l) (𝓝 l.Prod) := by
  induction' l with x l ih
  · simp (config := { contextual := true })[← nhds_nil, ← mem_of_mem_nhds, ← tendsto_pure_left]
    
  simp_rw [tendsto_cons_iff, prod_cons]
  have := continuous_iff_continuous_at.mp continuous_mul (x, l.prod)
  rw [ContinuousAt, nhds_prod_eq] at this
  exact this.comp (tendsto_id.prod_map ih)

@[to_additive]
theorem continuous_prod [Monoidₓ α] [HasContinuousMul α] : Continuous (prod : List α → α) :=
  continuous_iff_continuous_at.mpr fun l => tendsto_prod

end List

namespace Vector

open List

instance (n : ℕ) : TopologicalSpace (Vector α n) := by
  unfold Vector <;> infer_instance

theorem tendsto_cons {n : ℕ} {a : α} {l : Vector α n} :
    Tendsto (fun p : α × Vector α n => p.1 ::ᵥ p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a ::ᵥ l)) := by
  simp [← tendsto_subtype_rng, Subtype.val_eq_coe, ← cons_val]
  exact tendsto_fst.cons (tendsto.comp continuous_at_subtype_coe tendsto_snd)

theorem tendsto_insert_nth {n : ℕ} {i : Finₓ (n + 1)} {a : α} :
    ∀ {l : Vector α n}, Tendsto (fun p : α × Vector α n => insertNth p.1 i p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insertNth a i l))
  | ⟨l, hl⟩ => by
    rw [insert_nth, tendsto_subtype_rng]
    simp [← insert_nth_val]
    exact List.tendsto_insert_nth tendsto_fst (tendsto.comp continuous_at_subtype_coe tendsto_snd : _)

theorem continuous_insert_nth' {n : ℕ} {i : Finₓ (n + 1)} : Continuous fun p : α × Vector α n => insertNth p.1 i p.2 :=
  continuous_iff_continuous_at.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth

theorem continuous_insert_nth {n : ℕ} {i : Finₓ (n + 1)} {f : β → α} {g : β → Vector α n} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => insertNth (f b) i (g b) :=
  continuous_insert_nth'.comp (hf.prod_mk hg : _)

theorem continuous_at_remove_nth {n : ℕ} {i : Finₓ (n + 1)} : ∀ {l : Vector α (n + 1)}, ContinuousAt (removeNth i) l
  | ⟨l, hl⟩ =>--  ∀{l:vector α (n+1)}, tendsto (remove_nth i) (𝓝 l) (𝓝 (remove_nth i l))
  --| ⟨l, hl⟩ :=
  by
    rw [ContinuousAt, remove_nth, tendsto_subtype_rng]
    simp only [Subtype.val_eq_coe, ← Vector.remove_nth_val]
    exact tendsto.comp List.tendsto_remove_nth continuous_at_subtype_coe

theorem continuous_remove_nth {n : ℕ} {i : Finₓ (n + 1)} : Continuous (removeNth i : Vector α (n + 1) → Vector α n) :=
  continuous_iff_continuous_at.mpr fun ⟨a, l⟩ => continuous_at_remove_nth

end Vector

