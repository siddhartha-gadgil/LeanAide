import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

universe u v w

def FiniteParticularPointTopology_mk{α : Type u}[Fintype α ](p : α ) : TopologicalSpace α  where
  IsOpen X:= p ∈ X ∨ X = ∅
  isOpen_univ :=
    by
      simp only [mem_univ, univ_eq_empty_iff, true_or]
  isOpen_inter := by
    intro s t hs ht
    simp only [mem_inter_iff]
    cases hs with
      | inl hp =>
        cases ht with
          | inl hq =>
            left
            exact ⟨hp,hq⟩
          | inr hq =>
            right
            rw [hq]
            simp only [inter_empty]
      | inr hp =>
        right
        rw [hp]
        simp only [empty_inter]
  isOpen_sUnion := by
    intro S hS
    by_cases hSempty : ⋃₀S = ∅
    · simp only [hSempty, mem_empty_iff_false, or_true]
    · simp only [mem_sUnion,hSempty,exists_prop,or_false]
      push_neg at hSempty
      rw[← Set.nonempty_iff_ne_empty] at hSempty
      set x := hSempty.some with hxdef
      have hx : x ∈ ⋃₀S := Set.Nonempty.some_mem hSempty
      rw[Set.mem_sUnion] at hx
      cases hx with
        | intro t ht =>
          use t
          have hnt : t.Nonempty := Set.nonempty_of_mem ht.2
          simp at hS
          exact ⟨ht.1, Or.resolve_right (hS t ht.1) (Set.nonempty_iff_ne_empty.mp hnt)⟩


class FiniteParticularPointTopology (α : Type u)(p : α)[t : TopologicalSpace α][Fintype α] where
  topology_eq : t = FiniteParticularPointTopology_mk p

section FiniteParticularPointTopology
variable (α : Type u)[t :TopologicalSpace α][f : Fintype α](p : α)[t1: FiniteParticularPointTopology α p]

theorem FPT_open_iff {X : Set α} : IsOpen X ↔ p ∈ X ∨ X = ∅ := by
  rw [t1.topology_eq]
  exact Iff.rfl

def FPT_T₀ : T0Space α := by
    rw[t0Space_iff_inseparable]
    intro x y hxy
    by_contra ha
    by_cases h : (x = p) ∨ (y = p);
    · wlog hp : x = p
      apply this α p
      have hinsep : Inseparable y x:= Inseparable.symm hxy
      apply hinsep
      apply Ne.symm ha
      exact h.symm
      exact Or.resolve_left h hp
      rw[inseparable_iff_forall_open] at hxy
      let s : Set α := {p}
      have hsdef : s = {p} := by rfl
      have hs : IsOpen s := by
        rw[FPT_open_iff α p ]
        left
        exact rfl
      apply ha
      have hy : y ∈ s := by
        rwa[←hxy s hs]
      rw [hsdef] at hy
      simp only [mem_singleton_iff] at hy
      rw[hy,hp]
    · push_neg at h
      apply ha
      rw[inseparable_iff_forall_open] at hxy
      let s : Set α := {p,x}
      have hsdef : s = {p,x} := by rfl
      have hs : IsOpen s := by
        rw[FPT_open_iff α p ]
        left
        simp only [mem_singleton_iff, mem_insert_iff, true_or]
      have hx : x ∈ s := by
        simp only [mem_singleton_iff, mem_insert_iff]
        right
        trivial
      have hy : y ∈ s := by
        rwa[← hxy s hs ]
      rw [hsdef] at hy
      simp only [mem_singleton_iff, mem_insert_iff] at hy
      exact (Or.resolve_left hy h.2).symm



  end FiniteParticularPointTopology
