/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Order.Lattice
import Mathbin.Data.List.Sort
import Mathbin.Logic.Equiv.Fin
import Mathbin.Logic.Equiv.Functor
import Mathbin.Data.Fintype.Basic

/-!
# Jordan-Hölder Theorem

This file proves the Jordan Hölder theorem for a `jordan_holder_lattice`, a class also defined in
this file. Examples of `jordan_holder_lattice` include `subgroup G` if `G` is a group, and
`submodule R M` if `M` is an `R`-module. Using this approach the theorem need not be proved
seperately for both groups and modules, the proof in this file can be applied to both.

## Main definitions
The main definitions in this file are `jordan_holder_lattice` and `composition_series`,
and the relation `equivalent` on `composition_series`

A `jordan_holder_lattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `is_maximal`, and a notion
of isomorphism of pairs `iso`. In the example of subgroups of a group, `is_maximal H K` means that
`H` is a maximal normal subgroup of `K`, and `iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `iso (H, H ⊔ K) (H ⊓ K, K)`.

A `composition_series X` is a finite nonempty series of elements of the lattice `X` such that
each element is maximal inside the next. The length of a `composition_series X` is
one less than the number of elements in the series. Note that there is no stipulation
that a series start from the bottom of the lattice and finish at the top.
For a composition series `s`, `s.top` is the largest element of the series,
and `s.bot` is the least element.

Two `composition_series X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : fin s₁.length ≃ fin s₂.length` such that for any `i`,
`iso (s₁ i, s₁ i.succ) (s₂ (e i), s₂ (e i.succ))`

## Main theorems

The main theorem is `composition_series.jordan_holder`, which says that if two composition
series have the same least element and the same largest element,
then they are `equivalent`.

## TODO

Provide instances of `jordan_holder_lattice` for both submodules and subgroups, and potentially
for modular lattices.

It is not entirely clear how this should be done. Possibly there should be no global instances
of `jordan_holder_lattice`, and the instances should only be defined locally in order to prove
the Jordan-Hölder theorem for modules/groups and the API should be transferred because many of the
theorems in this file will have stronger versions for modules. There will also need to be an API for
mapping composition series across homomorphisms. It is also probably possible to
provide an instance of `jordan_holder_lattice` for any `modular_lattice`, and in this case the
Jordan-Hölder theorem will say that there is a well defined notion of length of a modular lattice.
However an instance of `jordan_holder_lattice` for a modular lattice will not be able to contain
the correct notion of isomorphism for modules, so a separate instance for modules will still be
required and this will clash with the instance for modular lattices, and so at least one of these
instances should not be a global instance.
-/


universe u

open Set

/-- A `jordan_holder_lattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `is_maximal`, and a notion
of isomorphism of pairs `iso`. In the example of subgroups of a group, `is_maximal H K` means that
`H` is a maximal normal subgroup of `K`, and `iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `iso (H, H ⊔ K) (H ⊓ K, K)`.
Examples include `subgroup G` if `G` is a group, and `submodule R M` if `M` is an `R`-module.
-/
class JordanHolderLattice (X : Type u) [Lattice X] where
  IsMaximal : X → X → Prop
  lt_of_is_maximal : ∀ {x y}, is_maximal x y → x < y
  sup_eq_of_is_maximal : ∀ {x y z}, is_maximal x z → is_maximal y z → x ≠ y → x⊔y = z
  is_maximal_inf_left_of_is_maximal_sup : ∀ {x y}, is_maximal x (x⊔y) → is_maximal y (x⊔y) → is_maximal (x⊓y) x
  Iso : X × X → X × X → Prop
  iso_symm : ∀ {x y}, iso x y → iso y x
  iso_trans : ∀ {x y z}, iso x y → iso y z → iso x z
  second_iso : ∀ {x y}, is_maximal x (x⊔y) → iso (x, x⊔y) (x⊓y, y)

namespace JordanHolderLattice

variable {X : Type u} [Lattice X] [JordanHolderLattice X]

theorem is_maximal_inf_right_of_is_maximal_sup {x y : X} (hxz : IsMaximal x (x⊔y)) (hyz : IsMaximal y (x⊔y)) :
    IsMaximal (x⊓y) y := by
  rw [inf_comm]
  rw [sup_comm] at hxz hyz
  exact is_maximal_inf_left_of_is_maximal_sup hyz hxz

theorem is_maximal_of_eq_inf (x b : X) {a y : X} (ha : x⊓y = a) (hxy : x ≠ y) (hxb : IsMaximal x b)
    (hyb : IsMaximal y b) : IsMaximal a y := by
  have hb : x⊔y = b := sup_eq_of_is_maximal hxb hyb hxy
  substs a b
  exact is_maximal_inf_right_of_is_maximal_sup hxb hyb

theorem second_iso_of_eq {x y a b : X} (hm : IsMaximal x a) (ha : x⊔y = a) (hb : x⊓y = b) : Iso (x, a) (b, y) := by
  substs a b <;> exact second_iso hm

theorem IsMaximal.iso_refl {x y : X} (h : IsMaximal x y) : Iso (x, y) (x, y) :=
  second_iso_of_eq h (sup_eq_right.2 (le_of_ltₓ (lt_of_is_maximal h))) (inf_eq_left.2 (le_of_ltₓ (lt_of_is_maximal h)))

end JordanHolderLattice

open JordanHolderLattice

attribute [symm] iso_symm

attribute [trans] iso_trans

/-- A `composition_series X` is a finite nonempty series of elements of a
`jordan_holder_lattice` such that each element is maximal inside the next. The length of a
`composition_series X` is one less than the number of elements in the series.
Note that there is no stipulation that a series start from the bottom of the lattice and finish at
the top. For a composition series `s`, `s.top` is the largest element of the series,
and `s.bot` is the least element.
-/
structure CompositionSeries (X : Type u) [Lattice X] [JordanHolderLattice X] : Type u where
  length : ℕ
  series : Finₓ (length + 1) → X
  step' : ∀ i : Finₓ length, IsMaximal (series i.cast_succ) (series i.succ)

namespace CompositionSeries

variable {X : Type u} [Lattice X] [JordanHolderLattice X]

instance : CoeFun (CompositionSeries X) fun x => Finₓ (x.length + 1) → X where coe := CompositionSeries.series

instance [Inhabited X] : Inhabited (CompositionSeries X) :=
  ⟨{ length := 0, series := default, step' := fun x => x.elim0 }⟩

variable {X}

theorem step (s : CompositionSeries X) : ∀ i : Finₓ s.length, IsMaximal (s i.cast_succ) (s i.succ) :=
  s.step'

@[simp]
theorem coe_fn_mk (length : ℕ) (series step) :
    (@CompositionSeries.mk X _ _ length series step : Finₓ length.succ → X) = series :=
  rfl

theorem lt_succ (s : CompositionSeries X) (i : Finₓ s.length) : s i.cast_succ < s i.succ :=
  lt_of_is_maximal (s.step _)

protected theorem strict_mono (s : CompositionSeries X) : StrictMono s :=
  Finₓ.strict_mono_iff_lt_succ.2 s.lt_succ

protected theorem injective (s : CompositionSeries X) : Function.Injective s :=
  s.StrictMono.Injective

@[simp]
protected theorem inj (s : CompositionSeries X) {i j : Finₓ s.length.succ} : s i = s j ↔ i = j :=
  s.Injective.eq_iff

instance : HasMem X (CompositionSeries X) :=
  ⟨fun x s => x ∈ Set.Range s⟩

theorem mem_def {x : X} {s : CompositionSeries X} : x ∈ s ↔ x ∈ Set.Range s :=
  Iff.rfl

theorem total {s : CompositionSeries X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x := by
  rcases Set.mem_range.1 hx with ⟨i, rfl⟩
  rcases Set.mem_range.1 hy with ⟨j, rfl⟩
  rw [s.strict_mono.le_iff_le, s.strict_mono.le_iff_le]
  exact le_totalₓ i j

/-- The ordered `list X` of elements of a `composition_series X`. -/
def toList (s : CompositionSeries X) : List X :=
  List.ofFnₓ s

/-- Two `composition_series` are equal if they are the same length and
have the same `i`th element for every `i` -/
theorem ext_fun {s₁ s₂ : CompositionSeries X} (hl : s₁.length = s₂.length)
    (h : ∀ i, s₁ i = s₂ (Finₓ.cast (congr_arg Nat.succ hl) i)) : s₁ = s₂ := by
  cases s₁
  cases s₂
  dsimp'  at *
  subst hl
  simpa [← Function.funext_iffₓ] using h

@[simp]
theorem length_to_list (s : CompositionSeries X) : s.toList.length = s.length + 1 := by
  rw [to_list, List.length_of_fn]

theorem to_list_ne_nil (s : CompositionSeries X) : s.toList ≠ [] := by
  rw [← List.length_pos_iff_ne_nilₓ, length_to_list] <;> exact Nat.succ_posₓ _

theorem to_list_injective : Function.Injective (@CompositionSeries.toList X _ _) :=
  fun s₁ s₂ (h : List.ofFnₓ s₁ = List.ofFnₓ s₂) => by
  have h₁ : s₁.length = s₂.length :=
    Nat.succ_injective ((List.length_of_fn s₁).symm.trans <| (congr_arg List.length h).trans <| List.length_of_fn s₂)
  have h₂ : ∀ i : Finₓ s₁.length.succ, s₁ i = s₂ (Finₓ.cast (congr_arg Nat.succ h₁) i) := by
    intro i
    rw [← List.nth_le_of_fn s₁ i, ← List.nth_le_of_fn s₂]
    simp [← h]
  cases s₁
  cases s₂
  dsimp'  at *
  subst h₁
  simp only [← heq_iff_eq, ← eq_self_iff_true, ← true_andₓ]
  simp only [← Finₓ.cast_refl] at h₂
  exact funext h₂

theorem chain'_to_list (s : CompositionSeries X) : List.Chain' IsMaximal s.toList :=
  List.chain'_iff_nth_le.2
    (by
      intro i hi
      simp only [← to_list, ← List.nth_le_of_fn']
      rw [length_to_list] at hi
      exact s.step ⟨i, hi⟩)

theorem to_list_sorted (s : CompositionSeries X) : s.toList.Sorted (· < ·) :=
  List.pairwise_iff_nth_le.2 fun i j hi hij => by
    dsimp' [← to_list]
    rw [List.nth_le_of_fn', List.nth_le_of_fn']
    exact s.strict_mono hij

theorem to_list_nodup (s : CompositionSeries X) : s.toList.Nodup :=
  s.to_list_sorted.Nodup

@[simp]
theorem mem_to_list {s : CompositionSeries X} {x : X} : x ∈ s.toList ↔ x ∈ s := by
  rw [to_list, List.mem_of_fn, mem_def]

/-- Make a `composition_series X` from the ordered list of its elements. -/
def ofList (l : List X) (hl : l ≠ []) (hc : List.Chain' IsMaximal l) : CompositionSeries X where
  length := l.length - 1
  series := fun i =>
    l.nthLe i
      (by
        conv_rhs => rw [← tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ (List.length_pos_of_ne_nilₓ hl))]
        exact i.2)
  step' := fun ⟨i, hi⟩ => List.chain'_iff_nth_le.1 hc i hi

theorem length_of_list (l : List X) (hl : l ≠ []) (hc : List.Chain' IsMaximal l) :
    (ofList l hl hc).length = l.length - 1 :=
  rfl

theorem of_list_to_list (s : CompositionSeries X) : ofList s.toList s.to_list_ne_nil s.chain'_to_list = s := by
  refine' ext_fun _ _
  · rw [length_of_list, length_to_list, Nat.succ_sub_one]
    
  · rintro ⟨i, hi⟩
    dsimp' [← of_list, ← to_list]
    rw [List.nth_le_of_fn']
    

@[simp]
theorem of_list_to_list' (s : CompositionSeries X) : ofList s.toList s.to_list_ne_nil s.chain'_to_list = s :=
  of_list_to_list s

@[simp]
theorem to_list_of_list (l : List X) (hl : l ≠ []) (hc : List.Chain' IsMaximal l) : toList (ofList l hl hc) = l := by
  refine' List.ext_le _ _
  · rw [length_to_list, length_of_list, tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ <| List.length_pos_of_ne_nilₓ hl)]
    
  · intro i hi hi'
    dsimp' [← of_list, ← to_list]
    rw [List.nth_le_of_fn']
    rfl
    

/-- Two `composition_series` are equal if they have the same elements. See also `ext_fun`. -/
@[ext]
theorem ext {s₁ s₂ : CompositionSeries X} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  to_list_injective <|
    List.eq_of_perm_of_sorted
      (by
        classical <;>
          exact
            List.perm_of_nodup_nodup_to_finset_eq s₁.to_list_nodup s₂.to_list_nodup
              (Finset.ext <| by
                simp [*]))
      s₁.to_list_sorted s₂.to_list_sorted

/-- The largest element of a `composition_series` -/
def top (s : CompositionSeries X) : X :=
  s (Finₓ.last _)

theorem top_mem (s : CompositionSeries X) : s.top ∈ s :=
  mem_def.2 (Set.mem_range.2 ⟨Finₓ.last _, rfl⟩)

@[simp]
theorem le_top {s : CompositionSeries X} (i : Finₓ (s.length + 1)) : s i ≤ s.top :=
  s.StrictMono.Monotone (Finₓ.le_last _)

theorem le_top_of_mem {s : CompositionSeries X} {x : X} (hx : x ∈ s) : x ≤ s.top :=
  let ⟨i, hi⟩ := Set.mem_range.2 hx
  hi ▸ le_top _

/-- The smallest element of a `composition_series` -/
def bot (s : CompositionSeries X) : X :=
  s 0

theorem bot_mem (s : CompositionSeries X) : s.bot ∈ s :=
  mem_def.2 (Set.mem_range.2 ⟨0, rfl⟩)

@[simp]
theorem bot_le {s : CompositionSeries X} (i : Finₓ (s.length + 1)) : s.bot ≤ s i :=
  s.StrictMono.Monotone (Finₓ.zero_le _)

theorem bot_le_of_mem {s : CompositionSeries X} {x : X} (hx : x ∈ s) : s.bot ≤ x :=
  let ⟨i, hi⟩ := Set.mem_range.2 hx
  hi ▸ bot_le _

theorem length_pos_of_mem_ne {s : CompositionSeries X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    0 < s.length :=
  let ⟨i, hi⟩ := hx
  let ⟨j, hj⟩ := hy
  have hij : i ≠ j := (mt s.inj.2) fun h => hxy (hi ▸ hj ▸ h)
  hij.lt_or_lt.elim (fun hij => lt_of_le_of_ltₓ (zero_le i) (lt_of_lt_of_leₓ hij (Nat.le_of_lt_succₓ j.2))) fun hji =>
    lt_of_le_of_ltₓ (zero_le j) (lt_of_lt_of_leₓ hji (Nat.le_of_lt_succₓ i.2))

theorem forall_mem_eq_of_length_eq_zero {s : CompositionSeries X} (hs : s.length = 0) {x y} (hx : x ∈ s) (hy : y ∈ s) :
    x = y :=
  by_contradiction fun hxy => pos_iff_ne_zero.1 (length_pos_of_mem_ne hx hy hxy) hs

/-- Remove the largest element from a `composition_series`. If the series `s`
has length zero, then `s.erase_top = s` -/
@[simps]
def eraseTop (s : CompositionSeries X) : CompositionSeries X where
  length := s.length - 1
  series := fun i => s ⟨i, lt_of_lt_of_leₓ i.2 (Nat.succ_le_succₓ tsub_le_self)⟩
  step' := fun i => by
    have := s.step ⟨i, lt_of_lt_of_leₓ i.2 tsub_le_self⟩
    cases i
    exact this

theorem top_erase_top (s : CompositionSeries X) :
    s.eraseTop.top = s ⟨s.length - 1, lt_of_le_of_ltₓ tsub_le_self (Nat.lt_succ_selfₓ _)⟩ :=
  show s _ = s _ from
    congr_arg s
      (by
        ext
        simp only [← erase_top_length, ← Finₓ.coe_last, ← Finₓ.coe_cast_succ, ← Finₓ.coe_of_nat_eq_mod, ← Finₓ.coe_mk, ←
          coe_coe])

theorem erase_top_top_le (s : CompositionSeries X) : s.eraseTop.top ≤ s.top := by
  simp [← erase_top, ← top, ← s.strict_mono.le_iff_le, ← Finₓ.le_iff_coe_le_coe, ← tsub_le_self]

@[simp]
theorem bot_erase_top (s : CompositionSeries X) : s.eraseTop.bot = s.bot :=
  rfl

theorem mem_erase_top_of_ne_of_mem {s : CompositionSeries X} {x : X} (hx : x ≠ s.top) (hxs : x ∈ s) : x ∈ s.eraseTop :=
  by
  rcases hxs with ⟨i, rfl⟩
  have hi : (i : ℕ) < (s.length - 1).succ := by
    conv_rhs => rw [← Nat.succ_subₓ (length_pos_of_mem_ne ⟨i, rfl⟩ s.top_mem hx), Nat.succ_sub_one]
    exact
      lt_of_le_of_neₓ (Nat.le_of_lt_succₓ i.2)
        (by
          simpa [← top, ← s.inj, ← Finₓ.ext_iff] using hx)
  refine' ⟨i.cast_succ, _⟩
  simp [← Finₓ.ext_iff, ← Nat.mod_eq_of_ltₓ hi]

theorem mem_erase_top {s : CompositionSeries X} {x : X} (h : 0 < s.length) : x ∈ s.eraseTop ↔ x ≠ s.top ∧ x ∈ s := by
  simp only [← mem_def]
  dsimp' only [← erase_top, ← coe_fn_mk]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) < s.length := by
      conv_rhs => rw [← Nat.succ_sub_one s.length, Nat.succ_subₓ h]
      exact i.2
    simp [← top, ← Finₓ.ext_iff, ← ne_of_ltₓ hi]
    
  · intro h
    exact mem_erase_top_of_ne_of_mem h.1 h.2
    

theorem lt_top_of_mem_erase_top {s : CompositionSeries X} {x : X} (h : 0 < s.length) (hx : x ∈ s.eraseTop) :
    x < s.top :=
  lt_of_le_of_neₓ (le_top_of_mem ((mem_erase_top h).1 hx).2) ((mem_erase_top h).1 hx).1

theorem is_maximal_erase_top_top {s : CompositionSeries X} (h : 0 < s.length) : IsMaximal s.eraseTop.top s.top := by
  have : s.length - 1 + 1 = s.length := by
    conv_rhs => rw [← Nat.succ_sub_one s.length] <;> rw [Nat.succ_subₓ h]
  rw [top_erase_top, top]
  convert s.step ⟨s.length - 1, Nat.sub_ltₓ h zero_lt_one⟩ <;> ext <;> simp [← this]

theorem append_cast_add_aux {s₁ s₂ : CompositionSeries X} (i : Finₓ s₁.length) :
    Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂ (Finₓ.castAdd s₂.length i).cast_succ = s₁ i.cast_succ :=
  by
  cases i
  simp [← Finₓ.append, *]

theorem append_succ_cast_add_aux {s₁ s₂ : CompositionSeries X} (i : Finₓ s₁.length) (h : s₁ (Finₓ.last _) = s₂ 0) :
    Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂ (Finₓ.castAdd s₂.length i).succ = s₁ i.succ := by
  cases' i with i hi
  simp only [← Finₓ.append, ← hi, ← Finₓ.succ_mk, ← Function.comp_app, ← Finₓ.cast_succ_mk, ← Finₓ.coe_mk, ←
    Finₓ.cast_add_mk]
  split_ifs
  · rfl
    
  · have : i + 1 = s₁.length := le_antisymmₓ hi (le_of_not_gtₓ h_1)
    calc
      s₂
            ⟨i + 1 - s₁.length, by
              simp [← this]⟩ =
          s₂ 0 :=
        congr_arg s₂
          (by
            simp [← Finₓ.ext_iff, ← this])_ = s₁ (Finₓ.last _) :=
        h.symm _ = _ :=
        congr_arg s₁
          (by
            simp [← Finₓ.ext_iff, ← this])
    

theorem append_nat_add_aux {s₁ s₂ : CompositionSeries X} (i : Finₓ s₂.length) :
    Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂ (Finₓ.natAdd s₁.length i).cast_succ = s₂ i.cast_succ :=
  by
  cases i
  simp only [← Finₓ.append, ← Nat.not_lt_zeroₓ, ← Finₓ.nat_add_mk, ← add_lt_iff_neg_left, ← add_tsub_cancel_left, ←
    dif_neg, ← Finₓ.cast_succ_mk, ← not_false_iff, ← Finₓ.coe_mk]

theorem append_succ_nat_add_aux {s₁ s₂ : CompositionSeries X} (i : Finₓ s₂.length) :
    Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂ (Finₓ.natAdd s₁.length i).succ = s₂ i.succ := by
  cases' i with i hi
  simp only [← Finₓ.append, ← add_assocₓ, ← Nat.not_lt_zeroₓ, ← Finₓ.nat_add_mk, ← add_lt_iff_neg_left, ←
    add_tsub_cancel_left, ← Finₓ.succ_mk, ← dif_neg, ← not_false_iff, ← Finₓ.coe_mk]

/-- Append two composition series `s₁` and `s₂` such that
the least element of `s₁` is the maximum element of `s₂`. -/
@[simps length]
def append (s₁ s₂ : CompositionSeries X) (h : s₁.top = s₂.bot) : CompositionSeries X where
  length := s₁.length + s₂.length
  series := Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂
  step' := fun i => by
    refine' Finₓ.addCases _ _ i
    · intro i
      rw [append_succ_cast_add_aux _ h, append_cast_add_aux]
      exact s₁.step i
      
    · intro i
      rw [append_nat_add_aux, append_succ_nat_add_aux]
      exact s₂.step i
      

@[simp]
theorem append_cast_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₁.length) :
    append s₁ s₂ h (Finₓ.castAdd s₂.length i).cast_succ = s₁ i.cast_succ :=
  append_cast_add_aux i

@[simp]
theorem append_succ_cast_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₁.length) :
    append s₁ s₂ h (Finₓ.castAdd s₂.length i).succ = s₁ i.succ :=
  append_succ_cast_add_aux i h

@[simp]
theorem append_nat_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₂.length) :
    append s₁ s₂ h (Finₓ.natAdd s₁.length i).cast_succ = s₂ i.cast_succ :=
  append_nat_add_aux i

@[simp]
theorem append_succ_nat_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₂.length) :
    append s₁ s₂ h (Finₓ.natAdd s₁.length i).succ = s₂ i.succ :=
  append_succ_nat_add_aux i

/-- Add an element to the top of a `composition_series` -/
@[simps length]
def snoc (s : CompositionSeries X) (x : X) (hsat : IsMaximal s.top x) : CompositionSeries X where
  length := s.length + 1
  series := Finₓ.snoc s x
  step' := fun i => by
    refine' Finₓ.lastCases _ _ i
    · rwa [Finₓ.snoc_cast_succ, Finₓ.succ_last, Finₓ.snoc_last, ← top]
      
    · intro i
      rw [Finₓ.snoc_cast_succ, ← Finₓ.cast_succ_fin_succ, Finₓ.snoc_cast_succ]
      exact s.step _
      

@[simp]
theorem top_snoc (s : CompositionSeries X) (x : X) (hsat : IsMaximal s.top x) : (snoc s x hsat).top = x :=
  Finₓ.snoc_last _ _

@[simp]
theorem snoc_last (s : CompositionSeries X) (x : X) (hsat : IsMaximal s.top x) :
    snoc s x hsat (Finₓ.last (s.length + 1)) = x :=
  Finₓ.snoc_last _ _

@[simp]
theorem snoc_cast_succ (s : CompositionSeries X) (x : X) (hsat : IsMaximal s.top x) (i : Finₓ (s.length + 1)) :
    snoc s x hsat i.cast_succ = s i :=
  Finₓ.snoc_cast_succ _ _ _

@[simp]
theorem bot_snoc (s : CompositionSeries X) (x : X) (hsat : IsMaximal s.top x) : (snoc s x hsat).bot = s.bot := by
  rw [bot, bot, ← Finₓ.cast_succ_zero, snoc_cast_succ]

theorem mem_snoc {s : CompositionSeries X} {x y : X} {hsat : IsMaximal s.top x} : y ∈ snoc s x hsat ↔ y ∈ s ∨ y = x :=
  by
  simp only [← snoc, ← mem_def]
  constructor
  · rintro ⟨i, rfl⟩
    refine' Finₓ.lastCases _ (fun i => _) i
    · right
      simp
      
    · left
      simp
      
    
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · use i.cast_succ
      simp
      
    · use Finₓ.last _
      simp
      
    

theorem eq_snoc_erase_top {s : CompositionSeries X} (h : 0 < s.length) :
    s = snoc (eraseTop s) s.top (is_maximal_erase_top_top h) := by
  ext x
  simp [← mem_snoc, ← mem_erase_top h]
  by_cases' h : x = s.top <;> simp [*, ← s.top_mem]

@[simp]
theorem snoc_erase_top_top {s : CompositionSeries X} (h : IsMaximal s.eraseTop.top s.top) :
    s.eraseTop.snoc s.top h = s :=
  have h : 0 < s.length :=
    Nat.pos_of_ne_zeroₓ
      (by
        intro hs
        refine' ne_of_gtₓ (lt_of_is_maximal h) _
        simp [← top, ← Finₓ.ext_iff, ← hs])
  (eq_snoc_erase_top h).symm

/-- Two `composition_series X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : fin s₁.length ≃ fin s₂.length` such that for any `i`,
`iso (s₁ i) (s₁ i.succ) (s₂ (e i), s₂ (e i.succ))` -/
def Equivalent (s₁ s₂ : CompositionSeries X) : Prop :=
  ∃ f : Finₓ s₁.length ≃ Finₓ s₂.length,
    ∀ i : Finₓ s₁.length, Iso (s₁ i.cast_succ, s₁ i.succ) (s₂ (f i).cast_succ, s₂ (f i).succ)

namespace Equivalent

@[refl]
theorem refl (s : CompositionSeries X) : Equivalent s s :=
  ⟨Equivₓ.refl _, fun _ => (s.step _).iso_refl⟩

@[symm]
theorem symm {s₁ s₂ : CompositionSeries X} (h : Equivalent s₁ s₂) : Equivalent s₂ s₁ :=
  ⟨h.some.symm, fun i =>
    iso_symm
      (by
        simpa using h.some_spec (h.some.symm i))⟩

@[trans]
theorem trans {s₁ s₂ s₃ : CompositionSeries X} (h₁ : Equivalent s₁ s₂) (h₂ : Equivalent s₂ s₃) : Equivalent s₁ s₃ :=
  ⟨h₁.some.trans h₂.some, fun i => iso_trans (h₁.some_spec i) (h₂.some_spec (h₁.some i))⟩

theorem append {s₁ s₂ t₁ t₂ : CompositionSeries X} (hs : s₁.top = s₂.bot) (ht : t₁.top = t₂.bot) (h₁ : Equivalent s₁ t₁)
    (h₂ : Equivalent s₂ t₂) : Equivalent (append s₁ s₂ hs) (append t₁ t₂ ht) :=
  let e : Finₓ (s₁.length + s₂.length) ≃ Finₓ (t₁.length + t₂.length) :=
    calc
      Finₓ (s₁.length + s₂.length) ≃ Sum (Finₓ s₁.length) (Finₓ s₂.length) := finSumFinEquiv.symm
      _ ≃ Sum (Finₓ t₁.length) (Finₓ t₂.length) := Equivₓ.sumCongr h₁.some h₂.some
      _ ≃ Finₓ (t₁.length + t₂.length) := finSumFinEquiv
      
  ⟨e, by
    intro i
    refine' Finₓ.addCases _ _ i
    · intro i
      simpa [← top, ← bot] using h₁.some_spec i
      
    · intro i
      simpa [← top, ← bot] using h₂.some_spec i
      ⟩

protected theorem snoc {s₁ s₂ : CompositionSeries X} {x₁ x₂ : X} {hsat₁ : IsMaximal s₁.top x₁}
    {hsat₂ : IsMaximal s₂.top x₂} (hequiv : Equivalent s₁ s₂) (htop : Iso (s₁.top, x₁) (s₂.top, x₂)) :
    Equivalent (s₁.snoc x₁ hsat₁) (s₂.snoc x₂ hsat₂) :=
  let e : Finₓ s₁.length.succ ≃ Finₓ s₂.length.succ :=
    calc
      Finₓ (s₁.length + 1) ≃ Option (Finₓ s₁.length) := finSuccEquivLast
      _ ≃ Option (Finₓ s₂.length) := Functor.mapEquiv Option hequiv.some
      _ ≃ Finₓ (s₂.length + 1) := finSuccEquivLast.symm
      
  ⟨e, fun i => by
    refine' Finₓ.lastCases _ _ i
    · simpa [← top] using htop
      
    · intro i
      simpa [← Finₓ.succ_cast_succ] using hequiv.some_spec i
      ⟩

theorem length_eq {s₁ s₂ : CompositionSeries X} (h : Equivalent s₁ s₂) : s₁.length = s₂.length := by
  simpa using Fintype.card_congr h.some

theorem snoc_snoc_swap {s : CompositionSeries X} {x₁ x₂ y₁ y₂ : X} {hsat₁ : IsMaximal s.top x₁}
    {hsat₂ : IsMaximal s.top x₂} {hsaty₁ : IsMaximal (snoc s x₁ hsat₁).top y₁}
    {hsaty₂ : IsMaximal (snoc s x₂ hsat₂).top y₂} (hr₁ : Iso (s.top, x₁) (x₂, y₂)) (hr₂ : Iso (x₁, y₁) (s.top, x₂)) :
    Equivalent (snoc (snoc s x₁ hsat₁) y₁ hsaty₁) (snoc (snoc s x₂ hsat₂) y₂ hsaty₂) :=
  let e : Finₓ (s.length + 1 + 1) ≃ Finₓ (s.length + 1 + 1) := Equivₓ.swap (Finₓ.last _) (Finₓ.castSucc (Finₓ.last _))
  have h1 : ∀ {i : Finₓ s.length}, i.cast_succ.cast_succ ≠ (Finₓ.last _).cast_succ := fun _ =>
    ne_of_ltₓ
      (by
        simp [← Finₓ.cast_succ_lt_last])
  have h2 : ∀ {i : Finₓ s.length}, i.cast_succ.cast_succ ≠ Finₓ.last _ := fun _ =>
    ne_of_ltₓ
      (by
        simp [← Finₓ.cast_succ_lt_last])
  ⟨e, by
    intro i
    dsimp' only [← e]
    refine' Finₓ.lastCases _ (fun i => _) i
    · erw [Equivₓ.swap_apply_left, snoc_cast_succ, snoc_last, Finₓ.succ_last, snoc_last, snoc_cast_succ, snoc_cast_succ,
        Finₓ.succ_cast_succ, snoc_cast_succ, Finₓ.succ_last, snoc_last]
      exact hr₂
      
    · refine' Finₓ.lastCases _ (fun i => _) i
      · erw [Equivₓ.swap_apply_right, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ, Finₓ.succ_cast_succ,
          snoc_cast_succ, Finₓ.succ_last, snoc_last, snoc_last, Finₓ.succ_last, snoc_last]
        exact hr₁
        
      · erw [Equivₓ.swap_apply_of_ne_of_ne h2 h1, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ,
          Finₓ.succ_cast_succ, snoc_cast_succ, Finₓ.succ_cast_succ, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ]
        exact (s.step i).iso_refl
        
      ⟩

end Equivalent

theorem length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero {s₁ s₂ : CompositionSeries X}
    (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) (hs₁ : s₁.length = 0) : s₂.length = 0 := by
  have : s₁.bot = s₁.top :=
    congr_arg s₁
      (Finₓ.ext
        (by
          simp [← hs₁]))
  have : Finₓ.last s₂.length = (0 : Finₓ s₂.length.succ) := s₂.injective (hb.symm.trans (this.trans ht)).symm
  simpa [← Finₓ.ext_iff]

theorem length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos {s₁ s₂ : CompositionSeries X} (hb : s₁.bot = s₂.bot)
    (ht : s₁.top = s₂.top) : 0 < s₁.length → 0 < s₂.length :=
  not_imp_not.1
    (by
      simp only [← pos_iff_ne_zero, ← Ne.def, ← not_iff_not, ← not_not]
      exact length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb.symm ht.symm)

theorem eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero {s₁ s₂ : CompositionSeries X} (hb : s₁.bot = s₂.bot)
    (ht : s₁.top = s₂.top) (hs₁0 : s₁.length = 0) : s₁ = s₂ := by
  have : ∀ x, x ∈ s₁ ↔ x = s₁.top := fun x =>
    ⟨fun hx => forall_mem_eq_of_length_eq_zero hs₁0 hx s₁.top_mem, fun hx => hx.symm ▸ s₁.top_mem⟩
  have : ∀ x, x ∈ s₂ ↔ x = s₂.top := fun x =>
    ⟨fun hx =>
      forall_mem_eq_of_length_eq_zero (length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hs₁0) hx
        s₂.top_mem,
      fun hx => hx.symm ▸ s₂.top_mem⟩
  ext
  simp [*]

/-- Given a `composition_series`, `s`, and an element `x`
such that `x` is maximal inside `s.top` there is a series, `t`,
such that `t.top = x`, `t.bot = s.bot`
and `snoc t s.top _` is equivalent to `s`. -/
theorem exists_top_eq_snoc_equivalant (s : CompositionSeries X) (x : X) (hm : IsMaximal x s.top) (hb : s.bot ≤ x) :
    ∃ t : CompositionSeries X,
      t.bot = s.bot ∧ t.length + 1 = s.length ∧ ∃ htx : t.top = x, Equivalent s (snoc t s.top (htx.symm ▸ hm)) :=
  by
  induction' hn : s.length with n ih generalizing s x
  · exact
      (ne_of_gtₓ (lt_of_le_of_ltₓ hb (lt_of_is_maximal hm))
          (forall_mem_eq_of_length_eq_zero hn s.top_mem s.bot_mem)).elim
    
  · have h0s : 0 < s.length := hn.symm ▸ Nat.succ_posₓ _
    by_cases' hetx : s.erase_top.top = x
    · use s.erase_top
      simp [hetx, ← hn]
      
    · have imxs : is_maximal (x⊓s.erase_top.top) s.erase_top.top :=
        is_maximal_of_eq_inf x s.top rfl (Ne.symm hetx) hm (is_maximal_erase_top_top h0s)
      have :=
        ih _ _ imxs
          (le_inf
            (by
              simpa)
            (le_top_of_mem s.erase_top.bot_mem))
          (by
            simp [← hn])
      rcases this with ⟨t, htb, htl, htt, hteqv⟩
      have hmtx : is_maximal t.top x :=
        is_maximal_of_eq_inf s.erase_top.top s.top
          (by
            rw [inf_comm, htt])
          hetx (is_maximal_erase_top_top h0s) hm
      use snoc t x hmtx
      refine'
        ⟨by
          simp [← htb], by
          simp [← htl], by
          simp , _⟩
      have :
        s.equivalent
          ((snoc t s.erase_top.top (htt.symm ▸ imxs)).snoc s.top
            (by
              simpa using is_maximal_erase_top_top h0s)) :=
        by
        conv_lhs => rw [eq_snoc_erase_top h0s]
        exact
          equivalent.snoc hteqv
            (by
              simpa using (is_maximal_erase_top_top h0s).iso_refl)
      refine' this.trans _
      refine' equivalent.snoc_snoc_swap _ _
      · exact
          iso_symm
            (second_iso_of_eq hm (sup_eq_of_is_maximal hm (is_maximal_erase_top_top h0s) (Ne.symm hetx)) htt.symm)
        
      · exact
          second_iso_of_eq (is_maximal_erase_top_top h0s) (sup_eq_of_is_maximal (is_maximal_erase_top_top h0s) hm hetx)
            (by
              rw [inf_comm, htt])
        
      
    

/-- The **Jordan-Hölder** theorem, stated for any `jordan_holder_lattice`.
If two composition series start and finish at the same place, they are equivalent. -/
theorem jordan_holder (s₁ s₂ : CompositionSeries X) (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) : Equivalent s₁ s₂ :=
  by
  induction' hle : s₁.length with n ih generalizing s₁ s₂
  · rw [eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hle]
    
  · have h0s₂ : 0 < s₂.length := length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos hb ht (hle.symm ▸ Nat.succ_posₓ _)
    rcases exists_top_eq_snoc_equivalant s₁ s₂.erase_top.top (ht.symm ▸ is_maximal_erase_top_top h0s₂)
        (hb.symm ▸ s₂.bot_erase_top ▸ bot_le_of_mem (top_mem _)) with
      ⟨t, htb, htl, htt, hteq⟩
    have :=
      ih t s₂.erase_top
        (by
          simp [← htb, hb])
        htt (Nat.succ_inj'.1 (htl.trans hle))
    refine' hteq.trans _
    conv_rhs => rw [eq_snoc_erase_top h0s₂]
    simp only [← ht]
    exact
      equivalent.snoc this
        (by
          simp [← htt, ← (is_maximal_erase_top_top h0s₂).iso_refl])
    

end CompositionSeries

