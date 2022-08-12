/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Logic.Denumerable

/-!
# Equivalences involving `list`-like types

This file defines some additional constructive equivalences using `encodable` and the pairing
function on `ℕ`.
-/


open Nat List

namespace Encodable

variable {α : Type _}

section List

variable [Encodable α]

/-- Explicit encoding function for `list α` -/
def encodeList : List α → ℕ
  | [] => 0
  | a :: l => succ (mkpair (encode a) (encode_list l))

/-- Explicit decoding function for `list α` -/
def decodeList : ℕ → Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_leₓ h
      (· :: ·) <$> decode α v₁ <*> decode_list v₂

/-- If `α` is encodable, then so is `list α`. This uses the `mkpair` and `unpair` functions from
`data.nat.pairing`. -/
instance _root_.list.encodable : Encodable (List α) :=
  ⟨encodeList, decodeList, fun l => by
    induction' l with a l IH <;> simp [← encode_list, ← decode_list, ← unpair_mkpair, ← encodek, *]⟩

@[simp]
theorem encode_list_nil : encode (@nil α) = 0 :=
  rfl

@[simp]
theorem encode_list_cons (a : α) (l : List α) : encode (a :: l) = succ (mkpair (encode a) (encode l)) :=
  rfl

@[simp]
theorem decode_list_zero : decode (List α) 0 = some [] :=
  show decodeList 0 = some [] by
    rw [decode_list]

@[simp]
theorem decode_list_succ (v : ℕ) :
    decode (List α) (succ v) = (· :: ·) <$> decode α v.unpair.1 <*> decode (List α) v.unpair.2 :=
  show decodeList (succ v) = _ by
    cases' e : unpair v with v₁ v₂
    simp [← decode_list, ← e]
    rfl

theorem length_le_encode : ∀ l : List α, length l ≤ encode l
  | [] => zero_le _
  | a :: l => succ_le_succ <| (length_le_encode l).trans (right_le_mkpair _ _)

end List

section Finset

variable [Encodable α]

private def enle : α → α → Prop :=
  encode ⁻¹'o (· ≤ ·)

private theorem enle.is_linear_order : IsLinearOrder α Enle :=
  (RelEmbedding.preimage ⟨encode, encode_injective⟩ (· ≤ ·)).IsLinearOrder

private def decidable_enle (a b : α) : Decidable (Enle a b) := by
  unfold enle Order.Preimage <;> infer_instance

attribute [local instance] enle.is_linear_order decidable_enle

/-- Explicit encoding function for `multiset α` -/
def encodeMultiset (s : Multiset α) : ℕ :=
  encode (s.sort Enle)

/-- Explicit decoding function for `multiset α` -/
def decodeMultiset (n : ℕ) : Option (Multiset α) :=
  coe <$> decode (List α) n

/-- If `α` is encodable, then so is `multiset α`. -/
instance _root_.multiset.encodable : Encodable (Multiset α) :=
  ⟨encodeMultiset, decodeMultiset, fun s => by
    simp [← encode_multiset, ← decode_multiset, ← encodek]⟩

end Finset

/-- A listable type with decidable equality is encodable. -/
def encodableOfList [DecidableEq α] (l : List α) (H : ∀ x, x ∈ l) : Encodable α :=
  ⟨fun a => indexOfₓ a l, l.nth, fun a => index_of_nth (H _)⟩

/-- A finite type is encodable. Because the encoding is not unique, we wrap it in `trunc` to
preserve computability. -/
def _root_.fintype.trunc_encodable (α : Type _) [DecidableEq α] [Fintype α] : Trunc (Encodable α) :=
  @Quot.recOnSubsingleton _ (fun s : Multiset α => (∀ x : α, x ∈ s) → Trunc (Encodable α)) _ Finset.univ.1
    (fun l H => Trunc.mk <| encodableOfList l H) Finset.mem_univ

/-- A noncomputable way to arbitrarily choose an ordering on a finite type.
It is not made into a global instance, since it involves an arbitrary choice.
This can be locally made into an instance with `local attribute [instance] fintype.to_encodable`. -/
noncomputable def _root_.fintype.to_encodable (α : Type _) [Fintype α] : Encodable α := by
  classical
  exact (Fintype.truncEncodable α).out

/-- If `α` is encodable, then so is `vector α n`. -/
instance _root_.vector.encodable [Encodable α] {n} : Encodable (Vector α n) :=
  Subtype.encodable

/-- If `α` is encodable, then so is `fin n → α`. -/
instance finArrow [Encodable α] {n} : Encodable (Finₓ n → α) :=
  ofEquiv _ (Equivₓ.vectorEquivFin _ _).symm

instance finPi (n) (π : Finₓ n → Type _) [∀ i, Encodable (π i)] : Encodable (∀ i, π i) :=
  ofEquiv _ (Equivₓ.piEquivSubtypeSigma (Finₓ n) π)

/-- If `α` is encodable, then so is `array n α`. -/
instance _root_.array.encodable [Encodable α] {n} : Encodable (Arrayₓ n α) :=
  ofEquiv _ (Equivₓ.arrayEquivFin _ _)

/-- If `α` is encodable, then so is `finset α`. -/
instance _root_.finset.encodable [Encodable α] : Encodable (Finset α) :=
  have := decidable_eq_of_encodable α
  of_equiv { s : Multiset α // s.Nodup }
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- When `α` is finite and `β` is encodable, `α → β` is encodable too. Because the encoding is not
unique, we wrap it in `trunc` to preserve computability. -/
-- TODO: Unify with `fintype_pi` and find a better name
def fintypeArrow (α : Type _) (β : Type _) [DecidableEq α] [Fintype α] [Encodable β] : Trunc (Encodable (α → β)) :=
  (Fintype.truncEquivFin α).map fun f =>
    Encodable.ofEquiv (Finₓ (Fintype.card α) → β) <| Equivₓ.arrowCongr f (Equivₓ.refl _)

/-- When `α` is finite and all `π a` are encodable, `Π a, π a` is encodable too. Because the
encoding is not unique, we wrap it in `trunc` to preserve computability. -/
def fintypePi (α : Type _) (π : α → Type _) [DecidableEq α] [Fintype α] [∀ a, Encodable (π a)] :
    Trunc (Encodable (∀ a, π a)) :=
  (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σa, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
      Trunc.mk <| @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _) (Equivₓ.piEquivSubtypeSigma α π)

/-- The elements of a `fintype` as a sorted list. -/
def sortedUniv (α) [Fintype α] [Encodable α] : List α :=
  Finset.univ.sort (Encodable.encode' α ⁻¹'o (· ≤ ·))

@[simp]
theorem mem_sorted_univ {α} [Fintype α] [Encodable α] (x : α) : x ∈ sortedUniv α :=
  (Finset.mem_sort _).2 (Finset.mem_univ _)

@[simp]
theorem length_sorted_univ (α) [Fintype α] [Encodable α] : (sortedUniv α).length = Fintype.card α :=
  Finset.length_sort _

@[simp]
theorem sorted_univ_nodup (α) [Fintype α] [Encodable α] : (sortedUniv α).Nodup :=
  Finset.sort_nodup _ _

@[simp]
theorem sorted_univ_to_finset (α) [Fintype α] [Encodable α] [DecidableEq α] : (sortedUniv α).toFinset = Finset.univ :=
  Finset.sort_to_finset _ _

/-- An encodable `fintype` is equivalent to the same size `fin`. -/
def fintypeEquivFin {α} [Fintype α] [Encodable α] : α ≃ Finₓ (Fintype.card α) := by
  have : DecidableEq α := Encodable.decidableEqOfEncodable _
  trans
  · exact ((sorted_univ_nodup α).nthLeEquivOfForallMemList _ mem_sorted_univ).symm
    
  exact Equivₓ.cast (congr_arg _ (length_sorted_univ α))

/-- If `α` and `β` are encodable and `α` is a fintype, then `α → β` is encodable as well. -/
instance fintypeArrowOfEncodable {α β : Type _} [Encodable α] [Fintype α] [Encodable β] : Encodable (α → β) :=
  ofEquiv (Finₓ (Fintype.card α) → β) <| Equivₓ.arrowCongr fintypeEquivFin (Equivₓ.refl _)

end Encodable

namespace Denumerable

variable {α : Type _} {β : Type _} [Denumerable α] [Denumerable β]

open Encodable

section List

theorem denumerable_list_aux : ∀ n : ℕ, ∃ a ∈ @decodeList α _ n, encodeList a = n
  | 0 => by
    rw [decode_list] <;> exact ⟨_, rfl, rfl⟩
  | succ v => by
    cases' e : unpair v with v₁ v₂
    have h := unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use of_nat α v₁ :: a
    simp [← decode_list, ← e, ← h₂, ← h₁, ← encode_list, ← mkpair_unpair' e]

/-- If `α` is denumerable, then so is `list α`. -/
instance denumerableList : Denumerable (List α) :=
  ⟨denumerable_list_aux⟩

@[simp]
theorem list_of_nat_zero : ofNat (List α) 0 = [] := by
  rw [← @encode_list_nil α, of_nat_encode]

@[simp]
theorem list_of_nat_succ (v : ℕ) : ofNat (List α) (succ v) = ofNat α v.unpair.1 :: ofNat (List α) v.unpair.2 :=
  of_nat_of_decode <|
    show decodeList (succ v) = _ by
      cases' e : unpair v with v₁ v₂
      simp [← decode_list, ← e]
      rw [show decode_list v₂ = decode (List α) v₂ from rfl, decode_eq_of_nat] <;> rfl

end List

section Multiset

/-- Outputs the list of differences of the input list, that is
`lower [a₁, a₂, ...] n = [a₁ - n, a₂ - a₁, ...]` -/
def lower : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m - n) :: lower l m

/-- Outputs the list of partial sums of the input list, that is
`raise [a₁, a₂, ...] n = [n + a₁, n + a₁ + a₂, ...]` -/
def raise : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m + n) :: raise l (m + n)

theorem lower_raise : ∀ l n, lower (raise l n) n = l
  | [], n => rfl
  | m :: l, n => by
    rw [raise, lower, add_tsub_cancel_right, lower_raise]

theorem raise_lower : ∀ {l n}, List.Sorted (· ≤ ·) (n :: l) → raise (lower l n) n = l
  | [], n, h => rfl
  | m :: l, n, h => by
    have : n ≤ m := List.rel_of_sorted_cons h _ (l.mem_cons_self _)
    simp [← raise, ← lower, ← tsub_add_cancel_of_le this, ← raise_lower h.of_cons]

theorem raise_chain : ∀ l n, List.Chain (· ≤ ·) n (raise l n)
  | [], n => List.Chain.nil
  | m :: l, n => List.Chain.cons (Nat.le_add_leftₓ _ _) (raise_chain _ _)

/-- `raise l n` is an non-decreasing sequence. -/
theorem raise_sorted : ∀ l n, List.Sorted (· ≤ ·) (raise l n)
  | [], n => List.sorted_nil
  | m :: l, n => (List.chain_iff_pairwise (@le_transₓ _ _)).1 (raise_chain _ _)

/-- If `α` is denumerable, then so is `multiset α`. Warning: this is *not* the same encoding as used
in `multiset.encodable`. -/
instance multiset : Denumerable (Multiset α) :=
  mk'
    ⟨fun s : Multiset α => encode <| lower ((s.map encode).sort (· ≤ ·)) 0, fun n =>
      Multiset.map (ofNat α) (raise (ofNat (List ℕ) n) 0), fun s => by
      have := raise_lower (List.sorted_cons.2 ⟨fun n _ => zero_le n, (s.map encode).sort_sorted _⟩) <;>
        simp [-Multiset.coe_map, ← this],
      fun n => by
      simp [-Multiset.coe_map, ← List.merge_sort_eq_self _ (raise_sorted _ _), ← lower_raise]⟩

end Multiset

section Finset

/-- Outputs the list of differences minus one of the input list, that is
`lower' [a₁, a₂, a₃, ...] n = [a₁ - n, a₂ - a₁ - 1, a₃ - a₂ - 1, ...]`. -/
def lower' : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m - n) :: lower' l (m + 1)

/-- Outputs the list of partial sums plus one of the input list, that is
`raise [a₁, a₂, a₃, ...] n = [n + a₁, n + a₁ + a₂ + 1, n + a₁ + a₂ + a₃ + 2, ...]`. Adding one each
time ensures the elements are distinct. -/
def raise' : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m + n) :: raise' l (m + n + 1)

theorem lower_raise' : ∀ l n, lower' (raise' l n) n = l
  | [], n => rfl
  | m :: l, n => by
    simp [← raise', ← lower', ← add_tsub_cancel_right, ← lower_raise']

theorem raise_lower' : ∀ {l n}, (∀, ∀ m ∈ l, ∀, n ≤ m) → List.Sorted (· < ·) l → raise' (lower' l n) n = l
  | [], n, h₁, h₂ => rfl
  | m :: l, n, h₁, h₂ => by
    have : n ≤ m := h₁ _ (l.mem_cons_self _)
    simp [← raise', ← lower', ← tsub_add_cancel_of_le this, ←
      raise_lower' (List.rel_of_sorted_cons h₂ : ∀, ∀ a ∈ l, ∀, m < a) h₂.of_cons]

theorem raise'_chain : ∀ (l) {m n}, m < n → List.Chain (· < ·) m (raise' l n)
  | [], m, n, h => List.Chain.nil
  | a :: l, m, n, h => List.Chain.cons (lt_of_lt_of_leₓ h (Nat.le_add_leftₓ _ _)) (raise'_chain _ (lt_succ_selfₓ _))

/-- `raise' l n` is a strictly increasing sequence. -/
theorem raise'_sorted : ∀ l n, List.Sorted (· < ·) (raise' l n)
  | [], n => List.sorted_nil
  | m :: l, n => (List.chain_iff_pairwise (@lt_transₓ _ _)).1 (raise'_chain _ (lt_succ_selfₓ _))

/-- Makes `raise' l n` into a finset. Elements are distinct thanks to `raise'_sorted`. -/
def raise'Finset (l : List ℕ) (n : ℕ) : Finset ℕ :=
  ⟨raise' l n, (raise'_sorted _ _).imp (@ne_of_ltₓ _ _)⟩

/-- If `α` is denumerable, then so is `finset α`. Warning: this is *not* the same encoding as used
in `finset.encodable`. -/
instance finset : Denumerable (Finset α) :=
  mk'
    ⟨fun s : Finset α => encode <| lower' ((s.map (eqv α).toEmbedding).sort (· ≤ ·)) 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List ℕ) n) 0), fun s =>
      Finset.eq_of_veq <| by
        simp [-Multiset.coe_map, ← raise'_finset, ← raise_lower' (fun n _ => zero_le n) (Finset.sort_sorted_lt _)],
      fun n => by
      simp [-Multiset.coe_map, ← Finset.map, ← raise'_finset, ← Finset.sort, ←
        List.merge_sort_eq_self (· ≤ ·) ((raise'_sorted _ _).imp (@le_of_ltₓ _ _)), ← lower_raise']⟩

end Finset

end Denumerable

namespace Equivₓ

/-- The type lists on unit is canonically equivalent to the natural numbers. -/
def listUnitEquiv : List Unit ≃ ℕ where
  toFun := List.length
  invFun := List.repeat ()
  left_inv := fun u =>
    List.length_injective
      (by
        simp )
  right_inv := fun n => List.length_repeat () n

/-- `list ℕ` is equivalent to `ℕ`. -/
def listNatEquivNat : List ℕ ≃ ℕ :=
  Denumerable.eqv _

/-- If `α` is equivalent to `ℕ`, then `list α` is equivalent to `α`. -/
def listEquivSelfOfEquivNat {α : Type} (e : α ≃ ℕ) : List α ≃ α :=
  calc
    List α ≃ List ℕ := listEquivOfEquiv e
    _ ≃ ℕ := listNatEquivNat
    _ ≃ α := e.symm
    

end Equivₓ

