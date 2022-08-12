/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.List.MinMax
import Mathbin.Logic.Encodable.Basic

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/


/-- A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent of `α ≃ ℕ`. -/
class Denumerable (α : Type _) extends Encodable α where
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n

open Nat

namespace Denumerable

section

variable {α : Type _} {β : Type _} [Denumerable α] [Denumerable β]

open Encodable

theorem decode_is_some (α) [Denumerable α] (n : ℕ) : (decode α n).isSome :=
  Option.is_some_iff_exists.2 <| (decode_inv n).imp fun a => Exists.fst

/-- Returns the `n`-th element of `α` indexed by the decoding. -/
def ofNat (α) [f : Denumerable α] (n : ℕ) : α :=
  Option.getₓ (decode_is_some α n)

@[simp]
theorem decode_eq_of_nat (α) [Denumerable α] (n : ℕ) : decode α n = some (ofNat α n) :=
  Option.eq_some_of_is_some _

@[simp]
theorem of_nat_of_decode {n b} (h : decode α n = some b) : ofNat α n = b :=
  Option.some.injₓ <| (decode_eq_of_nat _ _).symm.trans h

@[simp]
theorem encode_of_nat (n) : encode (ofNat α n) = n := by
  let ⟨a, h, e⟩ := decode_inv n
  rwa [of_nat_of_decode h]

@[simp]
theorem of_nat_encode (a) : ofNat α (encode a) = a :=
  of_nat_of_decode (encodek _)

/-- A denumerable type is equivalent to `ℕ`. -/
def eqv (α) [Denumerable α] : α ≃ ℕ :=
  ⟨encode, ofNat α, of_nat_encode, encode_of_nat⟩

-- See Note [lower instance priority]
instance (priority := 100) : Infinite α :=
  Infinite.of_surjective _ (eqv α).Surjective

/-- A type equivalent to `ℕ` is denumerable. -/
def mk' {α} (e : α ≃ ℕ) : Denumerable α where
  encode := e
  decode := some ∘ e.symm
  encodek := fun a => congr_arg some (e.symm_apply_apply _)
  decode_inv := fun n => ⟨_, rfl, e.apply_symm_apply _⟩

/-- Denumerability is conserved by equivalences. This is transitivity of equivalence the denumerable
way. -/
def ofEquiv (α) {β} [Denumerable α] (e : β ≃ α) : Denumerable β :=
  { Encodable.ofEquiv _ e with
    decode_inv := fun n => by
      simp }

@[simp]
theorem of_equiv_of_nat (α) {β} [Denumerable α] (e : β ≃ α) (n) : @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n) := by
  apply of_nat_of_decode <;> show Option.map _ _ = _ <;> simp

/-- All denumerable types are equivalent. -/
def equiv₂ (α β) [Denumerable α] [Denumerable β] : α ≃ β :=
  (eqv α).trans (eqv β).symm

instance nat : Denumerable ℕ :=
  ⟨fun n => ⟨_, rfl, rfl⟩⟩

@[simp]
theorem of_nat_nat (n) : ofNat ℕ n = n :=
  rfl

/-- If `α` is denumerable, then so is `option α`. -/
instance option : Denumerable (Option α) :=
  ⟨fun n => by
    cases n
    · refine' ⟨none, _, encode_none⟩
      rw [decode_option_zero, Option.mem_def]
      
    refine' ⟨some (of_nat α n), _, _⟩
    · rw [decode_option_succ, decode_eq_of_nat, Option.map_some'ₓ, Option.mem_def]
      
    rw [encode_some, encode_of_nat]⟩

/-- If `α` and `β` are denumerable, then so is their sum. -/
instance sum : Denumerable (Sum α β) :=
  ⟨fun n => by
    suffices ∃ a ∈ @decode_sum α β _ _ n, encode_sum a = bit (bodd n) (div2 n) by
      simpa [← bit_decomp]
    simp [← decode_sum] <;> cases bodd n <;> simp [← decode_sum, ← bit, ← encode_sum]⟩

section Sigma

variable {γ : α → Type _} [∀ a, Denumerable (γ a)]

/-- A denumerable collection of denumerable types is denumerable. -/
instance sigma : Denumerable (Sigma γ) :=
  ⟨fun n => by
    simp [← decode_sigma] <;>
      exact
        ⟨_, _, ⟨rfl, HEq.rfl⟩, by
          simp ⟩⟩

@[simp]
theorem sigma_of_nat_val (n : ℕ) : ofNat (Sigma γ) n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩ :=
  Option.some.injₓ <| by
    rw [← decode_eq_of_nat, decode_sigma_val] <;> simp <;> rfl

end Sigma

/-- If `α` and `β` are denumerable, then so is their product. -/
instance prod : Denumerable (α × β) :=
  ofEquiv _ (Equivₓ.sigmaEquivProd α β).symm

@[simp]
theorem prod_of_nat_val (n : ℕ) : ofNat (α × β) n = (ofNat α (unpair n).1, ofNat β (unpair n).2) := by
  simp <;> rfl

@[simp]
theorem prod_nat_of_nat : ofNat (ℕ × ℕ) = unpair := by
  funext <;> simp

instance int : Denumerable ℤ :=
  Denumerable.mk' Equivₓ.intEquivNat

instance pnat : Denumerable ℕ+ :=
  Denumerable.mk' Equivₓ.pnatEquivNat

/-- The lift of a denumerable type is denumerable. -/
instance ulift : Denumerable (ULift α) :=
  ofEquiv _ Equivₓ.ulift

/-- The lift of a denumerable type is denumerable. -/
instance plift : Denumerable (Plift α) :=
  ofEquiv _ Equivₓ.plift

/-- If `α` is denumerable, then `α × α` and `α` are equivalent. -/
def pair : α × α ≃ α :=
  equiv₂ _ _

end

end Denumerable

namespace Nat.Subtype

open Function Encodable

/-! ### Subsets of `ℕ` -/


variable {s : Set ℕ} [Infinite s]

section Classical

open Classical

theorem exists_succ (x : s) : ∃ n, ↑x + n + 1 ∈ s :=
  Classical.by_contradiction fun h =>
    have : ∀ (a : ℕ) (ha : a ∈ s), a < succ x := fun a ha =>
      lt_of_not_geₓ fun hax =>
        h
          ⟨a - (x + 1), by
            rwa [add_right_commₓ, add_tsub_cancel_of_le hax]⟩
    Fintype.false
      ⟨(((Multiset.range (succ x)).filter (· ∈ s)).pmap (fun (y : ℕ) (hy : y ∈ s) => Subtype.mk y hy)
            (by
              simp [-Multiset.range_succ])).toFinset,
        by
        simpa [← Subtype.ext_iff_val, ← Multiset.mem_filter, -Multiset.range_succ] ⟩

end Classical

variable [DecidablePred (· ∈ s)]

/-- Returns the next natural in a set, according to the usual ordering of `ℕ`. -/
def succ (x : s) : s :=
  have h : ∃ m, ↑x + m + 1 ∈ s := exists_succ x
  ⟨↑x + Nat.findₓ h + 1, Nat.find_specₓ h⟩

theorem succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
  have hx : ∃ m, ↑y + m + 1 ∈ s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.findₓ hx ≤ k := Nat.find_min'ₓ _ (hk ▸ x.2)
  show (y : ℕ) + Nat.findₓ hx + 1 ≤ x by
    rw [hk] <;> exact add_le_add_right (add_le_add_left this _) _

theorem le_succ_of_forall_lt_le {x y : s} (h : ∀, ∀ z < x, ∀, z ≤ y) : x ≤ succ y :=
  have hx : ∃ m, ↑y + m + 1 ∈ s := exists_succ _
  show ↑x ≤ ↑y + Nat.findₓ hx + 1 from
    le_of_not_gtₓ fun hxy =>
      (h ⟨_, Nat.find_specₓ hx⟩ hxy).not_lt <|
        calc
          ↑y ≤ ↑y + Nat.findₓ hx := le_add_of_nonneg_right (Nat.zero_leₓ _)
          _ < ↑y + Nat.findₓ hx + 1 := Nat.lt_succ_selfₓ _
          

theorem lt_succ_self (x : s) : x < succ x :=
  calc
    (x : ℕ) ≤ x + _ := le_self_add
    _ < succ x := Nat.lt_succ_selfₓ (x + _)
    

theorem lt_succ_iff_le {x y : s} : x < succ y ↔ x ≤ y :=
  ⟨fun h => le_of_not_gtₓ fun h' => not_le_of_gtₓ h (succ_le_of_lt h'), fun h => lt_of_le_of_ltₓ h (lt_succ_self _)⟩

/-- Returns the `n`-th element of a set, according to the usual ordering of `ℕ`. -/
def ofNat (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : ℕ → s
  | 0 => ⊥
  | n + 1 => succ (of_nat n)

theorem of_nat_surjective_aux : ∀ {x : ℕ} (hx : x ∈ s), ∃ n, ofNat s n = ⟨x, hx⟩
  | x => fun hx => by
    let t : List s :=
      ((List.range x).filter fun y => y ∈ s).pmap (fun (y : ℕ) (hy : y ∈ s) => ⟨y, hy⟩)
        (by
          simp )
    have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩ := by
      simp [← List.mem_filterₓ, ← Subtype.ext_iff_val, ← t] <;> intros <;> rfl
    have wf : ∀ m : s, List.maximum t = m → ↑m < x := fun m hmax => by
      simpa [← hmt] using List.maximum_mem hmax
    cases' hmax : List.maximum t with m
    · exact
        ⟨0,
          le_antisymmₓ bot_le
            (le_of_not_gtₓ fun h =>
              List.not_mem_nilₓ (⊥ : s) <| by
                rw [← List.maximum_eq_none.1 hmax, hmt] <;> exact h)⟩
      
    cases' of_nat_surjective_aux m.2 with a ha
    exact
      ⟨a + 1,
        le_antisymmₓ
            (by
              rw [of_nat] <;>
                exact
                  succ_le_of_lt
                    (by
                      rw [ha] <;> exact wf _ hmax)) <|
          by
          rw [of_nat] <;>
            exact
              le_succ_of_forall_lt_le fun z hz => by
                rw [ha] <;> cases m <;> exact List.le_maximum_of_mem (hmt.2 hz) hmax⟩

theorem of_nat_surjective : Surjective (ofNat s) := fun ⟨x, hx⟩ => of_nat_surjective_aux hx

@[simp]
theorem of_nat_range : Set.Range (ofNat s) = Set.Univ :=
  of_nat_surjective.range_eq

@[simp]
theorem coe_comp_of_nat_range : Set.Range (coe ∘ ofNat s : ℕ → ℕ) = s := by
  rw [Set.range_comp coe, of_nat_range, Set.image_univ, Subtype.range_coe]

private def to_fun_aux (x : s) : ℕ :=
  (List.range x).countp (· ∈ s)

private theorem to_fun_aux_eq (x : s) : toFunAux x = ((Finset.range x).filter (· ∈ s)).card := by
  rw [to_fun_aux, List.countp_eq_length_filter] <;> rfl

open Finset

private theorem right_inverse_aux : ∀ n, toFunAux (ofNat s n) = n
  | 0 => by
    rw [to_fun_aux_eq, card_eq_zero, eq_empty_iff_forall_not_mem]
    rintro n hn
    rw [mem_filter, of_nat, mem_range] at hn
    exact bot_le.not_lt (show (⟨n, hn.2⟩ : s) < ⊥ from hn.1)
  | n + 1 => by
    have ih : toFunAux (ofNat s n) = n := right_inverse_aux n
    have h₁ : (ofNat s n : ℕ) ∉ (range (ofNat s n)).filter (· ∈ s) := by
      simp
    have h₂ : (range (succ (ofNat s n))).filter (· ∈ s) = insert (ofNat s n) ((range (ofNat s n)).filter (· ∈ s)) := by
      simp only [← Finset.ext_iff, ← mem_insert, ← mem_range, ← mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [← h.2, ← and_trueₓ] <;> exact Or.symm (lt_or_eq_of_leₓ ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
          fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (of_nat s n).Prop⟩) fun h => ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [← to_fun_aux_eq, ← of_nat, ← range_succ] at ih⊢
    conv => rhs rw [← ih, ← card_insert_of_not_mem h₁, ← h₂]

/-- Any infinite set of naturals is denumerable. -/
def denumerable (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : Denumerable s :=
  Denumerable.ofEquiv ℕ
    { toFun := toFunAux, invFun := ofNat s,
      left_inv := left_inverse_of_surjective_of_right_inverse of_nat_surjective right_inverse_aux,
      right_inv := right_inverse_aux }

end Nat.Subtype

namespace Denumerable

open Encodable

/-- An infinite encodable type is denumerable. -/
def ofEncodableOfInfinite (α : Type _) [Encodable α] [Infinite α] : Denumerable α := by
  let this := @decidable_range_encode α _ <;>
    let this : Infinite (Set.Range (@encode α _)) :=
      Infinite.of_injective _ (Equivₓ.ofInjective _ encode_injective).Injective
  let this := Nat.Subtype.denumerable (Set.Range (@encode α _))
  exact Denumerable.ofEquiv (Set.Range (@encode α _)) (equiv_range_encode α)

end Denumerable

