/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Num.Lemmas
import Mathbin.SetTheory.Cardinal.Ordinal
import Mathbin.Tactic.DeriveFintype

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `fin_encoding_nat_bool`   : a binary encoding of ℕ in a simple alphabet.
- `fin_encoding_nat_Γ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unary_fin_encoding_nat` : a unary encoding of ℕ
- `fin_encoding_bool_bool`  : an encoding of bool.
-/


universe u v

open Cardinal

namespace Computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure Encoding (α : Type u) where
  Γ : Type v
  encode : α → List Γ
  decode : List Γ → Option α
  decode_encode : ∀ x, decode (encode x) = some x

theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode := by
  refine' fun _ _ h => Option.some_injective _ _
  rw [← e.decode_encode, ← e.decode_encode, h]

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  ΓFin : Fintype Γ

instance {α : Type u} (e : FinEncoding α) : Fintype e.toEncoding.Γ :=
  e.ΓFin

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype

instance inhabitedΓ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩

/-- The natural inclusion of bool in Γ'. -/
def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit

/-- An arbitrary section of the natural inclusion of bool in Γ'. -/
def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => arbitrary Bool

theorem left_inverse_section_inclusion : Function.LeftInverse sectionΓ'Bool inclusionBoolΓ' := fun x =>
  Bool.casesOn x rfl rfl

theorem inclusion_bool_Γ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective (Exists.intro sectionΓ'Bool left_inverse_section_inclusion)

/-- An encoding function of the positive binary numbers in bool. -/
def encodePosNum : PosNum → List Bool
  | PosNum.one => [true]
  | PosNum.bit0 n => ff :: encode_pos_num n
  | PosNum.bit1 n => tt :: encode_pos_num n

/-- An encoding function of the binary numbers in bool. -/
def encodeNum : Num → List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n

/-- An encoding function of ℕ in bool. -/
def encodeNat (n : ℕ) : List Bool :=
  encodeNum n

/-- A decoding function from `list bool` to the positive binary numbers. -/
def decodePosNum : List Bool → PosNum
  | ff :: l => PosNum.bit0 (decode_pos_num l)
  | tt :: l => ite (l = []) PosNum.one (PosNum.bit1 (decode_pos_num l))
  | _ => PosNum.one

/-- A decoding function from `list bool` to the binary numbers. -/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l

/-- A decoding function from `list bool` to ℕ. -/
def decodeNat : List Bool → Nat := fun l => decodeNum l

theorem encode_pos_num_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun m => List.cons_ne_nil _ _) fun m => List.cons_ne_nil _ _

theorem decode_encode_pos_num : ∀ n, decodePosNum (encodePosNum n) = n := by
  intro n
  induction' n with m hm m hm <;> unfold encode_pos_num decode_pos_num
  · rfl
    
  · rw [hm]
    exact if_neg (encode_pos_num_nonempty m)
    
  · exact congr_arg PosNum.bit0 hm
    

theorem decode_encode_num : ∀ n, decodeNum (encodeNum n) = n := by
  intro n
  cases n <;> unfold encode_num decode_num
  · rfl
    
  rw [decode_encode_pos_num n]
  rw [PosNum.cast_to_num]
  exact if_neg (encode_pos_num_nonempty n)

theorem decode_encode_nat : ∀ n, decodeNat (encodeNat n) = n := by
  intro n
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg coe (decode_encode_num ↑n)

/-- A binary encoding of ℕ in bool. -/
def encodingNatBool : Encoding ℕ where
  Γ := Bool
  encode := encodeNat
  decode := fun n => some (decodeNat n)
  decode_encode := fun n => congr_arg _ (decode_encode_nat n)

/-- A binary fin_encoding of ℕ in bool. -/
def finEncodingNatBool : FinEncoding ℕ :=
  ⟨encodingNatBool, Bool.fintype⟩

/-- A binary encoding of ℕ in Γ'. -/
def encodingNatΓ' : Encoding ℕ where
  Γ := Γ'
  encode := fun x => List.map inclusionBoolΓ' (encodeNat x)
  decode := fun x => some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode := fun x =>
    congr_arg _ <| by
      rw [List.map_mapₓ, List.map_id' left_inverse_section_inclusion, decode_encode_nat]

/-- A binary fin_encoding of ℕ in Γ'. -/
def finEncodingNatΓ' : FinEncoding ℕ :=
  ⟨encodingNatΓ', Γ'.fintype⟩

/-- A unary encoding function of ℕ in bool. -/
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => tt :: unary_encode_nat n

/-- A unary decoding function from `list bool` to ℕ. -/
def unaryDecodeNat : List Bool → Nat :=
  List.length

theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n

/-- A unary fin_encoding of ℕ. -/
def unaryFinEncodingNat : FinEncoding ℕ where
  Γ := Bool
  encode := unaryEncodeNat
  decode := fun n => some (unaryDecodeNat n)
  decode_encode := fun n => congr_arg _ (unary_decode_encode_nat n)
  ΓFin := Bool.fintype

/-- An encoding function of bool in bool. -/
def encodeBool : Bool → List Bool :=
  List.ret

/-- A decoding function from `list bool` to bool. -/
def decodeBool : List Bool → Bool
  | b :: _ => b
  | _ => arbitrary Bool

theorem decode_encode_bool : ∀ b, decodeBool (encodeBool b) = b := fun b => Bool.casesOn b rfl rfl

/-- A fin_encoding of bool in bool. -/
def finEncodingBoolBool : FinEncoding Bool where
  Γ := Bool
  encode := encodeBool
  decode := fun x => some (decodeBool x)
  decode_encode := fun x => congr_arg _ (decode_encode_bool x)
  ΓFin := Bool.fintype

instance inhabitedFinEncoding : Inhabited (FinEncoding Bool) :=
  ⟨finEncodingBoolBool⟩

instance inhabitedEncoding : Inhabited (Encoding Bool) :=
  ⟨finEncodingBoolBool.toEncoding⟩

theorem Encoding.card_le_card_list {α : Type u} (e : Encoding.{u, v} α) :
    Cardinal.lift.{v} (# α) ≤ Cardinal.lift.{u} (# (List e.Γ)) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩

theorem Encoding.card_le_aleph_0 {α : Type u} (e : Encoding.{u, v} α) [Encodable e.Γ] : # α ≤ ℵ₀ := by
  refine' Cardinal.lift_le.1 (e.card_le_card_list.trans _)
  simp only [← Cardinal.lift_aleph_0, ← Cardinal.lift_le_aleph_0]
  cases' is_empty_or_nonempty e.Γ with h h
  · simp only [← Cardinal.mk_le_aleph_0]
    
  · rw [Cardinal.mk_list_eq_aleph_0]
    

theorem FinEncoding.card_le_aleph_0 {α : Type u} (e : FinEncoding α) : # α ≤ ℵ₀ := by
  have : Encodable e.Γ := Fintype.toEncodable _
  exact e.to_encoding.card_le_aleph_0

end Computability

