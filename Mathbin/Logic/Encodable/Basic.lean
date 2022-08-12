/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Logic.Equiv.Nat
import Mathbin.Order.Directed
import Mathbin.Order.RelIso

/-!
# Encodable types

This file defines encodable (constructively countable) types as a typeclass.
This is used to provide explicit encode/decode functions from and to `ℕ`, with the information that
those functions are inverses of each other.
The difference with `denumerable` is that finite types are encodable. For infinite types,
`encodable` and `denumerable` agree.

## Main declarations

* `encodable α`: States that there exists an explicit encoding function `encode : α → ℕ` with a
  partial inverse `decode : ℕ → option α`.
* `decode₂`: Version of `decode` that is equal to `none` outside of the range of `encode`. Useful as
  we do not require this in the definition of `decode`.
* `ulower α`: Any encodable type has an equivalent type living in the lowest universe, namely a
  subtype of `ℕ`. `ulower α` finds it.

## Implementation notes

The point of asking for an explicit partial inverse `decode : ℕ → option α` to `encode : α → ℕ` is
to make the range of `encode` decidable even when the finiteness of `α` is not.
-/


open Option List Nat Function

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`decode] []
/-- Constructively countable type. Made from an explicit injection `encode : α → ℕ` and a partial
inverse `decode : ℕ → option α`. Note that finite types *are* countable. See `denumerable` if you
wish to enforce infiniteness. -/
class Encodable (α : Type _) where
  encode : α → ℕ
  decode : ℕ → Option α
  encodek : ∀ a, decode (encode a) = some a

attribute [simp] Encodable.encodek

namespace Encodable

variable {α : Type _} {β : Type _}

universe u

theorem encode_injective [Encodable α] : Function.Injective (@encode α _)
  | x, y, e =>
    Option.some.injₓ <| by
      rw [← encodek, e, encodek]

@[simp]
theorem encode_inj [Encodable α] {a b : α} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff

theorem surjective_decode_iget (α : Type _) [Encodable α] [Inhabited α] :
    Surjective fun n => (Encodable.decode α n).iget := fun x =>
  ⟨Encodable.encode x, by
    simp_rw [Encodable.encodek]⟩

/-- An encodable type has decidable equality. Not set as an instance because this is usually not the
best way to infer decidability. -/
def decidableEqOfEncodable (α) [Encodable α] : DecidableEq α
  | a, b => decidableOfIff _ encode_inj

/-- If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable as well. -/
def ofLeftInjection [Encodable α] (f : β → α) (finv : α → Option β) (linv : ∀ b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode α n).bind finv, fun b => by
    simp [← Encodable.encodek, ← linv]⟩

/-- If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well. -/
def ofLeftInverse [Encodable α] (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) : Encodable β :=
  ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)

/-- Encodability is preserved by equivalence. -/
def ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β :=
  ofLeftInverse e e.symm e.left_inv

@[simp]
theorem encode_of_equiv {α β} [Encodable α] (e : β ≃ α) (b : β) : @encode _ (ofEquiv _ e) b = encode (e b) :=
  rfl

@[simp]
theorem decode_of_equiv {α β} [Encodable α] (e : β ≃ α) (n : ℕ) : @decode _ (ofEquiv _ e) n = (decode α n).map e.symm :=
  rfl

instance _root_.nat.encodable : Encodable ℕ :=
  ⟨id, some, fun a => rfl⟩

@[simp]
theorem encode_nat (n : ℕ) : encode n = n :=
  rfl

@[simp]
theorem decode_nat (n : ℕ) : decode ℕ n = some n :=
  rfl

instance (priority := 100) _root_.is_empty.to_encodable [IsEmpty α] : Encodable α :=
  ⟨isEmptyElim, fun n => none, isEmptyElim⟩

instance _root_.punit.encodable : Encodable PUnit :=
  ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by
    simp ⟩

@[simp]
theorem encode_star : encode PUnit.unit = 0 :=
  rfl

@[simp]
theorem decode_unit_zero : decode PUnit 0 = some PUnit.unit :=
  rfl

@[simp]
theorem decode_unit_succ (n) : decode PUnit (succ n) = none :=
  rfl

/-- If `α` is encodable, then so is `option α`. -/
instance _root_.option.encodable {α : Type _} [h : Encodable α] : Encodable (Option α) :=
  ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode α m).map some, fun o => by
    cases o <;> dsimp' <;> simp [← encodek, ← Nat.succ_ne_zero]⟩

@[simp]
theorem encode_none [Encodable α] : encode (@none α) = 0 :=
  rfl

@[simp]
theorem encode_some [Encodable α] (a : α) : encode (some a) = succ (encode a) :=
  rfl

@[simp]
theorem decode_option_zero [Encodable α] : decode (Option α) 0 = some none :=
  rfl

@[simp]
theorem decode_option_succ [Encodable α] (n) : decode (Option α) (succ n) = (decode α n).map some :=
  rfl

/-- Failsafe variant of `decode`. `decode₂ α n` returns the preimage of `n` under `encode` if it
exists, and returns `none` if it doesn't. This requirement could be imposed directly on `decode` but
is not to help make the definition easier to use. -/
def decode₂ (α) [Encodable α] (n : ℕ) : Option α :=
  (decode α n).bind (Option.guard fun a => encode a = n)

theorem mem_decode₂' [Encodable α] {n : ℕ} {a : α} : a ∈ decode₂ α n ↔ a ∈ decode α n ∧ encode a = n := by
  simp [← decode₂] <;> exact ⟨fun ⟨_, h₁, rfl, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨_, h₁, rfl, h₂⟩⟩

theorem mem_decode₂ [Encodable α] {n : ℕ} {a : α} : a ∈ decode₂ α n ↔ encode a = n :=
  mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)

theorem decode₂_eq_some [Encodable α] {n : ℕ} {a : α} : decode₂ α n = some a ↔ encode a = n :=
  mem_decode₂

@[simp]
theorem decode₂_encode [Encodable α] (a : α) : decode₂ α (encode a) = some a := by
  ext
  simp [← mem_decode₂, ← eq_comm]

theorem decode₂_ne_none_iff [Encodable α] {n : ℕ} : decode₂ α n ≠ none ↔ n ∈ Set.Range (encode : α → ℕ) := by
  simp_rw [Set.Range, Set.mem_set_of_eq, Ne.def, Option.eq_none_iff_forall_not_mem, Encodable.mem_decode₂, not_forall,
    not_not]

theorem decode₂_is_partial_inv [Encodable α] : IsPartialInv encode (decode₂ α) := fun a n => mem_decode₂

theorem decode₂_inj [Encodable α] {n : ℕ} {a₁ a₂ : α} (h₁ : a₁ ∈ decode₂ α n) (h₂ : a₂ ∈ decode₂ α n) : a₁ = a₂ :=
  encode_injective <| (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm

theorem encodek₂ [Encodable α] (a : α) : decode₂ α (encode a) = some a :=
  mem_decode₂.2 rfl

/-- The encoding function has decidable range. -/
def decidableRangeEncode (α : Type _) [Encodable α] : DecidablePred (· ∈ Set.Range (@encode α _)) := fun x =>
  decidableOfIff (Option.isSome (decode₂ α x))
    ⟨fun h =>
      ⟨Option.getₓ h, by
        rw [← decode₂_is_partial_inv (Option.getₓ h), Option.some_getₓ]⟩,
      fun ⟨n, hn⟩ => by
      rw [← hn, encodek₂] <;> exact rfl⟩

/-- An encodable type is equivalent to the range of its encoding function. -/
def equivRangeEncode (α : Type _) [Encodable α] : α ≃ Set.Range (@encode α _) where
  toFun := fun a : α => ⟨encode a, Set.mem_range_self _⟩
  invFun := fun n =>
    Option.getₓ
      (show isSome (decode₂ α n.1) by
        cases' n.2 with x hx <;> rw [← hx, encodek₂] <;> exact rfl)
  left_inv := fun a => by
    dsimp' <;> rw [← Option.some_inj, Option.some_getₓ, encodek₂]
  right_inv := fun ⟨n, x, hx⟩ => by
    apply Subtype.eq
    dsimp'
    conv => rhs rw [← hx]
    rw [encode_injective.eq_iff, ← Option.some_inj, Option.some_getₓ, ← hx, encodek₂]

/-- A type with unique element is encodable. This is not an instance to avoid diamonds. -/
def _root_.unique.encodable [Unique α] : Encodable α :=
  ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩

section Sum

variable [Encodable α] [Encodable β]

/-- Explicit encoding function for the sum of two encodable types. -/
def encodeSum : Sum α β → ℕ
  | Sum.inl a => bit0 <| encode a
  | Sum.inr b => bit1 <| encode b

/-- Explicit decoding function for the sum of two encodable types. -/
def decodeSum (n : ℕ) : Option (Sum α β) :=
  match boddDiv2 n with
  | (ff, m) => (decode α m).map Sum.inl
  | (tt, m) => (decode β m).map Sum.inr

/-- If `α` and `β` are encodable, then so is their sum. -/
instance _root_.sum.encodable : Encodable (Sum α β) :=
  ⟨encodeSum, decodeSum, fun s => by
    cases s <;> simp [← encode_sum, ← decode_sum, ← encodek] <;> rfl⟩

@[simp]
theorem encode_inl (a : α) : @encode (Sum α β) _ (Sum.inl a) = bit0 (encode a) :=
  rfl

@[simp]
theorem encode_inr (b : β) : @encode (Sum α β) _ (Sum.inr b) = bit1 (encode b) :=
  rfl

@[simp]
theorem decode_sum_val (n : ℕ) : decode (Sum α β) n = decodeSum n :=
  rfl

end Sum

instance _root_.bool.encodable : Encodable Bool :=
  ofEquiv (Sum Unit Unit) Equivₓ.boolEquivPunitSumPunit

@[simp]
theorem encode_tt : encode true = 1 :=
  rfl

@[simp]
theorem encode_ff : encode false = 0 :=
  rfl

@[simp]
theorem decode_zero : decode Bool 0 = some false :=
  rfl

@[simp]
theorem decode_one : decode Bool 1 = some true :=
  rfl

theorem decode_ge_two (n) (h : 2 ≤ n) : decode Bool n = none := by
  suffices decode_sum n = none by
    change (decode_sum n).map _ = none
    rw [this]
    rfl
  have : 1 ≤ div2 n := by
    rw [div2_val, Nat.le_div_iff_mul_leₓ]
    exacts[h, by
      decide]
  cases' exists_eq_succ_of_ne_zero (ne_of_gtₓ this) with m e
  simp [← decode_sum] <;> cases bodd n <;> simp [← decode_sum] <;> rw [e] <;> rfl

noncomputable instance _root_.Prop.encodable : Encodable Prop :=
  ofEquiv Bool Equivₓ.propEquivBool

section Sigma

variable {γ : α → Type _} [Encodable α] [∀ a, Encodable (γ a)]

/-- Explicit encoding function for `sigma γ` -/
def encodeSigma : Sigma γ → ℕ
  | ⟨a, b⟩ => mkpair (encode a) (encode b)

/-- Explicit decoding function for `sigma γ` -/
def decodeSigma (n : ℕ) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
  (decode α n₁).bind fun a => (decode (γ a) n₂).map <| Sigma.mk a

instance _root_.sigma.encodable : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [← encode_sigma, ← decode_sigma, ← unpair_mkpair, ← encodek]⟩

@[simp]
theorem decode_sigma_val (n : ℕ) :
    decode (Sigma γ) n = (decode α n.unpair.1).bind fun a => (decode (γ a) n.unpair.2).map <| Sigma.mk a :=
  show DecodeSigma._match1 _ = _ by
    cases n.unpair <;> rfl

@[simp]
theorem encode_sigma_val (a b) : @encode (Sigma γ) _ ⟨a, b⟩ = mkpair (encode a) (encode b) :=
  rfl

end Sigma

section Prod

variable [Encodable α] [Encodable β]

/-- If `α` and `β` are encodable, then so is their product. -/
instance _root_.prod.encodable : Encodable (α × β) :=
  ofEquiv _ (Equivₓ.sigmaEquivProd α β).symm

@[simp]
theorem decode_prod_val (n : ℕ) :
    decode (α × β) n = (decode α n.unpair.1).bind fun a => (decode β n.unpair.2).map <| Prod.mk a :=
  show (decode (Sigma fun _ => β) n).map (Equivₓ.sigmaEquivProd α β) = _ by
    simp <;> cases decode α n.unpair.1 <;> simp <;> cases decode β n.unpair.2 <;> rfl

@[simp]
theorem encode_prod_val (a b) : @encode (α × β) _ (a, b) = mkpair (encode a) (encode b) :=
  rfl

end Prod

section Subtype

open Subtype Decidable

variable {P : α → Prop} [encA : Encodable α] [decP : DecidablePred P]

include encA

/-- Explicit encoding function for a decidable subtype of an encodable type -/
def encodeSubtype : { a : α // P a } → ℕ
  | ⟨v, h⟩ => encode v

include decP

/-- Explicit decoding function for a decidable subtype of an encodable type -/
def decodeSubtype (v : ℕ) : Option { a : α // P a } :=
  (decode α v).bind fun a => if h : P a then some ⟨a, h⟩ else none

/-- A decidable subtype of an encodable type is encodable. -/
instance _root_.subtype.encodable : Encodable { a : α // P a } :=
  ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by
    simp [← encode_subtype, ← decode_subtype, ← encodek, ← h]⟩

theorem Subtype.encode_eq (a : Subtype P) : encode a = encode a.val := by
  cases a <;> rfl

end Subtype

instance _root_.fin.encodable (n) : Encodable (Finₓ n) :=
  Subtype.encodable

instance _root_.int.encodable : Encodable ℤ :=
  ofEquiv _ Equivₓ.intEquivNat

instance _root_.pnat.encodable : Encodable ℕ+ :=
  ofEquiv _ Equivₓ.pnatEquivNat

/-- The lift of an encodable type is encodable. -/
instance _root_.ulift.encodable [Encodable α] : Encodable (ULift α) :=
  ofEquiv _ Equivₓ.ulift

/-- The lift of an encodable type is encodable. -/
instance _root_.plift.encodable [Encodable α] : Encodable (Plift α) :=
  ofEquiv _ Equivₓ.plift

/-- If `β` is encodable and there is an injection `f : α → β`, then `α` is encodable as well. -/
noncomputable def ofInj [Encodable β] (f : α → β) (hf : Injective f) : Encodable α :=
  ofLeftInjection f (partialInv f) fun x => (partial_inv_of_injective hf _ _).2 rfl

end Encodable

section Ulower

attribute [local instance] Encodable.decidableRangeEncode

/-- `ulower α : Type` is an equivalent type in the lowest universe, given `encodable α`. -/
def Ulower (α : Type _) [Encodable α] : Type :=
  Set.Range (Encodable.encode : α → ℕ)deriving DecidableEq, Encodable

end Ulower

namespace Ulower

variable (α : Type _) [Encodable α]

/-- The equivalence between the encodable type `α` and `ulower α : Type`. -/
def equiv : α ≃ Ulower α :=
  Encodable.equivRangeEncode α

variable {α}

/-- Lowers an `a : α` into `ulower α`. -/
def down (a : α) : Ulower α :=
  equiv α a

instance [Inhabited α] : Inhabited (Ulower α) :=
  ⟨down default⟩

/-- Lifts an `a : ulower α` into `α`. -/
def up (a : Ulower α) : α :=
  (equiv α).symm a

@[simp]
theorem down_up {a : Ulower α} : down a.up = a :=
  Equivₓ.right_inv _ _

@[simp]
theorem up_down {a : α} : (down a).up = a :=
  Equivₓ.left_inv _ _

@[simp]
theorem up_eq_up {a b : Ulower α} : a.up = b.up ↔ a = b :=
  Equivₓ.apply_eq_iff_eq _

@[simp]
theorem down_eq_down {a b : α} : down a = down b ↔ a = b :=
  Equivₓ.apply_eq_iff_eq _

@[ext]
protected theorem ext {a b : Ulower α} : a.up = b.up → a = b :=
  up_eq_up.1

end Ulower

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) :
  p (choose ex) :=
-/
namespace Encodable

section FindA

variable {α : Type _} (p : α → Prop) [Encodable α] [DecidablePred p]

private def good : Option α → Prop
  | some a => p a
  | none => False

private def decidable_good : DecidablePred (Goodₓ p)
  | n => by
    cases n <;> unfold good <;> infer_instance

attribute [local instance] decidable_good

open Encodable

variable {p}

/-- Constructive choice function for a decidable subtype of an encodable type. -/
def chooseX (h : ∃ x, p x) : { a : α // p a } :=
  have : ∃ n, Goodₓ p (decode α n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by
      simp [← good, ← encodek, ← pw]⟩
  match _, Nat.find_specₓ this with
  | some a, h => ⟨a, h⟩

/-- Constructive choice function for a decidable predicate over an encodable type. -/
def choose (h : ∃ x, p x) : α :=
  (chooseX h).1

theorem choose_spec (h : ∃ x, p x) : p (choose h) :=
  (chooseX h).2

end FindA

/-- A constructive version of `classical.axiom_of_choice` for `encodable` types. -/
theorem axiom_of_choice {α : Type _} {β : α → Type _} {R : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (R x y)] (H : ∀ x, ∃ y, R x y) : ∃ f : ∀ a, β a, ∀ x, R x (f x) :=
  ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩

/-- A constructive version of `classical.skolem` for `encodable` types. -/
theorem skolem {α : Type _} {β : α → Type _} {P : ∀ x, β x → Prop} [c : ∀ a, Encodable (β a)]
    [d : ∀ x y, Decidable (P x y)] : (∀ x, ∃ y, P x y) ↔ ∃ f : ∀ a, β a, ∀ x, P x (f x) :=
  ⟨axiom_of_choice, fun ⟨f, H⟩ x => ⟨_, H x⟩⟩

/-- The `encode` function, viewed as an embedding. -/
/-
There is a total ordering on the elements of an encodable type, induced by the map to ℕ.
-/
def encode' (α) [Encodable α] : α ↪ ℕ :=
  ⟨Encodable.encode, Encodable.encode_injective⟩

instance {α} [Encodable α] : IsTrans _ (encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).IsTrans

instance {α} [Encodable α] : IsAntisymm _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).IsAntisymm

instance {α} [Encodable α] : IsTotal _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).IsTotal

end Encodable

namespace Directed

open Encodable

variable {α : Type _} {β : Type _} [Encodable α] [Inhabited α]

/-- Given a `directed r` function `f : α → β` defined on an encodable inhabited type,
construct a noncomputable sequence such that `r (f (x n)) (f (x (n + 1)))`
and `r (f a) (f (x (encode a + 1))`. -/
protected noncomputable def sequence {r : β → β → Prop} (f : α → β) (hf : Directed r f) : ℕ → α
  | 0 => default
  | n + 1 =>
    let p := sequence n
    match decode α n with
    | none => Classical.some (hf p p)
    | some a => Classical.some (hf p a)

theorem sequence_mono_nat {r : β → β → Prop} {f : α → β} (hf : Directed r f) (n : ℕ) :
    r (f (hf.sequence f n)) (f (hf.sequence f (n + 1))) := by
  dsimp' [← Directed.sequence]
  generalize eq : hf.sequence f n = p
  cases' h : decode α n with a
  · exact (Classical.some_spec (hf p p)).1
    
  · exact (Classical.some_spec (hf p a)).1
    

theorem rel_sequence {r : β → β → Prop} {f : α → β} (hf : Directed r f) (a : α) :
    r (f a) (f (hf.sequence f (encode a + 1))) := by
  simp only [← Directed.sequence, ← encodek]
  exact (Classical.some_spec (hf _ a)).2

variable [Preorderₓ β] {f : α → β} (hf : Directed (· ≤ ·) f)

theorem sequence_mono : Monotone (f ∘ hf.sequence f) :=
  monotone_nat_of_le_succ <| hf.sequence_mono_nat

theorem le_sequence (a : α) : f a ≤ f (hf.sequence f (encode a + 1)) :=
  hf.rel_sequence a

end Directed

section Quotientₓ

open Encodable Quotientₓ

variable {α : Type _} {s : Setoidₓ α} [@DecidableRel α (· ≈ ·)] [Encodable α]

/-- Representative of an equivalence class. This is a computable version of `quot.out` for a setoid
on an encodable type. -/
def Quotientₓ.rep (q : Quotientₓ s) : α :=
  choose (exists_rep q)

theorem Quotientₓ.rep_spec (q : Quotientₓ s) : ⟦q.rep⟧ = q :=
  choose_spec (exists_rep q)

/-- The quotient of an encodable space by a decidable equivalence relation is encodable. -/
def encodableQuotient : Encodable (Quotientₓ s) :=
  ⟨fun q => encode q.rep, fun n => Quotientₓ.mk <$> decode α n, by
    rintro ⟨l⟩ <;> rw [encodek] <;> exact congr_arg some ⟦l⟧.rep_spec⟩

end Quotientₓ

