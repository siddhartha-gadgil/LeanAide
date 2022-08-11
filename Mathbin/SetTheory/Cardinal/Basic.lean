/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathbin.Data.Nat.PartEnat
import Mathbin.Data.Set.Countable
import Mathbin.Logic.Small
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Order.SuccPred.Basic
import Mathbin.SetTheory.Cardinal.SchroederBernstein

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `cardinal` the type of cardinal numbers (in a given universe).
* `cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `cardinal`.
* Addition `c₁ + c₂` is defined by `cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `cardinal.mul_def : #α * #β = #(α × β)`.
* The order `c₁ ≤ c₂` is defined by `cardinal.le_def α β : #α ≤ #β ↔ nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `cardinal.aleph_0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `cardinal.aleph_0.{u} : cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.
* `cardinal.sum` is the sum of an indexed family of cardinals, i.e. the cardinality of the
  corresponding sigma type.
* `cardinal.prod` is the product of an indexed family of cardinals, i.e. the cardinality of the
  corresponding pi type.
* `cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## Main instances

* Cardinals form a `canonically_ordered_comm_semiring` with the aforementioned sum and product.
* Cardinals form a `succ_order`. Use `order.succ c` for the smallest cardinal greater than `c`.
* The less than relation on cardinals forms a well-order.
* Cardinals form a `conditionally_complete_linear_order_bot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `cardinal.bdd_above_iff_small`. One can use `Sup` for the cardinal supremum, and `Inf` for the
  minimum of a set of cardinals.

## Main Statements

* Cantor's theorem: `cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `set_theory/cardinal_ordinal.lean`.
* There is an instance `has_pow cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/


open Function Set Order

open Classical

noncomputable section

universe u v w

variable {α β : Type u}

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance Cardinal.isEquivalent : Setoidₓ (Type u) where
  R := fun α β => Nonempty (α ≃ β)
  iseqv := ⟨fun α => ⟨Equivₓ.refl α⟩, fun α β ⟨e⟩ => ⟨e.symm⟩, fun α β γ ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def Cardinal : Type (u + 1) :=
  Quotientₓ Cardinal.isEquivalent

namespace Cardinal

/-- The cardinal number of a type -/
def mk : Type u → Cardinal :=
  Quotientₓ.mk

-- mathport name: «expr#»
localized [Cardinal] notation "#" => Cardinal.mk

instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) :=
  ⟨mk, fun c => True, fun c _ => (Quot.induction_on c) fun α => ⟨α, rfl⟩⟩

@[elab_as_eliminator]
theorem induction_on {p : Cardinal → Prop} (c : Cardinal) (h : ∀ α, p (# α)) : p c :=
  Quotientₓ.induction_on c h

@[elab_as_eliminator]
theorem induction_on₂ {p : Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal) (h : ∀ α β, p (# α) (# β)) :
    p c₁ c₂ :=
  Quotientₓ.induction_on₂ c₁ c₂ h

@[elab_as_eliminator]
theorem induction_on₃ {p : Cardinal → Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal) (c₃ : Cardinal)
    (h : ∀ α β γ, p (# α) (# β) (# γ)) : p c₁ c₂ c₃ :=
  Quotientₓ.induction_on₃ c₁ c₂ c₃ h

protected theorem eq : # α = # β ↔ Nonempty (α ≃ β) :=
  Quotientₓ.eq

@[simp]
theorem mk_def (α : Type u) : @Eq Cardinal ⟦α⟧ (# α) :=
  rfl

@[simp]
theorem mk_out (c : Cardinal) : # c.out = c :=
  Quotientₓ.out_eq _

/-- The representative of the cardinal of a type is equivalent ot the original type. -/
def outMkEquiv {α : Type v} : (# α).out ≃ α :=
  Nonempty.some <|
    Cardinal.eq.mp
      (by
        simp )

theorem mk_congr (e : α ≃ β) : # α = # β :=
  Quot.sound ⟨e⟩

alias mk_congr ← _root_.equiv.cardinal_eq

/-- Lift a function between `Type*`s to a function between `cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotientₓ.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[simp]
theorem map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) : map f hf (# α) = # (f α) :=
  rfl

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  (Quotientₓ.map₂ f) fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : cardinal.{v} → cardinal.{max v u}` -/
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift (fun α β e => Equivₓ.ulift.trans <| e.trans Equivₓ.ulift.symm) c

@[simp]
theorem mk_ulift (α) : # (ULift.{v, u} α) = lift.{v} (# α) :=
  rfl

/-- `lift.{(max u v) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a => (induction_on a) fun α => (Equivₓ.ulift.trans Equivₓ.ulift.symm).cardinal_eq

/-- `lift.{(max v u) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax

/-- A cardinal lifted to a lower or equal universe equals itself. -/
@[simp]
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  (induction_on a) fun α => mk_congr Equivₓ.ulift

/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a

/-- A cardinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a

@[simp]
theorem lift_lift (a : Cardinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  (induction_on a) fun α => (Equivₓ.ulift.trans <| Equivₓ.ulift.trans Equivₓ.ulift.symm).cardinal_eq

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    (Quotientₓ.liftOn₂ q₁ q₂ fun α β => Nonempty <| α ↪ β) fun α β γ δ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance : PartialOrderₓ Cardinal.{u} where
  le := (· ≤ ·)
  le_refl := by
    rintro ⟨α⟩ <;> exact ⟨embedding.refl _⟩
  le_trans := by
    rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩ <;> exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotientₓ.sound (e₁.antisymm e₂)

theorem le_def (α β : Type u) : # α ≤ # β ↔ Nonempty (α ↪ β) :=
  Iff.rfl

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : # α ≤ # β :=
  ⟨⟨f, hf⟩⟩

theorem _root_.function.embedding.cardinal_le {α β : Type u} (f : α ↪ β) : # α ≤ # β :=
  ⟨f⟩

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : # β ≤ # α :=
  ⟨Embedding.ofSurjective f hf⟩

theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ # α ↔ ∃ p : Set α, # p = c :=
  ⟨(induction_on c) fun β ⟨⟨f, hf⟩⟩ => ⟨Set.Range f, (Equivₓ.ofInjective f hf).cardinal_eq.symm⟩, fun ⟨p, e⟩ =>
    e ▸ ⟨⟨Subtype.val, fun a b => Subtype.eq⟩⟩⟩

theorem mk_subtype_le {α : Type u} (p : α → Prop) : # (Subtype p) ≤ # α :=
  ⟨Embedding.subtype p⟩

theorem mk_set_le (s : Set α) : # s ≤ # α :=
  mk_subtype_le s

theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) := by
  trans _
  rw [← Quotientₓ.out_eq c, ← Quotientₓ.out_eq c']
  rfl

theorem lift_mk_le {α : Type u} {β : Type v} : lift.{max v w} (# α) ≤ lift.{max u w} (# β) ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equivₓ.ulift Equivₓ.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equivₓ.ulift.symm Equivₓ.ulift.symm f⟩⟩

/-- A variant of `cardinal.lift_mk_le` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} (# α) ≤ lift.{u} (# β) ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{u, v, 0}

theorem lift_mk_eq {α : Type u} {β : Type v} : lift.{max v w} (# α) = lift.{max u w} (# β) ↔ Nonempty (α ≃ β) :=
  Quotientₓ.eq.trans
    ⟨fun ⟨f⟩ => ⟨Equivₓ.ulift.symm.trans <| f.trans Equivₓ.ulift⟩, fun ⟨f⟩ =>
      ⟨Equivₓ.ulift.trans <| f.trans Equivₓ.ulift.symm⟩⟩

/-- A variant of `cardinal.lift_mk_eq` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} (# α) = lift.{u} (# β) ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}

@[simp]
theorem lift_le {a b : Cardinal} : lift a ≤ lift b ↔ a ≤ b :=
  (induction_on₂ a b) fun α β => by
    rw [← lift_umax]
    exact lift_mk_le

/-- `cardinal.lift` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def liftOrderEmbedding : Cardinal.{v} ↪o Cardinal.{max v u} :=
  OrderEmbedding.ofMapLeIff lift fun _ _ => lift_le

theorem lift_injective : Injective lift.{u, v} :=
  liftOrderEmbedding.Injective

@[simp]
theorem lift_inj {a b : Cardinal} : lift a = lift b ↔ a = b :=
  lift_injective.eq_iff

@[simp]
theorem lift_lt {a b : Cardinal} : lift a < lift b ↔ a < b :=
  liftOrderEmbedding.lt_iff_lt

theorem lift_strict_mono : StrictMono lift := fun a b => lift_lt.2

theorem lift_monotone : Monotone lift :=
  lift_strict_mono.Monotone

instance : Zero Cardinal.{u} :=
  ⟨# Pempty⟩

instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

theorem mk_eq_zero (α : Type u) [IsEmpty α] : # α = 0 :=
  (Equivₓ.equivPempty α).cardinal_eq

@[simp]
theorem lift_zero : lift 0 = 0 :=
  mk_congr (Equivₓ.equivPempty _)

@[simp]
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
  lift_injective.eq_iff' lift_zero

theorem mk_eq_zero_iff {α : Type u} : # α = 0 ↔ IsEmpty α :=
  ⟨fun e =>
    let ⟨h⟩ := Quotientₓ.exact e
    h.isEmpty,
    @mk_eq_zero α⟩

theorem mk_ne_zero_iff {α : Type u} : # α ≠ 0 ↔ Nonempty α :=
  (not_iff_not.2 mk_eq_zero_iff).trans not_is_empty_iff

@[simp]
theorem mk_ne_zero (α : Type u) [Nonempty α] : # α ≠ 0 :=
  mk_ne_zero_iff.2 ‹_›

instance : One Cardinal.{u} :=
  ⟨# PUnit⟩

instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩

theorem mk_eq_one (α : Type u) [Unique α] : # α = 1 :=
  (Equivₓ.equivPunit α).cardinal_eq

theorem le_one_iff_subsingleton {α : Type u} : # α ≤ 1 ↔ Subsingleton α :=
  ⟨fun ⟨f⟩ => ⟨fun a b => f.Injective (Subsingleton.elimₓ _ _)⟩, fun ⟨h⟩ => ⟨⟨fun a => PUnit.unit, fun a b _ => h _ _⟩⟩⟩

instance : Add Cardinal.{u} :=
  ⟨(map₂ Sum) fun α β γ δ => Equivₓ.sumCongr⟩

theorem add_def (α β : Type u) : # α + # β = # (Sum α β) :=
  rfl

instance : HasNatCast Cardinal.{u} :=
  ⟨Nat.unaryCast⟩

@[simp]
theorem mk_sum (α : Type u) (β : Type v) : # (Sum α β) = lift.{v, u} (# α) + lift.{u, v} (# β) :=
  mk_congr (Equivₓ.ulift.symm.sumCongr Equivₓ.ulift.symm)

@[simp]
theorem mk_option {α : Type u} : # (Option α) = # α + 1 :=
  (Equivₓ.optionEquivSumPunit α).cardinal_eq

@[simp]
theorem mk_psum (α : Type u) (β : Type v) : # (PSum α β) = lift.{v} (# α) + lift.{u} (# β) :=
  (mk_congr (Equivₓ.psumEquivSum α β)).trans (mk_sum α β)

@[simp]
theorem mk_fintype (α : Type u) [Fintype α] : # α = Fintype.card α := by
  refine' Fintype.induction_empty_option' _ _ _ α
  · intro α β h e hα
    let this := Fintype.ofEquiv β e.symm
    rwa [mk_congr e, Fintype.card_congr e] at hα
    
  · rfl
    
  · intro α h hα
    simp [← hα]
    rfl
    

instance : Mul Cardinal.{u} :=
  ⟨(map₂ Prod) fun α β γ δ => Equivₓ.prodCongr⟩

theorem mul_def (α β : Type u) : # α * # β = # (α × β) :=
  rfl

@[simp]
theorem mk_prod (α : Type u) (β : Type v) : # (α × β) = lift.{v, u} (# α) * lift.{u, v} (# β) :=
  mk_congr (Equivₓ.ulift.symm.prodCongr Equivₓ.ulift.symm)

private theorem mul_comm' (a b : Cardinal.{u}) : a * b = b * a :=
  (induction_on₂ a b) fun α β => mk_congr <| Equivₓ.prodComm α β

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
instance : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β → α) fun α β γ δ e₁ e₂ => e₂.arrowCongr e₁⟩

-- mathport name: «expr ^ »
local infixr:0 "^" => @Pow.pow Cardinal Cardinal Cardinal.hasPow

-- mathport name: «expr ^ℕ »
local infixr:80 " ^ℕ " => @Pow.pow Cardinal ℕ Monoidₓ.hasPow

theorem power_def (α β) : (# α^# β) = # (β → α) :=
  rfl

theorem mk_arrow (α : Type u) (β : Type v) : # (α → β) = (lift.{u} (# β)^lift.{v} (# α)) :=
  mk_congr (Equivₓ.ulift.symm.arrowCongr Equivₓ.ulift.symm)

@[simp]
theorem lift_power (a b) : lift (a^b) = (lift a^lift b) :=
  (induction_on₂ a b) fun α β => mk_congr <| Equivₓ.ulift.trans (Equivₓ.ulift.arrowCongr Equivₓ.ulift).symm

@[simp]
theorem power_zero {a : Cardinal} : (a^0) = 1 :=
  (induction_on a) fun α => mk_congr <| Equivₓ.pemptyArrowEquivPunit α

@[simp]
theorem power_one {a : Cardinal} : (a^1) = a :=
  (induction_on a) fun α => mk_congr <| Equivₓ.punitArrowEquiv α

theorem power_add {a b c : Cardinal} : (a^b + c) = (a^b) * (a^c) :=
  (induction_on₃ a b c) fun α β γ => mk_congr <| Equivₓ.sumArrowEquivProdArrow β γ α

instance : CommSemiringₓ Cardinal.{u} where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  zero_add := fun a => (induction_on a) fun α => mk_congr <| Equivₓ.emptySum Pempty α
  add_zero := fun a => (induction_on a) fun α => mk_congr <| Equivₓ.sumEmpty α Pempty
  add_assoc := fun a b c => (induction_on₃ a b c) fun α β γ => mk_congr <| Equivₓ.sumAssoc α β γ
  add_comm := fun a b => (induction_on₂ a b) fun α β => mk_congr <| Equivₓ.sumComm α β
  zero_mul := fun a => (induction_on a) fun α => mk_congr <| Equivₓ.pemptyProd α
  mul_zero := fun a => (induction_on a) fun α => mk_congr <| Equivₓ.prodPempty α
  one_mul := fun a => (induction_on a) fun α => mk_congr <| Equivₓ.punitProd α
  mul_one := fun a => (induction_on a) fun α => mk_congr <| Equivₓ.prodPunit α
  mul_assoc := fun a b c => (induction_on₃ a b c) fun α β γ => mk_congr <| Equivₓ.prodAssoc α β γ
  mul_comm := mul_comm'
  left_distrib := fun a b c => (induction_on₃ a b c) fun α β γ => mk_congr <| Equivₓ.prodSumDistrib α β γ
  right_distrib := fun a b c => (induction_on₃ a b c) fun α β γ => mk_congr <| Equivₓ.sumProdDistrib α β γ
  npow := fun n c => c^n
  npow_zero' := @power_zero
  npow_succ' := fun n c =>
    show (c^n + 1) = c * (c^n) by
      rw [power_add, power_one, mul_comm']

theorem power_bit0 (a b : Cardinal) : (a^bit0 b) = (a^b) * (a^b) :=
  power_add

theorem power_bit1 (a b : Cardinal) : (a^bit1 b) = (a^b) * (a^b) * a := by
  rw [bit1, ← power_bit0, power_add, power_one]

@[simp]
theorem one_power {a : Cardinal} : (1^a) = 1 :=
  (induction_on a) fun α => (Equivₓ.arrowPunitEquivPunit α).cardinal_eq

@[simp]
theorem mk_bool : # Bool = 2 := by
  simp

@[simp]
theorem mk_Prop : # Prop = 2 := by
  simp

@[simp]
theorem zero_power {a : Cardinal} : a ≠ 0 → (0^a) = 0 :=
  (induction_on a) fun α heq =>
    mk_eq_zero_iff.2 <|
      is_empty_pi.2 <|
        let ⟨a⟩ := mk_ne_zero_iff.1 HEq
        ⟨a, Pempty.is_empty⟩

theorem power_ne_zero {a : Cardinal} (b) : a ≠ 0 → (a^b) ≠ 0 :=
  (induction_on₂ a b) fun α β h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩

theorem mul_power {a b c : Cardinal} : (a * b^c) = (a^c) * (b^c) :=
  (induction_on₃ a b c) fun α β γ => mk_congr <| Equivₓ.arrowProdEquivProdArrow α β γ

theorem power_mul {a b c : Cardinal} : (a^b * c) = ((a^b)^c) := by
  rw [mul_comm b c]
  exact induction_on₃ a b c fun α β γ => mk_congr <| Equivₓ.curry γ β α

@[simp]
theorem pow_cast_right (a : Cardinal.{u}) (n : ℕ) : (a^(↑n : Cardinal.{u})) = a ^ℕ n :=
  rfl

@[simp]
theorem lift_one : lift 1 = 1 :=
  mk_congr <| Equivₓ.ulift.trans Equivₓ.punitEquivPunit

@[simp]
theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
  (induction_on₂ a b) fun α β => mk_congr <| Equivₓ.ulift.trans (Equivₓ.sumCongr Equivₓ.ulift Equivₓ.ulift).symm

@[simp]
theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
  (induction_on₂ a b) fun α β => mk_congr <| Equivₓ.ulift.trans (Equivₓ.prodCongr Equivₓ.ulift Equivₓ.ulift).symm

@[simp]
theorem lift_bit0 (a : Cardinal) : lift (bit0 a) = bit0 (lift a) :=
  lift_add a a

@[simp]
theorem lift_bit1 (a : Cardinal) : lift (bit1 a) = bit1 (lift a) := by
  simp [← bit1]

theorem lift_two : lift.{u, v} 2 = 2 := by
  simp

@[simp]
theorem mk_set {α : Type u} : # (Set α) = (2^# α) := by
  simp [← Set, ← mk_arrow]

/-- A variant of `cardinal.mk_set` expressed in terms of a `set` instead of a `Type`. -/
@[simp]
theorem mk_powerset {α : Type u} (s : Set α) : # ↥(𝒫 s) = (2^# ↥s) :=
  (mk_congr (Equivₓ.Set.powerset s)).trans mk_set

theorem lift_two_power (a) : lift (2^a) = (2^lift a) := by
  simp

section OrderProperties

open Sum

protected theorem zero_le : ∀ a : Cardinal, 0 ≤ a := by
  rintro ⟨α⟩ <;> exact ⟨embedding.of_is_empty⟩

private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩ <;> exact ⟨e₁.sum_map e₂⟩

instance add_covariant_class : CovariantClass Cardinal Cardinal (· + ·) (· ≤ ·) :=
  ⟨fun a b c => add_le_add' le_rfl⟩

instance add_swap_covariant_class : CovariantClass Cardinal Cardinal (swap (· + ·)) (· ≤ ·) :=
  ⟨fun a b c h => add_le_add' h le_rfl⟩

instance : CanonicallyOrderedCommSemiring Cardinal.{u} :=
  { Cardinal.commSemiring, Cardinal.partialOrder with bot := 0, bot_le := Cardinal.zero_le,
    add_le_add_left := fun a b => add_le_add_left,
    exists_add_of_le := fun a b =>
      (induction_on₂ a b) fun α β ⟨⟨f, hf⟩⟩ =>
        have : Sum α (Range fᶜ : Set β) ≃ β :=
          (Equivₓ.sumCongr (Equivₓ.ofInjective f hf) (Equivₓ.refl _)).trans <| Equivₓ.Set.sumCompl (Range f)
        ⟨# ↥(Range fᶜ), mk_congr this.symm⟩,
    le_self_add := fun a b => (add_zeroₓ a).Ge.trans <| add_le_add_left (Cardinal.zero_le _) _,
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b =>
      (induction_on₂ a b) fun α β => by
        simpa only [← mul_def, ← mk_eq_zero_iff, ← is_empty_prod] using id }

@[simp]
theorem zero_lt_one : (0 : Cardinal) < 1 :=
  lt_of_le_of_neₓ (zero_le _) zero_ne_one

theorem zero_power_le (c : Cardinal.{u}) : ((0 : Cardinal.{u})^c) ≤ 1 := by
  by_cases' h : c = 0
  rw [h, power_zero]
  rw [zero_power h]
  apply zero_le

theorem power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → (a^b) ≤ (a^c) := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩ <;>
    exact
      let ⟨a⟩ := mk_ne_zero_iff.1 hα
      ⟨@embedding.arrow_congr_left _ _ _ ⟨a⟩ e⟩

theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 ≤ b) : a ≤ (a^b) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le _
    
  · convert power_le_power_left ha hb
    exact power_one.symm
    

/-- **Cantor's theorem** -/
theorem cantor (a : Cardinal.{u}) : a < (2^a) := by
  induction' a using Cardinal.induction_on with α
  rw [← mk_set]
  refine' ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, _⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf

instance : NoMaxOrder Cardinal.{u} :=
  { Cardinal.partialOrder with exists_gt := fun a => ⟨_, cantor a⟩ }

instance : CanonicallyLinearOrderedAddMonoid Cardinal.{u} :=
  { (inferInstance : CanonicallyOrderedAddMonoid Cardinal), Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply embedding.total,
    decidableLe := Classical.decRel _ }

-- short-circuit type class inference
instance : DistribLattice Cardinal.{u} := by
  infer_instance

theorem one_lt_iff_nontrivial {α : Type u} : 1 < # α ↔ Nontrivial α := by
  rw [← not_leₓ, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, not_not]

theorem power_le_max_power_one {a b c : Cardinal} (h : b ≤ c) : (a^b) ≤ max (a^c) 1 := by
  by_cases' ha : a = 0
  simp [← ha, ← zero_power_le]
  exact (power_le_power_left ha h).trans (le_max_leftₓ _ _)

theorem power_le_power_right {a b c : Cardinal} : a ≤ b → (a^c) ≤ (b^c) :=
  (induction_on₃ a b c) fun α β γ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩

end OrderProperties

protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    Classical.by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι → Cardinal := Subtype.val
      have hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : ∀ j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        embedding.min_injective fun i => (f i).out
      apply hc (Acc.intro _ fun j h' => Classical.by_contradiction fun hj => h'.2 _)
      have : # _ ≤ # _ := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [← f, ← mk_out] using this⟩

instance : HasWellFounded Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩

instance wo : @IsWellOrder Cardinal.{u} (· < ·) :=
  ⟨Cardinal.lt_wf⟩

instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  IsWellOrder.conditionallyCompleteLinearOrderBot _

@[simp]
theorem Inf_empty : inf (∅ : Set Cardinal.{u}) = 0 :=
  dif_neg not_nonempty_empty

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
instance : SuccOrder Cardinal :=
  SuccOrder.ofSuccLeIff (fun c => inf { c' | c < c' }) fun a b => ⟨lt_of_lt_of_leₓ <| Inf_mem <| exists_gt a, cInf_le'⟩

theorem succ_def (c : Cardinal) : succ c = inf { c' | c < c' } :=
  rfl

theorem add_one_le_succ (c : Cardinal.{u}) : c + 1 ≤ succ c := by
  refine' (le_cInf_iff'' (exists_gt c)).2 fun b hlt => _
  rcases b, c with ⟨⟨β⟩, ⟨γ⟩⟩
  cases' le_of_ltₓ hlt with f
  have : ¬surjective f := fun hn => (not_le_of_lt hlt) (mk_le_of_surjective hn)
  simp only [← surjective, ← not_forall] at this
  rcases this with ⟨b, hb⟩
  calc # γ + 1 = # (Option γ) := mk_option.symm _ ≤ # β := (f.option_elim b hb).cardinal_le

theorem succ_pos : ∀ c : Cardinal, 0 < succ c :=
  bot_lt_succ

theorem succ_ne_zero (c : Cardinal) : succ c ≠ 0 :=
  (succ_pos _).ne'

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σi, (f i).out)

theorem le_sum {ι} (f : ι → Cardinal) (i) : f i ≤ sum f := by
  rw [← Quotientₓ.out_eq (f i)] <;>
    exact
      ⟨⟨fun a => ⟨i, a⟩, fun a b h =>
          eq_of_heq <| by
            injection h⟩⟩

@[simp]
theorem mk_sigma {ι} (f : ι → Type _) : # (Σi, f i) = sum fun i => # (f i) :=
  mk_congr <| Equivₓ.sigmaCongrRight fun i => outMkEquiv.symm

@[simp]
theorem sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun i : ι => a) = lift.{v} (# ι) * lift.{u} a :=
  (induction_on a) fun α =>
    mk_congr <|
      calc
        (Σi : ι, Quotientₓ.out (# α)) ≃ ι × Quotientₓ.out (# α) := Equivₓ.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equivₓ.ulift.symm.prodCongr (outMkEquiv.trans Equivₓ.ulift.symm)
        

theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = # ι * a := by
  simp

@[simp]
theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
  simpa only [← mk_sigma, ← mk_sum, ← mk_out, ← lift_id] using
    mk_congr (Equivₓ.sigmaSumDistrib (Quotientₓ.out ∘ f) (Quotientₓ.out ∘ g))

@[simp]
theorem sum_add_distrib' {ι} (f g : ι → Cardinal) : (Cardinal.sum fun i => f i + g i) = sum f + sum g :=
  sum_add_distrib f g

@[simp]
theorem lift_sum {ι : Type u} (f : ι → Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) :=
  Equivₓ.cardinal_eq <|
    Equivₓ.ulift.trans <|
      Equivₓ.sigmaCongrRight fun a =>
        Nonempty.some <| by
          rw [← lift_mk_eq, mk_out, mk_out, lift_lift]

theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
  ⟨(Embedding.refl _).sigma_map fun i =>
      Classical.choice <| by
        have := H i <;> rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩

theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α → β) (hf : ∀ b : β, # (f ⁻¹' {b}) ≤ c) : # α ≤ # β * c :=
  by
  simpa only [mk_congr (@Equivₓ.sigmaFiberEquiv α β f), ← mk_sigma, sum_const'] using sum_le_sum _ _ hf

/-- The range of an indexed cardinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. -/
theorem bdd_above_range {ι : Type u} (f : ι → Cardinal.{max u v}) : BddAbove (Set.Range f) :=
  ⟨_, by
    rintro a ⟨i, rfl⟩
    exact le_sum f i⟩

instance (a : Cardinal.{u}) : Small.{u} (Set.Iic a) := by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic (# a.out)) _ fun x => ⟨# x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to an usual ZFC set. -/
theorem bdd_above_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun x h => ha h) _, by
    rintro ⟨ι, ⟨e⟩⟩
    suffices (range fun x : ι => (e.symm x).1) = s by
      rw [← this]
      apply bdd_above_range.{u, u}
    ext x
    refine' ⟨_, fun hx => ⟨e ⟨x, hx⟩, _⟩⟩
    · rintro ⟨a, rfl⟩
      exact (e.symm a).Prop
      
    · simp_rw [Subtype.val_eq_coe, Equivₓ.symm_apply_apply]
      rfl
      ⟩

theorem bdd_above_image (f : Cardinal.{u} → Cardinal.{max u v}) {s : Set Cardinal.{u}} (hs : BddAbove s) :
    BddAbove (f '' s) := by
  rw [bdd_above_iff_small] at hs⊢
  exact small_lift _

theorem bdd_above_range_comp {ι : Type u} {f : ι → Cardinal.{v}} (hf : BddAbove (Range f))
    (g : Cardinal.{v} → Cardinal.{max v w}) : BddAbove (Range (g ∘ f)) := by
  rw [range_comp]
  exact bdd_above_image g hf

theorem supr_le_sum {ι} (f : ι → Cardinal) : supr f ≤ sum f :=
  csupr_le' <| le_sum _

theorem sum_le_supr_lift {ι : Type u} (f : ι → Cardinal.{max u v}) : sum f ≤ (# ι).lift * supr f := by
  rw [← (supr f).lift_id, ← lift_umax, lift_umax.{max u v, u}, ← sum_const]
  exact sum_le_sum _ _ (le_csupr <| bdd_above_range.{u, v} f)

theorem sum_le_supr {ι : Type u} (f : ι → Cardinal.{u}) : sum f ≤ # ι * supr f := by
  rw [← lift_id (# ι)]
  exact sum_le_supr_lift f

theorem sum_nat_eq_add_sum_succ (f : ℕ → Cardinal.{u}) : Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) := by
  refine' (Equivₓ.sigmaNatSucc fun i => Quotientₓ.out (f i)).cardinal_eq.trans _
  simp only [← mk_sum, ← mk_out, ← lift_id, ← mk_sigma]

/-- A variant of `csupr_of_empty` but with `0` on the RHS for convenience -/
@[simp]
protected theorem supr_of_empty {ι} (f : ι → Cardinal) [IsEmpty ι] : supr f = 0 :=
  csupr_of_empty f

@[simp]
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} (# (Shrink.{v} α)) = Cardinal.lift.{max v w} (# α) :=
  lift_mk_eq.2 ⟨(equivShrink α).symm⟩

@[simp]
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] : Cardinal.lift.{u} (# (Shrink.{v} α)) = Cardinal.lift.{v} (# α) :=
  lift_mk_shrink.{u, v, 0} α

@[simp]
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] : Cardinal.lift.{u} (# (Shrink.{v} α)) = # α := by
  rw [← lift_umax', lift_mk_shrink.{max u v, v, 0} α, ← lift_umax, lift_id]

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  # (∀ i, (f i).out)

@[simp]
theorem mk_pi {ι : Type u} (α : ι → Type v) : # (∀ i, α i) = prod fun i => # (α i) :=
  mk_congr <| Equivₓ.piCongrRight fun i => outMkEquiv.symm

@[simp]
theorem prod_const (ι : Type u) (a : Cardinal.{v}) : (prod fun i : ι => a) = (lift.{u} a^lift.{v} (# ι)) :=
  (induction_on a) fun α => mk_congr <| (Equivₓ.piCongr Equivₓ.ulift.symm) fun i => outMkEquiv.trans Equivₓ.ulift.symm

theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = (a^# ι) :=
  (induction_on a) fun α => (mk_pi _).symm

theorem prod_le_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
  ⟨embedding.Pi_congr_right fun i =>
      Classical.choice <| by
        have := H i <;> rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

@[simp]
theorem prod_eq_zero {ι} (f : ι → Cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 := by
  lift f to ι → Type u using fun _ => trivialₓ
  simp only [← mk_eq_zero_iff, mk_pi, ← is_empty_pi]

theorem prod_ne_zero {ι} (f : ι → Cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 := by
  simp [← prod_eq_zero]

@[simp]
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) : lift.{w} (prod c) = prod fun i => lift.{w} (c i) := by
  lift c to ι → Type v using fun _ => trivialₓ
  simp only [mk_pi, mk_ulift]
  exact mk_congr (equiv.ulift.trans <| Equivₓ.piCongrRight fun i => equiv.ulift.symm)

@[simp]
theorem lift_Inf (s : Set Cardinal) : lift (inf s) = inf (lift '' s) := by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
    
  · exact lift_monotone.map_Inf hs
    

@[simp]
theorem lift_infi {ι} (f : ι → Cardinal) : lift (infi f) = ⨅ i, lift (f i) := by
  unfold infi
  convert lift_Inf (range f)
  rw [range_comp]

theorem lift_down {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b ≤ lift a → ∃ a', lift a' = b :=
  (induction_on₂ a b) fun α β => by
    rw [← lift_id (# β), ← lift_umax, ← lift_umax.{u, v}, lift_mk_le] <;>
      exact fun ⟨f⟩ =>
        ⟨# (Set.Range f),
          Eq.symm <|
            lift_mk_eq.2
              ⟨(embedding.equiv_of_surjective (embedding.cod_restrict _ f Set.mem_range_self)) fun ⟨a, ⟨b, e⟩⟩ =>
                  ⟨b, Subtype.eq e⟩⟩⟩

theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h.le
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_lt.2 h⟩

@[simp]
theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
  le_antisymmₓ
    (le_of_not_gtₓ fun h => by
      rcases lt_lift_iff.1 h with ⟨b, e, h⟩
      rw [lt_succ_iff, ← lift_le, e] at h
      exact h.not_lt (lt_succ _))
    (succ_le_of_lt <| lift_lt.2 <| lt_succ a)

@[simp]
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by
  rw [← lift_lift, ← lift_lift, lift_inj]

@[simp]
theorem lift_min {a b : Cardinal} : lift (min a b) = min (lift a) (lift b) :=
  lift_monotone.map_min

@[simp]
theorem lift_max {a b : Cardinal} : lift (max a b) = max (lift a) (lift b) :=
  lift_monotone.map_max

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_Sup {s : Set Cardinal} (hs : BddAbove s) : lift.{u} (sup s) = sup (lift.{u} '' s) := by
  apply ((le_cSup_iff' (bdd_above_image _ hs)).2 fun c hc => _).antisymm (cSup_le' _)
  · by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.lift_down (not_leₓ.1 h).le
    simp_rw [lift_le] at h hc
    rw [cSup_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
    
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_cSup hs hj)
    

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_supr {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (Range f)) :
    lift.{u} (supr f) = ⨆ i, lift.{u} (f i) := by
  rw [supr, supr, lift_Sup hf, ← range_comp]

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
theorem lift_supr_le {ι : Type v} {f : ι → Cardinal.{w}} {t : Cardinal} (hf : BddAbove (Range f))
    (w : ∀ i, lift.{u} (f i) ≤ t) : lift.{u} (supr f) ≤ t := by
  rw [lift_supr hf]
  exact csupr_le' w

@[simp]
theorem lift_supr_le_iff {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (Range f)) {t : Cardinal} :
    lift.{u} (supr f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t := by
  rw [lift_supr hf]
  exact csupr_le_iff' (bdd_above_range_comp hf _)

universe v' w'

/-- To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
theorem lift_supr_le_lift_supr {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{w}} {f' : ι' → Cardinal.{w'}}
    (hf : BddAbove (Range f)) (hf' : BddAbove (Range f')) {g : ι → ι'}
    (h : ∀ i, lift.{w'} (f i) ≤ lift.{w} (f' (g i))) : lift.{w'} (supr f) ≤ lift.{w} (supr f') := by
  rw [lift_supr hf, lift_supr hf']
  exact csupr_mono' (bdd_above_range_comp hf' _) fun i => ⟨_, h i⟩

/-- A variant of `lift_supr_le_lift_supr` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
theorem lift_supr_le_lift_supr' {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{v}} {f' : ι' → Cardinal.{v'}}
    (hf : BddAbove (Range f)) (hf' : BddAbove (Range f')) (g : ι → ι')
    (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) : lift.{v'} (supr f) ≤ lift.{v} (supr f') :=
  lift_supr_le_lift_supr hf hf' h

/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph0 : Cardinal.{u} :=
  lift (# ℕ)

-- mathport name: «exprℵ₀»
localized [Cardinal] notation "ℵ₀" => Cardinal.aleph0

theorem mk_nat : # ℕ = ℵ₀ :=
  (lift_id _).symm

theorem aleph_0_ne_zero : ℵ₀ ≠ 0 :=
  mk_ne_zero _

theorem aleph_0_pos : 0 < ℵ₀ :=
  pos_iff_ne_zero.2 aleph_0_ne_zero

@[simp]
theorem lift_aleph_0 : lift ℵ₀ = ℵ₀ :=
  lift_lift _

@[simp]
theorem aleph_0_le_lift {c : Cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c := by
  rw [← lift_aleph_0, lift_le]

@[simp]
theorem lift_le_aleph_0 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ := by
  rw [← lift_aleph_0, lift_le]

/-! ### Properties about the cast from `ℕ` -/


@[simp]
theorem mk_fin (n : ℕ) : # (Finₓ n) = n := by
  simp

@[simp]
theorem lift_nat_cast (n : ℕ) : lift.{u} (n : Cardinal.{v}) = n := by
  induction n <;> simp [*]

@[simp]
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_nat_cast n)

@[simp]
theorem nat_eq_lift_iff {n : ℕ} {a : Cardinal.{u}} : (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by
  rw [← lift_nat_cast.{v} n, lift_inj]

theorem lift_mk_fin (n : ℕ) : lift (# (Finₓ n)) = n := by
  simp

theorem mk_coe_finset {α : Type u} {s : Finset α} : # s = ↑(Finset.card s) := by
  simp

theorem mk_finset_of_fintype [Fintype α] : # (Finset α) = 2 ^ℕ Fintype.card α := by
  simp

theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) ≤ # α := by
  rw [(_ : (s.card : Cardinal) = # s)]
  · exact ⟨Function.Embedding.subtype _⟩
    
  rw [Cardinal.mk_fintype, Fintype.card_coe]

@[simp, norm_cast]
theorem nat_cast_pow {m n : ℕ} : (↑(pow m n) : Cardinal) = (m^n) := by
  induction n <;> simp [← pow_succ'ₓ, ← power_add, *]

@[simp, norm_cast]
theorem nat_cast_le {m n : ℕ} : (m : Cardinal) ≤ n ↔ m ≤ n := by
  rw [← lift_mk_fin, ← lift_mk_fin, lift_le]
  exact
    ⟨fun ⟨⟨f, hf⟩⟩ => by
      simpa only [← Fintype.card_fin] using Fintype.card_le_of_injective f hf, fun h => ⟨(Finₓ.castLe h).toEmbedding⟩⟩

@[simp, norm_cast]
theorem nat_cast_lt {m n : ℕ} : (m : Cardinal) < n ↔ m < n := by
  simp [← lt_iff_le_not_leₓ, not_leₓ]

instance : CharZero Cardinal :=
  ⟨StrictMono.injective fun m n => nat_cast_lt.2⟩

theorem nat_cast_inj {m n : ℕ} : (m : Cardinal) = n ↔ m = n :=
  Nat.cast_inj

theorem nat_cast_injective : Injective (coe : ℕ → Cardinal) :=
  Nat.cast_injective

@[simp, norm_cast]
theorem nat_succ (n : ℕ) : (n.succ : Cardinal) = succ n :=
  (add_one_le_succ _).antisymm (succ_le_of_lt <| nat_cast_lt.2 <| Nat.lt_succ_selfₓ _)

@[simp]
theorem succ_zero : succ (0 : Cardinal) = 1 := by
  norm_cast

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : Finset α, s.card ≤ n) : # α ≤ n := by
  refine' le_of_lt_succ (lt_of_not_geₓ fun hn => _)
  rw [← Cardinal.nat_succ, ← lift_mk_fin n.succ] at hn
  cases' hn with f
  refine' (H <| finset.univ.map f).not_lt _
  rw [Finset.card_map, ← Fintype.card, Fintype.card_ulift, Fintype.card_fin]
  exact n.lt_succ_self

theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < (b^a) := by
  rw [← succ_le_iff,
    (by
      norm_cast : succ (1 : Cardinal) = 2)] at
    hb
  exact (cantor a).trans_le (power_le_power_right hb)

theorem one_le_iff_pos {c : Cardinal} : 1 ≤ c ↔ 0 < c := by
  rw [← succ_zero, succ_le_iff]

theorem one_le_iff_ne_zero {c : Cardinal} : 1 ≤ c ↔ c ≠ 0 := by
  rw [one_le_iff_pos, pos_iff_ne_zero]

theorem nat_lt_aleph_0 (n : ℕ) : (n : Cardinal.{u}) < ℵ₀ :=
  succ_le_iff.1
    (by
      rw [← nat_succ, ← lift_mk_fin, aleph_0, lift_mk_le.{0, 0, u}]
      exact ⟨⟨coe, fun a b => Finₓ.ext⟩⟩)

@[simp]
theorem one_lt_aleph_0 : 1 < ℵ₀ := by
  simpa using nat_lt_aleph_0 1

theorem one_le_aleph_0 : 1 ≤ ℵ₀ :=
  one_lt_aleph_0.le

theorem lt_aleph_0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
  ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.finite by
      lift S to Finset ℕ using this
      simp
    contrapose! h'
    have := infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨n, e⟩ => e.symm ▸ nat_lt_aleph_0 _⟩

theorem aleph_0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c :=
  ⟨fun h n => (nat_lt_aleph_0 _).le.trans h, fun h =>
    le_of_not_ltₓ fun hn => by
      rcases lt_aleph_0.1 hn with ⟨n, rfl⟩
      exact (Nat.lt_succ_selfₓ _).not_le (nat_cast_le.1 (h (n + 1)))⟩

theorem mk_eq_nat_iff {α : Type u} {n : ℕ} : # α = n ↔ Nonempty (α ≃ Finₓ n) := by
  rw [← lift_mk_fin, ← lift_uzero (# α), lift_mk_eq']

theorem lt_aleph_0_iff_finite {α : Type u} : # α < ℵ₀ ↔ Finite α := by
  simp only [← lt_aleph_0, ← mk_eq_nat_iff, ← finite_iff_exists_equiv_fin]

theorem lt_aleph_0_iff_fintype {α : Type u} : # α < ℵ₀ ↔ Nonempty (Fintype α) :=
  lt_aleph_0_iff_finite.trans (finite_iff_nonempty_fintype _)

theorem lt_aleph_0_of_finite (α : Type u) [Finite α] : # α < ℵ₀ :=
  lt_aleph_0_iff_finite.2 ‹_›

theorem lt_aleph_0_iff_set_finite {α} {S : Set α} : # S < ℵ₀ ↔ S.Finite :=
  lt_aleph_0_iff_finite.trans finite_coe_iff

alias lt_aleph_0_iff_set_finite ↔ _ _root_.set.finite.lt_aleph_0

instance canLiftCardinalNat : CanLift Cardinal ℕ :=
  ⟨coe, fun x => x < ℵ₀, fun x hx =>
    let ⟨n, hn⟩ := lt_aleph_0.mp hx
    ⟨n, hn.symm⟩⟩

theorem add_lt_aleph_0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
  match a, b, lt_aleph_0.1 ha, lt_aleph_0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← Nat.cast_addₓ] <;> apply nat_lt_aleph_0

theorem add_lt_aleph_0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
  ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩, fun ⟨h1, h2⟩ =>
    add_lt_aleph_0 h1 h2⟩

theorem aleph_0_le_add_iff {a b : Cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b := by
  simp only [not_ltₓ, ← add_lt_aleph_0_iff, ← not_and_distrib]

/-- See also `cardinal.nsmul_lt_aleph_0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
theorem nsmul_lt_aleph_0_iff {n : ℕ} {a : Cardinal} : n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀ := by
  cases n
  · simpa using nat_lt_aleph_0 0
    
  simp only [← Nat.succ_ne_zero, ← false_orₓ]
  induction' n with n ih
  · simp
    
  rw [succ_nsmul, add_lt_aleph_0_iff, ih, and_selfₓ]

/-- See also `cardinal.nsmul_lt_aleph_0_iff` for a hypothesis-free version. -/
theorem nsmul_lt_aleph_0_iff_of_ne_zero {n : ℕ} {a : Cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
  nsmul_lt_aleph_0_iff.trans <| or_iff_right h

theorem mul_lt_aleph_0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
  match a, b, lt_aleph_0.1 ha, lt_aleph_0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← Nat.cast_mulₓ] <;> apply nat_lt_aleph_0

theorem mul_lt_aleph_0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ := by
  refine' ⟨fun h => _, _⟩
  · by_cases' ha : a = 0
    · exact Or.inl ha
      
    right
    by_cases' hb : b = 0
    · exact Or.inl hb
      
    right
    rw [← Ne, ← one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_oneₓ a]
      refine' (mul_le_mul' le_rfl hb).trans_lt h
      
    · rw [← one_mulₓ b]
      refine' (mul_le_mul' ha le_rfl).trans_lt h
      
    
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, ← mul_lt_aleph_0, ← aleph_0_pos, ← zero_mul, ← mul_zero]

/-- See also `cardinal.aleph_0_le_mul_iff`. -/
theorem aleph_0_le_mul_iff {a b : Cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) := by
  let h := (@mul_lt_aleph_0_iff a b).Not
  rwa [not_ltₓ, not_or_distrib, not_or_distrib, not_and_distrib, not_ltₓ, not_ltₓ] at h

/-- See also `cardinal.aleph_0_le_mul_iff'`. -/
theorem aleph_0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 := by
  have : ∀ {a : Cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0 := fun a => ne_bot_of_le_ne_bot aleph_0_ne_zero
  simp only [← aleph_0_le_mul_iff, ← and_or_distrib_left, ← and_iff_right_of_imp this, ← @And.left_comm (a ≠ 0)]
  simp only [← And.comm, ← Or.comm]

theorem mul_lt_aleph_0_iff_of_ne_zero {a b : Cardinal} (ha : a ≠ 0) (hb : b ≠ 0) : a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by
  simp [← mul_lt_aleph_0_iff, ← ha, ← hb]

theorem power_lt_aleph_0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : (a^b) < ℵ₀ :=
  match a, b, lt_aleph_0.1 ha, lt_aleph_0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← nat_cast_pow] <;> apply nat_lt_aleph_0

theorem eq_one_iff_unique {α : Type _} : # α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    # α = 1 ↔ # α ≤ 1 ∧ 1 ≤ # α := le_antisymm_iffₓ
    _ ↔ Subsingleton α ∧ Nonempty α := le_one_iff_subsingleton.And (one_le_iff_ne_zero.trans mk_ne_zero_iff)
    

theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ ≤ # α := by
  rw [← not_ltₓ, lt_aleph_0_iff_finite, not_finite_iff_infinite]

@[simp]
theorem aleph_0_le_mk (α : Type u) [Infinite α] : ℵ₀ ≤ # α :=
  infinite_iff.1 ‹_›

theorem encodable_iff {α : Type u} : Nonempty (Encodable α) ↔ # α ≤ ℵ₀ :=
  ⟨fun ⟨h⟩ => ⟨(@Encodable.encode' α h).trans Equivₓ.ulift.symm.toEmbedding⟩, fun ⟨h⟩ =>
    ⟨Encodable.ofInj _ (h.trans Equivₓ.ulift.toEmbedding).Injective⟩⟩

@[simp]
theorem mk_le_aleph_0 [Encodable α] : # α ≤ ℵ₀ :=
  encodable_iff.1 ⟨‹_›⟩

theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ # α = ℵ₀ :=
  ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equivₓ.ulift.symm), fun h => by
    cases' Quotientₓ.exact h with f
    exact ⟨Denumerable.mk' <| f.trans Equivₓ.ulift⟩⟩

@[simp]
theorem mk_denumerable (α : Type u) [Denumerable α] : # α = ℵ₀ :=
  denumerable_iff.1 ⟨‹_›⟩

@[simp]
theorem mk_set_le_aleph_0 (s : Set α) : # s ≤ ℵ₀ ↔ s.Countable := by
  rw [Set.countable_iff_exists_injective]
  constructor
  · rintro ⟨f'⟩
    cases' embedding.trans f' equiv.ulift.to_embedding with f hf
    exact ⟨f, hf⟩
    
  · rintro ⟨f, hf⟩
    exact ⟨embedding.trans ⟨f, hf⟩ equiv.ulift.symm.to_embedding⟩
    

@[simp]
theorem mk_subtype_le_aleph_0 (p : α → Prop) : # { x // p x } ≤ ℵ₀ ↔ { x | p x }.Countable :=
  mk_set_le_aleph_0 _

@[simp]
theorem aleph_0_add_aleph_0 : ℵ₀ + ℵ₀ = ℵ₀ :=
  mk_denumerable _

theorem aleph_0_mul_aleph_0 : ℵ₀ * ℵ₀ = ℵ₀ :=
  mk_denumerable _

@[simp]
theorem add_le_aleph_0 {c₁ c₂ : Cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
  ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h => aleph_0_add_aleph_0 ▸ add_le_add h.1 h.2⟩

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
def toNat : ZeroHom Cardinal ℕ :=
  ⟨fun c => if h : c < aleph_0.{v} then Classical.some (lt_aleph_0.1 h) else 0, by
    have h : 0 < ℵ₀ := nat_lt_aleph_0 0
    rw [dif_pos h, ← Cardinal.nat_cast_inj, ← Classical.some_spec (lt_aleph_0.1 h), Nat.cast_zeroₓ]⟩

theorem to_nat_apply_of_lt_aleph_0 {c : Cardinal} (h : c < ℵ₀) : c.toNat = Classical.some (lt_aleph_0.1 h) :=
  dif_pos h

theorem to_nat_apply_of_aleph_0_le {c : Cardinal} (h : ℵ₀ ≤ c) : c.toNat = 0 :=
  dif_neg h.not_lt

theorem cast_to_nat_of_lt_aleph_0 {c : Cardinal} (h : c < ℵ₀) : ↑c.toNat = c := by
  rw [to_nat_apply_of_lt_aleph_0 h, ← Classical.some_spec (lt_aleph_0.1 h)]

theorem cast_to_nat_of_aleph_0_le {c : Cardinal} (h : ℵ₀ ≤ c) : ↑c.toNat = (0 : Cardinal) := by
  rw [to_nat_apply_of_aleph_0_le h, Nat.cast_zeroₓ]

theorem to_nat_le_iff_le_of_lt_aleph_0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) : c.toNat ≤ d.toNat ↔ c ≤ d := by
  rw [← nat_cast_le, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]

theorem to_nat_lt_iff_lt_of_lt_aleph_0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) : c.toNat < d.toNat ↔ c < d := by
  rw [← nat_cast_lt, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]

theorem to_nat_le_of_le_of_lt_aleph_0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c ≤ d) : c.toNat ≤ d.toNat :=
  (to_nat_le_iff_le_of_lt_aleph_0 (hcd.trans_lt hd) hd).mpr hcd

theorem to_nat_lt_of_lt_of_lt_aleph_0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c < d) : c.toNat < d.toNat :=
  (to_nat_lt_iff_lt_of_lt_aleph_0 (hcd.trans hd) hd).mpr hcd

@[simp]
theorem to_nat_cast (n : ℕ) : Cardinal.toNat n = n := by
  rw [to_nat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), ← nat_cast_inj]
  exact (Classical.some_spec (lt_aleph_0.1 (nat_lt_aleph_0 n))).symm

/-- `to_nat` has a right-inverse: coercion. -/
theorem to_nat_right_inverse : Function.RightInverse (coe : ℕ → Cardinal) toNat :=
  to_nat_cast

theorem to_nat_surjective : Surjective toNat :=
  to_nat_right_inverse.Surjective

@[simp]
theorem mk_to_nat_of_infinite [h : Infinite α] : (# α).toNat = 0 :=
  dif_neg (infinite_iff.1 h).not_lt

@[simp]
theorem aleph_0_to_nat : toNat ℵ₀ = 0 :=
  to_nat_apply_of_aleph_0_le le_rfl

theorem mk_to_nat_eq_card [Fintype α] : (# α).toNat = Fintype.card α := by
  simp

@[simp]
theorem zero_to_nat : toNat 0 = 0 := by
  rw [← to_nat_cast 0, Nat.cast_zeroₓ]

@[simp]
theorem one_to_nat : toNat 1 = 1 := by
  rw [← to_nat_cast 1, Nat.cast_oneₓ]

@[simp]
theorem to_nat_eq_one {c : Cardinal} : toNat c = 1 ↔ c = 1 :=
  ⟨fun h =>
    (cast_to_nat_of_lt_aleph_0 (lt_of_not_geₓ (one_ne_zero ∘ h.symm.trans ∘ to_nat_apply_of_aleph_0_le))).symm.trans
      ((congr_arg coe h).trans Nat.cast_oneₓ),
    fun h => (congr_arg toNat h).trans one_to_nat⟩

theorem to_nat_eq_one_iff_unique {α : Type _} : (# α).toNat = 1 ↔ Subsingleton α ∧ Nonempty α :=
  to_nat_eq_one.trans eq_one_iff_unique

@[simp]
theorem to_nat_lift (c : Cardinal.{v}) : (lift.{u, v} c).toNat = c.toNat := by
  apply nat_cast_injective
  cases' lt_or_geₓ c ℵ₀ with hc hc
  · rw [cast_to_nat_of_lt_aleph_0, ← lift_nat_cast, cast_to_nat_of_lt_aleph_0 hc]
    rwa [← lift_aleph_0, lift_lt]
    
  · rw [cast_to_nat_of_aleph_0_le, ← lift_nat_cast, cast_to_nat_of_aleph_0_le hc, lift_zero]
    rwa [← lift_aleph_0, lift_le]
    

theorem to_nat_congr {β : Type v} (e : α ≃ β) : (# α).toNat = (# β).toNat := by
  rw [← to_nat_lift, lift_mk_eq.mpr ⟨e⟩, to_nat_lift]

@[simp]
theorem to_nat_mul (x y : Cardinal) : (x * y).toNat = x.toNat * y.toNat := by
  rcases eq_or_ne x 0 with (rfl | hx1)
  · rw [zero_mul, zero_to_nat, zero_mul]
    
  rcases eq_or_ne y 0 with (rfl | hy1)
  · rw [mul_zero, zero_to_nat, mul_zero]
    
  cases' lt_or_leₓ x ℵ₀ with hx2 hx2
  · cases' lt_or_leₓ y ℵ₀ with hy2 hy2
    · lift x to ℕ using hx2
      lift y to ℕ using hy2
      rw [← Nat.cast_mulₓ, to_nat_cast, to_nat_cast, to_nat_cast]
      
    · rw [to_nat_apply_of_aleph_0_le hy2, mul_zero, to_nat_apply_of_aleph_0_le]
      exact aleph_0_le_mul_iff'.2 (Or.inl ⟨hx1, hy2⟩)
      
    
  · rw [to_nat_apply_of_aleph_0_le hx2, zero_mul, to_nat_apply_of_aleph_0_le]
    exact aleph_0_le_mul_iff'.2 (Or.inr ⟨hx2, hy1⟩)
    

@[simp]
theorem to_nat_add_of_lt_aleph_0 {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀) :
    (lift.{v, u} a + lift.{u, v} b).toNat = a.toNat + b.toNat := by
  apply Cardinal.nat_cast_injective
  replace ha : lift.{v, u} a < ℵ₀ := by
    rw [← lift_aleph_0]
    exact lift_lt.2 ha
  replace hb : lift.{u, v} b < ℵ₀ := by
    rw [← lift_aleph_0]
    exact lift_lt.2 hb
  rw [Nat.cast_addₓ, ← to_nat_lift.{v, u} a, ← to_nat_lift.{u, v} b, cast_to_nat_of_lt_aleph_0 ha,
    cast_to_nat_of_lt_aleph_0 hb, cast_to_nat_of_lt_aleph_0 (add_lt_aleph_0 ha hb)]

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to `⊤`. -/
def toPartEnat : Cardinal →+ PartEnat where
  toFun := fun c => if c < ℵ₀ then c.toNat else ⊤
  map_zero' := by
    simp [← if_pos (zero_lt_one.trans one_lt_aleph_0)]
  map_add' := fun x y => by
    by_cases' hx : x < ℵ₀
    · obtain ⟨x0, rfl⟩ := lt_aleph_0.1 hx
      by_cases' hy : y < ℵ₀
      · obtain ⟨y0, rfl⟩ := lt_aleph_0.1 hy
        simp only [← add_lt_aleph_0 hx hy, ← hx, ← hy, ← to_nat_cast, ← if_true]
        rw [← Nat.cast_addₓ, to_nat_cast, Nat.cast_addₓ]
        
      · rw [if_neg hy, if_neg, PartEnat.add_top]
        contrapose! hy
        apply le_add_self.trans_lt hy
        
      
    · rw [if_neg hx, if_neg, PartEnat.top_add]
      contrapose! hx
      apply le_self_add.trans_lt hx
      

theorem to_part_enat_apply_of_lt_aleph_0 {c : Cardinal} (h : c < ℵ₀) : c.toPartEnat = c.toNat :=
  if_pos h

theorem to_part_enat_apply_of_aleph_0_le {c : Cardinal} (h : ℵ₀ ≤ c) : c.toPartEnat = ⊤ :=
  if_neg h.not_lt

@[simp]
theorem to_part_enat_cast (n : ℕ) : Cardinal.toPartEnat n = n := by
  rw [to_part_enat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), to_nat_cast]

@[simp]
theorem mk_to_part_enat_of_infinite [h : Infinite α] : (# α).toPartEnat = ⊤ :=
  to_part_enat_apply_of_aleph_0_le (infinite_iff.1 h)

@[simp]
theorem aleph_0_to_part_enat : toPartEnat ℵ₀ = ⊤ :=
  to_part_enat_apply_of_aleph_0_le le_rfl

theorem to_part_enat_surjective : Surjective toPartEnat := fun x =>
  (PartEnat.cases_on x ⟨ℵ₀, to_part_enat_apply_of_aleph_0_le le_rfl⟩) fun n => ⟨n, to_part_enat_cast n⟩

theorem mk_to_part_enat_eq_coe_card [Fintype α] : (# α).toPartEnat = Fintype.card α := by
  simp

theorem mk_int : # ℤ = ℵ₀ :=
  mk_denumerable ℤ

theorem mk_pnat : # ℕ+ = ℵ₀ :=
  mk_denumerable ℕ+

/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
  lt_of_not_geₓ fun ⟨F⟩ => by
    have : Inhabited (∀ i : ι, (g i).out) := by
      refine' ⟨fun i => Classical.choice <| mk_ne_zero_iff.1 _⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := inv_fun F
    have sG : surjective G := inv_fun_surjective F.2
    choose C hc using
      show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b by
        intro i
        simp only [-not_exists, ← not_exists.symm, ← not_forall.symm]
        refine' fun h => (H i).not_le _
        rw [← mk_out (f i), ← mk_out (g i)]
        exact ⟨embedding.of_surjective _ h⟩
    exact
      let ⟨⟨i, a⟩, h⟩ := sG C
      hc i a (congr_fun h _)

@[simp]
theorem mk_empty : # Empty = 0 :=
  mk_eq_zero _

@[simp]
theorem mk_pempty : # Pempty = 0 :=
  mk_eq_zero _

@[simp]
theorem mk_punit : # PUnit = 1 :=
  mk_eq_one PUnit

theorem mk_unit : # Unit = 1 :=
  mk_punit

@[simp]
theorem mk_singleton {α : Type u} (x : α) : # ({x} : Set α) = 1 :=
  mk_eq_one _

@[simp]
theorem mk_plift_true : # (Plift True) = 1 :=
  mk_eq_one _

@[simp]
theorem mk_plift_false : # (Plift False) = 0 :=
  mk_eq_zero _

@[simp]
theorem mk_vector (α : Type u) (n : ℕ) : # (Vector α n) = # α ^ℕ n :=
  (mk_congr (Equivₓ.vectorEquivFin α n)).trans <| by
    simp

theorem mk_list_eq_sum_pow (α : Type u) : # (List α) = sum fun n : ℕ => # α ^ℕ n :=
  calc
    # (List α) = # (Σn, Vector α n) := mk_congr (Equivₓ.sigmaFiberEquiv List.length).symm
    _ = sum fun n : ℕ => # α ^ℕ n := by
      simp
    

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : # (Quot r) ≤ # α :=
  mk_le_of_surjective Quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : Setoidₓ α} : # (Quotientₓ s) ≤ # α :=
  mk_quot_le

theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) : # (Subtype p) ≤ # (Subtype q) :=
  ⟨Embedding.subtypeMap (Embedding.refl α) h⟩

@[simp]
theorem mk_emptyc (α : Type u) : # (∅ : Set α) = 0 :=
  mk_eq_zero _

theorem mk_emptyc_iff {α : Type u} {s : Set α} : # s = 0 ↔ s = ∅ := by
  constructor
  · intro h
    rw [mk_eq_zero_iff] at h
    exact eq_empty_iff_forall_not_mem.2 fun x hx => h.elim' ⟨x, hx⟩
    
  · rintro rfl
    exact mk_emptyc _
    

@[simp]
theorem mk_univ {α : Type u} : # (@Univ α) = # α :=
  mk_congr (Equivₓ.Set.univ α)

theorem mk_image_le {α β : Type u} {f : α → β} {s : Set α} : # (f '' s) ≤ # s :=
  mk_le_of_surjective surjective_onto_image

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : Set α} : lift.{u} (# (f '' s)) ≤ lift.{v} (# s) :=
  lift_mk_le.{v, u, 0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_image⟩

theorem mk_range_le {α β : Type u} {f : α → β} : # (Range f) ≤ # α :=
  mk_le_of_surjective surjective_onto_range

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} : lift.{u} (# (Range f)) ≤ lift.{v} (# α) :=
  lift_mk_le.{v, u, 0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_range⟩

theorem mk_range_eq (f : α → β) (h : Injective f) : # (Range f) = # α :=
  mk_congr (Equivₓ.ofInjective f h).symm

theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{u} (# (Range f)) = lift.{v} (# α) :=
  lift_mk_eq'.mpr ⟨(Equivₓ.ofInjective f hf).symm⟩

theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{max u w} (# (Range f)) = lift.{max v w} (# α) :=
  lift_mk_eq.mpr ⟨(Equivₓ.ofInjective f hf).symm⟩

theorem mk_image_eq {α β : Type u} {f : α → β} {s : Set α} (hf : Injective f) : # (f '' s) = # s :=
  mk_congr (Equivₓ.Set.image f s hf).symm

theorem mk_Union_le_sum_mk {α ι : Type u} {f : ι → Set α} : # (⋃ i, f i) ≤ sum fun i => # (f i) :=
  calc
    # (⋃ i, f i) ≤ # (Σi, f i) := mk_le_of_surjective (Set.sigma_to_Union_surjective f)
    _ = sum fun i => # (f i) := mk_sigma _
    

theorem mk_Union_eq_sum_mk {α ι : Type u} {f : ι → Set α} (h : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    # (⋃ i, f i) = sum fun i => # (f i) :=
  calc
    # (⋃ i, f i) = # (Σi, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => # (f i) := mk_sigma _
    

theorem mk_Union_le {α ι : Type u} (f : ι → Set α) : # (⋃ i, f i) ≤ # ι * ⨆ i, # (f i) :=
  mk_Union_le_sum_mk.trans (sum_le_supr _)

theorem mk_sUnion_le {α : Type u} (A : Set (Set α)) : # (⋃₀A) ≤ # A * ⨆ s : A, # s := by
  rw [sUnion_eq_Union]
  apply mk_Union_le

theorem mk_bUnion_le {ι α : Type u} (A : ι → Set α) (s : Set ι) : # (⋃ x ∈ s, A x) ≤ # s * ⨆ x : s, # (A x.1) := by
  rw [bUnion_eq_Union]
  apply mk_Union_le

theorem finset_card_lt_aleph_0 (s : Finset α) : # (↑s : Set α) < ℵ₀ :=
  lt_aleph_0_of_finite _

theorem mk_eq_nat_iff_finset {α} {s : Set α} {n : ℕ} : # s = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n := by
  constructor
  · intro h
    lift s to Finset α using lt_aleph_0_iff_set_finite.1 (h.symm ▸ nat_lt_aleph_0 n)
    simpa using h
    
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset
    

theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} : # (S ∪ T : Set α) + # (S ∩ T : Set α) = # S + # T :=
  Quot.sound ⟨Equivₓ.Set.unionSumInter S T⟩

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
theorem mk_union_le {α : Type u} (S T : Set α) : # (S ∪ T : Set α) ≤ # S + # T :=
  @mk_union_add_mk_inter α S T ▸ self_le_add_right (# (S ∪ T : Set α)) (# (S ∩ T : Set α))

theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) : # (S ∪ T : Set α) = # S + # T :=
  Quot.sound ⟨Equivₓ.Set.union H⟩

theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) : # (insert a s : Set α) = # s + 1 := by
  rw [← union_singleton, mk_union_of_disjoint, mk_singleton]
  simpa

theorem mk_sum_compl {α} (s : Set α) : # s + # (sᶜ : Set α) = # α :=
  mk_congr (Equivₓ.Set.sumCompl s)

theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s ⊆ t) : # s ≤ # t :=
  ⟨Set.embeddingOfSubset s t h⟩

theorem mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) : # { x // p x } ≤ # { x // q x } :=
  ⟨embeddingOfSubset _ _ h⟩

theorem mk_union_le_aleph_0 {α} {P Q : Set α} : # (P ∪ Q : Set α) ≤ ℵ₀ ↔ # P ≤ ℵ₀ ∧ # Q ≤ ℵ₀ := by
  simp

theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : Injective f) :
    lift.{u} (# (f '' s)) = lift.{v} (# s) :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equivₓ.Set.image f s h).symm⟩

theorem mk_image_eq_of_inj_on_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : InjOn f s) :
    lift.{u} (# (f '' s)) = lift.{v} (# s) :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equivₓ.Set.imageOfInjOn f s h).symm⟩

theorem mk_image_eq_of_inj_on {α β : Type u} (f : α → β) (s : Set α) (h : InjOn f s) : # (f '' s) = # s :=
  mk_congr (Equivₓ.Set.imageOfInjOn f s h).symm

theorem mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) : # { a : α // p (e a) } = # { b : β // p b } :=
  mk_congr (Equivₓ.subtypeEquivOfSubtype e)

theorem mk_sep (s : Set α) (t : α → Prop) : # ({ x ∈ s | t x } : Set α) = # { x : s | t x.1 } :=
  mk_congr (Equivₓ.Set.sep s t)

theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β) (h : Injective f) :
    lift.{v} (# (f ⁻¹' s)) ≤ lift.{u} (# s) := by
  rw [lift_mk_le.{u, v, 0}]
  use Subtype.coind (fun x => f x.1) fun x => x.2
  apply Subtype.coind_injective
  exact h.comp Subtype.val_injective

theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β) (h : s ⊆ Range f) :
    lift.{u} (# s) ≤ lift.{v} (# (f ⁻¹' s)) := by
  rw [lift_mk_le.{v, u, 0}]
  refine' ⟨⟨_, _⟩⟩
  · rintro ⟨y, hy⟩
    rcases Classical.subtypeOfExists (h hy) with ⟨x, rfl⟩
    exact ⟨x, hy⟩
    
  rintro ⟨y, hy⟩ ⟨y', hy'⟩
  dsimp'
  rcases Classical.subtypeOfExists (h hy) with ⟨x, rfl⟩
  rcases Classical.subtypeOfExists (h hy') with ⟨x', rfl⟩
  simp
  intro hxx'
  rw [hxx']

theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : Set β) (h : Injective f)
    (h2 : s ⊆ Range f) : lift.{v} (# (f ⁻¹' s)) = lift.{u} (# s) :=
  le_antisymmₓ (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

theorem mk_preimage_of_injective (f : α → β) (s : Set β) (h : Injective f) : # (f ⁻¹' s) ≤ # s := by
  convert mk_preimage_of_injective_lift.{u, u} f s h using 1 <;> rw [lift_id]

theorem mk_preimage_of_subset_range (f : α → β) (s : Set β) (h : s ⊆ Range f) : # s ≤ # (f ⁻¹' s) := by
  convert mk_preimage_of_subset_range_lift.{u, u} f s h using 1 <;> rw [lift_id]

theorem mk_preimage_of_injective_of_subset_range (f : α → β) (s : Set β) (h : Injective f) (h2 : s ⊆ Range f) :
    # (f ⁻¹' s) = # s := by
  convert mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]

theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : Set α} {t : Set β}
    (h : t ⊆ f '' s) : lift.{u} (# t) ≤ lift.{v} (# ({ x ∈ s | f x ∈ t } : Set α)) := by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl

theorem mk_subset_ge_of_subset_image (f : α → β) {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
    # t ≤ # ({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl

theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} : c ≤ # s ↔ ∃ p : Set α, p ⊆ s ∧ # p = c := by
  rw [le_mk_iff_exists_set, ← Subtype.exists_set_subtype]
  apply exists_congr
  intro t
  rw [mk_image_eq]
  apply Subtype.val_injective

theorem two_le_iff : (2 : Cardinal) ≤ # α ↔ ∃ x y : α, x ≠ y := by
  constructor
  · rintro ⟨f⟩
    refine' ⟨f <| Sum.inl ⟨⟩, f <| Sum.inr ⟨⟩, _⟩
    intro h
    cases f.2 h
    
  · rintro ⟨x, y, h⟩
    by_contra h'
    rw [not_leₓ, ← Nat.cast_two, nat_succ, lt_succ_iff, Nat.cast_oneₓ, le_one_iff_subsingleton] at h'
    apply h
    exact Subsingleton.elimₓ _ _
    

theorem two_le_iff' (x : α) : (2 : Cardinal) ≤ # α ↔ ∃ y : α, x ≠ y := by
  rw [two_le_iff]
  constructor
  · rintro ⟨y, z, h⟩
    refine' Classical.by_cases (fun h' : x = y => _) fun h' => ⟨y, h'⟩
    rw [← h'] at h
    exact ⟨z, h⟩
    
  · rintro ⟨y, h⟩
    exact ⟨x, y, h⟩
    

theorem exists_not_mem_of_length_le {α : Type _} (l : List α) (h : ↑l.length < # α) : ∃ z : α, z ∉ l := by
  contrapose! h
  calc # α = # (Set.Univ : Set α) := mk_univ.symm _ ≤ # l.to_finset :=
      mk_le_mk_of_subset fun x _ => list.mem_to_finset.mpr (h x)_ = l.to_finset.card :=
      Cardinal.mk_coe_finset _ ≤ l.length := cardinal.nat_cast_le.mpr (List.to_finset_card_le l)

theorem three_le {α : Type _} (h : 3 ≤ # α) (x : α) (y : α) : ∃ z : α, z ≠ x ∧ z ≠ y := by
  have : ↑(3 : ℕ) ≤ # α
  simpa using h
  have : ↑(2 : ℕ) < # α
  rwa [← succ_le_iff, ← Cardinal.nat_succ]
  have := exists_not_mem_of_length_le [x, y] this
  simpa [← not_or_distrib] using this

/-- The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`. -/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a^c

-- mathport name: «expr ^< »
infixl:80 " ^< " => powerlt

theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a^c) ≤ a ^< b := by
  apply @le_csupr _ _ _ (fun y : Iio b => a^y) _ ⟨c, h⟩
  rw [← image_eq_range]
  exact bdd_above_image.{u, u} _ bdd_above_Iio

theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b ≤ c ↔ ∀, ∀ x < b, ∀, (a^x) ≤ c := by
  rw [powerlt, csupr_le_iff']
  · simp
    
  · rw [← image_eq_range]
    exact bdd_above_image.{u, u} _ bdd_above_Iio
    

theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
  powerlt_le.2 fun x hx => le_powerlt a <| hx.trans_le h

theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun b c => powerlt_le_powerlt_left

theorem powerlt_succ {a b : Cardinal} (h : a ≠ 0) : a ^< succ b = (a^b) :=
  (powerlt_le.2 fun c h' => power_le_power_left h <| le_of_lt_succ h').antisymm <| le_powerlt a (lt_succ b)

theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min

theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_max

theorem zero_powerlt {a : Cardinal} (h : a ≠ 0) : 0 ^< a = 1 := by
  apply (powerlt_le.2 fun c hc => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)

@[simp]
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 := by
  convert Cardinal.supr_of_empty _
  exact Subtype.is_empty_of_false fun x => (Cardinal.zero_le _).not_lt

end Cardinal

