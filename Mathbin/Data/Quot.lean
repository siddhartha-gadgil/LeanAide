/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Logic.Relator

/-!
# Quotient types

This module extends the core library's treatment of quotient types (`init.data.quot`).

## Tags

quotient
-/


variable {α : Sort _} {β : Sort _}

namespace Setoidₓ

theorem ext {α : Sort _} : ∀ {s t : Setoidₓ α}, (∀ a b, @Setoidₓ.R α s a b ↔ @Setoidₓ.R α t a b) → s = t
  | ⟨r, _⟩, ⟨p, _⟩, Eq => by
    have : r = p := funext fun a => funext fun b => propext <| Eq a b
    subst this

end Setoidₓ

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort _}

-- mathport name: «expr⟦ ⟧»
local notation:arg "⟦" a "⟧" => Quot.mk _ a

instance (r : α → α → Prop) [Inhabited α] : Inhabited (Quot r) :=
  ⟨⟦default⟧⟩

instance [Subsingleton α] : Subsingleton (Quot ra) :=
  ⟨fun x => Quot.induction_on x fun y => Quot.ind fun b => congr_arg _ (Subsingleton.elimₓ _ _)⟩

/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quot ra) (qb : Quot rb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → HEq (f a₁ b) (f a₂ b)) (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → HEq (f a b₁) (f a b₂)) :
    φ qa qb :=
  (Quot.hrecOn qa fun a => Quot.hrecOn qb (f a) fun b₁ b₂ pb => cb pb) fun a₁ a₂ pa =>
    (Quot.induction_on qb) fun b =>
      calc
        HEq (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _)) (f a₁ b) := by
          simp [← heq_self_iff_true]
        HEq _ (f a₂ b) := ca pa
        HEq _ (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _)) := by
          simp [← heq_self_iff_true]
        

/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `quot ra → quot rb`. -/
protected def map (f : α → β) (h : (ra⇒rb) f f) : Quot ra → Quot rb :=
  (Quot.lift fun x => ⟦f x⟧) fun x y (h₁ : ra x y) => Quot.sound <| h h₁

/-- If `ra` is a subrelation of `ra'`, then we have a natural map `quot ra → quot ra'`. -/
protected def mapRight {ra' : α → α → Prop} (h : ∀ a₁ a₂, ra a₁ a₂ → ra' a₁ a₂) : Quot ra → Quot ra' :=
  Quot.map id h

/-- Weaken the relation of a quotient. This is the same as `quot.map id`. -/
def factor {α : Type _} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) : Quot r → Quot s :=
  Quot.lift (Quot.mk s) fun x y rxy => Quot.sound (h x y rxy)

theorem factor_mk_eq {α : Type _} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
    factor r s h ∘ Quot.mk _ = Quot.mk _ :=
  rfl

variable {γ : Sort _} {r : α → α → Prop} {s : β → β → Prop}

/-- **Alias** of `quot.lift_beta`. -/
theorem lift_mk (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) : Quot.lift f h (Quot.mk r a) = f a :=
  Quot.lift_beta f h a

@[simp]
theorem lift_on_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) : Quot.liftOn (Quot.mk r a) f h = f a :=
  rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β`. -/
@[reducible, elab_as_eliminator]
protected def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a => Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha => funext fun q => Quot.induction_on q fun b => hs a₁ a₂ b ha) q₁ q₂

@[simp]
theorem lift₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    (a : α) (b : β) : Quot.lift₂ f hr hs (Quot.mk r a) (Quot.mk s b) = f a b :=
  rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it. -/
@[reducible, elab_as_eliminator]
protected def liftOn₂ (p : Quot r) (q : Quot s) (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : γ :=
  Quot.lift₂ f hr hs p q

@[simp]
theorem lift_on₂_mk (a : α) (b : β) (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : Quot.liftOn₂ (Quot.mk r a) (Quot.mk s b) f hr hs = f a b :=
  rfl

variable {t : γ → γ → Prop}

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` wih values in a quotient of
`γ`. -/
protected def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b => Quot.mk t <| f a b) (fun a b₁ b₂ hb => Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha => Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

@[simp]
theorem map₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (a : α) (b : β) :
    Quot.map₂ f hr hs (Quot.mk r a) (Quot.mk s b) = Quot.mk t (f a b) :=
  rfl

/-- A binary version of `quot.rec_on_subsingleton`. -/
@[reducible, elab_as_eliminator]
protected def recOnSubsingleton₂ {φ : Quot r → Quot s → Sort _} [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quot r)
    (q₂ : Quot s) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  (@Quot.recOnSubsingleton _ r (fun q => φ q q₂) (fun a => Quot.ind (h a) q₂) q₁) fun a =>
    (Quot.recOnSubsingleton q₂) fun b => f a b

@[elab_as_eliminator]
protected theorem induction_on₂ {δ : Quot r → Quot s → Prop} (q₁ : Quot r) (q₂ : Quot s)
    (h : ∀ a b, δ (Quot.mk r a) (Quot.mk s b)) : δ q₁ q₂ :=
  Quot.ind (fun a₁ => Quot.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_eliminator]
protected theorem induction_on₃ {δ : Quot r → Quot s → Quot t → Prop} (q₁ : Quot r) (q₂ : Quot s) (q₃ : Quot t)
    (h : ∀ a b c, δ (Quot.mk r a) (Quot.mk s b) (Quot.mk t c)) : δ q₁ q₂ q₃ :=
  Quot.ind (fun a₁ => Quot.ind (fun a₂ => Quot.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁

instance (r : α → α → Prop) (f : α → Prop) (h : ∀ a b, r a b → f a = f b) [hf : DecidablePred f] :
    DecidablePred (Quot.lift f h) := fun q => Quot.recOnSubsingleton q hf

/-- Note that this provides `decidable_rel (quot.lift₂ f ha hb)` when `α = β`. -/
instance (r : α → α → Prop) (s : β → β → Prop) (f : α → β → Prop) (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) [hf : ∀ a, DecidablePred (f a)] (q₁ : Quot r) :
    DecidablePred (Quot.lift₂ f ha hb q₁) := fun q₂ => Quot.recOnSubsingleton₂ q₁ q₂ hf

instance (r : α → α → Prop) (q : Quot r) (f : α → Prop) (h : ∀ a b, r a b → f a = f b) [DecidablePred f] :
    Decidable (Quot.liftOn q f h) :=
  Quot.lift.decidablePred _ _ _ _

instance (r : α → α → Prop) (s : β → β → Prop) (q₁ : Quot r) (q₂ : Quot s) (f : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) [∀ a, DecidablePred (f a)] :
    Decidable (Quot.liftOn₂ q₁ q₂ f ha hb) :=
  Quot.lift₂.decidablePred _ _ _ _ _ _ _

end Quot

namespace Quotientₓ

variable [sa : Setoidₓ α] [sb : Setoidₓ β]

variable {φ : Quotientₓ sa → Quotientₓ sb → Sort _}

instance (s : Setoidₓ α) [Inhabited α] : Inhabited (Quotientₓ s) :=
  ⟨⟦default⟧⟩

instance (s : Setoidₓ α) [Subsingleton α] : Subsingleton (Quotientₓ s) :=
  Quot.subsingleton

instance {α : Type _} [Setoidₓ α] : IsEquiv α (· ≈ ·) where
  refl := Setoidₓ.refl
  symm := fun a b => Setoidₓ.symm
  trans := fun a b c => Setoidₓ.trans

/-- Induction on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quotientₓ sa) (qb : Quotientₓ sb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) : φ qa qb :=
  Quot.hrecOn₂ qa qb f (fun _ _ _ p => c _ _ _ _ p (Setoidₓ.refl _)) fun _ _ _ p => c _ _ _ _ (Setoidₓ.refl _) p

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map (f : α → β) (h : ((· ≈ ·)⇒(· ≈ ·)) f f) : Quotientₓ sa → Quotientₓ sb :=
  Quot.map f h

@[simp]
theorem map_mk (f : α → β) (h : ((· ≈ ·)⇒(· ≈ ·)) f f) (x : α) :
    Quotientₓ.map f h (⟦x⟧ : Quotientₓ sa) = (⟦f x⟧ : Quotientₓ sb) :=
  rfl

variable {γ : Sort _} [sc : Setoidₓ γ]

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : quotient sa → quotient sb → quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ (f : α → β → γ) (h : ((· ≈ ·)⇒(· ≈ ·)⇒(· ≈ ·)) f f) : Quotientₓ sa → Quotientₓ sb → Quotientₓ sc :=
  Quotientₓ.lift₂ (fun x y => ⟦f x y⟧) fun x₁ y₁ x₂ y₂ h₁ h₂ => Quot.sound <| h h₁ h₂

@[simp]
theorem map₂_mk (f : α → β → γ) (h : ((· ≈ ·)⇒(· ≈ ·)⇒(· ≈ ·)) f f) (x : α) (y : β) :
    Quotientₓ.map₂ f h (⟦x⟧ : Quotientₓ sa) (⟦y⟧ : Quotientₓ sb) = (⟦f x y⟧ : Quotientₓ sc) :=
  rfl

include sa

instance (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] : DecidablePred (Quotientₓ.lift f h) :=
  Quot.lift.decidablePred _ _ _

include sb

/-- Note that this provides `decidable_rel (quotient.lift₂ f h)` when `α = β`. -/
instance (f : α → β → Prop) (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) [hf : ∀ a, DecidablePred (f a)]
    (q₁ : Quotientₓ sa) : DecidablePred (Quotientₓ.lift₂ f h q₁) := fun q₂ => Quotientₓ.recOnSubsingleton₂ q₁ q₂ hf

omit sb

instance (q : Quotientₓ sa) (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] :
    Decidable (Quotientₓ.liftOn q f h) :=
  Quotientₓ.lift.decidablePred _ _ _

instance (q₁ : Quotientₓ sa) (q₂ : Quotientₓ sb) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) [∀ a, DecidablePred (f a)] :
    Decidable (Quotientₓ.liftOn₂ q₁ q₂ f h) :=
  Quotientₓ.lift₂.decidablePred _ _ _ _

end Quotientₓ

theorem Quot.eq {α : Type _} {r : α → α → Prop} {x y : α} : Quot.mk r x = Quot.mk r y ↔ EqvGen r x y :=
  ⟨Quot.exact r, Quot.eqv_gen_sound⟩

@[simp]
theorem Quotientₓ.eq [r : Setoidₓ α] {x y : α} : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
  ⟨Quotientₓ.exact, Quotientₓ.sound⟩

theorem forall_quotient_iff {α : Type _} [r : Setoidₓ α] {p : Quotientₓ r → Prop} :
    (∀ a : Quotientₓ r, p a) ↔ ∀ a : α, p ⟦a⟧ :=
  ⟨fun h x => h _, fun h a => a.induction_on h⟩

@[simp]
theorem Quotientₓ.lift_mk [s : Setoidₓ α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotientₓ.lift f h (Quotientₓ.mk x) = f x :=
  rfl

@[simp]
theorem Quotientₓ.lift_comp_mk [Setoidₓ α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) :
    Quotientₓ.lift f h ∘ Quotientₓ.mk = f :=
  rfl

@[simp]
theorem Quotientₓ.lift₂_mk {α : Sort _} {β : Sort _} {γ : Sort _} [Setoidₓ α] [Setoidₓ β] (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (a : α) (b : β) :
    Quotientₓ.lift₂ f h (Quotientₓ.mk a) (Quotientₓ.mk b) = f a b :=
  rfl

@[simp]
theorem Quotientₓ.lift_on_mk [s : Setoidₓ α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotientₓ.liftOn (Quotientₓ.mk x) f h = f x :=
  rfl

@[simp]
theorem Quotientₓ.lift_on₂_mk {α : Sort _} {β : Sort _} [Setoidₓ α] (f : α → α → β)
    (h : ∀ a₁ a₂ b₁ b₂ : α, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (x y : α) :
    Quotientₓ.liftOn₂ (Quotientₓ.mk x) (Quotientₓ.mk y) f h = f x y :=
  rfl

/-- `quot.mk r` is a surjective function. -/
theorem surjective_quot_mk (r : α → α → Prop) : Function.Surjective (Quot.mk r) :=
  Quot.exists_rep

/-- `quotient.mk` is a surjective function. -/
theorem surjective_quotient_mk (α : Sort _) [s : Setoidₓ α] : Function.Surjective (Quotientₓ.mk : α → Quotientₓ s) :=
  Quot.exists_rep

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.some (Quot.exists_rep q)

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
unsafe def quot.unquot {r : α → α → Prop} : Quot r → α :=
  unchecked_cast

@[simp]
theorem Quot.out_eq {r : α → α → Prop} (q : Quot r) : Quot.mk r q.out = q :=
  Classical.some_spec (Quot.exists_rep q)

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quotientₓ.out [s : Setoidₓ α] : Quotientₓ s → α :=
  Quot.out

@[simp]
theorem Quotientₓ.out_eq [s : Setoidₓ α] (q : Quotientₓ s) : ⟦q.out⟧ = q :=
  q.out_eq

theorem Quotientₓ.mk_out [s : Setoidₓ α] (a : α) : ⟦a⟧.out ≈ a :=
  Quotientₓ.exact (Quotientₓ.out_eq _)

theorem Quotientₓ.mk_eq_iff_out [s : Setoidₓ α] {x : α} {y : Quotientₓ s} : ⟦x⟧ = y ↔ x ≈ Quotientₓ.out y := by
  refine' Iff.trans _ Quotientₓ.eq
  rw [Quotientₓ.out_eq y]

theorem Quotientₓ.eq_mk_iff_out [s : Setoidₓ α] {x : Quotientₓ s} {y : α} : x = ⟦y⟧ ↔ Quotientₓ.out x ≈ y := by
  refine' Iff.trans _ Quotientₓ.eq
  rw [Quotientₓ.out_eq x]

@[simp]
theorem Quotientₓ.out_equiv_out {s : Setoidₓ α} {x y : Quotientₓ s} : x.out ≈ y.out ↔ x = y := by
  rw [← Quotientₓ.eq_mk_iff_out, Quotientₓ.out_eq]

theorem Quotientₓ.out_injective {s : Setoidₓ α} : Function.Injective (@Quotientₓ.out α s) := fun a b h =>
  Quotientₓ.out_equiv_out.1 <| h ▸ Setoidₓ.refl _

@[simp]
theorem Quotientₓ.out_inj {s : Setoidₓ α} {x y : Quotientₓ s} : x.out = y.out ↔ x = y :=
  ⟨fun h => Quotientₓ.out_injective h, fun h => h ▸ rfl⟩

section Pi

instance piSetoid {ι : Sort _} {α : ι → Sort _} [∀ i, Setoidₓ (α i)] : Setoidₓ (∀ i, α i) where
  R := fun a b => ∀ i, a i ≈ b i
  iseqv :=
    ⟨fun a i => Setoidₓ.refl _, fun a b h i => Setoidₓ.symm (h _), fun a b c h₁ h₂ i => Setoidₓ.trans (h₁ _) (h₂ _)⟩

/-- Given a function `f : Π i, quotient (S i)`, returns the class of functions `Π i, α i` sending
each `i` to an element of the class `f i`. -/
noncomputable def Quotientₓ.choice {ι : Type _} {α : ι → Type _} [S : ∀ i, Setoidₓ (α i)] (f : ∀ i, Quotientₓ (S i)) :
    @Quotientₓ (∀ i, α i)
      (by
        infer_instance) :=
  ⟦fun i => (f i).out⟧

@[simp]
theorem Quotientₓ.choice_eq {ι : Type _} {α : ι → Type _} [∀ i, Setoidₓ (α i)] (f : ∀ i, α i) :
    (Quotientₓ.choice fun i => ⟦f i⟧) = ⟦f⟧ :=
  Quotientₓ.sound fun i => Quotientₓ.mk_out _

@[elab_as_eliminator]
theorem Quotientₓ.induction_on_pi {ι : Type _} {α : ι → Sort _} [s : ∀ i, Setoidₓ (α i)]
    {p : (∀ i, Quotientₓ (s i)) → Prop} (f : ∀ i, Quotientₓ (s i)) (h : ∀ a : ∀ i, α i, p fun i => ⟦a i⟧) : p f := by
  rw [← (funext fun i => Quotientₓ.out_eq (f i) : (fun i => ⟦(f i).out⟧) = f)]
  apply h

end Pi

theorem nonempty_quotient_iff (s : Setoidₓ α) : Nonempty (Quotientₓ s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => Quotientₓ.induction_on a Nonempty.intro, fun ⟨a⟩ => ⟨⟦a⟧⟩⟩

/-! ### Truncation -/


/-- `trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `nonempty α`, but unlike `nonempty α`, `trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def Trunc.{u} (α : Sort u) : Sort u :=
  @Quot α fun _ _ => True

theorem true_equivalence : @Equivalenceₓ α fun _ _ => True :=
  ⟨fun _ => trivialₓ, fun _ _ _ => trivialₓ, fun _ _ _ _ _ => trivialₓ⟩

namespace Trunc

/-- Constructor for `trunc α` -/
def mk (a : α) : Trunc α :=
  Quot.mk _ a

instance [Inhabited α] : Inhabited (Trunc α) :=
  ⟨mk default⟩

/-- Any constant function lifts to a function out of the truncation -/
def lift (f : α → β) (c : ∀ a b : α, f a = f b) : Trunc α → β :=
  Quot.lift f fun a b _ => c a b

theorem ind {β : Trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : Trunc α, β q :=
  Quot.ind

protected theorem lift_mk (f : α → β) (c) (a : α) : lift f c (mk a) = f a :=
  rfl

/-- Lift a constant function on `q : trunc α`. -/
@[reducible, elab_as_eliminator]
protected def liftOn (q : Trunc α) (f : α → β) (c : ∀ a b : α, f a = f b) : β :=
  lift f c q

@[elab_as_eliminator]
protected theorem induction_on {β : Trunc α → Prop} (q : Trunc α) (h : ∀ a, β (mk a)) : β q :=
  ind h q

theorem exists_rep (q : Trunc α) : ∃ a : α, mk a = q :=
  Quot.exists_rep q

@[elab_as_eliminator]
protected theorem induction_on₂ {C : Trunc α → Trunc β → Prop} (q₁ : Trunc α) (q₂ : Trunc β)
    (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
  (Trunc.induction_on q₁) fun a₁ => Trunc.induction_on q₂ (h a₁)

protected theorem eq (a b : Trunc α) : a = b :=
  Trunc.induction_on₂ a b fun x y => Quot.sound trivialₓ

instance : Subsingleton (Trunc α) :=
  ⟨Trunc.eq⟩

/-- The `bind` operator for the `trunc` monad. -/
def bind (q : Trunc α) (f : α → Trunc β) : Trunc β :=
  Trunc.liftOn q f fun a b => Trunc.eq _ _

/-- A function `f : α → β` defines a function `map f : trunc α → trunc β`. -/
def map (f : α → β) (q : Trunc α) : Trunc β :=
  bind q (Trunc.mk ∘ f)

instance : Monadₓ Trunc where
  pure := @Trunc.mk
  bind := @Trunc.bind

instance : IsLawfulMonad Trunc where
  id_map := fun α q => Trunc.eq _ _
  pure_bind := fun α β q f => rfl
  bind_assoc := fun α β γ x f g => Trunc.eq _ _

variable {C : Trunc α → Sort _}

/-- Recursion/induction principle for `trunc`. -/
@[reducible, elab_as_eliminator]
protected def rec (f : ∀ a, C (mk a)) (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
    (q : Trunc α) : C q :=
  Quot.rec f (fun a b _ => h a b) q

/-- A version of `trunc.rec` taking `q : trunc α` as the first argument. -/
@[reducible, elab_as_eliminator]
protected def recOn (q : Trunc α) (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
  Trunc.rec f h q

/-- A version of `trunc.rec_on` assuming the codomain is a `subsingleton`. -/
@[reducible, elab_as_eliminator]
protected def recOnSubsingleton [∀ a, Subsingleton (C (mk a))] (q : Trunc α) (f : ∀ a, C (mk a)) : C q :=
  Trunc.rec f (fun a b => Subsingleton.elimₓ _ (f b)) q

/-- Noncomputably extract a representative of `trunc α` (using the axiom of choice). -/
noncomputable def out : Trunc α → α :=
  Quot.out

@[simp]
theorem out_eq (q : Trunc α) : mk q.out = q :=
  Trunc.eq _ _

protected theorem nonempty (q : Trunc α) : Nonempty α :=
  nonempty_of_exists q.exists_rep

end Trunc

/-! ### `quotient` with implicit `setoid` -/


namespace Quotientₓ

variable {γ : Sort _} {φ : Sort _} {s₁ : Setoidₓ α} {s₂ : Setoidₓ β} {s₃ : Setoidₓ γ}

/-! Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules. -/


/-- A version of `quotient.mk` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
protected def mk' (a : α) : Quotientₓ s₁ :=
  Quot.mk s₁.1 a

/-- `quotient.mk'` is a surjective function. -/
theorem surjective_quotient_mk' : Function.Surjective (Quotientₓ.mk' : α → Quotientₓ s₁) :=
  Quot.exists_rep

/-- A version of `quotient.lift_on` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_eliminator, reducible]
protected def liftOn' (q : Quotientₓ s₁) (f : α → φ) (h : ∀ a b, @Setoidₓ.R α s₁ a b → f a = f b) : φ :=
  Quotientₓ.liftOn q f h

@[simp]
protected theorem lift_on'_mk' (f : α → φ) (h) (x : α) : Quotientₓ.liftOn' (@Quotientₓ.mk' _ s₁ x) f h = f x :=
  rfl

/-- A version of `quotient.lift_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_eliminator, reducible]
protected def liftOn₂' (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂) (f : α → β → γ)
    (h : ∀ a₁ a₂ b₁ b₂, @Setoidₓ.R α s₁ a₁ b₁ → @Setoidₓ.R β s₂ a₂ b₂ → f a₁ a₂ = f b₁ b₂) : γ :=
  Quotientₓ.liftOn₂ q₁ q₂ f h

@[simp]
protected theorem lift_on₂'_mk' (f : α → β → γ) (h) (a : α) (b : β) :
    Quotientₓ.liftOn₂' (@Quotientₓ.mk' _ s₁ a) (@Quotientₓ.mk' _ s₂ b) f h = f a b :=
  rfl

/-- A version of `quotient.ind` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_eliminator]
protected theorem ind' {p : Quotientₓ s₁ → Prop} (h : ∀ a, p (Quotientₓ.mk' a)) (q : Quotientₓ s₁) : p q :=
  Quotientₓ.ind h q

/-- A version of `quotient.ind₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_eliminator]
protected theorem ind₂' {p : Quotientₓ s₁ → Quotientₓ s₂ → Prop} (h : ∀ a₁ a₂, p (Quotientₓ.mk' a₁) (Quotientₓ.mk' a₂))
    (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂) : p q₁ q₂ :=
  Quotientₓ.ind₂ h q₁ q₂

/-- A version of `quotient.induction_on` taking `{s : setoid α}` as an implicit argument instead
of an instance argument. -/
@[elab_as_eliminator]
protected theorem induction_on' {p : Quotientₓ s₁ → Prop} (q : Quotientₓ s₁) (h : ∀ a, p (Quotientₓ.mk' a)) : p q :=
  Quotientₓ.induction_on q h

/-- A version of `quotient.induction_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit
arguments instead of instance arguments. -/
@[elab_as_eliminator]
protected theorem induction_on₂' {p : Quotientₓ s₁ → Quotientₓ s₂ → Prop} (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂)
    (h : ∀ a₁ a₂, p (Quotientₓ.mk' a₁) (Quotientₓ.mk' a₂)) : p q₁ q₂ :=
  Quotientₓ.induction_on₂ q₁ q₂ h

/-- A version of `quotient.induction_on₃` taking `{s₁ : setoid α} {s₂ : setoid β} {s₃ : setoid γ}`
as implicit arguments instead of instance arguments. -/
@[elab_as_eliminator]
protected theorem induction_on₃' {p : Quotientₓ s₁ → Quotientₓ s₂ → Quotientₓ s₃ → Prop} (q₁ : Quotientₓ s₁)
    (q₂ : Quotientₓ s₂) (q₃ : Quotientₓ s₃)
    (h : ∀ a₁ a₂ a₃, p (Quotientₓ.mk' a₁) (Quotientₓ.mk' a₂) (Quotientₓ.mk' a₃)) : p q₁ q₂ q₃ :=
  Quotientₓ.induction_on₃ q₁ q₂ q₃ h

/-- A version of `quotient.rec_on_subsingleton` taking `{s₁ : setoid α}` as an implicit argument
instead of an instance argument. -/
@[elab_as_eliminator]
protected def recOnSubsingleton' {φ : Quotientₓ s₁ → Sort _} [h : ∀ a, Subsingleton (φ ⟦a⟧)] (q : Quotientₓ s₁)
    (f : ∀ a, φ (Quotientₓ.mk' a)) : φ q :=
  Quotientₓ.recOnSubsingleton q f

/-- A version of `quotient.rec_on_subsingleton₂` taking `{s₁ : setoid α} {s₂ : setoid α}`
as implicit arguments instead of instance arguments. -/
@[reducible, elab_as_eliminator]
protected def recOnSubsingleton₂' {φ : Quotientₓ s₁ → Quotientₓ s₂ → Sort _} [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)]
    (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂) (f : ∀ a₁ a₂, φ (Quotientₓ.mk' a₁) (Quotientₓ.mk' a₂)) : φ q₁ q₂ :=
  Quotientₓ.recOnSubsingleton₂ q₁ q₂ f

/-- Recursion on a `quotient` argument `a`, result type depends on `⟦a⟧`. -/
protected def hrecOn' {φ : Quotientₓ s₁ → Sort _} (qa : Quotientₓ s₁) (f : ∀ a, φ (Quotientₓ.mk' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → HEq (f a₁) (f a₂)) : φ qa :=
  Quot.hrecOn qa f c

@[simp]
theorem hrec_on'_mk' {φ : Quotientₓ s₁ → Sort _} (f : ∀ a, φ (Quotientₓ.mk' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → HEq (f a₁) (f a₂)) (x : α) : (Quotientₓ.mk' x).hrecOn' f c = f x :=
  rfl

/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂' {φ : Quotientₓ s₁ → Quotientₓ s₂ → Sort _} (qa : Quotientₓ s₁) (qb : Quotientₓ s₂)
    (f : ∀ a b, φ (Quotientₓ.mk' a) (Quotientₓ.mk' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) : φ qa qb :=
  Quotientₓ.hrecOn₂ qa qb f c

@[simp]
theorem hrec_on₂'_mk' {φ : Quotientₓ s₁ → Quotientₓ s₂ → Sort _} (f : ∀ a b, φ (Quotientₓ.mk' a) (Quotientₓ.mk' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) (x : α) (qb : Quotientₓ s₂) :
    (Quotientₓ.mk' x).hrecOn₂' qb f c = qb.hrecOn' (f x) fun b₁ b₂ => c _ _ _ _ (Setoidₓ.refl _) :=
  rfl

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map' (f : α → β) (h : (s₁.R⇒s₂.R) f f) : Quotientₓ s₁ → Quotientₓ s₂ :=
  Quot.map f h

@[simp]
theorem map'_mk' (f : α → β) (h) (x : α) :
    (Quotientₓ.mk' x : Quotientₓ s₁).map' f h = (Quotientₓ.mk' (f x) : Quotientₓ s₂) :=
  rfl

/-- A version of `quotient.map₂` using curly braces and unification. -/
protected def map₂' (f : α → β → γ) (h : (s₁.R⇒s₂.R⇒s₃.R) f f) : Quotientₓ s₁ → Quotientₓ s₂ → Quotientₓ s₃ :=
  Quotientₓ.map₂ f h

@[simp]
theorem map₂'_mk' (f : α → β → γ) (h) (x : α) :
    (Quotientₓ.mk' x : Quotientₓ s₁).map₂' f h =
      (Quotientₓ.map' (f x) (h (Setoidₓ.refl x)) : Quotientₓ s₂ → Quotientₓ s₃) :=
  rfl

theorem exact' {a b : α} : (Quotientₓ.mk' a : Quotientₓ s₁) = Quotientₓ.mk' b → @Setoidₓ.R _ s₁ a b :=
  Quotientₓ.exact

theorem sound' {a b : α} : @Setoidₓ.R _ s₁ a b → @Quotientₓ.mk' α s₁ a = Quotientₓ.mk' b :=
  Quotientₓ.sound

@[simp]
protected theorem eq' {a b : α} : @Quotientₓ.mk' α s₁ a = Quotientₓ.mk' b ↔ @Setoidₓ.R _ s₁ a b :=
  Quotientₓ.eq

/-- A version of `quotient.out` taking `{s₁ : setoid α}` as an implicit argument instead of an
instance argument. -/
noncomputable def out' (a : Quotientₓ s₁) : α :=
  Quotientₓ.out a

@[simp]
theorem out_eq' (q : Quotientₓ s₁) : Quotientₓ.mk' q.out' = q :=
  q.out_eq

theorem mk_out' (a : α) : @Setoidₓ.R α s₁ (Quotientₓ.mk' a : Quotientₓ s₁).out' a :=
  Quotientₓ.exact (Quotientₓ.out_eq _)

section

variable [Setoidₓ α]

protected theorem mk'_eq_mk (x : α) : Quotientₓ.mk' x = ⟦x⟧ :=
  rfl

@[simp]
protected theorem lift_on'_mk (x : α) (f : α → β) (h) : ⟦x⟧.liftOn' f h = f x :=
  rfl

@[simp]
protected theorem lift_on₂'_mk [Setoidₓ β] (f : α → β → γ) (h) (a : α) (b : β) :
    Quotientₓ.liftOn₂' ⟦a⟧ ⟦b⟧ f h = f a b :=
  Quotientₓ.lift_on₂'_mk' _ _ _ _

@[simp]
theorem map'_mk [Setoidₓ β] (f : α → β) (h) (x : α) : ⟦x⟧.map' f h = ⟦f x⟧ :=
  rfl

end

instance (q : Quotientₓ s₁) (f : α → Prop) (h : ∀ a b, @Setoidₓ.R α s₁ a b → f a = f b) [DecidablePred f] :
    Decidable (Quotientₓ.liftOn' q f h) :=
  Quotientₓ.lift.decidablePred _ _ q

instance (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, @Setoidₓ.R α s₁ a₁ a₂ → @Setoidₓ.R β s₂ b₁ b₂ → f a₁ b₁ = f a₂ b₂) [∀ a, DecidablePred (f a)] :
    Decidable (Quotientₓ.liftOn₂' q₁ q₂ f h) :=
  Quotientₓ.lift₂.decidablePred _ _ _ _

end Quotientₓ

