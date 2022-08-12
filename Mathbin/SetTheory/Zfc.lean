/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Set.Lattice

/-!
# A model of ZFC

In this file, we model Zermelo-Fraenkel set theory (+ Choice) using Lean's underlying type theory.
We do this in four main steps:
* Define pre-sets inductively.
* Define extensional equivalence on pre-sets and give it a `setoid` instance.
* Define ZFC sets by quotienting pre-sets by extensional equivalence.
* Define classes as sets of ZFC sets.
Then the rest is usual set theory.

## The model

* `pSet`: Pre-set. A pre-set is inductively defined by its indexing type and its members, which are
  themselves pre-sets.
* `Set`: ZFC set. Defined as `pSet` quotiented by `pSet.equiv`, the extensional equivalence.
* `Class`: Class. Defined as `set Set`.
* `Set.choice`: Axiom of choice. Proved from Lean's axiom of choice.

## Other definitions

* `arity α n`: `n`-ary function `α → α → ... → α`. Defined inductively.
* `arity.const a n`: `n`-ary constant function equal to `a`.
* `pSet.type`: Underlying type of a pre-set.
* `pSet.func`: Underlying family of pre-sets of a pre-set.
* `pSet.equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `pSet.omega`, `Set.omega`: The von Neumann ordinal `ω` as a `pSet`, as a `Set`.
* `pSet.arity.equiv`: Extensional equivalence of `n`-ary `pSet`-valued functions. Extension of
  `pSet.equiv`.
* `pSet.resp`: Collection of `n`-ary `pSet`-valued functions that respect extensional equivalence.
* `pSet.eval`: Turns a `pSet`-valued function that respect extensional equivalence into a
  `Set`-valued function.
* `classical.all_definable`: All functions are classically definable.
* `Set.is_func` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `Set.funs`: ZFC set of ZFC functions `x → y`.
* `Class.iota`: Definite description operator.

## Notes

To avoid confusion between the Lean `set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`set`" and "ZFC set".

## TODO

Prove `Set.map_definable_aux` computably.
-/


universe u v

/-- The type of `n`-ary functions `α → α → ... → α`. -/
def Arity (α : Type u) : ℕ → Type u
  | 0 => α
  | n + 1 => α → Arity n

@[simp]
theorem arity_zero (α : Type u) : Arity α 0 = α :=
  rfl

@[simp]
theorem arity_succ (α : Type u) (n : ℕ) : Arity α n.succ = (α → Arity α n) :=
  rfl

namespace Arity

/-- Constant `n`-ary function with value `a`. -/
def const {α : Type u} (a : α) : ∀ n, Arity α n
  | 0 => a
  | n + 1 => fun _ => const n

@[simp]
theorem const_zero {α : Type u} (a : α) : const a 0 = a :=
  rfl

@[simp]
theorem const_succ {α : Type u} (a : α) (n : ℕ) : const a n.succ = fun _ => const a n :=
  rfl

theorem const_succ_apply {α : Type u} (a : α) (n : ℕ) (x : α) : const a n.succ x = const a n :=
  rfl

instance Arity.inhabited {α n} [Inhabited α] : Inhabited (Arity α n) :=
  ⟨const default _⟩

end Arity

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet

/-- The underlying type of a pre-set -/
def Type : PSet → Type u
  | ⟨α, A⟩ => α

/-- The underlying pre-set family of a pre-set -/
def func : ∀ x : PSet, x.type → PSet
  | ⟨α, A⟩ => A

@[simp]
theorem mk_type (α A) : Type ⟨α, A⟩ = α :=
  rfl

@[simp]
theorem mk_func (α A) : func ⟨α, A⟩ = A :=
  rfl

@[simp]
theorem eta : ∀ x : PSet, mk x.type x.func = x
  | ⟨α, A⟩ => rfl

/-- Two pre-sets are extensionally equivalent if every element of the first family is extensionally
equivalent to some element of the second family and vice-versa. -/
def Equiv (x y : PSet) : Prop :=
  PSet.rec (fun α z m ⟨β, B⟩ => (∀ a, ∃ b, m a (B b)) ∧ ∀ b, ∃ a, m a (B b)) x y

theorem exists_equiv_left : ∀ {x y : PSet} (h : Equiv x y) (i : x.type), ∃ j, Equiv (x.func i) (y.func j)
  | ⟨α, A⟩, ⟨β, B⟩, h => h.1

theorem exists_equiv_right : ∀ {x y : PSet} (h : Equiv x y) (j : y.type), ∃ i, Equiv (x.func i) (y.func j)
  | ⟨α, A⟩, ⟨β, B⟩, h => h.2

protected theorem Equiv.refl (x) : Equiv x x :=
  (PSet.recOn x) fun α A IH => ⟨fun a => ⟨a, IH a⟩, fun a => ⟨a, IH a⟩⟩

protected theorem Equiv.rfl : ∀ {x}, Equiv x x :=
  Equivₓ.refl

protected theorem Equiv.euc {x} : ∀ {y z}, Equiv x y → Equiv z y → Equiv x z :=
  (PSet.recOn x) fun α A IH y =>
    (PSet.casesOn y) fun β B ⟨γ, Γ⟩ ⟨αβ, βα⟩ ⟨γβ, βγ⟩ =>
      ⟨fun a =>
        let ⟨b, ab⟩ := αβ a
        let ⟨c, bc⟩ := βγ b
        ⟨c, IH a ab bc⟩,
        fun c =>
        let ⟨b, cb⟩ := γβ c
        let ⟨a, ba⟩ := βα b
        ⟨a, IH a ba cb⟩⟩

protected theorem Equiv.symm {x y} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc

protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm

instance setoid : Setoidₓ PSet :=
  ⟨PSet.Equiv, Equiv.refl, fun x y => Equiv.symm, fun x y z => Equiv.trans⟩

/-- A pre-set is a subset of another pre-set if every element of the first family is extensionally
equivalent to some element of the second family.-/
protected def Subset (x y : PSet) : Prop :=
  ∀ a, ∃ b, Equiv (x.func a) (y.func b)

instance : HasSubset PSet :=
  ⟨PSet.Subset⟩

theorem Equiv.ext : ∀ x y : PSet, Equiv x y ↔ x ⊆ y ∧ y ⊆ x
  | ⟨α, A⟩, ⟨β, B⟩ =>
    ⟨fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩,
      fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩⟩

theorem Subset.congr_left : ∀ {x y z : PSet}, Equiv x y → (x ⊆ z ↔ y ⊆ z)
  | ⟨α, A⟩, ⟨β, B⟩, ⟨γ, Γ⟩, ⟨αβ, βα⟩ =>
    ⟨fun αγ b =>
      let ⟨a, ba⟩ := βα b
      let ⟨c, ac⟩ := αγ a
      ⟨c, (Equiv.symm ba).trans ac⟩,
      fun βγ a =>
      let ⟨b, ab⟩ := αβ a
      let ⟨c, bc⟩ := βγ b
      ⟨c, Equiv.trans ab bc⟩⟩

theorem Subset.congr_right : ∀ {x y z : PSet}, Equiv x y → (z ⊆ x ↔ z ⊆ y)
  | ⟨α, A⟩, ⟨β, B⟩, ⟨γ, Γ⟩, ⟨αβ, βα⟩ =>
    ⟨fun γα c =>
      let ⟨a, ca⟩ := γα c
      let ⟨b, ab⟩ := αβ a
      ⟨b, ca.trans ab⟩,
      fun γβ c =>
      let ⟨b, cb⟩ := γβ c
      let ⟨a, ab⟩ := βα b
      ⟨a, cb.trans (Equiv.symm ab)⟩⟩

/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member of the family `y`. -/
protected def Mem (x y : PSet.{u}) : Prop :=
  ∃ b, Equiv x (y.func b)

instance : HasMem PSet PSet :=
  ⟨PSet.Mem⟩

theorem Mem.mk {α : Type u} (A : α → PSet) (a : α) : A a ∈ mk α A :=
  ⟨a, Equiv.refl (A a)⟩

theorem Mem.ext : ∀ {x y : PSet.{u}}, (∀ w : PSet.{u}, w ∈ x ↔ w ∈ y) → Equiv x y
  | ⟨α, A⟩, ⟨β, B⟩, h =>
    ⟨fun a => (h (A a)).1 (Mem.mk A a), fun b =>
      let ⟨a, ha⟩ := (h (B b)).2 (Mem.mk B b)
      ⟨a, ha.symm⟩⟩

theorem Mem.congr_right : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y
  | ⟨α, A⟩, ⟨β, B⟩, ⟨αβ, βα⟩, w =>
    ⟨fun ⟨a, ha⟩ =>
      let ⟨b, hb⟩ := αβ a
      ⟨b, ha.trans hb⟩,
      fun ⟨b, hb⟩ =>
      let ⟨a, ha⟩ := βα b
      ⟨a, hb.euc ha⟩⟩

theorem equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y :=
  ⟨Mem.congr_right,
    match x, y with
    | ⟨α, A⟩, ⟨β, B⟩, h =>
      ⟨fun a => h.1 (Mem.mk A a), fun b =>
        let ⟨a, h⟩ := h.2 (Mem.mk B b)
        ⟨a, h.symm⟩⟩⟩

theorem Mem.congr_left : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, x ∈ w ↔ y ∈ w
  | x, y, h, ⟨α, A⟩ => ⟨fun ⟨a, ha⟩ => ⟨a, h.symm.trans ha⟩, fun ⟨a, ha⟩ => ⟨a, h.trans ha⟩⟩

/-- Convert a pre-set to a `set` of pre-sets. -/
def ToSet (u : PSet.{u}) : Set PSet.{u} :=
  { x | x ∈ u }

/-- Two pre-sets are equivalent iff they have the same members. -/
theorem Equiv.eq {x y : PSet} : Equiv x y ↔ ToSet x = ToSet y :=
  equiv_iff_mem.trans Set.ext_iff.symm

instance : Coe PSet (Set PSet) :=
  ⟨ToSet⟩

/-- The empty pre-set -/
protected def empty : PSet :=
  ⟨_, Pempty.elimₓ⟩

instance : HasEmptyc PSet :=
  ⟨PSet.empty⟩

instance : Inhabited PSet :=
  ⟨∅⟩

instance : IsEmpty (Type ∅) :=
  Pempty.is_empty

@[simp]
theorem mem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1

/-- Insert an element into a pre-set -/
protected def insert (x y : PSet) : PSet :=
  ⟨Option y.type, fun o => Option.rec x y.func o⟩

instance : HasInsert PSet PSet :=
  ⟨PSet.insert⟩

instance : HasSingleton PSet PSet :=
  ⟨fun s => insert s ∅⟩

instance : IsLawfulSingleton PSet PSet :=
  ⟨fun _ => rfl⟩

instance (x y : PSet) : Inhabited (insert x y).type :=
  Option.inhabited _

/-- The n-th von Neumann ordinal -/
def ofNat : ℕ → PSet
  | 0 => ∅
  | n + 1 => insert (of_nat n) (of_nat n)

/-- The von Neumann ordinal ω -/
def omega : PSet :=
  ⟨ULift ℕ, fun n => ofNat n.down⟩

/-- The pre-set separation operation `{x ∈ a | p x}` -/
protected def sep (p : PSet → Prop) (x : PSet) : PSet :=
  ⟨{ a // p (x.func a) }, fun y => x.func y.1⟩

instance : HasSep PSet PSet :=
  ⟨PSet.sep⟩

/-- The pre-set powerset operator -/
def powerset (x : PSet) : PSet :=
  ⟨Set x.type, fun p => ⟨{ a // p a }, fun y => x.func y.1⟩⟩

@[simp]
theorem mem_powerset : ∀ {x y : PSet}, y ∈ powerset x ↔ y ⊆ x
  | ⟨α, A⟩, ⟨β, B⟩ =>
    ⟨fun ⟨p, e⟩ => (Subset.congr_left e).2 fun ⟨a, pa⟩ => ⟨a, Equiv.refl (A a)⟩, fun βα =>
      ⟨{ a | ∃ b, Equiv (B b) (A a) }, fun b =>
        let ⟨a, ba⟩ := βα b
        ⟨⟨a, b, ba⟩, ba⟩,
        fun ⟨a, b, ba⟩ => ⟨b, ba⟩⟩⟩

/-- The pre-set union operator -/
def union (a : PSet) : PSet :=
  ⟨Σx, (a.func x).type, fun ⟨x, y⟩ => (a.func x).func y⟩

@[simp]
theorem mem_Union : ∀ {x y : PSet.{u}}, y ∈ union x ↔ ∃ z ∈ x, y ∈ z
  | ⟨α, A⟩, y =>
    ⟨fun ⟨⟨a, c⟩, (e : Equivₓ y ((A a).func c))⟩ =>
      have : func (A a) c ∈ mk (A a).type (A a).func := Mem.mk (A a).func c
      ⟨_, Mem.mk _ _,
        (Mem.congr_left e).2
          (by
            rwa [eta] at this)⟩,
      fun ⟨⟨β, B⟩, ⟨a, (e : Equivₓ (mk β B) (A a))⟩, ⟨b, yb⟩⟩ => by
      rw [← eta (A a)] at e
      exact
        let ⟨βt, tβ⟩ := e
        let ⟨c, bc⟩ := βt b
        ⟨⟨a, c⟩, yb.trans bc⟩⟩

/-- The image of a function from pre-sets to pre-sets. -/
def image (f : PSet.{u} → PSet.{u}) (x : PSet.{u}) : PSet :=
  ⟨x.type, f ∘ x.func⟩

theorem mem_image {f : PSet.{u} → PSet.{u}} (H : ∀ {x y}, Equiv x y → Equiv (f x) (f y)) :
    ∀ {x y : PSet.{u}}, y ∈ image f x ↔ ∃ z ∈ x, Equiv y (f z)
  | ⟨α, A⟩, y => ⟨fun ⟨a, ya⟩ => ⟨A a, Mem.mk A a, ya⟩, fun ⟨z, ⟨a, za⟩, yz⟩ => ⟨a, yz.trans (H za)⟩⟩

/-- Universe lift operation -/
protected def lift : PSet.{u} → PSet.{max u v}
  | ⟨α, A⟩ => ⟨ULift α, fun ⟨x⟩ => lift (A x)⟩

/-- Embedding of one universe in another -/
-- intended to be used with explicit universe parameters
@[nolint check_univs]
def embed : PSet.{max (u + 1) v} :=
  ⟨ULift.{v, u + 1} PSet, fun ⟨x⟩ => PSet.lift.{u, max (u + 1) v} x⟩

theorem lift_mem_embed : ∀ x : PSet.{u}, PSet.lift.{u, max (u + 1) v} x ∈ embed.{u, v} := fun x => ⟨⟨x⟩, Equiv.rfl⟩

/-- Function equivalence is defined so that `f ~ g` iff `∀ x y, x ~ y → f x ~ g y`. This extends to
equivalence of `n`-ary functions. -/
def Arity.Equiv : ∀ {n}, Arity PSet.{u} n → Arity PSet.{u} n → Prop
  | 0, a, b => Equiv a b
  | n + 1, a, b => ∀ x y, Equiv x y → arity.equiv (a x) (b y)

theorem Arity.equiv_const {a : PSet.{u}} : ∀ n, Arity.Equiv (Arity.const a n) (Arity.const a n)
  | 0 => Equiv.rfl
  | n + 1 => fun x y h => arity.equiv_const _

/-- `resp n` is the collection of n-ary functions on `pSet` that respect
  equivalence, i.e. when the inputs are equivalent the output is as well. -/
def Resp (n) :=
  { x : Arity PSet.{u} n // Arity.Equiv x x }

instance Resp.inhabited {n} : Inhabited (Resp n) :=
  ⟨⟨Arity.const default _, Arity.equiv_const _⟩⟩

/-- The `n`-ary image of a `(n + 1)`-ary function respecting equivalence as a function respecting
equivalence. -/
def Resp.f {n} (f : Resp (n + 1)) (x : PSet) : Resp n :=
  ⟨f.1 x, f.2 _ _ <| Equiv.refl x⟩

/-- Function equivalence for functions respecting equivalence. See `pSet.arity.equiv`. -/
def Resp.Equiv {n} (a b : Resp n) : Prop :=
  Arity.Equiv a.1 b.1

protected theorem Resp.Equiv.refl {n} (a : Resp n) : Resp.Equiv a a :=
  a.2

protected theorem Resp.Equiv.euc : ∀ {n} {a b c : Resp n}, Resp.Equiv a b → Resp.Equiv c b → Resp.Equiv a c
  | 0, a, b, c, hab, hcb => Equiv.euc hab hcb
  | n + 1, a, b, c, hab, hcb => fun x y h =>
    @resp.equiv.euc n (a.f x) (b.f y) (c.f y) (hab _ _ h) (hcb _ _ <| Equiv.refl y)

protected theorem Resp.Equiv.symm {n} {a b : Resp n} : Resp.Equiv a b → Resp.Equiv b a :=
  (Resp.Equiv.refl b).euc

protected theorem Resp.Equiv.trans {n} {x y z : Resp n} (h1 : Resp.Equiv x y) (h2 : Resp.Equiv y z) : Resp.Equiv x z :=
  h1.euc h2.symm

instance Resp.setoid {n} : Setoidₓ (Resp n) :=
  ⟨Resp.Equiv, Resp.Equiv.refl, fun x y => Resp.Equiv.symm, fun x y z => Resp.Equiv.trans⟩

end PSet

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
def Setₓ : Type (u + 1) :=
  Quotientₓ PSet.setoid.{u}

namespace PSet

namespace Resp

/-- Helper function for `pSet.eval`. -/
def evalAux : ∀ {n}, { f : Resp n → Arity Setₓ.{u} n // ∀ a b : Resp n, Resp.Equiv a b → f a = f b }
  | 0 => ⟨fun a => ⟦a.1⟧, fun a b h => Quotientₓ.sound h⟩
  | n + 1 =>
    let F : Resp (n + 1) → Arity Setₓ (n + 1) := fun a =>
      @Quotientₓ.lift _ _ PSet.setoid (fun x => eval_aux.1 (a.f x)) fun b c h => eval_aux.2 _ _ (a.2 _ _ h)
    ⟨F, fun b c h =>
      funext <|
        (@Quotientₓ.ind _ _ fun q => F b q = F c q) fun z =>
          eval_aux.2 (Resp.f b z) (Resp.f c z) (h _ _ (PSet.Equiv.refl z))⟩

/-- An equivalence-respecting function yields an n-ary ZFC set function. -/
def eval (n) : Resp n → Arity Setₓ.{u} n :=
  evalAux.1

theorem eval_val {n f x} : (@eval (n + 1) f : Setₓ → Arity Setₓ n) ⟦x⟧ = eval n (Resp.f f x) :=
  rfl

end Resp

/-- A set function is "definable" if it is the image of some n-ary pre-set
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
class inductive Definable (n) : Arity Setₓ.{u} n → Type (u + 1)
  | mk (f) : definable (Resp.eval n f)

attribute [instance] definable.mk

/-- The evaluation of a function respecting equivalence is definable, by that same function. -/
def Definable.eqMk {n} (f) : ∀ {s : Arity Setₓ.{u} n} (H : Resp.eval _ f = s), Definable n s
  | _, rfl => ⟨f⟩

/-- Turns a definable function into a function that respects equivalence. -/
def Definable.resp {n} : ∀ (s : Arity Setₓ.{u} n) [Definable n s], Resp n
  | _, ⟨f⟩ => f

theorem Definable.eq {n} : ∀ (s : Arity Setₓ.{u} n) [H : Definable n s], (@Definable.resp n s H).eval _ = s
  | _, ⟨f⟩ => rfl

end PSet

namespace Classical

open PSet

/-- All functions are classically definable. -/
noncomputable def allDefinable : ∀ {n} (F : Arity Setₓ.{u} n), Definable n F
  | 0, F =>
    let p := @Quotientₓ.exists_rep PSet _ F
    Definable.eqMk ⟨some p, Equiv.rfl⟩ (some_spec p)
  | n + 1, (F : Arity Setₓ.{u} (n + 1)) => by
    have I := fun x => all_definable (F x)
    refine' definable.eq_mk ⟨fun x : PSet => (@definable.resp _ _ (I ⟦x⟧)).1, _⟩ _
    · dsimp' [← arity.equiv]
      intro x y h
      rw [@Quotientₓ.sound PSet _ _ _ h]
      exact (definable.resp (F ⟦y⟧)).2
      
    refine' funext fun q => (Quotientₓ.induction_on q) fun x => _
    simp_rw [resp.eval_val, resp.f, Subtype.val_eq_coe, Subtype.coe_eta]
    exact @definable.eq _ (F ⟦x⟧) (I ⟦x⟧)

end Classical

namespace Setₓ

open PSet

/-- Turns a pre-set into a ZFC set. -/
def mk : PSet → Setₓ :=
  Quotientₓ.mk

@[simp]
theorem mk_eq (x : PSet) : @Eq Setₓ ⟦x⟧ (mk x) :=
  rfl

@[simp]
theorem mk_out : ∀ x : Setₓ, mk x.out = x :=
  Quotientₓ.out_eq

theorem eq {x y : PSet} : mk x = mk y ↔ Equivₓ x y :=
  Quotientₓ.eq

theorem sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y :=
  Quotientₓ.sound h

theorem exact {x y : PSet} : mk x = mk y → PSet.Equiv x y :=
  Quotientₓ.exact

@[simp]
theorem eval_mk {n f x} : (@Resp.eval (n + 1) f : Setₓ → Arity Setₓ n) (mk x) = Resp.eval n (Resp.f f x) :=
  rfl

/-- The membership relation for ZFC sets is inherited from the membership relation for pre-sets. -/
protected def Mem : Setₓ → Setₓ → Prop :=
  Quotientₓ.lift₂ PSet.Mem fun x y x' y' hx hy => propext ((Mem.congr_left hx).trans (Mem.congr_right hy))

instance : HasMem Setₓ Setₓ :=
  ⟨Setₓ.Mem⟩

/-- Convert a ZFC set into a `set` of ZFC sets -/
def ToSet (u : Setₓ.{u}) : Set Setₓ.{u} :=
  { x | x ∈ u }

/-- `x ⊆ y` as ZFC sets means that all members of `x` are members of `y`. -/
protected def Subset (x y : Setₓ.{u}) :=
  ∀ ⦃z⦄, z ∈ x → z ∈ y

instance hasSubset : HasSubset Setₓ :=
  ⟨Setₓ.Subset⟩

theorem subset_def {x y : Setₓ.{u}} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y :=
  Iff.rfl

@[simp]
theorem subset_iff : ∀ x y : PSet, mk x ⊆ mk y ↔ x ⊆ y
  | ⟨α, A⟩, ⟨β, B⟩ =>
    ⟨fun h a => @h ⟦A a⟧ (Mem.mk A a), fun h z =>
      Quotientₓ.induction_on z fun z ⟨a, za⟩ =>
        let ⟨b, ab⟩ := h a
        ⟨b, za.trans ab⟩⟩

theorem ext {x y : Setₓ.{u}} : (∀ z : Setₓ.{u}, z ∈ x ↔ z ∈ y) → x = y :=
  Quotientₓ.induction_on₂ x y fun u v h => Quotientₓ.sound (Mem.ext fun w => h ⟦w⟧)

theorem ext_iff {x y : Setₓ.{u}} : (∀ z : Setₓ.{u}, z ∈ x ↔ z ∈ y) ↔ x = y :=
  ⟨ext, fun h => by
    simp [← h]⟩

/-- The empty ZFC set -/
protected def empty : Setₓ :=
  mk ∅

instance : HasEmptyc Setₓ :=
  ⟨Setₓ.empty⟩

instance : Inhabited Setₓ :=
  ⟨∅⟩

@[simp]
theorem mem_empty (x) : x ∉ (∅ : Setₓ.{u}) :=
  Quotientₓ.induction_on x PSet.mem_empty

theorem eq_empty (x : Setₓ.{u}) : x = ∅ ↔ ∀ y : Setₓ.{u}, y ∉ x :=
  ⟨fun h y => h.symm ▸ mem_empty y, fun h =>
    ext fun y => ⟨fun yx => absurd yx (h y), fun y0 => absurd y0 (mem_empty _)⟩⟩

/-- `insert x y` is the set `{x} ∪ y` -/
protected def insert : Setₓ → Setₓ → Setₓ :=
  Resp.eval 2
    ⟨PSet.insert, fun u v uv ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun o =>
        match o with
        | some a =>
          let ⟨b, hb⟩ := αβ a
          ⟨some b, hb⟩
        | none => ⟨none, uv⟩,
        fun o =>
        match o with
        | some b =>
          let ⟨a, ha⟩ := βα b
          ⟨some a, ha⟩
        | none => ⟨none, uv⟩⟩⟩

instance : HasInsert Setₓ Setₓ :=
  ⟨Setₓ.insert⟩

instance : HasSingleton Setₓ Setₓ :=
  ⟨fun x => insert x ∅⟩

instance : IsLawfulSingleton Setₓ Setₓ :=
  ⟨fun x => rfl⟩

@[simp]
theorem mem_insert {x y z : Setₓ.{u}} : x ∈ insert y z ↔ x = y ∨ x ∈ z :=
  Quotientₓ.induction_on₃ x y z fun x y ⟨α, A⟩ =>
    show (x ∈ PSet.mk (Option α) fun o => Option.rec y A o) ↔ mk x = mk y ∨ x ∈ PSet.mk α A from
      ⟨fun m =>
        match m with
        | ⟨some a, ha⟩ => Or.inr ⟨a, ha⟩
        | ⟨none, h⟩ => Or.inl (Quotientₓ.sound h),
        fun m =>
        match m with
        | Or.inr ⟨a, ha⟩ => ⟨some a, ha⟩
        | Or.inl h => ⟨none, Quotientₓ.exact h⟩⟩

@[simp]
theorem mem_singleton {x y : Setₓ.{u}} : x ∈ @singleton Setₓ.{u} Setₓ.{u} _ y ↔ x = y :=
  Iff.trans mem_insert ⟨fun o => Or.ndrec (fun h => h) (fun n => absurd n (mem_empty _)) o, Or.inl⟩

@[simp]
theorem mem_pair {x y z : Setₓ.{u}} : x ∈ ({y, z} : Setₓ) ↔ x = y ∨ x = z :=
  Iff.trans mem_insert <| or_congr Iff.rfl mem_singleton

/-- `omega` is the first infinite von Neumann ordinal -/
def omega : Setₓ :=
  mk omega

@[simp]
theorem omega_zero : ∅ ∈ omega :=
  ⟨⟨0⟩, Equiv.rfl⟩

@[simp]
theorem omega_succ {n} : n ∈ omega.{u} → insert n n ∈ omega.{u} :=
  Quotientₓ.induction_on n fun x ⟨⟨n⟩, h⟩ =>
    ⟨⟨n + 1⟩,
      Setₓ.exact <|
        show insert (mk x) (mk x) = insert (mk <| ofNat n) (mk <| ofNat n) by
          rw [Setₓ.sound h]
          rfl⟩

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
protected def sep (p : Setₓ → Prop) : Setₓ → Setₓ :=
  Resp.eval 1
    ⟨PSet.sep fun y => p (mk y), fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by
            rwa [mk_func, ← Setₓ.sound hb]⟩,
          hb⟩,
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by
            rwa [mk_func, Setₓ.sound ha]⟩,
          ha⟩⟩⟩

instance : HasSep Setₓ Setₓ :=
  ⟨Setₓ.sep⟩

@[simp]
theorem mem_sep {p : Setₓ.{u} → Prop} {x y : Setₓ.{u}} : y ∈ { y ∈ x | p y } ↔ y ∈ x ∧ p y :=
  Quotientₓ.induction_on₂ x y fun ⟨α, A⟩ y =>
    ⟨fun ⟨⟨a, pa⟩, h⟩ =>
      ⟨⟨a, h⟩, by
        rwa [@Quotientₓ.sound PSet _ _ _ h]⟩,
      fun ⟨⟨a, h⟩, pa⟩ =>
      ⟨⟨a, by
          rw [mk_func] at h
          rwa [mk_func, ← Setₓ.sound h]⟩,
        h⟩⟩

/-- The powerset operation, the collection of subsets of a ZFC set -/
def powerset : Setₓ → Setₓ :=
  Resp.eval 1
    ⟨powerset, fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | ∃ a, p a ∧ Equivₓ (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨b, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | ∃ b, q b ∧ Equivₓ (A a) (B b) }, fun ⟨a, b, qb, ab⟩ => ⟨⟨b, qb⟩, ab⟩, fun ⟨b, qb⟩ =>
          let ⟨a, ab⟩ := βα b
          ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩⟩

@[simp]
theorem mem_powerset {x y : Setₓ.{u}} : y ∈ powerset x ↔ y ⊆ x :=
  Quotientₓ.induction_on₂ x y fun ⟨α, A⟩ ⟨β, B⟩ =>
    show (⟨β, B⟩ : PSet.{u}) ∈ PSet.powerset.{u} ⟨α, A⟩ ↔ _ by
      simp [← mem_powerset, ← subset_iff]

theorem Union_lem {α β : Type u} (A : α → PSet) (B : β → PSet) (αβ : ∀ a, ∃ b, Equivₓ (A a) (B b)) :
    ∀ a, ∃ b, Equivₓ ((union ⟨α, A⟩).func a) ((union ⟨β, B⟩).func b)
  | ⟨a, c⟩ => by
    let ⟨b, hb⟩ := αβ a
    induction' ea : A a with γ Γ
    induction' eb : B b with δ Δ
    rw [ea, eb] at hb
    cases' hb with γδ δγ
    exact
      let c : type (A a) := c
      let ⟨d, hd⟩ :=
        γδ
          (by
            rwa [ea] at c)
      have : PSet.Equiv ((A a).func c) ((B b).func (Eq.ndrec d (Eq.symm eb))) :=
        match A a, B b, ea, eb, c, d, hd with
        | _, _, rfl, rfl, x, y, hd => hd
      ⟨⟨b, by
          rw [mk_func]
          exact Eq.ndrec d (Eq.symm eb)⟩,
        this⟩

/-- The union operator, the collection of elements of elements of a ZFC set -/
def union : Setₓ → Setₓ :=
  Resp.eval 1
    ⟨PSet.union, fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨Union_lem A B αβ, fun a =>
        Exists.elim (Union_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a) fun b hb =>
          ⟨b, PSet.Equiv.symm hb⟩⟩⟩

-- mathport name: «expr⋃»
notation "⋃" => union

@[simp]
theorem mem_Union {x y : Setₓ.{u}} : y ∈ union x ↔ ∃ z ∈ x, y ∈ z :=
  Quotientₓ.induction_on₂ x y fun x y =>
    Iff.trans mem_Union ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotientₓ.induction_on z (fun z h => ⟨z, h⟩) h⟩

@[simp]
theorem Union_singleton {x : Setₓ.{u}} : union {x} = x :=
  ext fun y => by
    simp_rw [mem_Union, exists_prop, mem_singleton, exists_eq_left]

theorem singleton_inj {x y : Setₓ.{u}} (H : ({x} : Setₓ) = {y}) : x = y := by
  let this := congr_arg union H
  rwa [Union_singleton, Union_singleton] at this

/-- The binary union operation -/
protected def unionₓ (x y : Setₓ.{u}) : Setₓ.{u} :=
  ⋃ {x, y}

/-- The binary intersection operation -/
protected def inter (x y : Setₓ.{u}) : Setₓ.{u} :=
  { z ∈ x | z ∈ y }

/-- The set difference operation -/
protected def diff (x y : Setₓ.{u}) : Setₓ.{u} :=
  { z ∈ x | z ∉ y }

instance : HasUnion Setₓ :=
  ⟨Setₓ.unionₓ⟩

instance : HasInter Setₓ :=
  ⟨Setₓ.inter⟩

instance : HasSdiff Setₓ :=
  ⟨Setₓ.diff⟩

@[simp]
theorem mem_union {x y z : Setₓ.{u}} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y :=
  Iff.trans mem_Union
    ⟨fun ⟨w, wxy, zw⟩ =>
      match mem_pair.1 wxy with
      | Or.inl wx =>
        Or.inl
          (by
            rwa [← wx])
      | Or.inr wy =>
        Or.inr
          (by
            rwa [← wy]),
      fun zxy =>
      match zxy with
      | Or.inl zx => ⟨x, mem_pair.2 (Or.inl rfl), zx⟩
      | Or.inr zy => ⟨y, mem_pair.2 (Or.inr rfl), zy⟩⟩

@[simp]
theorem mem_inter {x y z : Setₓ.{u}} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y :=
  @mem_sep fun z : Setₓ.{u} => z ∈ y

@[simp]
theorem mem_diff {x y z : Setₓ.{u}} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y :=
  @mem_sep fun z : Setₓ.{u} => z ∉ y

theorem induction_on {p : Setₓ → Prop} (x) (h : ∀ x, (∀, ∀ y ∈ x, ∀, p y) → p x) : p x :=
  (Quotientₓ.induction_on x) fun u =>
    (PSet.recOn u) fun α A IH =>
      (h _) fun y =>
        show @HasMem.Mem _ _ Setₓ.hasMem y ⟦⟨α, A⟩⟧ → p y from
          Quotientₓ.induction_on y fun v ⟨a, ha⟩ => by
            rw [@Quotientₓ.sound PSet _ _ _ ha]
            exact IH a

theorem regularity (x : Setₓ.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
  Classical.by_contradiction fun ne =>
    h <|
      (eq_empty x).2 fun y =>
        (induction_on y) fun z (IH : ∀ w : Setₓ.{u}, w ∈ z → w ∉ x) =>
          show z ∉ x from fun zx =>
            Ne
              ⟨z, zx,
                (eq_empty _).2 fun w wxz =>
                  let ⟨wx, wz⟩ := mem_inter.1 wxz
                  IH w wz wx⟩

/-- The image of a (definable) ZFC set function -/
def image (f : Setₓ → Setₓ) [H : Definable 1 f] : Setₓ → Setₓ :=
  let r := @Definable.resp 1 f _
  Resp.eval 1
    ⟨image r.1, fun x y e =>
      mem.ext fun z =>
        Iff.trans (mem_image r.2) <|
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
                ⟨w, (mem.congr_right e).2 h1, h2⟩⟩ <|
            Iff.symm (mem_image r.2)⟩

theorem image.mk : ∀ (f : Setₓ.{u} → Setₓ.{u}) [H : Definable 1 f] (x) {y} (h : y ∈ x), f y ∈ @image f H x
  | _, ⟨F⟩, x, y => (Quotientₓ.induction_on₂ x y) fun ⟨α, A⟩ y ⟨a, ya⟩ => ⟨a, F.2 _ _ ya⟩

@[simp]
theorem mem_image :
    ∀ {f : Setₓ.{u} → Setₓ.{u}} [H : Definable 1 f] {x y : Setₓ.{u}}, y ∈ @image f H x ↔ ∃ z ∈ x, f z = y
  | _, ⟨F⟩, x, y =>
    (Quotientₓ.induction_on₂ x y) fun ⟨α, A⟩ y =>
      ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, Eq.symm <| Quotientₓ.sound ya⟩, fun ⟨z, hz, e⟩ => e ▸ image.mk _ _ hz⟩

/-- Kuratowski ordered pair -/
def pair (x y : Setₓ.{u}) : Setₓ.{u} :=
  {{x}, {x, y}}

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
def pairSep (p : Setₓ.{u} → Setₓ.{u} → Prop) (x y : Setₓ.{u}) : Setₓ.{u} :=
  { z ∈ powerset (powerset (x ∪ y)) | ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b }

@[simp]
theorem mem_pair_sep {p} {x y z : Setₓ.{u}} : z ∈ pairSep p x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b := by
  refine' mem_sep.trans ⟨And.right, fun e => ⟨_, e⟩⟩
  rcases e with ⟨a, ax, b, bY, rfl, pab⟩
  simp only [← mem_powerset, ← subset_def, ← mem_union, ← pair, ← mem_pair]
  rintro u (rfl | rfl) v <;> simp only [← mem_singleton, ← mem_pair]
  · rintro rfl
    exact Or.inl ax
    
  · rintro (rfl | rfl) <;> [left, right] <;> assumption
    

theorem pair_inj {x y x' y' : Setₓ.{u}} (H : pair x y = pair x' y') : x = x' ∧ y = y' := by
  have ae := ext_iff.2 H
  simp only [← pair, ← mem_pair] at ae
  obtain rfl : x = x' := by
    cases'
      (ae {x}).1
        (by
          simp ) with
      h h
    · exact singleton_inj h
      
    · have m : x' ∈ ({x} : Setₓ) := by
        simp [← h]
      rw [mem_singleton.mp m]
      
  have he : x = y → y = y' := by
    rintro rfl
    cases'
      (ae {x, y'}).2
        (by
          simp only [← eq_self_iff_true, ← or_trueₓ]) with
      xy'x xy'xx
    · rw [eq_comm, ← mem_singleton, ← xy'x, mem_pair]
      exact Or.inr rfl
      
    · simpa [← eq_comm] using
        (ext_iff.2 xy'xx y').1
          (by
            simp )
      
  obtain xyx | xyy' :=
    (ae {x, y}).1
      (by
        simp )
  · obtain rfl :=
      mem_singleton.mp
        ((ext_iff.2 xyx y).1 <| by
          simp )
    simp [← he rfl]
    
  · obtain rfl | yy' :=
      mem_pair.mp
        ((ext_iff.2 xyy' y).1 <| by
          simp )
    · simp [← he rfl]
      
    · simp [← yy']
      
    

/-- The cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
def prod : Setₓ.{u} → Setₓ.{u} → Setₓ.{u} :=
  pairSep fun a b => True

@[simp]
theorem mem_prod {x y z : Setₓ.{u}} : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b := by
  simp [← Prod]

@[simp]
theorem pair_mem_prod {x y a b : Setₓ.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y :=
  ⟨fun h =>
    let ⟨a', a'x, b', b'y, e⟩ := mem_prod.1 h
    match a', b', pair_inj e, a'x, b'y with
    | _, _, ⟨rfl, rfl⟩, ax, bY => ⟨ax, bY⟩,
    fun ⟨ax, bY⟩ => mem_prod.2 ⟨a, ax, b, bY, rfl⟩⟩

/-- `is_func x y f` is the assertion that `f` is a subset of `x × y` which relates to each element
of `x` a unique element of `y`, so that we can consider `f`as a ZFC function `x → y`. -/
def IsFunc (x y f : Setₓ.{u}) : Prop :=
  f ⊆ prod x y ∧ ∀ z : Setₓ.{u}, z ∈ x → ∃! w, pair z w ∈ f

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
def funs (x y : Setₓ.{u}) : Setₓ.{u} :=
  { f ∈ powerset (prod x y) | IsFunc x y f }

@[simp]
theorem mem_funs {x y f : Setₓ.{u}} : f ∈ funs x y ↔ IsFunc x y f := by
  simp [← funs, ← is_func]

-- TODO(Mario): Prove this computably
noncomputable instance mapDefinableAux (f : Setₓ → Setₓ) [H : Definable 1 f] : Definable 1 fun y => pair y (f y) :=
  @Classical.allDefinable 1 _

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
noncomputable def map (f : Setₓ → Setₓ) [H : Definable 1 f] : Setₓ → Setₓ :=
  image fun y => pair y (f y)

@[simp]
theorem mem_map {f : Setₓ → Setₓ} [H : Definable 1 f] {x y : Setₓ} : y ∈ map f x ↔ ∃ z ∈ x, pair z (f z) = y :=
  mem_image

theorem map_unique {f : Setₓ.{u} → Setₓ.{u}} [H : Definable 1 f] {x z : Setₓ.{u}} (zx : z ∈ x) :
    ∃! w, pair z w ∈ map f x :=
  ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, wx, we⟩ := mem_image.1 yx
    let ⟨wz, fy⟩ := pair_inj we
    rw [← fy, wz]⟩

@[simp]
theorem map_is_func {f : Setₓ → Setₓ} [H : Definable 1 f] {x y : Setₓ} :
    IsFunc x y (map f x) ↔ ∀, ∀ z ∈ x, ∀, f z ∈ y :=
  ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨t, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun y yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun z => map_unique⟩⟩

end Setₓ

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler has_sep Set
-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler has_insert Set
/-- The collection of all classes. A class is defined as a `set` of ZFC sets. -/
def Class :=
  Set Setₓ deriving HasSubset,
  «./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler has_sep Set», HasEmptyc, Inhabited,
  «./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler has_insert Set», HasUnion, HasInter,
  HasCompl, HasSdiff

namespace Class

/-- Coerce a ZFC set into a class -/
def OfSet (x : Setₓ.{u}) : Class.{u} :=
  { y | y ∈ x }

instance : Coe Setₓ Class :=
  ⟨OfSet⟩

/-- The universal class -/
def Univ : Class :=
  Set.Univ

/-- Assert that `A` is a ZFC set satisfying `p` -/
def ToSet (p : Setₓ.{u} → Prop) (A : Class.{u}) : Prop :=
  ∃ x, ↑x = A ∧ p x

/-- `A ∈ B` if `A` is a ZFC set which is a member of `B` -/
protected def Mem (A B : Class.{u}) : Prop :=
  ToSet.{u} B A

instance : HasMem Class Class :=
  ⟨Class.Mem⟩

theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : Setₓ.{u}, ↑x = A :=
  exists_congr fun x => and_trueₓ _

/-- Convert a conglomerate (a collection of classes) into a class -/
def CongToClass (x : Set Class.{u}) : Class.{u} :=
  { y | ↑y ∈ x }

/-- Convert a class into a conglomerate (a collection of classes) -/
def ClassToCong (x : Class.{u}) : Set Class.{u} :=
  { y | y ∈ x }

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def Powerset (x : Class) : Class :=
  CongToClass (Set.Powerset x)

/-- The union of a class is the class of all members of ZFC sets in the class -/
def Union (x : Class) : Class :=
  Set.SUnion (ClassToCong x)

-- mathport name: «expr⋃»
notation "⋃" => Union

theorem OfSet.inj {x y : Setₓ.{u}} (h : (x : Class.{u}) = y) : x = y :=
  Setₓ.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    rw [h]

@[simp]
theorem to_Set_of_Set (p : Setₓ.{u} → Prop) (x : Setₓ.{u}) : ToSet p x ↔ p x :=
  ⟨fun ⟨y, yx, py⟩ => by
    rwa [of_Set.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[simp]
theorem mem_hom_left (x : Setₓ.{u}) (A : Class.{u}) : (x : Class.{u}) ∈ A ↔ A x :=
  to_Set_of_Set _ _

@[simp]
theorem mem_hom_right (x y : Setₓ.{u}) : (y : Class.{u}) x ↔ x ∈ y :=
  Iff.rfl

@[simp]
theorem subset_hom (x y : Setₓ.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl

@[simp]
theorem sep_hom (p : Setₓ.{u} → Prop) (x : Setₓ.{u}) : (↑({ y ∈ x | p y }) : Class.{u}) = { y ∈ x | p y } :=
  Set.ext fun y => Setₓ.mem_sep

@[simp]
theorem empty_hom : ↑(∅ : Setₓ.{u}) = (∅ : Class.{u}) :=
  Set.ext fun y => (iff_falseₓ _).2 (Setₓ.mem_empty y)

@[simp]
theorem insert_hom (x y : Setₓ.{u}) : @insert Setₓ.{u} Class.{u} _ x y = ↑(insert x y) :=
  Set.ext fun z => Iff.symm Setₓ.mem_insert

@[simp]
theorem union_hom (x y : Setₓ.{u}) : (x : Class.{u}) ∪ y = (x ∪ y : Setₓ.{u}) :=
  Set.ext fun z => Iff.symm Setₓ.mem_union

@[simp]
theorem inter_hom (x y : Setₓ.{u}) : (x : Class.{u}) ∩ y = (x ∩ y : Setₓ.{u}) :=
  Set.ext fun z => Iff.symm Setₓ.mem_inter

@[simp]
theorem diff_hom (x y : Setₓ.{u}) : (x : Class.{u}) \ y = (x \ y : Setₓ.{u}) :=
  Set.ext fun z => Iff.symm Setₓ.mem_diff

@[simp]
theorem powerset_hom (x : Setₓ.{u}) : Powerset.{u} x = Setₓ.powerset x :=
  Set.ext fun z => Iff.symm Setₓ.mem_powerset

@[simp]
theorem Union_hom (x : Setₓ.{u}) : Union.{u} x = Setₓ.union x :=
  Set.ext fun z => by
    refine' Iff.trans _ Set.mem_Union.symm
    exact ⟨fun ⟨_, ⟨a, rfl, ax⟩, za⟩ => ⟨a, ax, za⟩, fun ⟨a, ax, za⟩ => ⟨_, ⟨a, rfl, ax⟩, za⟩⟩

/-- The definite description operator, which is `{x}` if `{a | p a} = {x}` and `∅` otherwise. -/
def Iota (p : Setₓ → Prop) : Class :=
  Union { x | ∀ y, p y ↔ y = x }

theorem iota_val (p : Setₓ → Prop) (x : Setₓ) (H : ∀ y, p y ↔ y = x) : Iota p = ↑x :=
  Set.ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by
      rwa [← (H x').1 <| (h x').2 rfl], fun yx => ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `(Set → Prop) → Set` function. -/
theorem iota_ex (p) : Iota.{u} p ∈ univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x, ∀ y, p y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val p x h⟩) fun hn =>
      ⟨∅, Set.ext fun z => empty_hom.symm ▸ ⟨False.ndrec _, fun ⟨_, ⟨x, rfl, H⟩, zA⟩ => hn ⟨x, H⟩⟩⟩

/-- Function value -/
def Fval (F A : Class.{u}) : Class.{u} :=
  Iota fun y => ToSet (fun x => F (Setₓ.pair x y)) A

-- mathport name: «expr ′ »
infixl:100 "′" => Fval

theorem fval_ex (F A : Class.{u}) : F′A ∈ univ.{u} :=
  iota_ex _

end Class

namespace Setₓ

@[simp]
theorem map_fval {f : Setₓ.{u} → Setₓ.{u}} [H : PSet.Definable 1 f] {x y : Setₓ.{u}} (h : y ∈ x) :
    (Setₓ.map f x′y : Class.{u}) = f y :=
  Class.iota_val _ _ fun z => by
    rw [Class.to_Set_of_Set, Class.mem_hom_right, mem_map]
    exact
      ⟨fun ⟨w, wz, pr⟩ => by
        let ⟨wy, fw⟩ := Setₓ.pair_inj pr
        rw [← fw, wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩

variable (x : Setₓ.{u}) (h : ∅ ∉ x)

/-- A choice function on the class of nonempty ZFC sets. -/
noncomputable def choice : Setₓ :=
  @map (fun y => Classical.epsilon fun z => z ∈ y) (Classical.allDefinable _) x

include h

theorem choice_mem_aux (y : Setₓ.{u}) (yx : y ∈ x) : (Classical.epsilon fun z : Setₓ.{u} => z ∈ y) ∈ y :=
  (@Classical.epsilon_spec _ fun z : Setₓ.{u} => z ∈ y) <|
    Classical.by_contradiction fun n =>
      h <| by
        rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]

theorem choice_is_func : IsFunc x (union x) (choice x) :=
  (@map_is_func _ (Classical.allDefinable _) _ _).2 fun y yx => mem_Union.2 ⟨y, yx, choice_mem_aux x h y yx⟩

theorem choice_mem (y : Setₓ.{u}) (yx : y ∈ x) : (choice x′y : Class.{u}) ∈ (y : Class.{u}) := by
  delta' choice
  rw [map_fval yx, Class.mem_hom_left, Class.mem_hom_right]
  exact choice_mem_aux x h y yx

end Setₓ

