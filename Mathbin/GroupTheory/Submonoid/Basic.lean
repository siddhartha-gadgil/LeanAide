/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathbin.GroupTheory.Subsemigroup.Basic

/-!
# Submonoids: definition and `complete_lattice` structure

This file defines bundled multiplicative and additive submonoids. We also define
a `complete_lattice` structure on `submonoid`s, define the closure of a set as the minimal submonoid
that includes this set, and prove a few results about extending properties from a dense set (i.e.
a set with `closure s = ⊤`) to the whole monoid, see `submonoid.dense_induction` and
`monoid_hom.of_mdense`.

## Main definitions

* `submonoid M`: the type of bundled submonoids of a monoid `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : set M)`.
* `add_submonoid M` : the type of bundled submonoids of an additive monoid `M`.

For each of the following definitions in the `submonoid` namespace, there is a corresponding
definition in the `add_submonoid` namespace.

* `submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `submonoid`.
* `submonoid.closure` :  monoid closure of a set, i.e., the least submonoid that includes the set.
* `submonoid.gi` : `closure : set M → submonoid M` and coercion `coe : submonoid M → set M`
  form a `galois_insertion`;
* `monoid_hom.eq_mlocus`: the submonoid of elements `x : M` such that `f x = g x`;
* `monoid_hom.of_mdense`:  if a map `f : M → N` between two monoids satisfies `f 1 = 1` and
  `f (x * y) = f x * f y` for `y` from some dense set `s`, then `f` is a monoid homomorphism.
  E.g., if `f : ℕ → M` satisfies `f 0 = 0` and `f (x + 1) = f x + f 1`, then `f` is an additive
  monoid homomorphism.

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

Note that `submonoid M` does not actually require `monoid M`, instead requiring only the weaker
`mul_one_class M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers. `submonoid` is implemented by extending `subsemigroup` requiring `one_mem'`.

## Tags
submonoid, submonoids
-/


variable {M : Type _} {N : Type _}

variable {A : Type _}

section NonAssoc

variable [MulOneClassₓ M] {s : Set M}

variable [AddZeroClassₓ A] {t : Set A}

/-- `one_mem_class S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
class OneMemClass (S : Type _) (M : outParam <| Type _) [One M] [SetLike S M] where
  one_mem : ∀ s : S, (1 : M) ∈ s

export OneMemClass (one_mem)

/-- `zero_mem_class S M` says `S` is a type of subsets `s ≤ M`, such that `0 ∈ s` for all `s`. -/
class ZeroMemClass (S : Type _) (M : outParam <| Type _) [Zero M] [SetLike S M] where
  zero_mem : ∀ s : S, (0 : M) ∈ s

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

section

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure Submonoid (M : Type _) [MulOneClassₓ M] extends Subsemigroup M where
  one_mem' : (1 : M) ∈ carrier

end

/-- A submonoid of a monoid `M` can be considered as a subsemigroup of that monoid. -/
add_decl_doc Submonoid.toSubsemigroup

/-- `submonoid_class S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)` -/
class SubmonoidClass (S : Type _) (M : outParam <| Type _) [MulOneClassₓ M] [SetLike S M] extends MulMemClass S M where
  one_mem : ∀ s : S, (1 : M) ∈ s

section

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure AddSubmonoid (M : Type _) [AddZeroClassₓ M] extends AddSubsemigroup M where
  zero_mem' : (0 : M) ∈ carrier

end

/-- An additive submonoid of an additive monoid `M` can be considered as an
additive subsemigroup of that additive monoid. -/
add_decl_doc AddSubmonoid.toAddSubsemigroup

/-- `add_submonoid_class S M` says `S` is a type of subsets `s ≤ M` that contain `0`
and are closed under `(+)` -/
class AddSubmonoidClass (S : Type _) (M : outParam <| Type _) [AddZeroClassₓ M] [SetLike S M] extends
  AddMemClass S M where
  zero_mem : ∀ s : S, (0 : M) ∈ s

attribute [to_additive] Submonoid SubmonoidClass

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SubmonoidClass.toOneMemClass (S : Type _) (M : outParam <| Type _) [MulOneClassₓ M]
    [SetLike S M] [h : SubmonoidClass S M] : OneMemClass S M :=
  { h with }

@[to_additive]
theorem pow_mem {M} [Monoidₓ M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} {x : M} (hx : x ∈ S) :
    ∀ n : ℕ, x ^ n ∈ S
  | 0 => by
    rw [pow_zeroₓ]
    exact OneMemClass.one_mem S
  | n + 1 => by
    rw [pow_succₓ]
    exact MulMemClass.mul_mem hx (pow_mem n)

namespace Submonoid

@[to_additive]
instance : SetLike (Submonoid M) M where
  coe := Submonoid.Carrier
  coe_injective' := fun p q h => by
    cases p <;> cases q <;> congr

@[to_additive]
instance : SubmonoidClass (Submonoid M) M where
  one_mem := Submonoid.one_mem'
  mul_mem := Submonoid.mul_mem'

/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection]"]
def Simps.Coe (S : Submonoid M) : Set M :=
  S

initialize_simps_projections Submonoid (Carrier → coe)

initialize_simps_projections AddSubmonoid (Carrier → coe)

@[simp, to_additive]
theorem mem_carrier {s : Submonoid M} {x : M} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

@[simp, to_additive]
theorem mem_mk {s : Set M} {x : M} (h_one) (h_mul) : x ∈ mk s h_one h_mul ↔ x ∈ s :=
  Iff.rfl

@[simp, to_additive]
theorem coe_set_mk {s : Set M} (h_one) (h_mul) : (mk s h_one h_mul : Set M) = s :=
  rfl

@[simp, to_additive]
theorem mk_le_mk {s t : Set M} (h_one) (h_mul) (h_one') (h_mul') : mk s h_one h_mul ≤ mk t h_one' h_mul' ↔ s ⊆ t :=
  Iff.rfl

/-- Two submonoids are equal if they have the same elements. -/
@[ext, to_additive "Two `add_submonoid`s are equal if they have the same elements."]
theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive submonoid replacing `carrier` with a set that is equal to it."]
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M where
  Carrier := s
  one_mem' := hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'

variable {S : Submonoid M}

@[simp, to_additive]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S)

/-- A submonoid contains the monoid's 1. -/
@[to_additive "An `add_submonoid` contains the monoid's 0."]
protected theorem one_mem : (1 : M) ∈ S :=
  one_mem S

/-- A submonoid is closed under multiplication. -/
@[to_additive "An `add_submonoid` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive "The additive submonoid `M` of the `add_monoid M`."]
instance : HasTop (Submonoid M) :=
  ⟨{ Carrier := Set.Univ, one_mem' := Set.mem_univ 1, mul_mem' := fun _ _ _ _ => Set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of an monoid `M`. -/
@[to_additive "The trivial `add_submonoid` `{0}` of an `add_monoid` `M`."]
instance : HasBot (Submonoid M) :=
  ⟨{ Carrier := {1}, one_mem' := Set.mem_singleton 1,
      mul_mem' := fun a b ha hb => by
        simp only [← Set.mem_singleton_iff] at *
        rw [ha, hb, mul_oneₓ] }⟩

@[to_additive]
instance : Inhabited (Submonoid M) :=
  ⟨⊥⟩

@[simp, to_additive]
theorem mem_bot {x : M} : x ∈ (⊥ : Submonoid M) ↔ x = 1 :=
  Set.mem_singleton_iff

@[simp, to_additive]
theorem mem_top (x : M) : x ∈ (⊤ : Submonoid M) :=
  Set.mem_univ x

@[simp, to_additive]
theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.Univ :=
  rfl

@[simp, to_additive]
theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} :=
  rfl

/-- The inf of two submonoids is their intersection. -/
@[to_additive "The inf of two `add_submonoid`s is their intersection."]
instance : HasInf (Submonoid M) :=
  ⟨fun S₁ S₂ =>
    { Carrier := S₁ ∩ S₂, one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩,
      mul_mem' := fun _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[simp, to_additive]
theorem coe_inf (p p' : Submonoid M) : ((p⊓p' : Submonoid M) : Set M) = p ∩ p' :=
  rfl

@[simp, to_additive]
theorem mem_inf {p p' : Submonoid M} {x : M} : x ∈ p⊓p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

@[to_additive]
instance : HasInfₓ (Submonoid M) :=
  ⟨fun s =>
    { Carrier := ⋂ t ∈ s, ↑t, one_mem' := Set.mem_bInter fun i h => i.one_mem,
      mul_mem' := fun x y hx hy =>
        Set.mem_bInter fun i h =>
          i.mul_mem
            (by
              apply Set.mem_Inter₂.1 hx i h)
            (by
              apply Set.mem_Inter₂.1 hy i h) }⟩

@[simp, norm_cast, to_additive]
theorem coe_Inf (S : Set (Submonoid M)) : ((inf S : Submonoid M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl

@[to_additive]
theorem mem_Inf {S : Set (Submonoid M)} {x : M} : x ∈ inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p :=
  Set.mem_Inter₂

@[to_additive]
theorem mem_infi {ι : Sort _} {S : ι → Submonoid M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [← infi, ← mem_Inf, ← Set.forall_range_iff]

@[simp, norm_cast, to_additive]
theorem coe_infi {ι : Sort _} {S : ι → Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [← infi, ← coe_Inf, ← Set.bInter_range]

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive "The `add_submonoid`s of an `add_monoid` form a complete lattice."]
instance : CompleteLattice (Submonoid M) :=
  { (completeLatticeOfInf (Submonoid M)) fun s =>
      IsGlb.of_image (fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe) is_glb_binfi with
    le := (· ≤ ·), lt := (· < ·), bot := ⊥, bot_le := fun S x hx => (mem_bot.1 hx).symm ▸ S.one_mem, top := ⊤,
    le_top := fun S x hx => mem_top x, inf := (·⊓·), inf := HasInfₓ.inf,
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩, inf_le_left := fun a b x => And.left,
    inf_le_right := fun a b x => And.right }

@[simp, to_additive]
theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M :=
  ⟨fun h =>
    ⟨fun x y =>
      have : ∀ i : M, i = 1 := fun i => mem_bot.mp <| Subsingleton.elimₓ (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun h =>
    ⟨fun x y =>
      Submonoid.ext fun i =>
        Subsingleton.elimₓ 1 i ▸ by
          simp [← Submonoid.one_mem]⟩⟩

@[simp, to_additive]
theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M :=
  not_iff_not.mp ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans not_nontrivial_iff_subsingleton.symm)

@[to_additive]
instance [Subsingleton M] : Unique (Submonoid M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elimₓ _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]
instance [Nontrivial M] : Nontrivial (Submonoid M) :=
  nontrivial_iff.mpr ‹_›

/-- The `submonoid` generated by a set. -/
@[to_additive "The `add_submonoid` generated by a set"]
def closure (s : Set M) : Submonoid M :=
  inf { S | s ⊆ S }

@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Submonoid M, s ⊆ S → x ∈ S :=
  mem_Inf

/-- The submonoid generated by a set includes the set. -/
@[simp, to_additive "The `add_submonoid` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx

@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h => hP (subset_closure h)

variable {S}

open Set

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[simp, to_additive "An additive submonoid `S` includes `closure s` if and only if it includes `s`"]
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => Inf_le h⟩

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive
      "Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,\nthen `closure s ≤ closure t`"]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure

@[to_additive]
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymmₓ (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator,
  to_additive
      "An induction principle for additive closure membership. If `p`\nholds for `0` and all elements of `s`, and is preserved under addition, then `p` holds for all\nelements of the additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (Hs : ∀, ∀ x ∈ s, ∀, p x) (H1 : p 1)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, Hmul, H1⟩).2 Hs h

/-- A dependent version of `submonoid.closure_induction`.  -/
@[elab_as_eliminator, to_additive "A dependent version of `add_submonoid.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop} (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (H1 : p 1 (one_mem _)) (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  exact closure_induction hx (fun x hx => ⟨_, Hs x hx⟩) ⟨_, H1⟩ fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ => ⟨_, Hmul _ _ _ _ hx hy⟩

/-- An induction principle for closure membership for predicates with two arguments.  -/
@[elab_as_eliminator,
  to_additive "An induction principle for additive closure membership for\npredicates with two arguments."]
theorem closure_induction₂ {p : M → M → Prop} {x} {y : M} (hx : x ∈ closure s) (hy : y ∈ closure s)
    (Hs : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, p x y) (H1_left : ∀ x, p 1 x) (H1_right : ∀ x, p x 1)
    (Hmul_left : ∀ x y z, p x z → p y z → p (x * y) z) (Hmul_right : ∀ x y z, p z x → p z y → p z (x * y)) : p x y :=
  closure_induction hx (fun x xs => closure_induction hy (Hs x xs) (H1_right x) fun z y h₁ h₂ => Hmul_right z _ _ h₁ h₂)
    (H1_left y) fun x z h₁ h₂ => Hmul_left _ _ _ h₁ h₂

/-- If `s` is a dense set in a monoid `M`, `submonoid.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[elab_as_eliminator,
  to_additive
      "If `s` is a dense set in an additive monoid `M`,\n`add_submonoid.closure s = ⊤`, then in order to prove that some predicate `p` holds for all `x : M`\nit suffices to verify `p x` for `x ∈ s`, verify `p 0`, and verify that `p x` and `p y` imply\n`p (x + y)`."]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤) (Hs : ∀, ∀ x ∈ s, ∀, p x) (H1 : p 1)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x := by
  have : ∀, ∀ x ∈ closure s, ∀, p x := fun x hx => closure_induction hx Hs H1 Hmul
  simpa [← hs] using this x

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : GaloisInsertion (@closure M _) coe where
  choice := fun s _ => closure s
  gc := fun s t => closure_le
  le_l_u := fun s => subset_closure
  choice_eq := fun s h => rfl

variable {M}

/-- Closure of a submonoid `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive submonoid `S` equals `S`"]
theorem closure_eq : closure (S : Set M) = S :=
  (Submonoid.gi M).l_u_eq S

@[simp, to_additive]
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Submonoid.gi M).gc.l_bot

@[simp, to_additive]
theorem closure_univ : closure (Univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤

@[to_additive]
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s⊔closure t :=
  (Submonoid.gi M).gc.l_sup

@[to_additive]
theorem closure_Union {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Submonoid.gi M).gc.l_supr

@[simp, to_additive]
theorem closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]

@[to_additive]
theorem mem_supr {ι : Sort _} (p : ι → Submonoid M) {m : M} : (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← closure_singleton_le_iff_mem, le_supr_iff]
  simp only [← closure_singleton_le_iff_mem]

@[to_additive]
theorem supr_eq_closure {ι : Sort _} (p : ι → Submonoid M) : (⨆ i, p i) = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Submonoid.closure_Union, Submonoid.closure_eq]

@[to_additive]
theorem disjoint_def {p₁ p₂ : Submonoid M} : Disjoint p₁ p₂ ↔ ∀ {x : M}, x ∈ p₁ → x ∈ p₂ → x = 1 :=
  show (∀ x, x ∈ p₁ ∧ x ∈ p₂ → x ∈ ({1} : Set M)) ↔ _ by
    simp

@[to_additive]
theorem disjoint_def' {p₁ p₂ : Submonoid M} : Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 :=
  disjoint_def.trans ⟨fun h x y hx hy hxy => h hx <| hxy.symm ▸ hy, fun h x hx hx' => h hx hx' rfl⟩

end Submonoid

namespace MonoidHom

variable [MulOneClassₓ N]

open Submonoid

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive submonoid of elements `x : M` such that `f x = g x`"]
def eqMlocus (f g : M →* N) : Submonoid M where
  Carrier := { x | f x = g x }
  one_mem' := by
    rw [Set.mem_set_of_eq, f.map_one, g.map_one]
  mul_mem' := fun x y (hx : _ = _) (hy : _ = _) => by
    simp [*]

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive]
theorem eq_on_mclosure {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqMlocus g from closure_le.2 h

@[to_additive]
theorem eq_of_eq_on_mtop {f g : M →* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g :=
  ext fun x => h trivialₓ

@[to_additive]
theorem eq_of_eq_on_mdense {s : Set M} (hs : closure s = ⊤) {f g : M →* N} (h : s.EqOn f g) : f = g :=
  eq_of_eq_on_mtop <| hs ▸ eq_on_mclosure h

end MonoidHom

end NonAssoc

section Assoc

variable [Monoidₓ M] [Monoidₓ N] {s : Set M}

section IsUnit

/-- The submonoid consisting of the units of a monoid -/
@[to_additive "The additive submonoid consisting of the additive units of an additive monoid"]
def IsUnit.submonoid (M : Type _) [Monoidₓ M] : Submonoid M where
  Carrier := SetOf IsUnit
  one_mem' := by
    simp only [← is_unit_one, ← Set.mem_set_of_eq]
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_set_of_eq] at *
    exact IsUnit.mul ha hb

@[to_additive]
theorem IsUnit.mem_submonoid_iff {M : Type _} [Monoidₓ M] (a : M) : a ∈ IsUnit.submonoid M ↔ IsUnit a := by
  change a ∈ SetOf IsUnit ↔ IsUnit a
  rw [Set.mem_set_of_eq]

end IsUnit

namespace MonoidHom

open Submonoid

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `monoid_hom.of_mdense` defines a monoid homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
def ofMdense {M N} [Monoidₓ M] [Monoidₓ N] {s : Set M} (f : M → N) (hs : closure s = ⊤) (h1 : f 1 = 1)
    (hmul : ∀ (x), ∀ y ∈ s, ∀, f (x * y) = f x * f y) : M →* N where
  toFun := f
  map_one' := h1
  map_mul' := fun x y =>
    dense_induction y hs (fun y hy x => hmul x y hy)
      (by
        simp [← h1])
      (fun y₁ y₂ h₁ h₂ x => by
        simp only [mul_assoc, ← h₁, ← h₂])
      x

/-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is the whole monoid.
Then `add_monoid_hom.of_mdense` defines an additive monoid homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc AddMonoidHom.ofMdense

@[simp, norm_cast, to_additive]
theorem coe_of_mdense (f : M → N) (hs : closure s = ⊤) (h1 hmul) : ⇑(ofMdense f hs h1 hmul) = f :=
  rfl

end MonoidHom

end Assoc

