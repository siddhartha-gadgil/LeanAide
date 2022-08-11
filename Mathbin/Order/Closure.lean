/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathbin.Data.Set.Lattice
import Mathbin.Data.SetLike.Basic
import Mathbin.Order.GaloisConnection
import Mathbin.Order.Hom.Basic
import Mathbin.Tactic.Monotonicity.Default

/-!
# Closure operators between preorders

We define (bundled) closure operators on a preorder as monotone (increasing), extensive
(inflationary) and idempotent functions.
We define closed elements for the operator as elements which are fixed by it.

Lower adjoints to a function between preorders `u : β → α` allow to generalise closure operators to
situations where the closure operator we are dealing with naturally decomposes as `u ∘ l` where `l`
is a worthy function to have on its own. Typical examples include
`l : set G → subgroup G := subgroup.closure`, `u : subgroup G → set G := coe`, where `G` is a group.
This shows there is a close connection between closure operators, lower adjoints and Galois
connections/insertions: every Galois connection induces a lower adjoint which itself induces a
closure operator by composition (see `galois_connection.lower_adjoint` and
`lower_adjoint.closure_operator`), and every closure operator on a partial order induces a Galois
insertion from the set of closed elements to the underlying type (see `closure_operator.gi`).

## Main definitions

* `closure_operator`: A closure operator is a monotone function `f : α → α` such that
  `∀ x, x ≤ f x` and `∀ x, f (f x) = f x`.
* `lower_adjoint`: A lower adjoint to `u : β → α` is a function `l : α → β` such that `l` and `u`
  form a Galois connection.

## Implementation details

Although `lower_adjoint` is technically a generalisation of `closure_operator` (by defining
`to_fun := id`), it is desirable to have both as otherwise `id`s would be carried all over the
place when using concrete closure operators such as `convex_hull`.

`lower_adjoint` really is a semibundled `structure` version of `galois_connection`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets
-/


universe u

/-! ### Closure operator -/


variable (α : Type _) {ι : Sort _} {κ : ι → Sort _}

/-- A closure operator on the preorder `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent. -/
structure ClosureOperator [Preorderₓ α] extends α →o α where
  le_closure' : ∀ x, x ≤ to_fun x
  idempotent' : ∀ x, to_fun (to_fun x) = to_fun x

namespace ClosureOperator

instance [Preorderₓ α] : CoeFun (ClosureOperator α) fun _ => α → α :=
  ⟨fun c => c.toFun⟩

/-- See Note [custom simps projection] -/
def Simps.apply [Preorderₓ α] (f : ClosureOperator α) : α → α :=
  f

initialize_simps_projections ClosureOperator (to_order_hom_to_fun → apply, -toOrderHom)

section PartialOrderₓ

variable [PartialOrderₓ α]

/-- The identity function as a closure operator. -/
@[simps]
def id : ClosureOperator α where
  toOrderHom := OrderHom.id
  le_closure' := fun _ => le_rfl
  idempotent' := fun _ => rfl

instance : Inhabited (ClosureOperator α) :=
  ⟨id α⟩

variable {α} (c : ClosureOperator α)

@[ext]
theorem ext : ∀ c₁ c₂ : ClosureOperator α, (c₁ : α → α) = (c₂ : α → α) → c₁ = c₂
  | ⟨⟨c₁, _⟩, _, _⟩, ⟨⟨c₂, _⟩, _, _⟩, h => by
    congr
    exact h

/-- Constructor for a closure operator using the weaker idempotency axiom: `f (f x) ≤ f x`. -/
@[simps]
def mk' (f : α → α) (hf₁ : Monotone f) (hf₂ : ∀ x, x ≤ f x) (hf₃ : ∀ x, f (f x) ≤ f x) : ClosureOperator α where
  toFun := f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' := fun x => (hf₃ x).antisymm (hf₁ (hf₂ x))

/-- Convenience constructor for a closure operator using the weaker minimality axiom:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice. -/
@[simps]
def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) : ClosureOperator α where
  toFun := f
  monotone' := fun x y hxy => hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' := fun x => (hmin le_rfl).antisymm (hf _)

/-- Expanded out version of `mk₂`. `p` implies being closed. This constructor should be used when
you already know a sufficient condition for being closed and using `mem_mk₃_closed` will avoid you
the (slight) hassle of having to prove it both inside and outside the constructor. -/
@[simps]
def mk₃ (f : α → α) (p : α → Prop) (hf : ∀ x, x ≤ f x) (hfp : ∀ x, p (f x)) (hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y) :
    ClosureOperator α :=
  mk₂ f hf fun x y hxy => hmin hxy (hfp y)

/-- This lemma shows that the image of `x` of a closure operator built from the `mk₃` constructor
respects `p`, the property that was fed into it. -/
theorem closure_mem_mk₃ {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
    {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} (x : α) : p (mk₃ f p hf hfp hmin x) :=
  hfp x

/-- Analogue of `closure_le_closed_iff_le` but with the `p` that was fed into the `mk₃` constructor.
-/
theorem closure_le_mk₃_iff {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
    {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} {x y : α} (hxy : x ≤ y) (hy : p y) : mk₃ f p hf hfp hmin x ≤ y :=
  hmin hxy hy

@[mono]
theorem monotone : Monotone c :=
  c.monotone'

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
theorem le_closure (x : α) : x ≤ c x :=
  c.le_closure' x

@[simp]
theorem idempotent (x : α) : c (c x) = c x :=
  c.idempotent' x

theorem le_closure_iff (x y : α) : x ≤ c y ↔ c x ≤ c y :=
  ⟨fun h => c.idempotent y ▸ c.Monotone h, fun h => (c.le_closure x).trans h⟩

/-- An element `x` is closed for the closure operator `c` if it is a fixed point for it. -/
def Closed : Set α := fun x => c x = x

theorem mem_closed_iff (x : α) : x ∈ c.Closed ↔ c x = x :=
  Iff.rfl

theorem mem_closed_iff_closure_le (x : α) : x ∈ c.Closed ↔ c x ≤ x :=
  ⟨le_of_eqₓ, fun h => h.antisymm (c.le_closure x)⟩

theorem closure_eq_self_of_mem_closed {x : α} (h : x ∈ c.Closed) : c x = x :=
  h

@[simp]
theorem closure_is_closed (x : α) : c x ∈ c.Closed :=
  c.idempotent x

/-- The set of closed elements for `c` is exactly its range. -/
theorem closed_eq_range_close : c.Closed = Set.Range c :=
  Set.ext fun x =>
    ⟨fun h => ⟨x, h⟩, by
      rintro ⟨y, rfl⟩
      apply c.idempotent⟩

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def toClosed (x : α) : c.Closed :=
  ⟨c x, c.closure_is_closed x⟩

@[simp]
theorem closure_le_closed_iff_le (x : α) {y : α} (hy : c.Closed y) : c x ≤ y ↔ x ≤ y := by
  rw [← c.closure_eq_self_of_mem_closed hy, ← le_closure_iff]

/-- A closure operator is equal to the closure operator obtained by feeding `c.closed` into the
`mk₃` constructor. -/
theorem eq_mk₃_closed (c : ClosureOperator α) :
    c = mk₃ c c.Closed c.le_closure c.closure_is_closed fun x y hxy hy => (c.closure_le_closed_iff_le x hy).2 hxy := by
  ext
  rfl

/-- The property `p` fed into the `mk₃` constructor implies being closed. -/
theorem mem_mk₃_closed {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
    {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} {x : α} (hx : p x) : x ∈ (mk₃ f p hf hfp hmin).Closed :=
  (hmin le_rfl hx).antisymm (hf _)

end PartialOrderₓ

variable {α}

section OrderTop

variable [PartialOrderₓ α] [OrderTop α] (c : ClosureOperator α)

@[simp]
theorem closure_top : c ⊤ = ⊤ :=
  le_top.antisymm (c.le_closure _)

theorem top_mem_closed : ⊤ ∈ c.Closed :=
  c.closure_top

end OrderTop

theorem closure_inf_le [SemilatticeInf α] (c : ClosureOperator α) (x y : α) : c (x⊓y) ≤ c x⊓c y :=
  c.Monotone.map_inf_le _ _

section SemilatticeSup

variable [SemilatticeSup α] (c : ClosureOperator α)

theorem closure_sup_closure_le (x y : α) : c x⊔c y ≤ c (x⊔y) :=
  c.Monotone.le_map_sup _ _

theorem closure_sup_closure_left (x y : α) : c (c x⊔y) = c (x⊔y) :=
  ((c.le_closure_iff _ _).1 (sup_le (c.Monotone le_sup_left) (le_sup_right.trans (c.le_closure _)))).antisymm
    (c.Monotone (sup_le_sup_right (c.le_closure _) _))

theorem closure_sup_closure_right (x y : α) : c (x⊔c y) = c (x⊔y) := by
  rw [sup_comm, closure_sup_closure_left, sup_comm]

theorem closure_sup_closure (x y : α) : c (c x⊔c y) = c (x⊔y) := by
  rw [closure_sup_closure_left, closure_sup_closure_right]

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] (c : ClosureOperator α)

@[simp]
theorem closure_supr_closure (f : ι → α) : c (⨆ i, c (f i)) = c (⨆ i, f i) :=
  le_antisymmₓ ((c.le_closure_iff _ _).1 <| supr_le fun i => c.Monotone <| le_supr f i) <|
    c.Monotone <| supr_mono fun i => c.le_closure _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem closure_supr₂_closure (f : ∀ i, κ i → α) : c (⨆ (i) (j), c (f i j)) = c (⨆ (i) (j), f i j) :=
  le_antisymmₓ ((c.le_closure_iff _ _).1 <| supr₂_le fun i j => c.Monotone <| le_supr₂ i j) <|
    c.Monotone <| supr₂_mono fun i j => c.le_closure _

end CompleteLattice

end ClosureOperator

/-! ### Lower adjoint -/


variable {α} {β : Type _}

/-- A lower adjoint of `u` on the preorder `α` is a function `l` such that `l` and `u` form a Galois
connection. It allows us to define closure operators whose output does not match the input. In
practice, `u` is often `coe : β → α`. -/
structure LowerAdjoint [Preorderₓ α] [Preorderₓ β] (u : β → α) where
  toFun : α → β
  gc' : GaloisConnection to_fun u

namespace LowerAdjoint

variable (α)

/-- The identity function as a lower adjoint to itself. -/
@[simps]
protected def id [Preorderₓ α] : LowerAdjoint (id : α → α) where
  toFun := fun x => x
  gc' := GaloisConnection.id

variable {α}

instance [Preorderₓ α] : Inhabited (LowerAdjoint (id : α → α)) :=
  ⟨LowerAdjoint.id α⟩

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {u : β → α} (l : LowerAdjoint u)

instance : CoeFun (LowerAdjoint u) fun _ => α → β where coe := toFun

/-- See Note [custom simps projection] -/
def Simps.apply : α → β :=
  l

theorem gc : GaloisConnection l u :=
  l.gc'

@[ext]
theorem ext : ∀ l₁ l₂ : LowerAdjoint u, (l₁ : α → β) = (l₂ : α → β) → l₁ = l₂
  | ⟨l₁, _⟩, ⟨l₂, _⟩, h => by
    congr
    exact h

@[mono]
theorem monotone : Monotone (u ∘ l) :=
  l.gc.monotone_u.comp l.gc.monotone_l

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
theorem le_closure (x : α) : x ≤ u (l x) :=
  l.gc.le_u_l _

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [Preorderₓ β] {u : β → α} (l : LowerAdjoint u)

/-- Every lower adjoint induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps]
def closureOperator : ClosureOperator α where
  toFun := fun x => u (l x)
  monotone' := l.Monotone
  le_closure' := l.le_closure
  idempotent' := fun x => l.gc.u_l_u_eq_u (l x)

theorem idempotent (x : α) : u (l (u (l x))) = u (l x) :=
  l.ClosureOperator.idempotent _

theorem le_closure_iff (x y : α) : x ≤ u (l y) ↔ u (l x) ≤ u (l y) :=
  l.ClosureOperator.le_closure_iff _ _

end PartialOrderₓ

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {u : β → α} (l : LowerAdjoint u)

/-- An element `x` is closed for `l : lower_adjoint u` if it is a fixed point: `u (l x) = x` -/
def Closed : Set α := fun x => u (l x) = x

theorem mem_closed_iff (x : α) : x ∈ l.Closed ↔ u (l x) = x :=
  Iff.rfl

theorem closure_eq_self_of_mem_closed {x : α} (h : x ∈ l.Closed) : u (l x) = x :=
  h

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [PartialOrderₓ β] {u : β → α} (l : LowerAdjoint u)

theorem mem_closed_iff_closure_le (x : α) : x ∈ l.Closed ↔ u (l x) ≤ x :=
  l.ClosureOperator.mem_closed_iff_closure_le _

@[simp]
theorem closure_is_closed (x : α) : u (l x) ∈ l.Closed :=
  l.idempotent x

/-- The set of closed elements for `l` is the range of `u ∘ l`. -/
theorem closed_eq_range_close : l.Closed = Set.Range (u ∘ l) :=
  l.ClosureOperator.closed_eq_range_close

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def toClosed (x : α) : l.Closed :=
  ⟨u (l x), l.closure_is_closed x⟩

@[simp]
theorem closure_le_closed_iff_le (x : α) {y : α} (hy : l.Closed y) : u (l x) ≤ y ↔ x ≤ y :=
  l.ClosureOperator.closure_le_closed_iff_le x hy

end PartialOrderₓ

theorem closure_top [PartialOrderₓ α] [OrderTop α] [Preorderₓ β] {u : β → α} (l : LowerAdjoint u) : u (l ⊤) = ⊤ :=
  l.ClosureOperator.closure_top

theorem closure_inf_le [SemilatticeInf α] [Preorderₓ β] {u : β → α} (l : LowerAdjoint u) (x y : α) :
    u (l (x⊓y)) ≤ u (l x)⊓u (l y) :=
  l.ClosureOperator.closure_inf_le x y

section SemilatticeSup

variable [SemilatticeSup α] [Preorderₓ β] {u : β → α} (l : LowerAdjoint u)

theorem closure_sup_closure_le (x y : α) : u (l x)⊔u (l y) ≤ u (l (x⊔y)) :=
  l.ClosureOperator.closure_sup_closure_le x y

theorem closure_sup_closure_left (x y : α) : u (l (u (l x)⊔y)) = u (l (x⊔y)) :=
  l.ClosureOperator.closure_sup_closure_left x y

theorem closure_sup_closure_right (x y : α) : u (l (x⊔u (l y))) = u (l (x⊔y)) :=
  l.ClosureOperator.closure_sup_closure_right x y

theorem closure_sup_closure (x y : α) : u (l (u (l x)⊔u (l y))) = u (l (x⊔y)) :=
  l.ClosureOperator.closure_sup_closure x y

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [Preorderₓ β] {u : β → α} (l : LowerAdjoint u)

theorem closure_supr_closure (f : ι → α) : u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i)) :=
  l.ClosureOperator.closure_supr_closure _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem closure_supr₂_closure (f : ∀ i, κ i → α) : u (l <| ⨆ (i) (j), u (l <| f i j)) = u (l <| ⨆ (i) (j), f i j) :=
  l.ClosureOperator.closure_supr₂_closure _

end CompleteLattice

-- Lemmas for `lower_adjoint (coe : α → set β)`, where `set_like α β`
section CoeToSet

variable [SetLike α β] (l : LowerAdjoint (coe : α → Set β))

theorem subset_closure (s : Set β) : s ⊆ l s :=
  l.le_closure s

theorem not_mem_of_not_mem_closure {s : Set β} {P : β} (hP : P ∉ l s) : P ∉ s := fun h => hP (subset_closure _ s h)

theorem le_iff_subset (s : Set β) (S : α) : l s ≤ S ↔ s ⊆ S :=
  l.gc s S

theorem mem_iff (s : Set β) (x : β) : x ∈ l s ↔ ∀ S : α, s ⊆ S → x ∈ S := by
  simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← l.le_iff_subset]
  exact ⟨fun h S => h.trans, fun h => h _ le_rfl⟩

theorem eq_of_le {s : Set β} {S : α} (h₁ : s ⊆ S) (h₂ : S ≤ l s) : l s = S :=
  ((l.le_iff_subset _ _).2 h₁).antisymm h₂

theorem closure_union_closure_subset (x y : α) : (l x : Set β) ∪ l y ⊆ l (x ∪ y) :=
  l.closure_sup_closure_le x y

@[simp]
theorem closure_union_closure_left (x y : α) : (l (l x ∪ y) : Set β) = l (x ∪ y) :=
  l.closure_sup_closure_left x y

@[simp]
theorem closure_union_closure_right (x y : α) : l (x ∪ l y) = l (x ∪ y) :=
  SetLike.coe_injective (l.closure_sup_closure_right x y)

@[simp]
theorem closure_union_closure (x y : α) : l (l x ∪ l y) = l (x ∪ y) :=
  SetLike.coe_injective (l.ClosureOperator.closure_sup_closure x y)

@[simp]
theorem closure_Union_closure (f : ι → α) : l (⋃ i, l (f i)) = l (⋃ i, f i) :=
  SetLike.coe_injective <| l.closure_supr_closure _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem closure_Union₂_closure (f : ∀ i, κ i → α) : l (⋃ (i) (j), l (f i j)) = l (⋃ (i) (j), f i j) :=
  SetLike.coe_injective <| l.closure_supr₂_closure _

end CoeToSet

end LowerAdjoint

/-! ### Translations between `galois_connection`, `lower_adjoint`, `closure_operator` -/


variable {α}

/-- Every Galois connection induces a lower adjoint. -/
@[simps]
def GaloisConnection.lowerAdjoint [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    LowerAdjoint u where
  toFun := l
  gc' := gc

/-- Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps]
def GaloisConnection.closureOperator [PartialOrderₓ α] [Preorderₓ β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : ClosureOperator α :=
  gc.LowerAdjoint.ClosureOperator

/-- The set of closed elements has a Galois insertion to the underlying type. -/
def ClosureOperator.gi [PartialOrderₓ α] (c : ClosureOperator α) : GaloisInsertion c.toClosed coe where
  choice := fun x hx => ⟨x, hx.antisymm (c.le_closure x)⟩
  gc := fun x y => c.closure_le_closed_iff_le _ y.2
  le_l_u := fun x => c.le_closure _
  choice_eq := fun x hx => le_antisymmₓ (c.le_closure x) hx

/-- The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.
Note that the inverse in the opposite direction does not hold in general. -/
@[simp]
theorem closure_operator_gi_self [PartialOrderₓ α] (c : ClosureOperator α) : c.gi.gc.ClosureOperator = c := by
  ext x
  rfl

