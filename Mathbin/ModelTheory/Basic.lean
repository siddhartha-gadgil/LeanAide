/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.CategoryTheory.ConcreteCategory.Bundled
import Mathbin.Data.Fin.Tuple.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.Logic.Encodable.Basic
import Mathbin.Logic.Small
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `first_order.language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `first_order.language.Structure` interprets the symbols of a given `first_order.language` in the
  context of a given type.
* A `first_order.language.hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `first_order.language.embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.elementary_embedding`, denoted `M ↪ₑ[L] N`, is an embedding from the
  `L`-structure `M` to the `L`-structure `N` that commutes with the realizations of all formulas.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v u' v' w w'

open Cardinal

open Cardinal

namespace FirstOrder

/-! ### Languages and Structures -/


/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
-- intended to be used with explicit universe parameters
@[nolint check_univs]
structure Language where
  Functions : ℕ → Type u
  Relations : ℕ → Type v

/-- Used to define `first_order.language₂`. -/
@[simp]
def Sequence₂ (a₀ a₁ a₂ : Type u) : ℕ → Type u
  | 0 => a₀
  | 1 => a₁
  | 2 => a₂
  | _ => Pempty

namespace Sequence₂

variable (a₀ a₁ a₂ : Type u)

instance inhabited₀ [h : Inhabited a₀] : Inhabited (Sequence₂ a₀ a₁ a₂ 0) :=
  h

instance inhabited₁ [h : Inhabited a₁] : Inhabited (Sequence₂ a₀ a₁ a₂ 1) :=
  h

instance inhabited₂ [h : Inhabited a₂] : Inhabited (Sequence₂ a₀ a₁ a₂ 2) :=
  h

instance {n : ℕ} : IsEmpty (Sequence₂ a₀ a₁ a₂ (n + 3)) :=
  Pempty.is_empty

@[simp]
theorem lift_mk {i : ℕ} : Cardinal.lift (# (Sequence₂ a₀ a₁ a₂ i)) = # (Sequence₂ (ULift a₀) (ULift a₁) (ULift a₂) i) :=
  by
  rcases i with (_ | _ | _ | i) <;>
    simp only [← sequence₂, ← mk_ulift, ← mk_fintype, ← Fintype.card_of_is_empty, ← Nat.cast_zeroₓ, ← lift_zero]

@[simp]
theorem sum_card : (Cardinal.sum fun i => # (Sequence₂ a₀ a₁ a₂ i)) = # a₀ + # a₁ + # a₂ := by
  rw [sum_nat_eq_add_sum_succ, sum_nat_eq_add_sum_succ, sum_nat_eq_add_sum_succ]
  simp [← add_assocₓ]

end Sequence₂

namespace Language

/-- A constructor for languages with only constants, unary and binary functions, and
unary and binary relations. -/
@[simps]
protected def mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) : Language :=
  ⟨Sequence₂ c f₁ f₂, Sequence₂ Pempty r₁ r₂⟩

/-- The empty language has no symbols. -/
protected def empty : Language :=
  ⟨fun _ => Empty, fun _ => Empty⟩

instance : Inhabited Language :=
  ⟨Language.empty⟩

/-- The sum of two languages consists of the disjoint union of their symbols. -/
protected def sum (L : Language.{u, v}) (L' : Language.{u', v'}) : Language :=
  ⟨fun n => Sum (L.Functions n) (L'.Functions n), fun n => Sum (L.Relations n) (L'.Relations n)⟩

variable (L : Language.{u, v})

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance]
protected def Constants :=
  L.Functions 0

@[simp]
theorem constants_mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) : (Language.mk₂ c f₁ f₂ r₁ r₂).Constants = c :=
  rfl

/-- The type of symbols in a given language. -/
@[nolint has_inhabited_instance]
def Symbols :=
  Sum (Σl, L.Functions l) (Σl, L.Relations l)

/-- The cardinality of a language is the cardinality of its type of symbols. -/
def card : Cardinal :=
  # L.Symbols

/-- A language is countable when it has countably many symbols. -/
class Countable : Prop where
  card_le_aleph_0' : L.card ≤ ℵ₀

theorem card_le_aleph_0 [L.Countable] : L.card ≤ ℵ₀ :=
  countable.card_le_aleph_0'

/-- A language is relational when it has no function symbols. -/
class IsRelational : Prop where
  empty_functions : ∀ n, IsEmpty (L.Functions n)

/-- A language is algebraic when it has no relation symbols. -/
class IsAlgebraic : Prop where
  empty_relations : ∀ n, IsEmpty (L.Relations n)

/-- A language is countable when it has countably many symbols. -/
class CountableFunctions : Prop where
  card_functions_le_aleph_0' : # (Σl, L.Functions l) ≤ ℵ₀

theorem card_functions_le_aleph_0 [L.CountableFunctions] : # (Σl, L.Functions l) ≤ ℵ₀ :=
  countable_functions.card_functions_le_aleph_0'

variable {L} {L' : Language.{u', v'}}

theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun l => Cardinal.lift.{v} (# (L.Functions l))) +
        Cardinal.sum fun l => Cardinal.lift.{u} (# (L.Relations l)) :=
  by
  simp [← card, ← symbols]

instance [L.IsRelational] {n : ℕ} : IsEmpty (L.Functions n) :=
  IsRelational.empty_functions n

instance [L.IsAlgebraic] {n : ℕ} : IsEmpty (L.Relations n) :=
  IsAlgebraic.empty_relations n

instance is_relational_of_empty_functions {symb : ℕ → Type _} : IsRelational ⟨fun _ => Empty, symb⟩ :=
  ⟨fun _ => Empty.is_empty⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type _} : IsAlgebraic ⟨symb, fun _ => Empty⟩ :=
  ⟨fun _ => Empty.is_empty⟩

instance is_relational_empty : IsRelational Language.empty :=
  language.is_relational_of_empty_functions

instance is_algebraic_empty : IsAlgebraic Language.empty :=
  language.is_algebraic_of_empty_relations

instance is_relational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.Sum L') :=
  ⟨fun n => Sum.is_empty⟩

instance is_algebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.Sum L') :=
  ⟨fun n => Sum.is_empty⟩

instance is_relational_mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h0 : IsEmpty c] [h1 : IsEmpty f₁] [h2 : IsEmpty f₂] :
    IsRelational (Language.mk₂ c f₁ f₂ r₁ r₂) :=
  ⟨fun n => Nat.casesOn n h0 fun n => Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ => Pempty.is_empty⟩

instance is_algebraic_mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h1 : IsEmpty r₁] [h2 : IsEmpty r₂] :
    IsAlgebraic (Language.mk₂ c f₁ f₂ r₁ r₂) :=
  ⟨fun n => Nat.casesOn n Pempty.is_empty fun n => Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ => Pempty.is_empty⟩

instance subsingleton_mk₂_functions {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h0 : Subsingleton c] [h1 : Subsingleton f₁]
    [h2 : Subsingleton f₂] {n : ℕ} : Subsingleton ((Language.mk₂ c f₁ f₂ r₁ r₂).Functions n) :=
  Nat.casesOn n h0 fun n => Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun n => ⟨fun x => Pempty.elimₓ x⟩

instance subsingleton_mk₂_relations {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h1 : Subsingleton r₁] [h2 : Subsingleton r₂]
    {n : ℕ} : Subsingleton ((Language.mk₂ c f₁ f₂ r₁ r₂).Relations n) :=
  Nat.casesOn n ⟨fun x => Pempty.elimₓ x⟩ fun n =>
    Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun n => ⟨fun x => Pempty.elimₓ x⟩

theorem Encodable.countable [h : Encodable L.Symbols] : L.Countable :=
  ⟨Cardinal.encodable_iff.1 ⟨h⟩⟩

@[simp]
theorem empty_card : Language.empty.card = 0 := by
  simp [← card_eq_card_functions_add_card_relations]

instance countable_empty : Language.empty.Countable :=
  ⟨by
    simp ⟩

instance (priority := 100) Countable.countable_functions [L.Countable] : L.CountableFunctions :=
  ⟨by
    refine' lift_le_aleph_0.1 (trans _ L.card_le_aleph_0)
    rw [card, symbols, mk_sum]
    exact le_self_add⟩

theorem Encodable.countable_functions [h : Encodable (Σl, L.Functions l)] : L.CountableFunctions :=
  ⟨Cardinal.encodable_iff.1 ⟨h⟩⟩

instance (priority := 100) IsRelational.countable_functions [L.IsRelational] : L.CountableFunctions :=
  encodable.countable_functions

@[simp]
theorem card_functions_sum (i : ℕ) :
    # ((L.Sum L').Functions i) = (# (L.Functions i)).lift + Cardinal.lift.{u} (# (L'.Functions i)) := by
  simp [← language.sum]

@[simp]
theorem card_relations_sum (i : ℕ) :
    # ((L.Sum L').Relations i) = (# (L.Relations i)).lift + Cardinal.lift.{v} (# (L'.Relations i)) := by
  simp [← language.sum]

@[simp]
theorem card_sum : (L.Sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card := by
  simp only [← card_eq_card_functions_add_card_relations, ← card_functions_sum, ← card_relations_sum, ←
    sum_add_distrib', ← lift_add, ← lift_sum, ← lift_lift]
  rw [add_assocₓ, ← add_assocₓ (Cardinal.sum fun i => (# (L'.functions i)).lift),
    add_commₓ (Cardinal.sum fun i => (# (L'.functions i)).lift), add_assocₓ, add_assocₓ]

@[simp]
theorem card_mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) :
    (Language.mk₂ c f₁ f₂ r₁ r₂).card =
      Cardinal.lift.{v} (# c) + Cardinal.lift.{v} (# f₁) + Cardinal.lift.{v} (# f₂) + Cardinal.lift.{u} (# r₁) +
        Cardinal.lift.{u} (# r₂) :=
  by
  simp [← card_eq_card_functions_add_card_relations, ← add_assocₓ]

variable (L) (M : Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
@[ext]
class Structure where
  funMap : ∀ {n}, L.Functions n → (Finₓ n → M) → M
  rel_map : ∀ {n}, L.Relations n → (Finₓ n → M) → Prop

variable (N : Type w') [L.Structure M] [L.Structure N]

open Structure

/-- Used for defining `first_order.language.Theory.Model.inhabited`. -/
def trivialUnitStructure : L.Structure Unit :=
  ⟨default, default⟩

/-! ### Maps -/


/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
structure Hom where
  toFun : M → N
  map_fun' : ∀ {n} (f : L.Functions n) (x), to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r x → RelMap r (to_fun ∘ x) := by
    run_tac
      obviously

-- mathport name: «expr →[ ] »
localized [FirstOrder] notation:25 A " →[" L "] " B => FirstOrder.Language.Hom L A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
@[ancestor Function.Embedding]
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (to_fun ∘ x) ↔ RelMap r x := by
    run_tac
      obviously

-- mathport name: «expr ↪[ ] »
localized [FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (to_fun ∘ x) ↔ RelMap r x := by
    run_tac
      obviously

-- mathport name: «expr ≃[ ] »
localized [FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

variable {L M N} {P : Type _} [L.Structure P] {Q : Type _} [L.Structure Q]

instance : CoeTₓ L.Constants M :=
  ⟨fun c => funMap c default⟩

theorem fun_map_eq_coe_constants {c : L.Constants} {x : Finₓ 0 → M} : funMap c x = c :=
  congr rfl (funext Finₓ.elim0)

/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
theorem nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M :=
  h.map coe

/-- The function map for `first_order.language.Structure₂`. -/
def funMap₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (c' : c → M) (f₁' : f₁ → M → M) (f₂' : f₂ → M → M → M) :
    ∀ {n}, (Language.mk₂ c f₁ f₂ r₁ r₂).Functions n → (Finₓ n → M) → M
  | 0, f, _ => c' f
  | 1, f, x => f₁' f (x 0)
  | 2, f, x => f₂' f (x 0) (x 1)
  | n + 3, f, _ => Pempty.elimₓ f

/-- The relation map for `first_order.language.Structure₂`. -/
def RelMap₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (r₁' : r₁ → Set M) (r₂' : r₂ → M → M → Prop) :
    ∀ {n}, (Language.mk₂ c f₁ f₂ r₁ r₂).Relations n → (Finₓ n → M) → Prop
  | 0, r, _ => Pempty.elimₓ r
  | 1, r, x => x 0 ∈ r₁' r
  | 2, r, x => r₂' r (x 0) (x 1)
  | n + 3, r, _ => Pempty.elimₓ r

/-- A structure constructor to match `first_order.language₂`. -/
protected def Structure.mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (c' : c → M) (f₁' : f₁ → M → M) (f₂' : f₂ → M → M → M)
    (r₁' : r₁ → Set M) (r₂' : r₂ → M → M → Prop) : (Language.mk₂ c f₁ f₂ r₁ r₂).Structure M :=
  ⟨fun _ => funMap₂ c' f₁' f₂', fun _ => RelMap₂ r₁' r₂'⟩

namespace Structure

variable {c f₁ f₂ : Type u} {r₁ r₂ : Type v}

variable {c' : c → M} {f₁' : f₁ → M → M} {f₂' : f₂ → M → M → M}

variable {r₁' : r₁ → Set M} {r₂' : r₂ → M → M → Prop}

@[simp]
theorem fun_map_apply₀ (c₀ : c) {x : Finₓ 0 → M} :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 0 c₀ x = c' c₀ :=
  rfl

@[simp]
theorem fun_map_apply₁ (f : f₁) (x : M) : @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 1 f ![x] = f₁' f x :=
  rfl

@[simp]
theorem fun_map_apply₂ (f : f₂) (x y : M) :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 2 f ![x, y] = f₂' f x y :=
  rfl

@[simp]
theorem rel_map_apply₁ (r : r₁) (x : M) :
    @Structure.RelMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 1 r ![x] = (x ∈ r₁' r) :=
  rfl

@[simp]
theorem rel_map_apply₂ (r : r₂) (x y : M) :
    @Structure.RelMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 2 r ![x, y] = r₂' r x y :=
  rfl

end Structure

/-- `hom_class L F M N` states that `F` is a type of `L`-homomorphisms. You should extend this
  typeclass when you extend `first_order.language.hom`. -/
class HomClass (L : outParam Language) (F : Type _) (M N : outParam <| Type _) [FunLike F M fun _ => N] [L.Structure M]
  [L.Structure N] where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r x → RelMap r (φ ∘ x)

/-- `strong_hom_class L F M N` states that `F` is a type of `L`-homomorphisms which preserve
  relations in both directions. -/
class StrongHomClass (L : outParam Language) (F : Type _) (M N : outParam <| Type _) [FunLike F M fun _ => N]
  [L.Structure M] [L.Structure N] where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r (φ ∘ x) ↔ RelMap r x

instance (priority := 100) StrongHomClass.homClass {F M N} [L.Structure M] [L.Structure N] [FunLike F M fun _ => N]
    [StrongHomClass L F M N] : HomClass L F M N where
  map_fun := StrongHomClass.map_fun
  map_rel := fun φ n R x => (StrongHomClass.map_rel φ R x).2

/-- Not an instance to avoid a loop. -/
def HomClass.strongHomClassOfIsAlgebraic [L.IsAlgebraic] {F M N} [L.Structure M] [L.Structure N]
    [FunLike F M fun _ => N] [HomClass L F M N] : StrongHomClass L F M N where
  map_fun := HomClass.map_fun
  map_rel := fun φ n R x => (IsAlgebraic.empty_relations n).elim R

theorem HomClass.map_constants {F M N} [L.Structure M] [L.Structure N] [FunLike F M fun _ => N] [HomClass L F M N]
    (φ : F) (c : L.Constants) : φ c = c :=
  (HomClass.map_fun φ c default).trans (congr rfl (funext default))

namespace Hom

instance funLike : FunLike (M →[L] N) M fun _ => N where
  coe := Hom.toFun
  coe_injective' := fun f g h => by
    cases f
    cases g
    cases h
    rfl

instance homClass : HomClass L (M →[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

instance [L.IsAlgebraic] : StrongHomClass L (M →[L] N) M N :=
  hom_class.strong_hom_class_of_is_algebraic

instance hasCoeToFun : CoeFun (M →[L] N) fun _ => M → N :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : M →[L] N} : f.toFun = (f : M → N) :=
  rfl

@[ext]
theorem ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

theorem ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[simp]
theorem map_fun (φ : M →[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
theorem map_constants (φ : M →[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
theorem map_rel (φ : M →[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r x → RelMap r (φ ∘ x) :=
  HomClass.map_rel φ r x

variable (L) (M)

/-- The identity map from a structure to itself -/
@[refl]
def id : M →[L] M where toFun := id

variable {L} {M}

instance : Inhabited (M →[L] M) :=
  ⟨id L M⟩

@[simp]
theorem id_apply (x : M) : id L M x = x :=
  rfl

/-- Composition of first-order homomorphisms -/
@[trans]
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
  toFun := hnp ∘ hmn
  map_rel' := fun _ _ _ h => by
    simp [← h]

@[simp]
theorem comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end Hom

/-- Any element of a `hom_class` can be realized as a first_order homomorphism. -/
def HomClass.toHom {F M N} [L.Structure M] [L.Structure N] [FunLike F M fun _ => N] [HomClass L F M N] : F → M →[L] N :=
  fun φ => ⟨φ, fun _ => HomClass.map_fun φ, fun _ => HomClass.map_rel φ⟩

namespace Embedding

instance embeddingLike : EmbeddingLike (M ↪[L] N) M N where
  coe := fun f => f.toFun
  injective' := fun f => f.toEmbedding.Injective
  coe_injective' := fun f g h => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iffₓ.1 h x

instance strongHomClass : StrongHomClass L (M ↪[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

instance hasCoeToFun : CoeFun (M ↪[L] N) fun _ => M → N :=
  FunLike.hasCoeToFun

@[simp]
theorem map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
theorem map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
theorem map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order embedding is also a first-order homomorphism. -/
def toHom : (M ↪[L] N) → M →[L] N :=
  hom_class.to_hom

@[simp]
theorem coe_to_hom {f : M ↪[L] N} : (f.toHom : M → N) = f :=
  rfl

theorem coe_injective : @Function.Injective (M ↪[L] N) (M → N) coeFn
  | f, g, h => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iffₓ.1 h x

@[ext]
theorem ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

theorem injective (f : M ↪[L] N) : Function.Injective f :=
  f.toEmbedding.Injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps]
def ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with inj' := hf, map_rel' := fun n r x => StrongHomClass.map_rel f r x }

@[simp]
theorem coe_fn_of_injective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : (ofInjective hf : M → N) = f :=
  rfl

@[simp]
theorem of_injective_to_hom [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : (ofInjective hf).toHom = f :=
  by
  ext
  simp

variable (L) (M)

/-- The identity embedding from a structure to itself -/
@[refl]
def refl : M ↪[L] M where toEmbedding := Function.Embedding.refl M

variable {L} {M}

instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of first-order embeddings -/
@[trans]
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
  toFun := hnp ∘ hmn
  inj' := hnp.Injective.comp hmn.Injective

@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order embeddings is associative. -/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_to_hom (hnp : N ↪[L] P) (hmn : M ↪[L] N) : (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom := by
  ext
  simp only [← coe_to_hom, ← comp_apply, ← hom.comp_apply]

end Embedding

/-- Any element of an injective `strong_hom_class` can be realized as a first_order embedding. -/
def StrongHomClass.toEmbedding {F M N} [L.Structure M] [L.Structure N] [EmbeddingLike F M N] [StrongHomClass L F M N] :
    F → M ↪[L] N := fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, fun _ => StrongHomClass.map_fun φ, fun _ => StrongHomClass.map_rel φ⟩

namespace Equivₓ

instance : EquivLike (M ≃[L] N) M N where
  coe := fun f => f.toFun
  inv := fun f => f.invFun
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv
  coe_injective' := fun f g h₁ h₂ => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iffₓ.1 h₁ x

instance : StrongHomClass L (M ≃[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
def symm (f : M ≃[L] N) : N ≃[L] M :=
  { f.toEquiv.symm with
    map_fun' := fun n f' x => by
      simp only [← Equivₓ.to_fun_as_coe]
      rw [Equivₓ.symm_apply_eq]
      refine' Eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm
      rw [← Function.comp.assoc, Equivₓ.to_fun_as_coe, Equivₓ.self_comp_symm, Function.comp.left_id],
    map_rel' := fun n r x => by
      simp only [← Equivₓ.to_fun_as_coe]
      refine' (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _
      rw [← Function.comp.assoc, Equivₓ.to_fun_as_coe, Equivₓ.self_comp_symm, Function.comp.left_id] }

instance hasCoeToFun : CoeFun (M ≃[L] N) fun _ => M → N :=
  FunLike.hasCoeToFun

@[simp]
theorem apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a :=
  f.toEquiv.apply_symm_apply a

@[simp]
theorem symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a

@[simp]
theorem map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
theorem map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
theorem map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order equivalence is also a first-order embedding. -/
def toEmbedding : (M ≃[L] N) → M ↪[L] N :=
  strong_hom_class.to_embedding

/-- A first-order equivalence is also a first-order homomorphism. -/
def toHom : (M ≃[L] N) → M →[L] N :=
  hom_class.to_hom

@[simp]
theorem to_embedding_to_hom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
theorem coe_to_hom {f : M ≃[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl

@[simp]
theorem coe_to_embedding (f : M ≃[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl

theorem coe_injective : @Function.Injective (M ≃[L] N) (M → N) coeFn :=
  FunLike.coe_injective

@[ext]
theorem ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

theorem bijective (f : M ≃[L] N) : Function.Bijective f :=
  EquivLike.bijective f

theorem injective (f : M ≃[L] N) : Function.Injective f :=
  EquivLike.injective f

theorem surjective (f : M ≃[L] N) : Function.Surjective f :=
  EquivLike.surjective f

variable (L) (M)

/-- The identity equivalence from a structure to itself -/
@[refl]
def refl : M ≃[L] M where toEquiv := Equivₓ.refl M

variable {L} {M}

instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of first-order equivalences -/
@[trans]
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
  { hmn.toEquiv.trans hnp.toEquiv with toFun := hnp ∘ hmn }

@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end Equivₓ

/-- Any element of a bijective `strong_hom_class` can be realized as a first_order isomorphism. -/
def StrongHomClass.toEquiv {F M N} [L.Structure M] [L.Structure N] [EquivLike F M N] [StrongHomClass L F M N] :
    F → M ≃[L] N := fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, fun _ => HomClass.map_fun φ, fun _ =>
    StrongHomClass.map_rel φ⟩

section SumStructure

variable (L₁ L₂ : Language) (S : Type _) [L₁.Structure S] [L₂.Structure S]

instance sumStructure : (L₁.Sum L₂).Structure S where
  funMap := fun n => Sum.elim funMap funMap
  rel_map := fun n => Sum.elim RelMap RelMap

variable {L₁ L₂ S}

@[simp]
theorem fun_map_sum_inl {n : ℕ} (f : L₁.Functions n) : @funMap (L₁.Sum L₂) S _ n (Sum.inl f) = funMap f :=
  rfl

@[simp]
theorem fun_map_sum_inr {n : ℕ} (f : L₂.Functions n) : @funMap (L₁.Sum L₂) S _ n (Sum.inr f) = funMap f :=
  rfl

@[simp]
theorem rel_map_sum_inl {n : ℕ} (R : L₁.Relations n) : @RelMap (L₁.Sum L₂) S _ n (Sum.inl R) = RelMap R :=
  rfl

@[simp]
theorem rel_map_sum_inr {n : ℕ} (R : L₂.Relations n) : @RelMap (L₁.Sum L₂) S _ n (Sum.inr R) = RelMap R :=
  rfl

end SumStructure

section Empty

section

variable [Language.empty.Structure M] [Language.empty.Structure N]

@[simp]
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[language.empty] N) ↔ Cardinal.lift.{w'} (# M) ≤ Cardinal.lift.{w} (# N) :=
  trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map fun f => { toEmbedding := f }⟩ Cardinal.lift_mk_le'.symm

@[simp]
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[language.empty] N) ↔ Cardinal.lift.{w'} (# M) = Cardinal.lift.{w} (# N) :=
  trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩ Cardinal.lift_mk_eq'.symm

end

instance emptyStructure : Language.empty.Structure M :=
  ⟨fun _ => Empty.elim, fun _ => Empty.elim⟩

instance : Unique (Language.empty.Structure M) :=
  ⟨⟨Language.emptyStructure⟩, fun a => by
    ext n f
    · exact Empty.elim f
      
    · exact Subsingleton.elimₓ _ _
      ⟩

instance (priority := 100) strongHomClassEmpty {F M N} [FunLike F M fun _ => N] : StrongHomClass Language.empty F M N :=
  ⟨fun _ _ f => Empty.elim f, fun _ _ r => Empty.elim r⟩

/-- Makes a `language.empty.hom` out of any function. -/
@[simps]
def _root_.function.empty_hom (f : M → N) : M →[language.empty] N where toFun := f

/-- Makes a `language.empty.embedding` out of any function. -/
@[simps]
def _root_.embedding.empty (f : M ↪ N) : M ↪[language.empty] N where toEmbedding := f

/-- Makes a `language.empty.equiv` out of any function. -/
@[simps]
def _root_.equiv.empty (f : M ≃ N) : M ≃[language.empty] N where toEquiv := f

end Empty

end Language

end FirstOrder

namespace Equivₓ

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open FirstOrder

variable {L : Language} {M : Type _} {N : Type _} [L.Structure M]

/-- A structure induced by a bijection. -/
@[simps]
def inducedStructure (e : M ≃ N) : L.Structure N :=
  ⟨fun n f x => e (funMap f (e.symm ∘ x)), fun n r x => RelMap r (e.symm ∘ x)⟩

/-- A bijection as a first-order isomorphism with the induced structure on the codomain. -/
@[simps]
def inducedStructureEquiv (e : M ≃ N) : @Language.Equiv L M N _ (inducedStructure e) :=
  { e with
    map_fun' := fun n f x => by
      simp [Function.comp.assoc e.symm e x],
    map_rel' := fun n r x => by
      simp [Function.comp.assoc e.symm e x] }

end Equivₓ

