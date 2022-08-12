/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Analysis.Complex.Circle
import Mathbin.Topology.ContinuousFunction.Algebra

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `continuous_monoid_hom A B`: The continuous homomorphisms `A →* B`.
* `continuous_add_monoid_hom α β`: The continuous additive homomorphisms `α →+ β`.
-/


open Pointwise

open Function

variable {F α β : Type _} (A B C D E : Type _) [Monoidₓ A] [Monoidₓ B] [Monoidₓ C] [Monoidₓ D] [CommGroupₓ E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace E]
  [TopologicalGroup E]

/-- The type of continuous additive monoid homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : continuous_add_monoid_hom α β)`,
you should parametrize over `(F : Type*) [continuous_add_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_add_monoid_hom_class`. -/
structure ContinuousAddMonoidHom (A B : Type _) [AddMonoidₓ A] [AddMonoidₓ B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B where
  continuous_to_fun : Continuous to_fun

/-- The type of continuous monoid homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : continuous_monoid_hom α β)`,
you should parametrize over `(F : Type*) [continuous_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_add_monoid_hom_class`. -/
@[to_additive]
structure ContinuousMonoidHom extends A →* B where
  continuous_to_fun : Continuous to_fun

/-- `continuous_add_monoid_hom_class F α β` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `continuous_add_monoid_hom`. -/
class ContinuousAddMonoidHomClass (F α β : Type _) [AddMonoidₓ α] [AddMonoidₓ β] [TopologicalSpace α]
  [TopologicalSpace β] extends AddMonoidHomClass F α β where
  map_continuous (f : F) : Continuous f

/-- `continuous_monoid_hom_class F α β` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `continuous_monoid_hom`. -/
@[to_additive]
class ContinuousMonoidHomClass (F α β : Type _) [Monoidₓ α] [Monoidₓ β] [TopologicalSpace α]
  [TopologicalSpace β] extends MonoidHomClass F α β where
  map_continuous (f : F) : Continuous f

/-- Reinterpret a `continuous_monoid_hom` as a `monoid_hom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `continuous_add_monoid_hom` as an `add_monoid_hom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) ContinuousMonoidHomClass.toContinuousMapClass [Monoidₓ α] [Monoidₓ β] [TopologicalSpace α]
    [TopologicalSpace β] [ContinuousMonoidHomClass F α β] : ContinuousMapClass F α β :=
  { ‹ContinuousMonoidHomClass F α β› with }

namespace ContinuousMonoidHom

variable {A B C D E} [Monoidₓ α] [Monoidₓ β] [TopologicalSpace α] [TopologicalSpace β]

@[to_additive]
instance : ContinuousMonoidHomClass (ContinuousMonoidHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'
  map_continuous := fun f => f.continuous_to_fun

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive]
instance : CoeFun (ContinuousMonoidHom A B) fun _ => A → B :=
  FunLike.hasCoeToFun

@[to_additive]
theorem ext {f g : ContinuousMonoidHom A B} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

/-- Reinterpret a `continuous_monoid_hom` as a `continuous_map`. -/
@[to_additive "Reinterpret a `continuous_add_monoid_hom` as a `continuous_map`."]
def toContinuousMap (f : ContinuousMonoidHom α β) : C(α, β) :=
  { f with }

@[to_additive]
theorem to_continuous_map_injective : Injective (toContinuousMap : _ → C(α, β)) := fun f g h =>
  ext <| by
    convert FunLike.ext_iff.1 h

/-- Construct a `continuous_monoid_hom` from a `continuous` `monoid_hom`. -/
@[to_additive "Construct a `continuous_add_monoid_hom` from a `continuous` `add_monoid_hom`.", simps]
def mk' (f : A →* B) (hf : Continuous f) : ContinuousMonoidHom A B :=
  { f with continuous_to_fun := hf }

/-- Composition of two continuous homomorphisms. -/
@[to_additive "Composition of two continuous homomorphisms.", simps]
def comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ContinuousMonoidHom A C :=
  mk' (g.toMonoidHom.comp f.toMonoidHom) (g.continuous_to_fun.comp f.continuous_to_fun)

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive "Product of two continuous homomorphisms on the same space.", simps]
def prod (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C) : ContinuousMonoidHom A (B × C) :=
  mk' (f.toMonoidHom.Prod g.toMonoidHom) (f.continuous_to_fun.prod_mk g.continuous_to_fun)

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive "Product of two continuous homomorphisms on different spaces.", simps]
def prodMap (f : ContinuousMonoidHom A C) (g : ContinuousMonoidHom B D) : ContinuousMonoidHom (A × B) (C × D) :=
  mk' (f.toMonoidHom.prod_map g.toMonoidHom) (f.continuous_to_fun.prod_map g.continuous_to_fun)

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive "The trivial continuous homomorphism.", simps]
def one : ContinuousMonoidHom A B :=
  mk' 1 continuous_const

@[to_additive]
instance : Inhabited (ContinuousMonoidHom A B) :=
  ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive "The identity continuous homomorphism.", simps]
def id : ContinuousMonoidHom A A :=
  mk' (MonoidHom.id A) continuous_id

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive "The continuous homomorphism given by projection onto the first factor.", simps]
def fst : ContinuousMonoidHom (A × B) A :=
  mk' (MonoidHom.fst A B) continuous_fst

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive "The continuous homomorphism given by projection onto the second factor.", simps]
def snd : ContinuousMonoidHom (A × B) B :=
  mk' (MonoidHom.snd A B) continuous_snd

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the first factor.", simps]
def inl : ContinuousMonoidHom A (A × B) :=
  prod (id A) (one A B)

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the second factor.", simps]
def inr : ContinuousMonoidHom B (A × B) :=
  prod (one B A) (id B)

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive "The continuous homomorphism given by the diagonal embedding.", simps]
def diag : ContinuousMonoidHom A (A × A) :=
  prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive "The continuous homomorphism given by swapping components.", simps]
def swap : ContinuousMonoidHom (A × B) (B × A) :=
  prod (snd A B) (fst A B)

/-- The continuous homomorphism given by multiplication. -/
@[to_additive "The continuous homomorphism given by addition.", simps]
def mul : ContinuousMonoidHom (E × E) E :=
  mk' mulMonoidHom continuous_mul

/-- The continuous homomorphism given by inversion. -/
@[to_additive "The continuous homomorphism given by negation.", simps]
def inv : ContinuousMonoidHom E E :=
  mk' invMonoidHom continuous_inv

variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive "Coproduct of two continuous homomorphisms to the same space.", simps]
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) : ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prod_map g)

@[to_additive]
instance : CommGroupₓ (ContinuousMonoidHom A E) where
  mul := fun f g => (mul E).comp (f.Prod g)
  mul_comm := fun f g => ext fun x => mul_comm (f x) (g x)
  mul_assoc := fun f g h => ext fun x => mul_assoc (f x) (g x) (h x)
  one := one A E
  one_mul := fun f => ext fun x => one_mulₓ (f x)
  mul_one := fun f => ext fun x => mul_oneₓ (f x)
  inv := fun f => (inv E).comp f
  mul_left_inv := fun f => ext fun x => mul_left_invₓ (f x)

instance : TopologicalSpace (ContinuousMonoidHom A B) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

variable (A B C D E)

theorem is_inducing : Inducing (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨rfl⟩

theorem is_embedding : Embedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨is_inducing A B, to_continuous_map_injective⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (U V W)
theorem is_closed_embedding [HasContinuousMul B] [T2Space B] :
    ClosedEmbedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨is_embedding A B,
    ⟨by
      suffices
        Set.Range (to_continuous_map : ContinuousMonoidHom A B → C(A, B)) =
          ({ f | f '' {1} ⊆ {1}ᶜ } ∪
              ⋃ (x) (y) (U) (V) (W) (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (h : Disjoint (U * V) W),
                { f | f '' {x} ⊆ U } ∩ { f | f '' {y} ⊆ V } ∩ { f | f '' {x * y} ⊆ W })ᶜ
        by
        rw [this, compl_compl]
        refine' (ContinuousMap.is_open_gen is_compact_singleton is_open_compl_singleton).union _
        repeat'
          apply is_open_Union
          intro
        repeat'
          apply IsOpen.inter
        all_goals
          apply ContinuousMap.is_open_gen is_compact_singleton
          assumption
      simp_rw [Set.compl_union, Set.compl_Union, Set.image_singleton, Set.singleton_subset_iff, Set.ext_iff,
        Set.mem_inter_iff, Set.mem_Inter, Set.mem_compl_iff]
      refine' fun f => ⟨_, _⟩
      · rintro ⟨f, rfl⟩
        exact
          ⟨fun h => h (map_one f), fun x y U V W hU hV hW h ⟨⟨hfU, hfV⟩, hfW⟩ =>
            h ⟨Set.mul_mem_mul hfU hfV, (congr_arg (· ∈ W) (map_mul f x y)).mp hfW⟩⟩
        
      · rintro ⟨hf1, hf2⟩
        suffices ∀ x y, f (x * y) = f x * f y by
          refine'
            ⟨({ f with map_one' := of_not_not hf1, map_mul' := this } : ContinuousMonoidHom A B),
              ContinuousMap.ext fun _ => rfl⟩
        intro x y
        contrapose! hf2
        obtain ⟨UV, W, hUV, hW, hfUV, hfW, h⟩ := t2_separation hf2.symm
        have hB := @continuous_mul B _ _ _
        obtain ⟨U, V, hU, hV, hfU, hfV, h'⟩ := is_open_prod_iff.mp (hUV.preimage hB) (f x) (f y) hfUV
        refine' ⟨x, y, U, V, W, hU, hV, hW, h.mono_left _, ⟨hfU, hfV⟩, hfW⟩
        rintro _ ⟨x, y, hx : (x, y).1 ∈ U, hy : (x, y).2 ∈ V, rfl⟩
        exact h' ⟨hx, hy⟩
        ⟩⟩

variable {A B C D E}

instance [T2Space B] : T2Space (ContinuousMonoidHom A B) :=
  (is_embedding A B).T2Space

instance : TopologicalGroup (ContinuousMonoidHom A E) :=
  let hi := is_inducing A E
  let hc := hi.Continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prod_map hc hc)),
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

end ContinuousMonoidHom

/-- The Pontryagin dual of `G` is the group of continuous homomorphism `G → circle`. -/
def PontryaginDual (G : Type _) [Monoidₓ G] [TopologicalSpace G] :=
  ContinuousMonoidHom G circle deriving TopologicalSpace, T2Space, CommGroupₓ, TopologicalGroup, Inhabited

