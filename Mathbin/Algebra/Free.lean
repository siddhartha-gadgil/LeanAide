/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Control.Applicative
import Mathbin.Control.Traversable.Basic
import Mathbin.Logic.Equiv.Basic

/-!
# Free constructions

## Main definitions

* `free_magma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `magma.free_semigroup α`: free semigroup over magma `α`.
* `free_semigroup α`: free semigroup over alphabet `α`, defined as a synonym for `α × list α`
  (i.e. nonempty lists), with traversable instance and decidable equality.
* `free_semigroup_free_magma α`: isomorphism between `magma.free_semigroup (free_magma α)` and
  `free_semigroup α`.
* `free_magma.lift`: the universal property of the free magma, expressing its adjointness.
-/


universe u v l

/-- Free magma over a given alphabet. -/
inductive FreeMagma (α : Type u) : Type u
  | of : α → FreeMagma
  | mul : FreeMagma → FreeMagma → FreeMagma
  deriving DecidableEq

/-- Free nonabelian additive magma over a given alphabet. -/
inductive FreeAddMagma (α : Type u) : Type u
  | of : α → FreeAddMagma
  | add : FreeAddMagma → FreeAddMagma → FreeAddMagma
  deriving DecidableEq

attribute [to_additive] FreeMagma

namespace FreeMagma

variable {α : Type u}

@[to_additive]
instance [Inhabited α] : Inhabited (FreeMagma α) :=
  ⟨of default⟩

@[to_additive]
instance : Mul (FreeMagma α) :=
  ⟨FreeMagma.mul⟩

attribute [matchPattern] Mul.mul

@[simp, to_additive]
theorem mul_eq (x y : FreeMagma α) : mul x y = x * y :=
  rfl

/-- Recursor for `free_magma` using `x * y` instead of `free_magma.mul x y`. -/
@[elab_as_eliminator, to_additive "Recursor for `free_add_magma` using `x + y` instead of `free_add_magma.add x y`."]
def recOnMul {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C x → C y → C (x * y)) : C x :=
  FreeMagma.recOn x ih1 ih2

end FreeMagma

/-- Lifts a function `α → β` to a magma homomorphism `free_magma α → β` given a magma `β`. -/
def FreeMagma.liftAux {α : Type u} {β : Type v} [Mul β] (f : α → β) : FreeMagma α → β
  | FreeMagma.of x => f x
  | x * y => x.liftAux * y.liftAux

/-- Lifts a function `α → β` to an additive magma homomorphism `free_add_magma α → β` given
an additive magma `β`. -/
def FreeAddMagma.liftAux {α : Type u} {β : Type v} [Add β] (f : α → β) : FreeAddMagma α → β
  | FreeAddMagma.of x => f x
  | x + y => x.liftAux + y.liftAux

attribute [to_additive FreeAddMagma.liftAux] FreeMagma.liftAux

namespace FreeMagma

variable {α : Type u} {β : Type v} [Mul β] (f : α → β)

@[to_additive]
theorem lift_aux_unique (F : FreeMagma α →ₙ* β) : ⇑F = liftAux (F ∘ of) :=
  funext fun x =>
    (FreeMagma.recOn x fun x => rfl) fun x y ih1 ih2 => (F.map_mul x y).trans <| congr (congr_arg _ ih1) ih2

/-- The universal property of the free magma expressing its adjointness. -/
@[to_additive "The universal property of the free additive magma expressing its adjointness."]
def lift : (α → β) ≃ (FreeMagma α →ₙ* β) where
  toFun := fun f => { toFun := liftAux f, map_mul' := fun x y => rfl }
  invFun := fun F => F ∘ of
  left_inv := fun f => by
    ext
    simp only [← lift_aux, ← MulHom.coe_mk, ← Function.comp_app]
  right_inv := fun F => by
    ext
    rw [MulHom.coe_mk, lift_aux_unique]

@[simp, to_additive]
theorem lift_of (x) : lift f (of x) = f x :=
  rfl

end FreeMagma

/-- The unique magma homomorphism `free_magma α → free_magma β` that sends
each `of x` to `of (f x)`. -/
def FreeMagma.map {α : Type u} {β : Type v} (f : α → β) : FreeMagma α → FreeMagma β
  | FreeMagma.of x => FreeMagma.of (f x)
  | x * y => x.map * y.map

/-- The unique additive magma homomorphism `free_add_magma α → free_add_magma β` that sends
each `of x` to `of (f x)`. -/
def FreeAddMagma.map {α : Type u} {β : Type v} (f : α → β) : FreeAddMagma α → FreeAddMagma β
  | FreeAddMagma.of x => FreeAddMagma.of (f x)
  | x + y => x.map + y.map

attribute [to_additive FreeAddMagma.map] FreeMagma.map

namespace FreeMagma

variable {α : Type u}

section Map

variable {β : Type v} (f : α → β)

@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl

@[simp, to_additive]
theorem map_mul (x y) : map f (x * y) = map f x * map f y :=
  rfl

end Map

section Category

@[to_additive]
instance : Monadₓ FreeMagma where
  pure := fun _ => of
  bind := fun _ _ x f => lift f x

/-- Recursor on `free_magma` using `pure` instead of `of`. -/
@[elab_as_eliminator, to_additive "Recursor on `free_add_magma` using `pure` instead of `of`."]
protected def recOnPure {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
    C x :=
  FreeMagma.recOnMul x ih1 ih2

variable {β : Type u}

@[simp, to_additive]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeMagma β) = pure (f x) :=
  rfl

@[simp, to_additive]
theorem map_mul' (f : α → β) (x y : FreeMagma α) : f <$> (x * y) = f <$> x * f <$> y :=
  rfl

@[simp, to_additive]
theorem pure_bind (f : α → FreeMagma β) (x) : pure x >>= f = f x :=
  rfl

@[simp, to_additive]
theorem mul_bind (f : α → FreeMagma β) (x y : FreeMagma α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  rfl

@[simp, to_additive]
theorem pure_seq {α β : Type u} {f : α → β} {x : FreeMagma α} : pure f <*> x = f <$> x :=
  rfl

@[simp, to_additive]
theorem mul_seq {α β : Type u} {f g : FreeMagma (α → β)} {x : FreeMagma α} : f * g <*> x = (f <*> x) * (g <*> x) :=
  rfl

@[to_additive]
instance : IsLawfulMonad FreeMagma.{u} where
  pure_bind := fun _ _ _ _ => rfl
  bind_assoc := fun α β γ x f g =>
    FreeMagma.recOnPure x (fun x => rfl) fun x y ih1 ih2 => by
      rw [mul_bind, mul_bind, mul_bind, ih1, ih2]
  id_map := fun α x =>
    FreeMagma.recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by
      rw [map_mul', ih1, ih2]

end Category

end FreeMagma

/-- `free_magma` is traversable. -/
protected def FreeMagma.traverse {m : Type u → Type u} [Applicativeₓ m] {α β : Type u} (F : α → m β) :
    FreeMagma α → m (FreeMagma β)
  | FreeMagma.of x => FreeMagma.of <$> F x
  | x * y => (· * ·) <$> x.traverse <*> y.traverse

/-- `free_add_magma` is traversable. -/
protected def FreeAddMagma.traverse {m : Type u → Type u} [Applicativeₓ m] {α β : Type u} (F : α → m β) :
    FreeAddMagma α → m (FreeAddMagma β)
  | FreeAddMagma.of x => FreeAddMagma.of <$> F x
  | x + y => (· + ·) <$> x.traverse <*> y.traverse

attribute [to_additive FreeAddMagma.traverse] FreeMagma.traverse

namespace FreeMagma

variable {α : Type u}

section Category

variable {β : Type u}

@[to_additive]
instance : Traversable FreeMagma :=
  ⟨@FreeMagma.traverse⟩

variable {m : Type u → Type u} [Applicativeₓ m] (F : α → m β)

@[simp, to_additive]
theorem traverse_pure (x) : traverse F (pure x : FreeMagma α) = pure <$> F x :=
  rfl

@[simp, to_additive]
theorem traverse_pure' : traverse F ∘ pure = fun x => (pure <$> F x : m (FreeMagma β)) :=
  rfl

@[simp, to_additive]
theorem traverse_mul (x y : FreeMagma α) : traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  rfl

@[simp, to_additive]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ @Mul.mul (FreeMagma α) _ = fun x y => (· * ·) <$> traverse F x <*> traverse F y :=
  rfl

@[simp, to_additive]
theorem traverse_eq (x) : FreeMagma.traverse F x = traverse F x :=
  rfl

@[simp, to_additive]
theorem mul_map_seq (x y : FreeMagma α) : ((· * ·) <$> x <*> y : id (FreeMagma α)) = (x * y : FreeMagma α) :=
  rfl

@[to_additive]
instance : IsLawfulTraversable FreeMagma.{u} :=
  { FreeMagma.is_lawful_monad with
    id_traverse := fun α x =>
      FreeMagma.recOnPure x (fun x => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, mul_map_seq],
    comp_traverse := fun F G hf1 hg1 hf2 hg2 α β γ f g x =>
      FreeMagma.recOnPure x
        (fun x => by
          skip <;> simp' only [← traverse_pure, ← traverse_pure'] with functor_norm)
        fun x y ih1 ih2 => by
        skip <;> rw [traverse_mul, ih1, ih2, traverse_mul] <;> simp' only [← traverse_mul'] with functor_norm,
    naturality := fun F G hf1 hg1 hf2 hg2 η α β f x =>
      FreeMagma.recOnPure x
        (fun x => by
          simp' only [← traverse_pure] with functor_norm)
        fun x y ih1 ih2 => by
        simp' only [← traverse_mul] with functor_norm <;> rw [ih1, ih2],
    traverse_eq_map_id := fun α β f x =>
      FreeMagma.recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq] <;> rfl }

end Category

end FreeMagma

/-- Representation of an element of a free magma. -/
protected def FreeMagma.repr {α : Type u} [HasRepr α] : FreeMagma α → Stringₓ
  | FreeMagma.of x => reprₓ x
  | x * y => "( " ++ x.repr ++ " * " ++ y.repr ++ " )"

/-- Representation of an element of a free additive magma. -/
protected def FreeAddMagma.repr {α : Type u} [HasRepr α] : FreeAddMagma α → Stringₓ
  | FreeAddMagma.of x => reprₓ x
  | x + y => "( " ++ x.repr ++ " + " ++ y.repr ++ " )"

attribute [to_additive FreeAddMagma.repr] FreeMagma.repr

@[to_additive]
instance {α : Type u} [HasRepr α] : HasRepr (FreeMagma α) :=
  ⟨FreeMagma.repr⟩

/-- Length of an element of a free magma. -/
def FreeMagma.length {α : Type u} : FreeMagma α → ℕ
  | FreeMagma.of x => 1
  | x * y => x.length + y.length

/-- Length of an element of a free additive magma. -/
def FreeAddMagma.length {α : Type u} : FreeAddMagma α → ℕ
  | FreeAddMagma.of x => 1
  | x + y => x.length + y.length

attribute [to_additive FreeAddMagma.length] FreeMagma.length

/-- Associativity relations for a magma. -/
inductive Magma.FreeSemigroup.R (α : Type u) [Mul α] : α → α → Prop
  | intro : ∀ x y z, Magma.FreeSemigroup.R (x * y * z) (x * (y * z))
  | left : ∀ w x y z, Magma.FreeSemigroup.R (w * (x * y * z)) (w * (x * (y * z)))

/-- Associativity relations for an additive magma. -/
inductive AddMagma.FreeAddSemigroup.R (α : Type u) [Add α] : α → α → Prop
  | intro : ∀ x y z, AddMagma.FreeAddSemigroup.R (x + y + z) (x + (y + z))
  | left : ∀ w x y z, AddMagma.FreeAddSemigroup.R (w + (x + y + z)) (w + (x + (y + z)))

attribute [to_additive AddMagma.FreeAddSemigroup.R] Magma.FreeSemigroup.R

namespace Magma

/-- Free semigroup over a magma. -/
@[to_additive AddMagma.FreeAddSemigroup "Free additive semigroup over an additive magma."]
def FreeSemigroup (α : Type u) [Mul α] : Type u :=
  Quot <| FreeSemigroup.R α

namespace FreeSemigroup

variable {α : Type u} [Mul α]

/-- Embedding from magma to its free semigroup. -/
@[to_additive "Embedding from additive magma to its free additive semigroup."]
def of : α → FreeSemigroup α :=
  Quot.mk _

@[to_additive]
instance [Inhabited α] : Inhabited (FreeSemigroup α) :=
  ⟨of default⟩

@[elab_as_eliminator, to_additive]
protected theorem induction_on {C : FreeSemigroup α → Prop} (x : FreeSemigroup α) (ih : ∀ x, C (of x)) : C x :=
  Quot.induction_on x ih

@[to_additive]
theorem of_mul_assoc (x y z : α) : of (x * y * z) = of (x * (y * z)) :=
  Quot.sound <| R.intro x y z

@[to_additive]
theorem of_mul_assoc_left (w x y z : α) : of (w * (x * y * z)) = of (w * (x * (y * z))) :=
  Quot.sound <| R.left w x y z

@[to_additive]
theorem of_mul_assoc_right (w x y z : α) : of (w * x * y * z) = of (w * (x * y) * z) := by
  rw [of_mul_assoc, of_mul_assoc, of_mul_assoc, of_mul_assoc_left]

@[to_additive]
instance : Semigroupₓ (FreeSemigroup α) where
  mul := fun x y => by
    refine' Quot.liftOn x (fun p => Quot.liftOn y (fun q => (Quot.mk _ <| p * q : FreeSemigroup α)) _) _
    · rintro a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> change of _ = of _
      · rw [of_mul_assoc_left]
        
      · rw [← of_mul_assoc, of_mul_assoc_left, of_mul_assoc]
        
      
    · refine' Quot.induction_on y fun q => _
      rintro a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> change of _ = of _
      · rw [of_mul_assoc_right]
        
      · rw [of_mul_assoc, of_mul_assoc, of_mul_assoc_left, of_mul_assoc_left, of_mul_assoc_left, ← of_mul_assoc c d, ←
          of_mul_assoc c d, of_mul_assoc_left]
        
      
  mul_assoc := fun x y z =>
    (Quot.induction_on x) fun p => (Quot.induction_on y) fun q => (Quot.induction_on z) fun r => of_mul_assoc p q r

@[to_additive]
theorem of_mul (x y : α) : of (x * y) = of x * of y :=
  rfl

section lift

variable {β : Type v} [Semigroupₓ β] (f : α → β)

/-- Lifts a magma homomorphism `α → β` to a semigroup homomorphism `magma.free_semigroup α → β`
given a semigroup `β`. -/
@[to_additive
      "Lifts an additive magma homomorphism `α → β` to an additive semigroup homomorphism\n`add_magma.free_add_semigroup α → β` given an additive semigroup `β`."]
def lift (hf : ∀ x y, f (x * y) = f x * f y) : FreeSemigroup α → β :=
  Quot.lift f <| by
    rintro a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only [← hf, ← mul_assoc]

@[simp, to_additive]
theorem lift_of {hf} (x : α) : lift f hf (of x) = f x :=
  rfl

@[simp, to_additive]
theorem lift_mul {hf} (x y) : lift f hf (x * y) = lift f hf x * lift f hf y :=
  (Quot.induction_on x) fun p => (Quot.induction_on y) fun q => hf p q

@[to_additive]
theorem lift_unique (f : FreeSemigroup α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
    f = lift (f ∘ of) fun p q => hf (of p) (of q) :=
  funext fun x => (Quot.induction_on x) fun p => rfl

end lift

variable {β : Type v} [Mul β] (f : α → β)

/-- From a magma homomorphism `α → β` to a semigroup homomorphism
`magma.free_semigroup α → magma.free_semigroup β`. -/
@[to_additive
      "From an additive magma homomorphism `α → β` to an additive semigroup homomorphism\n`add_magma.free_add_semigroup α → add_magma.free_add_semigroup β`."]
def map (hf : ∀ x y, f (x * y) = f x * f y) : FreeSemigroup α → FreeSemigroup β :=
  lift (of ∘ f) fun x y => congr_arg of <| hf x y

@[simp, to_additive]
theorem map_of {hf} (x) : map f hf (of x) = of (f x) :=
  rfl

@[simp, to_additive]
theorem map_mul {hf} (x y) : map f hf (x * y) = map f hf x * map f hf y :=
  lift_mul _ _ _

end FreeSemigroup

end Magma

/-- Free semigroup over a given alphabet.
(Note: In this definition, the free semigroup does not contain the empty word.) -/
@[to_additive "Free additive semigroup over a given alphabet."]
def FreeSemigroup (α : Type u) : Type u :=
  α × List α

namespace FreeSemigroup

variable {α : Type u}

@[to_additive]
instance : Semigroupₓ (FreeSemigroup α) where
  mul := fun L1 L2 => (L1.1, L1.2 ++ L2.1 :: L2.2)
  mul_assoc := fun L1 L2 L3 => Prod.extₓ rfl <| List.append_assoc _ _ _

/-- The embedding `α → free_semigroup α`. -/
@[to_additive "The embedding `α → free_add_semigroup α`."]
def of (x : α) : FreeSemigroup α :=
  (x, [])

@[to_additive]
instance [Inhabited α] : Inhabited (FreeSemigroup α) :=
  ⟨of default⟩

/-- Recursor for free semigroup using `of` and `*`. -/
@[elab_as_eliminator, to_additive "Recursor for free additive semigroup using `of` and `+`."]
protected def recOn {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) : C x :=
  (Prod.recOn x) fun f s => List.recOn s ih1 (fun hd tl ih f => ih2 f (hd, tl) (ih1 f) (ih hd)) f

end FreeSemigroup

/-- Auxiliary function for `free_semigroup.lift`. -/
def FreeSemigroup.lift' {α : Type u} {β : Type v} [Semigroupₓ β] (f : α → β) : α → List α → β
  | x, [] => f x
  | x, hd :: tl => f x * FreeSemigroup.lift' hd tl

/-- Auxiliary function for `free_semigroup.lift`. -/
def FreeAddSemigroup.lift' {α : Type u} {β : Type v} [AddSemigroupₓ β] (f : α → β) : α → List α → β
  | x, [] => f x
  | x, hd :: tl => f x + FreeAddSemigroup.lift' hd tl

attribute [to_additive FreeAddSemigroup.lift'] FreeSemigroup.lift'

namespace FreeSemigroup

variable {α : Type u}

section lift

variable {β : Type v} [Semigroupₓ β] (f : α → β)

/-- Lifts a function `α → β` to a semigroup homomorphism `free_semigroup α → β` given
a semigroup `β`. -/
@[to_additive
      "Lifts a function `α → β` to an additive semigroup homomorphism\n`free_add_semigroup α → β` given an additive semigroup `β`."]
def lift (x : FreeSemigroup α) : β :=
  lift' f x.1 x.2

@[simp, to_additive]
theorem lift_of (x : α) : lift f (of x) = f x :=
  rfl

@[to_additive]
theorem lift_of_mul (x y) : lift f (of x * y) = f x * lift f y :=
  rfl

@[simp, to_additive]
theorem lift_mul (x y) : lift f (x * y) = lift f x * lift f y :=
  FreeSemigroup.recOn x (fun p => rfl) fun p x ih1 ih2 => by
    rw [mul_assoc, lift_of_mul, lift_of_mul, mul_assoc, ih2]

@[to_additive]
theorem lift_unique (f : FreeSemigroup α → β) (hf : ∀ x y, f (x * y) = f x * f y) : f = lift (f ∘ of) :=
  funext fun ⟨x, L⟩ =>
    List.recOn L (fun x => rfl) (fun hd tl ih x => (hf (of x) (hd, tl)).trans <| congr_arg _ <| ih _) x

end lift

section Map

variable {β : Type v} (f : α → β)

/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
@[to_additive "The unique additive semigroup homomorphism that sends `of x` to `of (f x)`."]
def map : FreeSemigroup α → FreeSemigroup β :=
  lift <| of ∘ f

@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl

@[simp, to_additive]
theorem map_mul (x y) : map f (x * y) = map f x * map f y :=
  lift_mul _ _ _

end Map

section Category

variable {β : Type u}

@[to_additive]
instance : Monadₓ FreeSemigroup where
  pure := fun _ => of
  bind := fun _ _ x f => lift f x

/-- Recursor that uses `pure` instead of `of`. -/
@[elab_as_eliminator, to_additive "Recursor that uses `pure` instead of `of`."]
def recOnPure {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (pure x))
    (ih2 : ∀ x y, C (pure x) → C y → C (pure x * y)) : C x :=
  FreeSemigroup.recOn x ih1 ih2

@[simp, to_additive]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeSemigroup β) = pure (f x) :=
  rfl

@[simp, to_additive]
theorem map_mul' (f : α → β) (x y : FreeSemigroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  map_mul _ _ _

@[simp, to_additive]
theorem pure_bind (f : α → FreeSemigroup β) (x) : pure x >>= f = f x :=
  rfl

@[simp, to_additive]
theorem mul_bind (f : α → FreeSemigroup β) (x y : FreeSemigroup α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  lift_mul _ _ _

@[simp, to_additive]
theorem pure_seq {f : α → β} {x : FreeSemigroup α} : pure f <*> x = f <$> x :=
  rfl

@[simp, to_additive]
theorem mul_seq {f g : FreeSemigroup (α → β)} {x : FreeSemigroup α} : f * g <*> x = (f <*> x) * (g <*> x) :=
  mul_bind _ _ _

@[to_additive]
instance : IsLawfulMonad FreeSemigroup.{u} where
  pure_bind := fun _ _ _ _ => rfl
  bind_assoc := fun α β γ x f g =>
    recOnPure x (fun x => rfl) fun x y ih1 ih2 => by
      rw [mul_bind, mul_bind, mul_bind, ih1, ih2]
  id_map := fun α x =>
    recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by
      rw [map_mul', ih1, ih2]

/-- `free_semigroup` is traversable. -/
@[to_additive "`free_add_semigroup` is traversable."]
protected def traverse {m : Type u → Type u} [Applicativeₓ m] {α β : Type u} (F : α → m β) (x : FreeSemigroup α) :
    m (FreeSemigroup β) :=
  recOnPure x (fun x => pure <$> F x) fun x y ihx ihy => (· * ·) <$> ihx <*> ihy

@[to_additive]
instance : Traversable FreeSemigroup :=
  ⟨@FreeSemigroup.traverse⟩

variable {m : Type u → Type u} [Applicativeₓ m] (F : α → m β)

@[simp, to_additive]
theorem traverse_pure (x) : traverse F (pure x : FreeSemigroup α) = pure <$> F x :=
  rfl

@[simp, to_additive]
theorem traverse_pure' : traverse F ∘ pure = fun x => (pure <$> F x : m (FreeSemigroup β)) :=
  rfl

section

variable [IsLawfulApplicative m]

@[simp, to_additive]
theorem traverse_mul (x y : FreeSemigroup α) : traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  let ⟨x, L1⟩ := x
  let ⟨y, L2⟩ := y
  List.recOn L1 (fun x => rfl)
    (fun hd tl ih x =>
      show
        (· * ·) <$> pure <$> F x <*> traverse F ((hd, tl) * (y, L2) : FreeSemigroup α) =
          (· * ·) <$> ((· * ·) <$> pure <$> F x <*> traverse F (hd, tl)) <*> traverse F (y, L2)
        by
        rw [ih] <;> simp' only [← (· ∘ ·), ← (mul_assoc _ _ _).symm] with functor_norm)
    x

@[simp, to_additive]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ @Mul.mul (FreeSemigroup α) _ = fun x y => (· * ·) <$> traverse F x <*> traverse F y :=
  funext fun x => funext fun y => traverse_mul F x y

end

@[simp, to_additive]
theorem traverse_eq (x) : FreeSemigroup.traverse F x = traverse F x :=
  rfl

@[simp, to_additive]
theorem mul_map_seq (x y : FreeSemigroup α) :
    ((· * ·) <$> x <*> y : id (FreeSemigroup α)) = (x * y : FreeSemigroup α) :=
  rfl

@[to_additive]
instance : IsLawfulTraversable FreeSemigroup.{u} :=
  { FreeSemigroup.is_lawful_monad with
    id_traverse := fun α x =>
      FreeSemigroup.recOn x (fun x => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, mul_map_seq],
    comp_traverse := fun F G hf1 hg1 hf2 hg2 α β γ f g x =>
      recOnPure x
        (fun x => by
          skip <;> simp' only [← traverse_pure, ← traverse_pure'] with functor_norm)
        fun x y ih1 ih2 => by
        skip <;> rw [traverse_mul, ih1, ih2, traverse_mul] <;> simp' only [← traverse_mul'] with functor_norm,
    naturality := fun F G hf1 hg1 hf2 hg2 η α β f x =>
      recOnPure x
        (fun x => by
          simp' only [← traverse_pure] with functor_norm)
        fun x y ih1 ih2 => by
        skip <;> simp' only [← traverse_mul] with functor_norm <;> rw [ih1, ih2],
    traverse_eq_map_id := fun α β f x =>
      FreeSemigroup.recOn x (fun _ => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq] <;> rfl }

end Category

@[to_additive]
instance [DecidableEq α] : DecidableEq (FreeSemigroup α) :=
  Prod.decidableEq

end FreeSemigroup

/-- Isomorphism between `magma.free_semigroup (free_magma α)` and `free_semigroup α`. -/
@[to_additive "Isomorphism between\n`add_magma.free_add_semigroup (free_add_magma α)` and `free_add_semigroup α`."]
def freeSemigroupFreeMagma (α : Type u) : Magma.FreeSemigroup (FreeMagma α) ≃ FreeSemigroup α where
  toFun := Magma.FreeSemigroup.lift (FreeMagma.lift FreeSemigroup.of) (FreeMagma.lift _).map_mul
  invFun := FreeSemigroup.lift (Magma.FreeSemigroup.of ∘ FreeMagma.of)
  left_inv := fun x =>
    (Magma.FreeSemigroup.induction_on x) fun p => by
      rw [Magma.FreeSemigroup.lift_of] <;>
        exact
          FreeMagma.recOnMul p
            (fun x => by
              rw [FreeMagma.lift_of, FreeSemigroup.lift_of])
            fun x y ihx ihy => by
            rw [MulHom.map_mul, FreeSemigroup.lift_mul, ihx, ihy, Magma.FreeSemigroup.of_mul]
  right_inv := fun x =>
    FreeSemigroup.recOn x
      (fun x => by
        rw [FreeSemigroup.lift_of, Magma.FreeSemigroup.lift_of, FreeMagma.lift_of])
      fun x y ihx ihy => by
      rw [FreeSemigroup.lift_mul, Magma.FreeSemigroup.lift_mul, ihx, ihy]

@[simp, to_additive]
theorem free_semigroup_free_magma_mul {α : Type u} (x y) :
    freeSemigroupFreeMagma α (x * y) = freeSemigroupFreeMagma α x * freeSemigroupFreeMagma α y :=
  Magma.FreeSemigroup.lift_mul _ _ _

