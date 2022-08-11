/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

The writer monad transformer for passing immutable state.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Equiv.Basic

universe u v w u₀ u₁ v₀ v₁

structure WriterTₓ (ω : Type u) (m : Type u → Type v) (α : Type u) : Type max u v where
  run : m (α × ω)

@[reducible]
def Writerₓ (ω : Type u) :=
  WriterTₓ ω id

attribute [pp_using_anonymous_constructor] WriterTₓ

namespace WriterTₓ

section

variable {ω : Type u}

variable {m : Type u → Type v}

variable [Monadₓ m]

variable {α β : Type u}

open Function

@[ext]
protected theorem ext (x x' : WriterTₓ ω m α) (h : x.run = x'.run) : x = x' := by
  cases x <;> cases x' <;> congr <;> apply h

@[inline]
protected def tell (w : ω) : WriterTₓ ω m PUnit :=
  ⟨pure (PUnit.unit, w)⟩

@[inline]
protected def listen : WriterTₓ ω m α → WriterTₓ ω m (α × ω)
  | ⟨cmd⟩ => ⟨(fun x : α × ω => ((x.1, x.2), x.2)) <$> cmd⟩

@[inline]
protected def pass : WriterTₓ ω m (α × (ω → ω)) → WriterTₓ ω m α
  | ⟨cmd⟩ => ⟨uncurry (uncurry fun x (f : ω → ω) w => (x, f w)) <$> cmd⟩

@[inline]
protected def pure [One ω] (a : α) : WriterTₓ ω m α :=
  ⟨pure (a, 1)⟩

@[inline]
protected def bind [Mul ω] (x : WriterTₓ ω m α) (f : α → WriterTₓ ω m β) : WriterTₓ ω m β :=
  ⟨do
    let x ← x.run
    let x' ← (f x.1).run
    pure (x'.1, x.2 * x'.2)⟩

instance [One ω] [Mul ω] : Monadₓ (WriterTₓ ω m) where
  pure := fun α => WriterTₓ.pure
  bind := fun α β => WriterTₓ.bind

instance [Monoidₓ ω] [IsLawfulMonad m] : IsLawfulMonad (WriterTₓ ω m) where
  id_map := by
    intros
    cases x
    simp [← (· <$> ·), ← WriterTₓ.bind, ← WriterTₓ.pure]
  pure_bind := by
    intros
    simp [← Pure.pure, ← WriterTₓ.pure, ← (· >>= ·), ← WriterTₓ.bind]
    ext <;> rfl
  bind_assoc := by
    intros
    simp' [← (· >>= ·), ← WriterTₓ.bind, ← mul_assoc] with functor_norm

@[inline]
protected def lift [One ω] (a : m α) : WriterTₓ ω m α :=
  ⟨flip Prod.mk 1 <$> a⟩

instance (m) [Monadₓ m] [One ω] : HasMonadLift m (WriterTₓ ω m) :=
  ⟨fun α => WriterTₓ.lift⟩

@[inline]
protected def monadMap {m m'} [Monadₓ m] [Monadₓ m'] {α} (f : ∀ {α}, m α → m' α) : WriterTₓ ω m α → WriterTₓ ω m' α :=
  fun x => ⟨f x.run⟩

instance (m m') [Monadₓ m] [Monadₓ m'] : MonadFunctorₓ m m' (WriterTₓ ω m) (WriterTₓ ω m') :=
  ⟨@WriterTₓ.monadMap ω m m' _ _⟩

@[inline]
protected def adapt {ω' : Type u} {α : Type u} (f : ω → ω') : WriterTₓ ω m α → WriterTₓ ω' m α := fun x =>
  ⟨Prod.map id f <$> x.run⟩

instance (ε) [One ω] [Monadₓ m] [MonadExcept ε m] : MonadExcept ε (WriterTₓ ω m) where
  throw := fun α => WriterTₓ.lift ∘ throw
  catch := fun α x c => ⟨catch x.run fun e => (c e).run⟩

end

end WriterTₓ

/-- An implementation of [MonadReader](
https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
It does not contain `local` because this function cannot be lifted using `monad_lift`.
Instead, the `monad_reader_adapter` class provides the more general `adapt_reader` function.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader (ρ : out_param (Type u)) (n : Type u → Type u) :=
(lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α) → n α)
```
-/
class MonadWriter (ω : outParam (Type u)) (m : Type u → Type v) where
  tell (w : ω) : m PUnit
  listen {α} : m α → m (α × ω)
  pass {α : Type u} : m (α × (ω → ω)) → m α

export MonadWriter ()

instance {ω : Type u} {m : Type u → Type v} [Monadₓ m] : MonadWriter ω (WriterTₓ ω m) where
  tell := WriterTₓ.tell
  listen := fun α => WriterTₓ.listen
  pass := fun α => WriterTₓ.pass

instance {ω ρ : Type u} {m : Type u → Type v} [Monadₓ m] [MonadWriter ω m] : MonadWriter ω (ReaderTₓ ρ m) where
  tell := fun x => monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨fun r => listen (cmd r)⟩
  pass := fun α ⟨cmd⟩ => ⟨fun r => pass (cmd r)⟩

def swapRight {α β γ} : (α × β) × γ → (α × γ) × β
  | ⟨⟨x, y⟩, z⟩ => ((x, z), y)

instance {ω σ : Type u} {m : Type u → Type v} [Monadₓ m] [MonadWriter ω m] : MonadWriter ω (StateTₓ σ m) where
  tell := fun x => monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨fun r => swapRight <$> listen (cmd r)⟩
  pass := fun α ⟨cmd⟩ => ⟨fun r => pass (swapRight <$> cmd r)⟩

open Function

def ExceptTₓ.passAux {ε α ω} : Except ε (α × (ω → ω)) → Except ε α × (ω → ω)
  | Except.error a => (Except.error a, id)
  | Except.ok (x, y) => (Except.ok x, y)

instance {ω ε : Type u} {m : Type u → Type v} [Monadₓ m] [MonadWriter ω m] : MonadWriter ω (ExceptTₓ ε m) where
  tell := fun x => monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨(uncurry fun x y => flip Prod.mk y <$> x) <$> listen cmd⟩
  pass := fun α ⟨cmd⟩ => ⟨pass (ExceptTₓ.passAux <$> cmd)⟩

def OptionTₓ.passAux {α ω} : Option (α × (ω → ω)) → Option α × (ω → ω)
  | none => (none, id)
  | some (x, y) => (some x, y)

instance {ω : Type u} {m : Type u → Type v} [Monadₓ m] [MonadWriter ω m] : MonadWriter ω (OptionTₓ m) where
  tell := fun x => monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨(uncurry fun x y => flip Prod.mk y <$> x) <$> listen cmd⟩
  pass := fun α ⟨cmd⟩ => ⟨pass (OptionTₓ.passAux <$> cmd)⟩

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to
[Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `monad_functor`.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader_functor (ρ ρ' : out_param (Type u)) (n n' : Type u → Type u) :=
(map {α : Type u} :
  (∀ {m : Type u → Type u} [monad m], reader_t ρ m α → reader_t ρ' m α) → n α → n' α)
```
-/
class MonadWriterAdapter (ω ω' : outParam (Type u)) (m m' : Type u → Type v) where
  adaptWriter {α : Type u} : (ω → ω') → m α → m' α

export MonadWriterAdapter (adaptWriter)

section

variable {ω ω' : Type u} {m m' : Type u → Type v}

/-- Transitivity.

This instance generates the type-class problem with a metavariable argument (which is why this
is marked as `[nolint dangerous_instance]`).
Currently that is not a problem, as there are almost no instances of `monad_functor` or
`monad_writer_adapter`.

see Note [lower instance priority] -/
@[nolint dangerous_instance]
instance (priority := 100) monadWriterAdapterTrans {n n' : Type u → Type v} [MonadWriterAdapter ω ω' m m']
    [MonadFunctorₓ m m' n n'] : MonadWriterAdapter ω ω' n n' :=
  ⟨fun α f => monadMap fun α => (adaptWriter f : m α → m' α)⟩

instance [Monadₓ m] : MonadWriterAdapter ω ω' (WriterTₓ ω m) (WriterTₓ ω' m) :=
  ⟨fun α => WriterTₓ.adapt⟩

end

instance (ω : Type u) (m out) [MonadRun out m] : MonadRun (fun α => out (α × ω)) (WriterTₓ ω m) :=
  ⟨fun α x => run <| x.run⟩

/-- reduce the equivalence between two writer monads to the equivalence between
their underlying monad -/
def WriterTₓ.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ ω₁ : Type u₀} {α₂ ω₂ : Type u₁}
    (F : m₁ (α₁ × ω₁) ≃ m₂ (α₂ × ω₂)) : WriterTₓ ω₁ m₁ α₁ ≃ WriterTₓ ω₂ m₂ α₂ where
  toFun := fun ⟨f⟩ => ⟨F f⟩
  invFun := fun ⟨f⟩ => ⟨F.symm f⟩
  left_inv := fun ⟨f⟩ => congr_arg WriterTₓ.mk <| F.left_inv _
  right_inv := fun ⟨f⟩ => congr_arg WriterTₓ.mk <| F.right_inv _

