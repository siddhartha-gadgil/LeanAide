/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.
-/

universe u v w

variable {α β γ : Type u}

-- mathport name: «expr $< »
notation:1 a " $< " f:1 => f a

section Functor

variable {f : Type u → Type v} [Functor f] [IsLawfulFunctor f]

run_cmd
  mk_simp_attr `functor_norm

run_cmd
  tactic.add_doc_string `simp_attr.functor_norm "Simp set for functor_norm"

@[functor_norm]
theorem Functor.map_mapₓ (m : α → β) (g : β → γ) (x : f α) : g <$> m <$> x = (g ∘ m) <$> x :=
  (comp_map _ _ _).symm

@[simp]
theorem id_map'ₓ (x : f α) : (fun a => a) <$> x = x :=
  id_map _

end Functor

section Applicativeₓ

variable {F : Type u → Type v} [Applicativeₓ F]

def mzipWith {α₁ α₂ φ : Type u} (f : α₁ → α₂ → F φ) : ∀ (ma₁ : List α₁) (ma₂ : List α₂), F (List φ)
  | x :: xs, y :: ys => (· :: ·) <$> f x y <*> mzipWith xs ys
  | _, _ => pure []

def mzipWith' (f : α → β → F γ) : List α → List β → F PUnit
  | x :: xs, y :: ys => f x y *> mzipWith' xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit

variable [IsLawfulApplicative F]

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[simp]
theorem pure_id'_seq (x : F α) : (pure fun x => x) <*> x = x :=
  pure_id_seqₓ x

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[functor_norm]
theorem seq_map_assoc (x : F (α → β)) (f : γ → α) (y : F γ) : x <*> f <$> y = (fun m : α → β => m ∘ f) <$> x <*> y := by
  simp [← (pure_seq_eq_map _ _).symm]
  simp [← seq_assoc, ← (comp_map _ _ _).symm, ← (· ∘ ·)]
  simp [← pure_seq_eq_map]

@[functor_norm]
theorem map_seq (f : β → γ) (x : F (α → β)) (y : F α) : f <$> (x <*> y) = (· ∘ ·) f <$> x <*> y := by
  simp [← (pure_seq_eq_map _ _).symm] <;> simp [← seq_assoc]

end Applicativeₓ

-- TODO: setup `functor_norm` for `monad` laws
attribute [functor_norm] pure_bind bind_assoc bind_pureₓ

section Monadₓ

variable {m : Type u → Type v} [Monadₓ m] [IsLawfulMonad m]

open List

def List.mpartition {f : Type → Type} [Monadₓ f] {α : Type} (p : α → f Bool) : List α → f (List α × List α)
  | [] => pure ([], [])
  | x :: xs => mcond (p x) (Prod.map (cons x) id <$> List.mpartition xs) (Prod.map id (cons x) <$> List.mpartition xs)

theorem map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = x >>= fun a => f <$> g a := by
  rw [← bind_pure_comp_eq_map, bind_assoc] <;> simp [← bind_pure_comp_eq_map]

theorem seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : f <$> x >>= g = x >>= g ∘ f :=
  show bind (f <$> x) g = bind x (g ∘ f) by
    rw [← bind_pure_comp_eq_map, bind_assoc] <;> simp [← pure_bind]

theorem seq_eq_bind_mapₓ {x : m α} {f : m (α → β)} : f <*> x = f >>= (· <$> x) :=
  (bind_map_eq_seq f x).symm

/-- This is the Kleisli composition -/
@[reducible]
def fish {m} [Monadₓ m] {α β γ} (f : α → m β) (g : β → m γ) := fun x => f x >>= g

-- mathport name: «expr >=> »
infixl:55
  " >=> " =>-- >=> is already defined in the core library but it is unusable
  -- because of its precedence (it is defined with precedence 2) and
  -- because it is defined as a lambda instead of having a named
  -- function
  fish

@[functor_norm]
theorem fish_pure {α β} (f : α → m β) : f >=> pure = f := by
  simp' only [← (· >=> ·)] with functor_norm

@[functor_norm]
theorem fish_pipe {α β} (f : α → m β) : pure >=> f = f := by
  simp' only [← (· >=> ·)] with functor_norm

@[functor_norm]
theorem fish_assoc {α β γ φ} (f : α → m β) (g : β → m γ) (h : γ → m φ) : f >=> g >=> h = f >=> (g >=> h) := by
  simp' only [← (· >=> ·)] with functor_norm

variable {β' γ' : Type v}

variable {m' : Type v → Type w} [Monadₓ m']

def List.mmapAccumr (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mmapAccumr a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)

def List.mmapAccuml (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mmapAccuml a' xs
    pure (a'', y :: ys)

end Monadₓ

section

variable {m : Type u → Type u} [Monadₓ m] [IsLawfulMonad m]

theorem mjoin_map_map {α β : Type u} (f : α → β) (a : m (m α)) : mjoin (Functor.map f <$> a) = f <$> mjoin a := by
  simp only [← mjoin, ← (· ∘ ·), ← id.def, ← (bind_pure_comp_eq_map _ _).symm, ← bind_assoc, ← map_bind, ← pure_bind]

theorem mjoin_map_mjoin {α : Type u} (a : m (m (m α))) : mjoin (mjoin <$> a) = mjoin (mjoin a) := by
  simp only [← mjoin, ← (· ∘ ·), ← id.def, ← map_bind, ← (bind_pure_comp_eq_map _ _).symm, ← bind_assoc, ← pure_bind]

@[simp]
theorem mjoin_map_pure {α : Type u} (a : m α) : mjoin (pure <$> a) = a := by
  simp only [← mjoin, ← (· ∘ ·), ← id.def, ← map_bind, ← (bind_pure_comp_eq_map _ _).symm, ← bind_assoc, ← pure_bind, ←
    bind_pureₓ]

@[simp]
theorem mjoin_pure {α : Type u} (a : m α) : mjoin (pure a) = a :=
  IsLawfulMonad.pure_bind a id

end

section Alternativeₓ

variable {F : Type → Type v} [Alternativeₓ F]

def succeeds {α} (x : F α) : F Bool :=
  x $> tt <|> pure false

def mtry {α} (x : F α) : F Unit :=
  x $> () <|> pure ()

@[simp]
theorem guard_true {h : Decidable True} : @guardₓ F _ True h = pure () := by
  simp [← guardₓ]

@[simp]
theorem guard_false {h : Decidable False} : @guardₓ F _ False h = failure := by
  simp [← guardₓ]

end Alternativeₓ

namespace Sum

variable {e : Type v}

protected def bindₓ {α β} : Sum e α → (α → Sum e β) → Sum e β
  | inl x, _ => inl x
  | inr x, f => f x

instance : Monadₓ (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bindₓ e

instance : IsLawfulFunctor (Sum.{v, u} e) := by
  refine' { .. } <;> intros <;> casesm Sum _ _ <;> rfl

instance : IsLawfulMonad (Sum.{v, u} e) where
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp_eq_map := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map_eq_seq := by
    intros
    cases f <;> rfl

end Sum

class IsCommApplicative (m : Type _ → Type _) [Applicativeₓ m] extends IsLawfulApplicative m : Prop where
  commutative_prod : ∀ {α β} (a : m α) (b : m β), Prod.mk <$> a <*> b = (fun b a => (a, b)) <$> b <*> a

open Functor

theorem IsCommApplicative.commutative_map {m : Type _ → Type _} [Applicativeₓ m] [IsCommApplicative m] {α β γ} (a : m α)
    (b : m β) {f : α → β → γ} : f <$> a <*> b = flip f <$> b <*> a :=
  calc
    f <$> a <*> b = (fun p : α × β => f p.1 p.2) <$> (Prod.mk <$> a <*> b) := by
      simp [← seq_map_assoc, ← map_seq, ← seq_assoc, ← seq_pure, ← map_map]
    _ = (fun b a => f a b) <$> b <*> a := by
      rw [IsCommApplicative.commutative_prod] <;> simp [← seq_map_assoc, ← map_seq, ← seq_assoc, ← seq_pure, ← map_map]
    

