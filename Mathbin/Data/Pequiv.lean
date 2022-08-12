/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Data.Set.Basic

/-!

# Partial Equivalences

In this file, we define partial equivalences `pequiv`, which are a bijection between a subset of `α`
and a subset of `β`. Notationally, a `pequiv` is denoted by "`≃.`" (note that the full stop is part
of the notation). The way we store these internally is with two functions `f : α → option β` and
the reverse function `g : β → option α`, with the condition that if `f a` is `option.some b`,
then `g b` is `option.some a`.

## Main results

- `pequiv.of_set`: creates a `pequiv` from a set `s`,
  which sends an element to itself if it is in `s`.
- `pequiv.single`: given two elements `a : α` and `b : β`, create a `pequiv` that sends them to
  each other, and ignores all other elements.
- `pequiv.injective_of_forall_ne_is_some`/`injective_of_forall_is_some`: If the domain of a `pequiv`
  is all of `α` (except possibly one point), its `to_fun` is injective.

## Canonical order

`pequiv` is canonically ordered by inclusion; that is, if a function `f` defined on a subset `s`
is equal to `g` on that subset, but `g` is also defined on a larger set, then `f ≤ g`. We also have
a definition of `⊥`, which is the empty `pequiv` (sends all to `none`), which in the end gives us a
`semilattice_inf` with an `order_bot` instance.

## Tags

pequiv, partial equivalence

-/


universe u v w x

/-- A `pequiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `local_equiv` for a version that requires `to_fun` and
`inv_fun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
structure Pequiv (α : Type u) (β : Type v) where
  toFun : α → Option β
  invFun : β → Option α
  inv : ∀ (a : α) (b : β), a ∈ inv_fun b ↔ b ∈ to_fun a

-- mathport name: «expr ≃. »
infixr:25 " ≃. " => Pequiv

namespace Pequiv

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Function Option

instance : CoeFun (α ≃. β) fun _ => α → Option β :=
  ⟨toFun⟩

@[simp]
theorem coe_mk_apply (f₁ : α → Option β) (f₂ : β → Option α) (h) (x : α) :
    (Pequiv.mk f₁ f₂ h : α → Option β) x = f₁ x :=
  rfl

@[ext]
theorem ext : ∀ {f g : α ≃. β} (h : ∀ x, f x = g x), f = g
  | ⟨f₁, f₂, hf⟩, ⟨g₁, g₂, hg⟩, h => by
    have h : f₁ = g₁ := funext h
    have : ∀ b, f₂ b = g₂ b := by
      subst h
      intro b
      have hf := fun a => hf a b
      have hg := fun a => hg a b
      cases' h : g₂ b with a
      · simp only [← h, ← Option.not_mem_none, ← false_iffₓ] at hg
        simp only [← hg, ← iff_falseₓ] at hf
        rwa [Option.eq_none_iff_forall_not_mem]
        
      · rw [← Option.mem_def, hf, ← hg, h, Option.mem_def]
        
    simp [*, ← funext_iff]

theorem ext_iff {f g : α ≃. β} : f = g ↔ ∀ x, f x = g x :=
  ⟨congr_fun ∘ congr_arg _, ext⟩

/-- The identity map as a partial equivalence. -/
@[refl]
protected def refl (α : Type _) : α ≃. α where
  toFun := some
  invFun := some
  inv := fun _ _ => eq_comm

/-- The inverse partial equivalence. -/
@[symm]
protected def symm (f : α ≃. β) : β ≃. α where
  toFun := f.2
  invFun := f.1
  inv := fun _ _ => (f.inv _ _).symm

theorem mem_iff_mem (f : α ≃. β) : ∀ {a : α} {b : β}, a ∈ f.symm b ↔ b ∈ f a :=
  f.3

theorem eq_some_iff (f : α ≃. β) : ∀ {a : α} {b : β}, f.symm b = some a ↔ f a = some b :=
  f.3

/-- Composition of partial equivalences `f : α ≃. β` and `g : β ≃. γ`. -/
@[trans]
protected def trans (f : α ≃. β) (g : β ≃. γ) : α ≃. γ where
  toFun := fun a => (f a).bind g
  invFun := fun a => (g.symm a).bind f.symm
  inv := fun a b => by
    simp_all [← And.comm, ← eq_some_iff f, ← eq_some_iff g]

@[simp]
theorem refl_apply (a : α) : Pequiv.refl α a = some a :=
  rfl

@[simp]
theorem symm_refl : (Pequiv.refl α).symm = Pequiv.refl α :=
  rfl

@[simp]
theorem symm_symm (f : α ≃. β) : f.symm.symm = f := by
  cases f <;> rfl

theorem symm_injective : Function.Injective (@Pequiv.symm α β) :=
  LeftInverse.injective symm_symm

theorem trans_assoc (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) : (f.trans g).trans h = f.trans (g.trans h) :=
  ext fun _ => Option.bind_assoc _ _ _

theorem mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) : c ∈ f.trans g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b :=
  Option.bind_eq_some'

theorem trans_eq_some (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    f.trans g a = some c ↔ ∃ b, f a = some b ∧ g b = some c :=
  Option.bind_eq_some'

theorem trans_eq_none (f : α ≃. β) (g : β ≃. γ) (a : α) : f.trans g a = none ↔ ∀ b c, b ∉ f a ∨ c ∉ g b := by
  simp only [← eq_none_iff_forall_not_mem, ← mem_trans, ← imp_iff_not_or.symm]
  push_neg
  tauto

@[simp]
theorem refl_trans (f : α ≃. β) : (Pequiv.refl α).trans f = f := by
  ext <;> dsimp' [← Pequiv.trans] <;> rfl

@[simp]
theorem trans_refl (f : α ≃. β) : f.trans (Pequiv.refl β) = f := by
  ext <;> dsimp' [← Pequiv.trans] <;> simp

protected theorem inj (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) : a₁ = a₂ := by
  rw [← mem_iff_mem] at * <;> cases h : f.symm b <;> simp_all

/-- If the domain of a `pequiv` is `α` except a point, its forward direction is injective. -/
theorem injective_of_forall_ne_is_some (f : α ≃. β) (a₂ : α) (h : ∀ a₁ : α, a₁ ≠ a₂ → isSome (f a₁)) : Injective f :=
  HasLeftInverse.injective
    ⟨fun b => Option.recOn b a₂ fun b' => Option.recOn (f.symm b') a₂ id, fun x => by
      classical
      cases hfx : f x
      · have : x = a₂ :=
          not_imp_comm.1 (h x)
            (hfx.symm ▸ by
              simp )
        simp [← this]
        
      · simp only [← hfx]
        rw [(eq_some_iff f).2 hfx]
        rfl
        ⟩

/-- If the domain of a `pequiv` is all of `α`, its forward direction is injective. -/
theorem injective_of_forall_is_some {f : α ≃. β} (h : ∀ a : α, isSome (f a)) : Injective f :=
  (Classical.em (Nonempty α)).elim (fun hn => injective_of_forall_ne_is_some f (Classical.choice hn) fun a _ => h a)
    fun hn x => (hn ⟨x⟩).elim

section OfSet

variable (s : Set α) [DecidablePred (· ∈ s)]

/-- Creates a `pequiv` that is the identity on `s`, and `none` outside of it. -/
def ofSet (s : Set α) [DecidablePred (· ∈ s)] : α ≃. α where
  toFun := fun a => if a ∈ s then some a else none
  invFun := fun a => if a ∈ s then some a else none
  inv := fun a b => by
    split_ifs with hb ha ha
    · simp [← eq_comm]
      
    · simp [← ne_of_mem_of_not_mem hb ha]
      
    · simp [← ne_of_mem_of_not_mem ha hb]
      
    · simp
      

theorem mem_of_set_self_iff {s : Set α} [DecidablePred (· ∈ s)] {a : α} : a ∈ ofSet s a ↔ a ∈ s := by
  dsimp' [← of_set] <;> split_ifs <;> simp [*]

theorem mem_of_set_iff {s : Set α} [DecidablePred (· ∈ s)] {a b : α} : a ∈ ofSet s b ↔ a = b ∧ a ∈ s := by
  dsimp' [← of_set]
  split_ifs
  · simp only [← iff_self_and, ← Option.mem_def, ← eq_comm]
    rintro rfl
    exact h
    
  · simp only [← false_iffₓ, ← not_and, ← Option.not_mem_none]
    rintro rfl
    exact h
    

@[simp]
theorem of_set_eq_some_iff {s : Set α} {h : DecidablePred (· ∈ s)} {a b : α} : ofSet s b = some a ↔ a = b ∧ a ∈ s :=
  mem_of_set_iff

@[simp]
theorem of_set_eq_some_self_iff {s : Set α} {h : DecidablePred (· ∈ s)} {a : α} : ofSet s a = some a ↔ a ∈ s :=
  mem_of_set_self_iff

@[simp]
theorem of_set_symm : (ofSet s).symm = ofSet s :=
  rfl

@[simp]
theorem of_set_univ : ofSet Set.Univ = Pequiv.refl α :=
  rfl

@[simp]
theorem of_set_eq_refl {s : Set α} [DecidablePred (· ∈ s)] : ofSet s = Pequiv.refl α ↔ s = Set.Univ :=
  ⟨fun h => by
    rw [Set.eq_univ_iff_forall]
    intro
    rw [← mem_of_set_self_iff, h]
    exact rfl, fun h => by
    simp only [of_set_univ, ← h]⟩

end OfSet

theorem symm_trans_rev (f : α ≃. β) (g : β ≃. γ) : (f.trans g).symm = g.symm.trans f.symm :=
  rfl

theorem self_trans_symm (f : α ≃. β) : f.trans f.symm = ofSet { a | (f a).isSome } := by
  ext
  dsimp' [← Pequiv.trans]
  simp only [← eq_some_iff f, ← Option.is_some_iff_exists, ← Option.mem_def, ← bind_eq_some', ← of_set_eq_some_iff]
  constructor
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨Pequiv.inj _ hb₂ hb₁, b, hb₂⟩
    
  · simp (config := { contextual := true })
    

theorem symm_trans_self (f : α ≃. β) : f.symm.trans f = ofSet { b | (f.symm b).isSome } :=
  symm_injective <| by
    simp [← symm_trans_rev, ← self_trans_symm, -symm_symm]

theorem trans_symm_eq_iff_forall_is_some {f : α ≃. β} : f.trans f.symm = Pequiv.refl α ↔ ∀ a, isSome (f a) := by
  rw [self_trans_symm, of_set_eq_refl, Set.eq_univ_iff_forall] <;> rfl

instance : HasBot (α ≃. β) :=
  ⟨{ toFun := fun _ => none, invFun := fun _ => none,
      inv := by
        simp }⟩

instance : Inhabited (α ≃. β) :=
  ⟨⊥⟩

@[simp]
theorem bot_apply (a : α) : (⊥ : α ≃. β) a = none :=
  rfl

@[simp]
theorem symm_bot : (⊥ : α ≃. β).symm = ⊥ :=
  rfl

@[simp]
theorem trans_bot (f : α ≃. β) : f.trans (⊥ : β ≃. γ) = ⊥ := by
  ext <;> dsimp' [← Pequiv.trans] <;> simp

@[simp]
theorem bot_trans (f : β ≃. γ) : (⊥ : α ≃. β).trans f = ⊥ := by
  ext <;> dsimp' [← Pequiv.trans] <;> simp

theorem is_some_symm_get (f : α ≃. β) {a : α} (h : isSome (f a)) : isSome (f.symm (Option.getₓ h)) :=
  is_some_iff_exists.2
    ⟨a, by
      rw [f.eq_some_iff, some_get]⟩

section Single

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Create a `pequiv` which sends `a` to `b` and `b` to `a`, but is otherwise `none`. -/
def single (a : α) (b : β) : α ≃. β where
  toFun := fun x => if x = a then some b else none
  invFun := fun x => if x = b then some a else none
  inv := fun _ _ => by
    simp <;> split_ifs <;> cc

theorem mem_single (a : α) (b : β) : b ∈ single a b a :=
  if_pos rfl

theorem mem_single_iff (a₁ a₂ : α) (b₁ b₂ : β) : b₁ ∈ single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  dsimp' [← single] <;> split_ifs <;> simp [*, ← eq_comm]

@[simp]
theorem symm_single (a : α) (b : β) : (single a b).symm = single b a :=
  rfl

@[simp]
theorem single_apply (a : α) (b : β) : single a b a = some b :=
  if_pos rfl

theorem single_apply_of_ne {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) : single a₁ b a₂ = none :=
  if_neg h.symm

theorem single_trans_of_mem (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c ∈ f b) : (single a b).trans f = single a c := by
  ext
  dsimp' [← single, ← Pequiv.trans]
  split_ifs <;> simp_all

theorem trans_single_of_mem {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b ∈ f a) : f.trans (single b c) = single a c :=
  symm_injective <| single_trans_of_mem _ ((mem_iff_mem f).2 h)

@[simp]
theorem single_trans_single (a : α) (b : β) (c : γ) : (single a b).trans (single b c) = single a c :=
  single_trans_of_mem _ (mem_single _ _)

@[simp]
theorem single_subsingleton_eq_refl [Subsingleton α] (a b : α) : single a b = Pequiv.refl α := by
  ext i j
  dsimp' [← single]
  rw [if_pos (Subsingleton.elimₓ i a), Subsingleton.elimₓ i j, Subsingleton.elimₓ b j]

theorem trans_single_of_eq_none {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none) : f.trans (single b c) = ⊥ := by
  ext
  simp only [← eq_none_iff_forall_not_mem, ← Option.mem_def, ← f.eq_some_iff] at h
  dsimp' [← Pequiv.trans, ← single]
  simp
  intros
  split_ifs <;> simp_all

theorem single_trans_of_eq_none (a : α) {b : β} {f : β ≃. δ} (h : f b = none) : (single a b).trans f = ⊥ :=
  symm_injective <| trans_single_of_eq_none _ h

theorem single_trans_single_of_ne {b₁ b₂ : β} (h : b₁ ≠ b₂) (a : α) (c : γ) : (single a b₁).trans (single b₂ c) = ⊥ :=
  single_trans_of_eq_none _ (single_apply_of_ne h.symm _)

end Single

section Order

instance : PartialOrderₓ (α ≃. β) where
  le := fun f g => ∀ (a : α) (b : β), b ∈ f a → b ∈ g a
  le_refl := fun _ _ _ => id
  le_trans := fun f g h fg gh a b => gh a b ∘ fg a b
  le_antisymm := fun f g fg gf =>
    ext
      (by
        intro a
        cases' h : g a with b
        · exact eq_none_iff_forall_not_mem.2 fun b hb => Option.not_mem_none b <| h ▸ fg a b hb
          
        · exact gf _ _ h
          )

theorem le_def {f g : α ≃. β} : f ≤ g ↔ ∀ (a : α) (b : β), b ∈ f a → b ∈ g a :=
  Iff.rfl

instance : OrderBot (α ≃. β) :=
  { Pequiv.hasBot with bot_le := fun _ _ _ h => (not_mem_none _ h).elim }

instance [DecidableEq α] [DecidableEq β] : SemilatticeInf (α ≃. β) :=
  { -- `split_ifs; finish` closes this goal from here
    Pequiv.partialOrder with
    inf := fun f g =>
      { toFun := fun a => if f a = g a then f a else none,
        invFun := fun b => if f.symm b = g.symm b then f.symm b else none,
        inv := fun a b => by
          have hf := @mem_iff_mem _ _ f a b
          have hg := @mem_iff_mem _ _ g a b
          split_ifs with h1 h2 h2 <;>
            try
              simp [← hf]
          · contrapose! h2
            rw [h2]
            rw [← h1, hf, h2] at hg
            simp only [← mem_def, ← true_iffₓ, ← eq_self_iff_true] at hg
            rw [hg]
            
          · contrapose! h1
            rw [h1] at *
            rw [← h2] at hg
            simp only [← mem_def, ← eq_self_iff_true, ← iff_trueₓ] at hf hg
            rw [hf, hg]
             },
    inf_le_left := fun _ _ _ _ => by
      simp <;> split_ifs <;> cc,
    inf_le_right := fun _ _ _ _ => by
      simp <;> split_ifs <;> cc,
    le_inf := fun f g h fg gh a b => by
      intro H
      have hf := fg a b H
      have hg := gh a b H
      simp only [← Option.mem_def, ← Pequiv.coe_mk_apply]
      split_ifs with h1
      · exact hf
        
      · exact h1 (hf.trans hg.symm)
         }

end Order

end Pequiv

namespace Equivₓ

variable {α : Type _} {β : Type _} {γ : Type _}

/-- Turns an `equiv` into a `pequiv` of the whole type. -/
def toPequiv (f : α ≃ β) : α ≃. β where
  toFun := some ∘ f
  invFun := some ∘ f.symm
  inv := by
    simp [← Equivₓ.eq_symm_apply, ← eq_comm]

@[simp]
theorem to_pequiv_refl : (Equivₓ.refl α).toPequiv = Pequiv.refl α :=
  rfl

theorem to_pequiv_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).toPequiv = f.toPequiv.trans g.toPequiv :=
  rfl

theorem to_pequiv_symm (f : α ≃ β) : f.symm.toPequiv = f.toPequiv.symm :=
  rfl

theorem to_pequiv_apply (f : α ≃ β) (x : α) : f.toPequiv x = some (f x) :=
  rfl

end Equivₓ

