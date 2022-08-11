/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Logic.IsEmpty
import Mathbin.Tactic.Basic
import Mathbin.Logic.Relator

/-!
# Option of a type

This file develops the basic theory of option types.

If `α` is a type, then `option α` can be understood as the type with one more element than `α`.
`option α` has terms `some a`, where `a : α`, and `none`, which is the added element.
This is useful in multiple ways:
* It is the prototype of addition of terms to a type. See for example `with_bot α` which uses
  `none` as an element smaller than all others.
* It can be used to define failsafe partial functions, which return `some the_result_we_expect`
  if we can find `the_result_we_expect`, and `none` if there is no meaningful result. This forces
  any subsequent use of the partial function to explicitly deal with the exceptions that make it
  return `none`.
* `option` is a monad. We love monads.

`part` is an alternative to `option` that can be seen as the type of `true`/`false` values
along with a term `a : α` if the value is `true`.

## Implementation notes

`option` is currently defined in core Lean, but this will change in Lean 4.
-/


namespace Option

variable {α : Type _} {β : Type _} {γ : Type _}

theorem coe_def : (coe : α → Option α) = some :=
  rfl

theorem some_ne_none (x : α) : some x ≠ none := fun h => Option.noConfusion h

protected theorem forall {p : Option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
  ⟨fun h => ⟨h _, fun x => h _⟩, fun h x => Option.casesOn x h.1 h.2⟩

protected theorem exists {p : Option α → Prop} : (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx⟩ => ((Option.casesOn x Or.inl) fun x hx => Or.inr ⟨x, hx⟩) hx, fun h =>
    h.elim (fun h => ⟨_, h⟩) fun ⟨x, hx⟩ => ⟨_, hx⟩⟩

@[simp]
theorem get_memₓ : ∀ {o : Option α} (h : isSome o), Option.getₓ h ∈ o
  | some a, _ => rfl

theorem get_of_memₓ {a : α} : ∀ {o : Option α} (h : isSome o), a ∈ o → Option.getₓ h = a
  | _, _, rfl => rfl

@[simp]
theorem not_mem_none (a : α) : a ∉ (none : Option α) := fun h => Option.noConfusion h

@[simp]
theorem some_getₓ : ∀ {x : Option α} (h : isSome x), some (Option.getₓ h) = x
  | some x, hx => rfl

@[simp]
theorem get_some (x : α) (h : isSome (some x)) : Option.getₓ h = x :=
  rfl

@[simp]
theorem get_or_else_some (x y : α) : Option.getOrElse (some x) y = x :=
  rfl

@[simp]
theorem get_or_else_none (x : α) : Option.getOrElse none x = x :=
  rfl

@[simp]
theorem get_or_else_coe (x y : α) : Option.getOrElse (↑x) y = x :=
  rfl

theorem get_or_else_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getOrElse y) = x := by
  cases x <;> [contradiction, rw [get_or_else_some]]

@[simp]
theorem coe_get {o : Option α} (h : o.isSome) : ((Option.getₓ h : α) : Option α) = o :=
  Option.some_getₓ h

theorem mem_unique {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  Option.some.injₓ <| ha.symm.trans hb

theorem eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a ∈ o1) (h2 : a ∈ o2) : o1 = o2 :=
  h1.trans h2.symm

theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Option α → Prop) := fun a o b => mem_unique

theorem some_injective (α : Type _) : Function.Injective (@some α) := fun _ _ => some_inj.mp

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.Injective f) : Function.Injective (Option.map f)
  | none, none, H => rfl
  | some a₁, some a₂, H => by
    rw [Hf (Option.some.injₓ H)]

@[ext]
theorem ext : ∀ {o₁ o₂ : Option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
  | none, none, H => rfl
  | some a, o, H => ((H _).1 rfl).symm
  | o, some b, H => (H _).2 rfl

theorem eq_none_iff_forall_not_mem {o : Option α} : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e a h => by
    rw [e] at h <;> cases h, fun h =>
    ext <| by
      simpa⟩

@[simp]
theorem none_bindₓ {α β} (f : α → Option β) : none >>= f = none :=
  rfl

@[simp]
theorem some_bindₓ {α β} (a : α) (f : α → Option β) : some a >>= f = f a :=
  rfl

@[simp]
theorem none_bind' (f : α → Option β) : none.bind f = none :=
  rfl

@[simp]
theorem some_bind' (a : α) (f : α → Option β) : (some a).bind f = f a :=
  rfl

@[simp]
theorem bind_some : ∀ x : Option α, x >>= some = x :=
  @bind_pureₓ α Option _ _

@[simp]
theorem bind_eq_someₓ {α β} {x : Option α} {f : α → Option β} {b : β} :
    x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

@[simp]
theorem bind_eq_some' {x : Option α} {f : α → Option β} {b : β} : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
  by
  cases x <;> simp

@[simp]
theorem bind_eq_none' {o : Option α} {f : α → Option β} : o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [← eq_none_iff_forall_not_mem, ← not_exists, ← not_and, ← mem_def, ← bind_eq_some']

@[simp]
theorem bind_eq_noneₓ {α β} {o : Option α} {f : α → Option β} : o >>= f = none ↔ ∀ b a, a ∈ o → b ∉ f a :=
  bind_eq_none'

theorem bind_comm {α β γ} {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl

theorem bind_assoc (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun y => (f y).bind g := by
  cases x <;> rfl

theorem join_eq_some {x : Option (Option α)} {a : α} : x.join = some a ↔ x = some (some a) := by
  simp

theorem join_ne_none {x : Option (Option α)} : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  simp

theorem join_ne_none' {x : Option (Option α)} : ¬x.join = none ↔ ∃ z, x = some (some z) := by
  simp

theorem join_eq_none {o : Option (Option α)} : o.join = none ↔ o = none ∨ o = some none := by
  rcases o with (_ | _ | _) <;> simp

theorem bind_id_eq_join {x : Option (Option α)} : x >>= id = x.join := by
  simp

theorem join_eq_join : mjoin = @join α :=
  funext fun x => by
    rw [mjoin, bind_id_eq_join]

theorem bind_eq_bind {α β : Type _} {f : α → Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl

@[simp]
theorem map_eq_map {α β} {f : α → β} : (· <$> ·) f = Option.map f :=
  rfl

theorem map_none {α β} {f : α → β} : f <$> none = none :=
  rfl

theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) :=
  rfl

theorem map_coe {α β} {a : α} {f : α → β} : f <$> (a : Option α) = ↑(f a) :=
  rfl

@[simp]
theorem map_none'ₓ {f : α → β} : Option.map f none = none :=
  rfl

@[simp]
theorem map_some'ₓ {a : α} {f : α → β} : Option.map f (some a) = some (f a) :=
  rfl

@[simp]
theorem map_coe' {a : α} {f : α → β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl

theorem map_eq_some {α β} {x : Option α} {f : α → β} {b : β} : f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b := by
  cases x <;> simp

@[simp]
theorem map_eq_some' {x : Option α} {f : α → β} {b : β} : x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by
  cases x <;> simp

theorem map_eq_none {α β} {x : Option α} {f : α → β} : f <$> x = none ↔ x = none := by
  cases x <;> simp only [← map_none, ← map_some, ← eq_self_iff_true]

@[simp]
theorem map_eq_none' {x : Option α} {f : α → β} : x.map f = none ↔ x = none := by
  cases x <;> simp only [← map_none', ← map_some', ← eq_self_iff_true]

theorem map_congr {f g : α → β} {x : Option α} (h : ∀, ∀ a ∈ x, ∀, f a = g a) : Option.map f x = Option.map g x := by
  cases x <;> simp only [← map_none', ← map_some', ← h, ← mem_def]

@[simp]
theorem map_id' : Option.map (@id α) = id :=
  map_id

@[simp]
theorem map_mapₓ (h : β → γ) (g : α → β) (x : Option α) : Option.map h (Option.map g x) = Option.map (h ∘ g) x := by
  cases x <;> simp only [← map_none', ← map_some']

theorem comp_mapₓ (h : β → γ) (g : α → β) (x : Option α) : Option.map (h ∘ g) x = Option.map h (Option.map g x) :=
  (map_mapₓ _ _ _).symm

@[simp]
theorem map_comp_mapₓ (f : α → β) (g : β → γ) : Option.map g ∘ Option.map f = Option.map (g ∘ f) := by
  ext x
  rw [comp_map]

theorem mem_map_of_mem {α β : Type _} {a : α} {x : Option α} (g : α → β) (h : a ∈ x) : g a ∈ x.map g :=
  mem_def.mpr ((mem_def.mp h).symm ▸ map_some')

theorem bind_map_commₓ {α β} {x : Option (Option α)} {f : α → β} : x >>= Option.map f = x.map (Option.map f) >>= id :=
  by
  cases x <;> simp

theorem join_map_eq_map_join {f : α → β} {x : Option (Option α)} : (x.map (Option.map f)).join = x.join.map f := by
  rcases x with (_ | _ | x) <;> simp

theorem join_join {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  rcases x with (_ | _ | _ | x) <;> simp

theorem mem_of_mem_join {a : α} {x : Option (Option α)} (h : a ∈ x.join) : some a ∈ x :=
  mem_def.mpr ((mem_def.mp h).symm ▸ join_eq_some.mp h)

section Pmap

variable {p : α → Prop} (f : ∀ a : α, p a → β) (x : Option α)

@[simp]
theorem pbind_eq_bind (f : α → Option β) (x : Option α) : (x.pbind fun a _ => f a) = x.bind f := by
  cases x <;> simp only [← pbind, ← none_bind', ← some_bind']

theorem map_bind {α β γ} (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x >>= g) = x >>= fun a => Option.map f (g a) := by
  simp_rw [← map_eq_map, ← bind_pure_comp_eq_map, IsLawfulMonad.bind_assoc]

theorem map_bind' (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x.bind g) = x.bind fun a => Option.map f (g a) := by
  cases x <;> simp

theorem map_pbind (f : β → γ) (x : Option α) (g : ∀ a, a ∈ x → Option β) :
    Option.map f (x.pbind g) = x.pbind fun a H => Option.map f (g a H) := by
  cases x <;> simp only [← pbind, ← map_none']

theorem pbind_map (f : α → β) (x : Option α) (g : ∀ b : β, b ∈ x.map f → Option γ) :
    pbind (Option.map f x) g = x.pbind fun a h => g (f a) (mem_map_of_mem _ h) := by
  cases x <;> rfl

@[simp]
theorem pmap_none (f : ∀ a : α, p a → β) {H} : pmap f (@none α) H = none :=
  rfl

@[simp]
theorem pmap_some (f : ∀ a : α, p a → β) {x : α} (h : p x) : pmap f (some x) = fun _ => some (f x h) :=
  rfl

theorem mem_pmem {a : α} (h : ∀, ∀ a ∈ x, ∀, p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h := by
  rw [mem_def] at ha⊢
  subst ha
  rfl

theorem pmap_map (g : γ → α) (x : Option γ) (H) :
    pmap f (x.map g) H = pmap (fun a h => f (g a) h) x fun a h => H _ (mem_map_of_mem _ h) := by
  cases x <;> simp only [← map_none', ← map_some', ← pmap]

theorem map_pmap (g : β → γ) (f : ∀ a, p a → β) (x H) : Option.map g (pmap f x H) = pmap (fun a h => g (f a h)) x H :=
  by
  cases x <;> simp only [← map_none', ← map_some', ← pmap]

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (x H) : @pmap _ _ p (fun a _ => f a) x H = Option.map f x := by
  cases x <;> simp only [← map_none', ← map_some', ← pmap]

theorem pmap_bind {α β γ} {x : Option α} {g : α → Option β} {p : β → Prop} {f : ∀ b, p b → γ} (H)
    (H' : ∀ (a : α), ∀ b ∈ g a, ∀, b ∈ x >>= g) :
    pmap f (x >>= g) H = x >>= fun a => pmap f (g a) fun b h => H _ (H' a _ h) := by
  cases x <;> simp only [← pmap, ← none_bind, ← some_bind]

theorem bind_pmap {α β γ} {p : α → Prop} (f : ∀ a, p a → β) (x : Option α) (g : β → Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h => g (f a (H _ h)) := by
  cases x <;> simp only [← pmap, ← none_bind, ← some_bind, ← pbind]

variable {f x}

theorem pbind_eq_none {f : ∀ a : α, a ∈ x → Option β} (h' : ∀, ∀ a ∈ x, ∀, f a H = none → x = none) :
    x.pbind f = none ↔ x = none := by
  cases x
  · simp
    
  · simp only [← pbind, ← iff_falseₓ]
    intro h
    cases h' x rfl h
    

theorem pbind_eq_some {f : ∀ a : α, a ∈ x → Option β} {y : β} : x.pbind f = some y ↔ ∃ z ∈ x, f z H = some y := by
  cases x
  · simp
    
  · simp only [← pbind]
    constructor
    · intro h
      use x
      simpa only [← mem_def, ← exists_prop_of_true] using h
      
    · rintro ⟨z, H, hz⟩
      simp only [← mem_def] at H
      simpa only [← H] using hz
      
    

@[simp]
theorem pmap_eq_none_iff {h} : pmap f x h = none ↔ x = none := by
  cases x <;> simp

@[simp]
theorem pmap_eq_some_iff {hf} {y : β} : pmap f x hf = some y ↔ ∃ (a : α)(H : x = some a), f a (hf a H) = y := by
  cases x
  · simp only [← not_mem_none, ← exists_false, ← pmap, ← not_false_iff, ← exists_prop_of_false]
    
  · constructor
    · intro h
      simp only [← pmap] at h
      exact ⟨x, rfl, h⟩
      
    · rintro ⟨a, H, rfl⟩
      simp only [← mem_def] at H
      simp only [← H, ← pmap]
      
    

@[simp]
theorem join_pmap_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h => H (some a) (mem_of_mem_join h) _ rfl := by
  rcases x with (_ | _ | x) <;> simp

end Pmap

@[simp]
theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl

@[simp]
theorem some_orelse' (a : α) (x : Option α) : (some a).orelse x = some a :=
  rfl

@[simp]
theorem some_orelse (a : α) (x : Option α) : (some a <|> x) = some a :=
  rfl

@[simp]
theorem none_orelse' (x : Option α) : none.orelse x = x := by
  cases x <;> rfl

@[simp]
theorem none_orelseₓ (x : Option α) : (none <|> x) = x :=
  none_orelse' x

@[simp]
theorem orelse_none' (x : Option α) : x.orelse none = x := by
  cases x <;> rfl

@[simp]
theorem orelse_none (x : Option α) : (x <|> none) = x :=
  orelse_none' x

@[simp]
theorem is_some_none : @isSome α none = ff :=
  rfl

@[simp]
theorem is_some_some {a : α} : isSome (some a) = tt :=
  rfl

theorem is_some_iff_exists {x : Option α} : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [← is_some] <;> exact ⟨_, rfl⟩

@[simp]
theorem is_none_none : @isNone α none = tt :=
  rfl

@[simp]
theorem is_none_some {a : α} : isNone (some a) = ff :=
  rfl

@[simp]
theorem not_is_some {a : Option α} : isSome a = ff ↔ a.isNone = tt := by
  cases a <;> simp

theorem eq_some_iff_get_eqₓ {o : Option α} {a : α} : o = some a ↔ ∃ h : o.isSome, Option.getₓ h = a := by
  cases o <;> simp

theorem not_is_some_iff_eq_none {o : Option α} : ¬o.isSome ↔ o = none := by
  cases o <;> simp

theorem ne_none_iff_is_some {o : Option α} : o ≠ none ↔ o.isSome := by
  cases o <;> simp

theorem ne_none_iff_exists {o : Option α} : o ≠ none ↔ ∃ x : α, some x = o := by
  cases o <;> simp

theorem ne_none_iff_exists' {o : Option α} : o ≠ none ↔ ∃ x : α, o = some x :=
  ne_none_iff_exists.trans <| exists_congr fun _ => eq_comm

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » none)
theorem bex_ne_none {p : Option α → Prop} : (∃ (x : _)(_ : x ≠ none), p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ =>
    ⟨get <| ne_none_iff_is_some.1 hx, by
      rwa [some_get]⟩,
    fun ⟨x, hx⟩ => ⟨some x, some_ne_none x, hx⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » none)
theorem ball_ne_none {p : Option α → Prop} : (∀ (x) (_ : x ≠ none), p x) ↔ ∀ x, p (some x) :=
  ⟨fun h x => h (some x) (some_ne_none x), fun h x hx => by
    simpa only [← some_get] using h (get <| ne_none_iff_is_some.1 hx)⟩

theorem iget_mem [Inhabited α] : ∀ {o : Option α}, isSome o → o.iget ∈ o
  | some a, _ => rfl

theorem iget_of_mem [Inhabited α] {a : α} : ∀ {o : Option α}, a ∈ o → o.iget = a
  | _, rfl => rfl

@[simp]
theorem guard_eq_some {p : α → Prop} [DecidablePred p] {a b : α} : guard p a = some b ↔ a = b ∧ p a := by
  by_cases' p a <;> simp [← Option.guard, ← h] <;> intro <;> contradiction

@[simp]
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : guardₓ p = some u ↔ p := by
  cases u
  by_cases' p <;>
    simp [← _root_.guard, ← h] <;>
      first |
        rfl|
        contradiction

theorem lift_or_get_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, liftOrGet f o₁ o₂ = o₁ ∨ liftOrGet f o₁ o₂ = o₂
  | none, none => Or.inl rfl
  | some a, none => Or.inl rfl
  | none, some b => Or.inr rfl
  | some a, some b => by
    simpa [← lift_or_get] using h a b

@[simp]
theorem lift_or_get_none_left {f} {b : Option α} : liftOrGet f none b = b := by
  cases b <;> rfl

@[simp]
theorem lift_or_get_none_right {f} {a : Option α} : liftOrGet f a none = a := by
  cases a <;> rfl

@[simp]
theorem lift_or_get_some_some {f} {a b : α} : liftOrGet f (some a) (some b) = f a b :=
  rfl

/-- Given an element of `a : option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def casesOn' : Option α → β → (α → β) → β
  | none, n, s => n
  | some a, n, s => s a

@[simp]
theorem cases_on'_none (x : β) (f : α → β) : casesOn' none x f = x :=
  rfl

@[simp]
theorem cases_on'_some (x : β) (f : α → β) (a : α) : casesOn' (some a) x f = f a :=
  rfl

@[simp]
theorem cases_on'_coe (x : β) (f : α → β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl

@[simp]
theorem cases_on'_none_coe (f : Option α → β) (o : Option α) : casesOn' o (f none) (f ∘ coe) = f o := by
  cases o <;> rfl

@[simp]
theorem get_or_else_map (f : α → β) (x : α) (o : Option α) : getOrElse (o.map f) (f x) = f (getOrElse o x) := by
  cases o <;> rfl

theorem orelse_eq_some (o o' : Option α) (x : α) : (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x := by
  cases o
  · simp only [← true_andₓ, ← false_orₓ, ← eq_self_iff_true, ← none_orelse]
    
  · simp only [← some_orelse, ← or_falseₓ, ← false_andₓ]
    

theorem orelse_eq_some' (o o' : Option α) (x : α) : o.orelse o' = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  Option.orelse_eq_some o o' x

@[simp]
theorem orelse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none := by
  cases o
  · simp only [← true_andₓ, ← none_orelse, ← eq_self_iff_true]
    
  · simp only [← some_orelse, ← false_andₓ]
    

@[simp]
theorem orelse_eq_none' (o o' : Option α) : o.orelse o' = none ↔ o = none ∧ o' = none :=
  Option.orelse_eq_none o o'

section

open Classical

/-- An arbitrary `some a` with `a : α` if `α` is nonempty, and otherwise `none`. -/
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some h.some else none

theorem choice_eq {α : Type _} [Subsingleton α] (a : α) : choice α = some a := by
  dsimp' [← choice]
  rw [dif_pos (⟨a⟩ : Nonempty α)]
  congr

theorem choice_eq_none (α : Type _) [IsEmpty α] : choice α = none :=
  dif_neg (not_nonempty_iff_imp_false.mpr isEmptyElim)

theorem choice_is_some_iff_nonempty {α : Type _} : (choice α).isSome ↔ Nonempty α := by
  fconstructor
  · intro h
    exact ⟨Option.getₓ h⟩
    
  · intro h
    dsimp' only [← choice]
    rw [dif_pos h]
    exact is_some_some
    

end

@[simp]
theorem to_list_some (a : α) : (a : Option α).toList = [a] :=
  rfl

@[simp]
theorem to_list_none (α : Type _) : (none : Option α).toList = [] :=
  rfl

@[simp]
theorem elim_none_some (f : Option α → β) : Option.elimₓ (f none) (f ∘ some) = f :=
  funext fun o => by
    cases o <;> rfl

end Option

