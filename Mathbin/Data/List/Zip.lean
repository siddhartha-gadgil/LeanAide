/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Mathbin.Data.List.BigOperators

/-!
# zip & unzip

This file provides results about `list.zip_with`, `list.zip` and `list.unzip` (definitions are in
core Lean).
`zip_with f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : list α` and `l₂ : list β`. It
applies, until one of the lists is exhausted. For example,
`zip_with f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zip_with` applied to `prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/


universe u

open Nat

namespace List

variable {α : Type u} {β γ δ : Type _}

@[simp]
theorem zip_with_cons_cons (f : α → β → γ) (a : α) (b : β) (l₁ : List α) (l₂ : List β) :
    zipWithₓ f (a :: l₁) (b :: l₂) = f a b :: zipWithₓ f l₁ l₂ :=
  rfl

@[simp]
theorem zip_cons_cons (a : α) (b : β) (l₁ : List α) (l₂ : List β) : zipₓ (a :: l₁) (b :: l₂) = (a, b) :: zipₓ l₁ l₂ :=
  rfl

@[simp]
theorem zip_with_nil_left (f : α → β → γ) (l) : zipWithₓ f [] l = [] :=
  rfl

@[simp]
theorem zip_with_nil_right (f : α → β → γ) (l) : zipWithₓ f l [] = [] := by
  cases l <;> rfl

@[simp]
theorem zip_with_eq_nil_iff {f : α → β → γ} {l l'} : zipWithₓ f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp

@[simp]
theorem zip_nil_left (l : List α) : zipₓ ([] : List β) l = [] :=
  rfl

@[simp]
theorem zip_nil_right (l : List α) : zipₓ l ([] : List β) = [] :=
  zip_with_nil_right _ l

@[simp]
theorem zip_swap : ∀ (l₁ : List α) (l₂ : List β), (zipₓ l₁ l₂).map Prod.swap = zipₓ l₂ l₁
  | [], l₂ => (zip_nil_right _).symm
  | l₁, [] => by
    rw [zip_nil_right] <;> rfl
  | a :: l₁, b :: l₂ => by
    simp only [← zip_cons_cons, ← map_cons, ← zip_swap l₁ l₂, ← Prod.swap_prod_mk] <;> constructor <;> rfl

@[simp]
theorem length_zip_with (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), length (zipWithₓ f l₁ l₂) = min (length l₁) (length l₂)
  | [], l₂ => rfl
  | l₁, [] => by
    simp only [← length, ← min_zero, ← zip_with_nil_right]
  | a :: l₁, b :: l₂ => by
    simp [← length, ← zip_cons_cons, ← length_zip_with l₁ l₂, ← min_add_add_right]

@[simp]
theorem length_zip : ∀ (l₁ : List α) (l₂ : List β), length (zipₓ l₁ l₂) = min (length l₁) (length l₂) :=
  length_zip_with _

theorem all₂_zip_with {f : α → β → γ} {p : γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂),
      All₂ p (zipWithₓ f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)) l₁ l₂
  | [], [], _ => by
    simp
  | a :: l₁, b :: l₂, h => by
    simp only [← length_cons, ← add_left_injₓ] at h
    simp [← all₂_zip_with h]

theorem lt_length_left_of_zip_with {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWithₓ f l l').length) : i < l.length := by
  rw [length_zip_with, lt_min_iff] at h
  exact h.left

theorem lt_length_right_of_zip_with {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWithₓ f l l').length) : i < l'.length := by
  rw [length_zip_with, lt_min_iff] at h
  exact h.right

theorem lt_length_left_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zipₓ l l').length) : i < l.length :=
  lt_length_left_of_zip_with h

theorem lt_length_right_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zipₓ l l').length) : i < l'.length :=
  lt_length_right_of_zip_with h

theorem zip_append :
    ∀ {l₁ r₁ : List α} {l₂ r₂ : List β} (h : length l₁ = length l₂),
      zipₓ (l₁ ++ r₁) (l₂ ++ r₂) = zipₓ l₁ l₂ ++ zipₓ r₁ r₂
  | [], r₁, l₂, r₂, h => by
    simp only [← eq_nil_of_length_eq_zero h.symm] <;> rfl
  | l₁, r₁, [], r₂, h => by
    simp only [← eq_nil_of_length_eq_zero h] <;> rfl
  | a :: l₁, r₁, b :: l₂, r₂, h => by
    simp only [← cons_append, ← zip_cons_cons, ← zip_append (succ.inj h)] <;> constructor <;> rfl

theorem zip_map (f : α → γ) (g : β → δ) :
    ∀ (l₁ : List α) (l₂ : List β), zipₓ (l₁.map f) (l₂.map g) = (zipₓ l₁ l₂).map (Prod.map f g)
  | [], l₂ => rfl
  | l₁, [] => by
    simp only [← map, ← zip_nil_right]
  | a :: l₁, b :: l₂ => by
    simp only [← map, ← zip_cons_cons, ← zip_map l₁ l₂, ← Prod.map] <;> constructor <;> rfl

theorem zip_map_left (f : α → γ) (l₁ : List α) (l₂ : List β) : zipₓ (l₁.map f) l₂ = (zipₓ l₁ l₂).map (Prod.map f id) :=
  by
  rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : List α) (l₂ : List β) : zipₓ l₁ (l₂.map f) = (zipₓ l₁ l₂).map (Prod.map id f) :=
  by
  rw [← zip_map, map_id]

@[simp]
theorem zip_with_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (as : List α) (bs : List β) :
    zipWithₓ f (as.map g) (bs.map h) = zipWithₓ (fun a b => f (g a) (h b)) as bs := by
  induction as generalizing bs
  · simp
    
  · cases bs <;> simp [*]
    

theorem zip_with_map_left (f : α → β → γ) (g : δ → α) (l : List δ) (l' : List β) :
    zipWithₓ f (l.map g) l' = zipWithₓ (f ∘ g) l l' := by
  convert zip_with_map f g id l l'
  exact Eq.symm (List.map_id _)

theorem zip_with_map_right (f : α → β → γ) (l : List α) (g : δ → β) (l' : List δ) :
    zipWithₓ f l (l'.map g) = zipWithₓ (fun x => f x ∘ g) l l' := by
  convert List.zip_with_map f id g l l'
  exact Eq.symm (List.map_id _)

theorem zip_map' (f : α → β) (g : α → γ) : ∀ l : List α, zipₓ (l.map f) (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by
    simp only [← map, ← zip_cons_cons, ← zip_map' l] <;> constructor <;> rfl

theorem map_zip_with {δ : Type _} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWithₓ g l l') = zipWithₓ (fun x y => f (g x y)) l l' := by
  induction' l with hd tl hl generalizing l'
  · simp
    
  · cases l'
    · simp
      
    · simp [← hl]
      
    

theorem mem_zip {a b} : ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ zipₓ l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
  | _ :: l₁, _ :: l₂, Or.inl rfl => ⟨Or.inl rfl, Or.inl rfl⟩
  | a' :: l₁, b' :: l₂, Or.inr h => by
    constructor <;> simp only [← mem_cons_iff, ← or_trueₓ, ← mem_zip h]

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem map_fst_zip : ∀ (l₁ : List α) (l₂ : List β), l₁.length ≤ l₂.length → map Prod.fst (zipₓ l₁ l₂) = l₁
  | [], bs, _ => rfl
  | a :: as, b :: bs, h => by
    simp at h
    simp [*]
  | a :: as, [], h => by
    simp at h
    contradiction

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem map_snd_zip : ∀ (l₁ : List α) (l₂ : List β), l₂.length ≤ l₁.length → map Prod.snd (zipₓ l₁ l₂) = l₂
  | _, [], _ => by
    rw [zip_nil_right]
    rfl
  | [], b :: bs, h => by
    simp at h
    contradiction
  | a :: as, b :: bs, h => by
    simp at h
    simp [*]

@[simp]
theorem unzip_nil : unzip (@nil (α × β)) = ([], []) :=
  rfl

@[simp]
theorem unzip_cons (a : α) (b : β) (l : List (α × β)) : unzip ((a, b) :: l) = (a :: (unzip l).1, b :: (unzip l).2) := by
  rw [unzip] <;> cases unzip l <;> rfl

theorem unzip_eq_map : ∀ l : List (α × β), unzip l = (l.map Prod.fst, l.map Prod.snd)
  | [] => rfl
  | (a, b) :: l => by
    simp only [← unzip_cons, ← map_cons, ← unzip_eq_map l]

theorem unzip_left (l : List (α × β)) : (unzip l).1 = l.map Prod.fst := by
  simp only [← unzip_eq_map]

theorem unzip_right (l : List (α × β)) : (unzip l).2 = l.map Prod.snd := by
  simp only [← unzip_eq_map]

theorem unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).swap := by
  simp only [← unzip_eq_map, ← map_map] <;> constructor <;> rfl

theorem zip_unzip : ∀ l : List (α × β), zipₓ (unzip l).1 (unzip l).2 = l
  | [] => rfl
  | (a, b) :: l => by
    simp only [← unzip_cons, ← zip_cons_cons, ← zip_unzip l] <;> constructor <;> rfl

theorem unzip_zip_left : ∀ {l₁ : List α} {l₂ : List β}, length l₁ ≤ length l₂ → (unzip (zipₓ l₁ l₂)).1 = l₁
  | [], l₂, h => rfl
  | l₁, [], h => by
    rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zeroₓ h)] <;> rfl
  | a :: l₁, b :: l₂, h => by
    simp only [← zip_cons_cons, ← unzip_cons, ← unzip_zip_left (le_of_succ_le_succ h)] <;> constructor <;> rfl

theorem unzip_zip_right {l₁ : List α} {l₂ : List β} (h : length l₂ ≤ length l₁) : (unzip (zipₓ l₁ l₂)).2 = l₂ := by
  rw [← zip_swap, unzip_swap] <;> exact unzip_zip_left h

theorem unzip_zip {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) : unzip (zipₓ l₁ l₂) = (l₁, l₂) := by
  rw [← @Prod.mk.eta _ _ (unzip (zip l₁ l₂)), unzip_zip_left (le_of_eqₓ h), unzip_zip_right (ge_of_eq h)]

theorem zip_of_prod {l : List α} {l' : List β} {lp : List (α × β)} (hl : lp.map Prod.fst = l)
    (hr : lp.map Prod.snd = l') : lp = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip lp, ← unzip_left, ← unzip_right, zip_unzip, zip_unzip]

theorem map_prod_left_eq_zip {l : List α} (f : α → β) : (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rw [← zip_map']
  congr
  exact map_id _

theorem map_prod_right_eq_zip {l : List α} (f : α → β) : (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rw [← zip_map']
  congr
  exact map_id _

theorem zip_with_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWithₓ f l l' = zipWithₓ f l' l := by
  induction' l with hd tl hl generalizing l'
  · simp
    
  · cases l'
    · simp
      
    · simp [← comm, ← hl]
      
    

instance (f : α → α → β) [IsSymmOp α β f] : IsSymmOp (List α) (List β) (zipWithₓ f) :=
  ⟨zip_with_comm f IsSymmOp.symm_op⟩

@[simp]
theorem length_revzip (l : List α) : length (revzipₓ l) = length l := by
  simp only [← revzip, ← length_zip, ← length_reverse, ← min_selfₓ]

@[simp]
theorem unzip_revzip (l : List α) : (revzipₓ l).unzip = (l, l.reverse) :=
  unzip_zip (length_reverse l).symm

@[simp]
theorem revzip_map_fst (l : List α) : (revzipₓ l).map Prod.fst = l := by
  rw [← unzip_left, unzip_revzip]

@[simp]
theorem revzip_map_snd (l : List α) : (revzipₓ l).map Prod.snd = l.reverse := by
  rw [← unzip_right, unzip_revzip]

theorem reverse_revzip (l : List α) : reverse l.revzip = revzipₓ l.reverse := by
  rw [← zip_unzip.{u, u} (revzip l).reverse, unzip_eq_map] <;> simp <;> simp [← revzip]

theorem revzip_swap (l : List α) : (revzipₓ l).map Prod.swap = revzipₓ l.reverse := by
  simp [← revzip]

theorem nth_zip_with (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ) :
    (zipWithₓ f l₁ l₂).nth i = ((l₁.nth i).map f).bind fun g => (l₂.nth i).map g := by
  induction l₁ generalizing l₂ i
  · simp [← zip_with, ← (· <*> ·)]
    
  · cases l₂ <;> simp only [← zip_with, ← Seqₓ.seq, ← Functor.map, ← nth, ← Option.map_none'ₓ]
    · cases (l₁_hd :: l₁_tl).nth i <;> rfl
      
    · cases i <;> simp only [← Option.map_some'ₓ, ← nth, ← Option.some_bind', *]
      
    

theorem nth_zip_with_eq_some {α β γ} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (z : γ) (i : ℕ) :
    (zipWithₓ f l₁ l₂).nth i = some z ↔ ∃ x y, l₁.nth i = some x ∧ l₂.nth i = some y ∧ f x y = z := by
  induction l₁ generalizing l₂ i
  · simp [← zip_with]
    
  · cases l₂ <;> simp only [← zip_with, ← nth, ← exists_false, ← and_falseₓ, ← false_andₓ]
    cases i <;> simp [*]
    

theorem nth_zip_eq_some (l₁ : List α) (l₂ : List β) (z : α × β) (i : ℕ) :
    (zipₓ l₁ l₂).nth i = some z ↔ l₁.nth i = some z.1 ∧ l₂.nth i = some z.2 := by
  cases z
  rw [zip, nth_zip_with_eq_some]
  constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    cc
    
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩
    

@[simp]
theorem nth_le_zip_with {f : α → β → γ} {l : List α} {l' : List β} {i : ℕ} {h : i < (zipWithₓ f l l').length} :
    (zipWithₓ f l l').nthLe i h =
      f (l.nthLe i (lt_length_left_of_zip_with h)) (l'.nthLe i (lt_length_right_of_zip_with h)) :=
  by
  rw [← Option.some_inj, ← nth_le_nth, nth_zip_with_eq_some]
  refine' ⟨l.nth_le i (lt_length_left_of_zip_with h), l'.nth_le i (lt_length_right_of_zip_with h), nth_le_nth _, _⟩
  simp only [nth_le_nth, ← eq_self_iff_true, ← and_selfₓ]

@[simp]
theorem nth_le_zip {l : List α} {l' : List β} {i : ℕ} {h : i < (zipₓ l l').length} :
    (zipₓ l l').nthLe i h = (l.nthLe i (lt_length_left_of_zip h), l'.nthLe i (lt_length_right_of_zip h)) :=
  nth_le_zip_with

theorem mem_zip_inits_tails {l : List α} {init tail : List α} :
    (init, tail) ∈ zipₓ l.inits l.tails ↔ init ++ tail = l := by
  induction l generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  · simp
    
  · constructor <;> rw [mem_cons_iff, zip_map_left, mem_map, Prod.exists]
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      · simp
        
      · simp [← l_ih.mp h]
        
      
    · cases init
      · simp
        
      · intro h
        right
        use init_tl, tail
        simp_all
        
      
    

theorem map_uncurry_zip_eq_zip_with (f : α → β → γ) (l : List α) (l' : List β) :
    map (Function.uncurry f) (l.zip l') = zipWithₓ f l l' := by
  induction' l with hd tl hl generalizing l'
  · simp
    
  · cases' l' with hd' tl'
    · simp
      
    · simp [← hl]
      
    

@[simp]
theorem sum_zip_with_distrib_left {γ : Type _} [Semiringₓ γ] (f : α → β → γ) (n : γ) (l : List α) (l' : List β) :
    (l.zipWith (fun x y => n * f x y) l').Sum = n * (l.zipWith f l').Sum := by
  induction' l with hd tl hl generalizing f n l'
  · simp
    
  · cases' l' with hd' tl'
    · simp
      
    · simp [← hl, ← mul_addₓ]
      
    

section Distribₓ

/-! ### Operations that can be applied before or after a `zip_with` -/


variable (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)

theorem zip_with_distrib_take : (zipWithₓ f l l').take n = zipWithₓ f (l.take n) (l'.take n) := by
  induction' l with hd tl hl generalizing l' n
  · simp
    
  · cases l'
    · simp
      
    · cases n
      · simp
        
      · simp [← hl]
        
      
    

theorem zip_with_distrib_drop : (zipWithₓ f l l').drop n = zipWithₓ f (l.drop n) (l'.drop n) := by
  induction' l with hd tl hl generalizing l' n
  · simp
    
  · cases l'
    · simp
      
    · cases n
      · simp
        
      · simp [← hl]
        
      
    

theorem zip_with_distrib_tail : (zipWithₓ f l l').tail = zipWithₓ f l.tail l'.tail := by
  simp_rw [← drop_one, zip_with_distrib_drop]

theorem zip_with_append (f : α → β → γ) (l la : List α) (l' lb : List β) (h : l.length = l'.length) :
    zipWithₓ f (l ++ la) (l' ++ lb) = zipWithₓ f l l' ++ zipWithₓ f la lb := by
  induction' l with hd tl hl generalizing l'
  · have : l' = [] :=
      eq_nil_of_length_eq_zero
        (by
          simpa using h.symm)
    simp [← this]
    
  · cases l'
    · simpa using h
      
    · simp only [← add_left_injₓ, ← length] at h
      simp [← hl _ h]
      
    

theorem zip_with_distrib_reverse (h : l.length = l'.length) :
    (zipWithₓ f l l').reverse = zipWithₓ f l.reverse l'.reverse := by
  induction' l with hd tl hl generalizing l'
  · simp
    
  · cases' l' with hd' tl'
    · simp
      
    · simp only [← add_left_injₓ, ← length] at h
      have : tl.reverse.length = tl'.reverse.length := by
        simp [← h]
      simp [← hl _ h, ← zip_with_append _ _ _ _ _ this]
      
    

end Distribₓ

section CommMonoidₓ

variable [CommMonoidₓ α]

@[to_additive]
theorem prod_mul_prod_eq_prod_zip_with_mul_prod_drop :
    ∀ L L' : List α, L.Prod * L'.Prod = (zipWithₓ (· * ·) L L').Prod * (L.drop L'.length).Prod * (L'.drop L.length).Prod
  | [], ys => by
    simp
  | xs, [] => by
    simp
  | x :: xs, y :: ys => by
    simp only [← drop, ← length, ← zip_with_cons_cons, ← prod_cons]
    rw [mul_assoc x, mul_comm xs.prod, mul_assoc y, mul_comm ys.prod,
      prod_mul_prod_eq_prod_zip_with_mul_prod_drop xs ys, mul_assoc, mul_assoc, mul_assoc, mul_assoc]

@[to_additive]
theorem prod_mul_prod_eq_prod_zip_with_of_length_eq (L L' : List α) (h : L.length = L'.length) :
    L.Prod * L'.Prod = (zipWithₓ (· * ·) L L').Prod :=
  (prod_mul_prod_eq_prod_zip_with_mul_prod_drop L L').trans
    (by
      simp [← h])

end CommMonoidₓ

end List

