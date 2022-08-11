/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys
-/
import Mathbin.Data.List.Basic

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f []` = none`

`minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/


namespace List

variable {α β : Type _}

section ArgAux

variable (r : α → α → Prop) [DecidableRel r] {l : List α} {o : Option α} {a m : α}

/-- Auxiliary definition for `argmax` and `argmin`. -/
def argAux (a : Option α) (b : α) : Option α :=
  (Option.casesOn a (some b)) fun c => if r b c then some b else some c

@[simp]
theorem foldl_arg_aux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none :=
  (List.reverseRecOn l
      (by
        simp ))
    fun tl hd => by
    simp [← arg_aux] <;>
      cases foldl (arg_aux r) o tl <;>
        simp <;>
          try
              split_ifs <;>
            simp

private theorem foldl_arg_aux_mem (l) : ∀ a m : α, m ∈ foldlₓ (argAux r) (some a) l → m ∈ a :: l :=
  List.reverseRecOn l
    (by
      simp [← eq_comm])
    (by
      intro tl hd ih a m
      simp only [← foldl_append, ← foldl_cons, ← foldl_nil, ← arg_aux]
      cases hf : foldl (arg_aux r) (some a) tl
      · simp (config := { contextual := true })
        
      · dsimp' only
        split_ifs
        · simp (config := { contextual := true })
          
        · -- `finish [ih _ _ hf]` closes this goal
          rcases ih _ _ hf with (rfl | H)
          · simp only [← mem_cons_iff, ← mem_append, ← mem_singleton, ← Option.mem_def]
            tauto
            
          · apply fun hm => Or.inr (list.mem_append.mpr <| Or.inl _)
            exact option.mem_some_iff.mp hm ▸ H
            
          
        )

@[simp]
theorem arg_aux_self (hr₀ : Irreflexive r) (a : α) : argAux r (some a) a = a :=
  if_neg <| hr₀ _

theorem not_of_mem_foldl_arg_aux (hr₀ : Irreflexive r) (hr₁ : Transitive r) :
    ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ foldlₓ (argAux r) o l → ¬r a m := by
  induction' l using List.reverseRecOn with tl a ih
  · exact fun _ _ _ h => absurd h <| not_mem_nil _
    
  intro b m o hb ho
  rw [foldl_append, foldl_cons, foldl_nil, arg_aux] at ho
  cases' hf : foldl (arg_aux r) o tl with c
  · rw [hf] at ho
    rw [foldl_arg_aux_eq_none] at hf
    simp_all [← hf.1, ← hf.2, ← hr₀ _]
    
  rw [hf, Option.mem_def] at ho
  dsimp' only  at ho
  split_ifs  at ho with hac hac <;> cases' mem_append.1 hb with h h <;> subst ho
  · exact fun hba => ih h hf (hr₁ hba hac)
    
  · simp_all [← hr₀ _]
    
  · exact ih h hf
    
  · simp_all
    

end ArgAux

section Preorderₓ

variable [Preorderₓ β] [@DecidableRel β (· < ·)] {f : α → β} {l : List α} {o : Option α} {a m : α}

/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f []` = none`. -/
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (arg_aux fun b c => f c < f b) none

/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f []` = none`. -/
def argmin (f : α → β) (l : List α) :=
  l.foldl (arg_aux fun b c => f b < f c) none

@[simp]
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl

@[simp]
theorem argmin_nil (f : α → β) : argmin f [] = none :=
  rfl

@[simp]
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = a :=
  rfl

@[simp]
theorem argmin_singleton {f : α → β} {a : α} : argmin f [a] = a :=
  rfl

theorem not_lt_of_mem_argmax : a ∈ l → m ∈ argmax f l → ¬f m < f a :=
  (not_of_mem_foldl_arg_aux _ fun _ => lt_irreflₓ _) fun _ _ _ => gt_transₓ

theorem not_lt_of_mem_argmin : a ∈ l → m ∈ argmin f l → ¬f a < f m :=
  (not_of_mem_foldl_arg_aux _ fun _ => lt_irreflₓ _) fun _ _ _ => lt_transₓ

theorem argmax_concat (f : α → β) (a : α) (l : List α) :
    argmax f (l ++ [a]) = Option.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c := by
  rw [argmax, argmax] <;> simp [← arg_aux]

theorem argmin_concat (f : α → β) (a : α) (l : List α) :
    argmin f (l ++ [a]) = Option.casesOn (argmin f l) (some a) fun c => if f a < f c then some a else some c :=
  @argmax_concat _ βᵒᵈ _ _ _ _ _

theorem argmax_mem : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
  | [], m => by
    simp
  | hd :: tl, m => by
    simpa [← argmax, ← arg_aux] using foldl_arg_aux_mem _ tl hd m

theorem argmin_mem : ∀ {l : List α} {m : α}, m ∈ argmin f l → m ∈ l :=
  @argmax_mem _ βᵒᵈ _ _ _

@[simp]
theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by
  simp [← argmax]

@[simp]
theorem argmin_eq_none : l.argmin f = none ↔ l = [] :=
  @argmax_eq_none _ βᵒᵈ _ _ _ _

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ β] {f : α → β} {l : List α} {o : Option α} {a m : α}

theorem le_of_mem_argmax : a ∈ l → m ∈ argmax f l → f a ≤ f m := fun ha hm =>
  le_of_not_ltₓ <| not_lt_of_mem_argmax ha hm

theorem le_of_mem_argmin : a ∈ l → m ∈ argmin f l → f m ≤ f a :=
  @le_of_mem_argmax _ βᵒᵈ _ _ _ _ _

theorem argmax_cons (f : α → β) (a : α) (l : List α) :
    argmax f (a :: l) = Option.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a :=
  (List.reverseRecOn l rfl) fun hd tl ih => by
    rw [← cons_append, argmax_concat, ih, argmax_concat]
    cases' h : argmax f hd with m
    · simp [← h]
      
    dsimp'
    rw [← apply_ite, ← apply_ite]
    dsimp'
    split_ifs <;>
      try
        rfl
    · exact absurd (lt_transₓ ‹f a < f m› ‹_›) ‹_›
      
    · cases (‹f a < f tl›.lt_or_lt _).elim ‹_› ‹_›
      

theorem argmin_cons (f : α → β) (a : α) (l : List α) :
    argmin f (a :: l) = Option.casesOn (argmin f l) (some a) fun c => if f c < f a then some c else some a := by
  convert @argmax_cons _ βᵒᵈ _ _ _ _

variable [DecidableEq α]

theorem index_of_argmax : ∀ {l : List α} {m : α}, m ∈ argmax f l → ∀ {a}, a ∈ l → f m ≤ f a → l.indexOf m ≤ l.indexOf a
  | [], m, _, _, _, _ => by
    simp
  | hd :: tl, m, hm, a, ha, ham => by
    simp only [← index_of_cons, ← argmax_cons, ← Option.mem_def] at hm⊢
    cases h : argmax f tl
    · rw [h] at hm
      simp_all
      
    rw [h] at hm
    dsimp' only  at hm
    obtain rfl | ha := ha <;> split_ifs  at hm <;> subst hm
    · cases not_le_of_lt ‹_› ‹_›
      
    · rw [if_neg, if_neg]
      exact Nat.succ_le_succₓ (index_of_argmax h ha ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_leₓ ‹_› ‹_›).ne'
        
      · exact ne_of_apply_ne _ ‹f hd < f val›.ne'
        
      
    · rw [if_pos rfl]
      exact bot_le
      

theorem index_of_argmin :
    ∀ {l : List α} {m : α}, m ∈ argmin f l → ∀ {a}, a ∈ l → f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @index_of_argmax _ βᵒᵈ _ _ _

theorem mem_argmax_iff :
    m ∈ argmax f l ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f a ≤ f m) ∧ ∀, ∀ a ∈ l, ∀, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun a ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩, by
    rintro ⟨hml, ham, hma⟩
    cases' harg : argmax f l with n
    · simp_all
      
    · have :=
        le_antisymmₓ (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
          (index_of_argmax harg hml (ham _ (argmax_mem harg)))
      rw [(index_of_inj hml (argmax_mem harg)).1 this, Option.mem_def]
      ⟩

theorem argmax_eq_some_iff :
    argmax f l = some m ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f a ≤ f m) ∧ ∀, ∀ a ∈ l, ∀, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  mem_argmax_iff

theorem mem_argmin_iff :
    m ∈ argmin f l ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f m ≤ f a) ∧ ∀, ∀ a ∈ l, ∀, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @mem_argmax_iff _ βᵒᵈ _ _ _ _ _

theorem argmin_eq_some_iff :
    argmin f l = some m ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f m ≤ f a) ∧ ∀, ∀ a ∈ l, ∀, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  mem_argmin_iff

end LinearOrderₓ

section MaximumMinimum

section Preorderₓ

variable [Preorderₓ α] [@DecidableRel α (· < ·)] {l : List α} {a m : α}

/-- `maximum l` returns an `with_bot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]`  -/
def maximum (l : List α) : WithBot α :=
  argmax id l

/-- `minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`  -/
def minimum (l : List α) : WithTop α :=
  argmin id l

@[simp]
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl

@[simp]
theorem minimum_nil : minimum ([] : List α) = ⊤ :=
  rfl

@[simp]
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl

@[simp]
theorem minimum_singleton (a : α) : minimum [a] = a :=
  rfl

theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem

theorem minimum_mem {l : List α} {m : α} : (minimum l : WithBot α) = m → m ∈ l :=
  argmin_mem

@[simp]
theorem maximum_eq_none {l : List α} : l.maximum = none ↔ l = [] :=
  argmax_eq_none

@[simp]
theorem minimum_eq_none {l : List α} : l.minimum = none ↔ l = [] :=
  argmin_eq_none

theorem not_lt_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → ¬m < a :=
  not_lt_of_mem_argmax

theorem minimum_not_lt_of_mem : a ∈ l → (minimum l : WithTop α) = m → ¬a < m :=
  not_lt_of_mem_argmin

theorem not_lt_maximum_of_mem' (ha : a ∈ l) : ¬maximum l < (a : WithBot α) := by
  cases h : l.maximum
  · simp_all
    
  · simp_rw [WithBot.some_eq_coe, WithBot.coe_lt_coe, not_lt_maximum_of_mem ha h, not_false_iff]
    

theorem not_lt_minimum_of_mem' (ha : a ∈ l) : ¬(a : WithTop α) < minimum l :=
  @not_lt_maximum_of_mem' αᵒᵈ _ _ _ _ ha

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ α] {l : List α} {a m : α}

theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a := by
  simp only [← maximum, ← argmax_concat, ← id]
  cases h : argmax id l
  · exact (max_eq_rightₓ bot_le).symm
    
  · simp [← Option.coe_def, ← max_def, not_ltₓ]
    

theorem le_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_of_mem_argmax

theorem minimum_le_of_mem : a ∈ l → (minimum l : WithTop α) = m → m ≤ a :=
  le_of_mem_argmin

theorem le_maximum_of_mem' (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  le_of_not_ltₓ <| not_lt_maximum_of_mem' ha

theorem le_minimum_of_mem' (ha : a ∈ l) : minimum l ≤ (a : WithTop α) :=
  @le_maximum_of_mem' αᵒᵈ _ _ _ ha

theorem minimum_concat (a : α) (l : List α) : minimum (l ++ [a]) = min (minimum l) a :=
  @maximum_concat αᵒᵈ _ _ _

theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max a (maximum l) :=
  List.reverseRecOn l
    (by
      simp [← @max_eq_leftₓ (WithBot α) _ _ _ bot_le])
    fun tl hd ih => by
    rw [← cons_append, maximum_concat, ih, maximum_concat, max_assocₓ]

theorem minimum_cons (a : α) (l : List α) : minimum (a :: l) = min a (minimum l) :=
  @maximum_cons αᵒᵈ _ _ _

theorem maximum_eq_coe_iff : maximum l = m ↔ m ∈ l ∧ ∀, ∀ a ∈ l, ∀, a ≤ m := by
  unfold_coes
  simp only [← maximum, ← argmax_eq_some_iff, ← id]
  constructor
  · simp (config := { contextual := true })only [← true_andₓ, ← forall_true_iff]
    
  · simp (config := { contextual := true })only [← true_andₓ, ← forall_true_iff]
    intro h a hal hma
    rw [le_antisymmₓ hma (h.2 a hal)]
    

theorem minimum_eq_coe_iff : minimum l = m ↔ m ∈ l ∧ ∀, ∀ a ∈ l, ∀, m ≤ a :=
  @maximum_eq_coe_iff αᵒᵈ _ _ _

end LinearOrderₓ

end MaximumMinimum

section Fold

variable [LinearOrderₓ α]

section OrderBot

variable [OrderBot α] {l : List α}

@[simp]
theorem foldr_max_of_ne_nil (h : l ≠ []) : ↑(l.foldr max ⊥) = l.maximum := by
  induction' l with hd tl IH
  · contradiction
    
  · rw [maximum_cons, foldr, WithBot.coe_max]
    by_cases' h : tl = []
    · simp [← h, -WithTop.coe_zero]
      
    · simp [← IH h]
      
    

theorem max_le_of_forall_le (l : List α) (a : α) (h : ∀, ∀ x ∈ l, ∀, x ≤ a) : l.foldr max ⊥ ≤ a := by
  induction' l with y l IH
  · simp
    
  · simpa [← h y (mem_cons_self _ _)] using IH fun x hx => h x <| mem_cons_of_mem _ hx
    

theorem le_max_of_le {l : List α} {a x : α} (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ := by
  induction' l with y l IH
  · exact absurd hx (not_mem_nil _)
    
  · obtain rfl | hl := hx
    simp only [← foldr, ← foldr_cons]
    · exact le_max_of_le_left h
      
    · exact le_max_of_le_right (IH hl)
      
    

end OrderBot

section OrderTop

variable [OrderTop α] {l : List α}

@[simp]
theorem foldr_min_of_ne_nil (h : l ≠ []) : ↑(l.foldr min ⊤) = l.minimum :=
  @foldr_max_of_ne_nil αᵒᵈ _ _ _ h

theorem le_min_of_forall_le (l : List α) (a : α) (h : ∀, ∀ x ∈ l, ∀, a ≤ x) : a ≤ l.foldr min ⊤ :=
  @max_le_of_forall_le αᵒᵈ _ _ _ _ h

theorem min_le_of_le (l : List α) (a : α) {x : α} (hx : x ∈ l) (h : x ≤ a) : l.foldr min ⊤ ≤ a :=
  @le_max_of_le αᵒᵈ _ _ _ _ _ hx h

end OrderTop

end Fold

end List

