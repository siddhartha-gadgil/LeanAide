/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.LazyList
import Mathbin.Data.Nat.Basic
import Mathbin.Data.Stream.Init
import Mathbin.Data.Seq.Computation

universe u v w

/-- A stream `s : option α` is a sequence if `s.nth n = none` implies `s.nth (n + 1) = none`.
-/
/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/
def Streamₓ.IsSeq {α : Type u} (s : Streamₓ (Option α)) : Prop :=
  ∀ {n : ℕ}, s n = none → s (n + 1) = none

/-- `seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
def Seqₓₓ (α : Type u) : Type u :=
  { f : Streamₓ (Option α) // f.IsSeq }

/-- `seq1 α` is the type of nonempty sequences. -/
def Seq1 (α) :=
  α × Seqₓₓ α

namespace Seqₓₓ

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence -/
def nil : Seqₓₓ α :=
  ⟨Streamₓ.const none, fun n h => rfl⟩

instance : Inhabited (Seqₓₓ α) :=
  ⟨nil⟩

/-- Prepend an element to a sequence -/
def cons (a : α) : Seqₓₓ α → Seqₓₓ α
  | ⟨f, al⟩ =>
    ⟨some a :: f, fun n h => by
      cases' n with n
      contradiction
      exact al h⟩

/-- Get the nth element of a sequence (if it exists) -/
def nth : Seqₓₓ α → ℕ → Option α :=
  Subtype.val

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seqₓₓ α) (n : ℕ) : Prop :=
  s.nth n = none

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Seqₓₓ α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidableOfIff' (s.nth n).isNone <| by
    unfold terminated_at <;> cases s.nth n <;> simp

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Seqₓₓ α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n

/-- Functorial action of the functor `option (α × _)` -/
@[simp]
def omap (f : β → γ) : Option (α × β) → Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)

/-- Get the first element of a sequence -/
def head (s : Seqₓₓ α) : Option α :=
  nth s 0

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail : Seqₓₓ α → Seqₓₓ α
  | ⟨f, al⟩ => ⟨f.tail, fun n => al⟩

protected def Mem (a : α) (s : Seqₓₓ α) :=
  some a ∈ s.1

instance : HasMem α (Seqₓₓ α) :=
  ⟨Seqₓₓ.Mem⟩

theorem le_stable (s : Seqₓₓ α) {m n} (h : m ≤ n) : s.nth m = none → s.nth n = none := by
  cases' s with f al
  induction' h with n h IH
  exacts[id, fun h2 => al (IH h2)]

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n `. -/
theorem terminated_stable (s : Seqₓₓ α) {m n : ℕ} (m_le_n : m ≤ n) (terminated_at_m : s.TerminatedAt m) :
    s.TerminatedAt n :=
  le_stable s m_le_n terminated_at_m

/-- If `s.nth n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.nth = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seqₓₓ α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n) (s_nth_eq_some : s.nth n = some aₙ) :
    ∃ aₘ : α, s.nth m = some aₘ :=
  have : s.nth n ≠ none := by
    simp [← s_nth_eq_some]
  have : s.nth m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

theorem not_mem_nil (a : α) : a ∉ @nil α := fun ⟨n, (h : some a = none)⟩ => by
  injection h

theorem mem_cons (a : α) : ∀ s : Seqₓₓ α, a ∈ cons a s
  | ⟨f, al⟩ => Streamₓ.mem_cons (some a) _

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : Seqₓₓ α}, a ∈ s → a ∈ cons y s
  | ⟨f, al⟩ => Streamₓ.mem_cons_of_mem (some y)

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : Seqₓₓ α}, a ∈ cons b s → a = b ∨ a ∈ s
  | ⟨f, al⟩, h =>
    (Streamₓ.eq_or_mem_of_mem_cons h).imp_left fun h => by
      injection h

@[simp]
theorem mem_cons_iff {a b : α} {s : Seqₓₓ α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, fun o => by
    cases' o with e m <;>
      [· rw [e]
        apply mem_cons
        ,
      exact mem_cons_of_mem _ m]⟩

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct (s : Seqₓₓ α) : Option (Seq1 α) :=
  (fun a' => (a', s.tail)) <$> nth s 0

theorem destruct_eq_nil {s : Seqₓₓ α} : destruct s = none → s = nil := by
  dsimp' [← destruct]
  induction' f0 : nth s 0 with <;> intro h
  · apply Subtype.eq
    funext n
    induction' n with n IH
    exacts[f0, s.2 IH]
    
  · contradiction
    

theorem destruct_eq_cons {s : Seqₓₓ α} {a s'} : destruct s = some (a, s') → s = cons a s' := by
  dsimp' [← destruct]
  induction' f0 : nth s 0 with a' <;> intro h
  · contradiction
    
  · cases' s with f al
    injections with _ h1 h2
    rw [← h2]
    apply Subtype.eq
    dsimp' [← tail, ← cons]
    rw [h1] at f0
    rw [← f0]
    exact (Streamₓ.eta f).symm
    

@[simp]
theorem destruct_nil : destruct (nil : Seqₓₓ α) = none :=
  rfl

@[simp]
theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.eq
    dsimp' [← tail]
    rw [Streamₓ.tail_cons]

theorem head_eq_destruct (s : Seqₓₓ α) : head s = Prod.fst <$> destruct s := by
  unfold destruct head <;> cases nth s 0 <;> rfl

@[simp]
theorem head_nil : head (nil : Seqₓₓ α) = none :=
  rfl

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct, destruct_cons] <;> rfl

@[simp]
theorem tail_nil : tail (nil : Seqₓₓ α) = nil :=
  rfl

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by
  cases' s with f al <;> apply Subtype.eq <;> dsimp' [← tail, ← cons] <;> rw [Streamₓ.tail_cons]

def casesOn {C : Seqₓₓ α → Sort v} (s : Seqₓₓ α) (h1 : C nil) (h2 : ∀ x s, C (cons x s)) : C s := by
  induction' H : destruct s with v v
  · rw [destruct_eq_nil H]
    apply h1
    
  · cases' v with a s'
    rw [destruct_eq_cons H]
    apply h2
    

theorem mem_rec_on {C : Seqₓₓ α → Prop} {a s} (M : a ∈ s) (h1 : ∀ b s', a = b ∨ C s' → C (cons b s')) : C s := by
  cases' M with k e
  unfold Streamₓ.nth  at e
  induction' k with k IH generalizing s
  · have TH : s = cons a (tail s) := by
      apply destruct_eq_cons
      unfold destruct nth Functor.map
      rw [← e]
      rfl
    rw [TH]
    apply h1 _ _ (Or.inl rfl)
    
  revert e
  apply s.cases_on _ fun b s' => _ <;> intro e
  · injection e
    
  · have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by
      cases s' <;> rfl
    rw [h_eq] at e
    apply h1 _ _ (Or.inr (IH e))
    

def Corec.f (f : β → Option (α × β)) : Option β → Option α × Option β
  | none => (none, none)
  | some b =>
    match f b with
    | none => (none, none)
    | some (a, b') => (some a, some b')

/-- Corecursor for `seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec (f : β → Option (α × β)) (b : β) : Seqₓₓ α := by
  refine' ⟨Streamₓ.corec' (corec.F f) (some b), fun n h => _⟩
  rw [Streamₓ.corec'_eq]
  change Streamₓ.corec' (corec.F f) (corec.F f (some b)).2 n = none
  revert h
  generalize some b = o
  revert o
  induction' n with n IH <;> intro o
  · change (corec.F f o).1 = none → (corec.F f (corec.F f o).2).1 = none
    cases' o with b <;> intro h
    · rfl
      
    dsimp' [← corec.F]  at h
    dsimp' [← corec.F]
    cases' f b with s
    · rfl
      
    · cases' s with a b'
      contradiction
      
    
  · rw [Streamₓ.corec'_eq (corec.F f) (corec.F f o).2, Streamₓ.corec'_eq (corec.F f) o]
    exact IH (corec.F f o).2
    

@[simp]
theorem corec_eq (f : β → Option (α × β)) (b : β) : destruct (corec f b) = omap (corec f) (f b) := by
  dsimp' [← corec, ← destruct, ← nth]
  change Streamₓ.corec' (corec.F f) (some b) 0 with (corec.F f (some b)).1
  dsimp' [← corec.F]
  induction' h : f b with s
  · rfl
    
  cases' s with a b'
  dsimp' [← corec.F]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.eq
  dsimp' [← corec, ← tail]
  rw [Streamₓ.corec'_eq, Streamₓ.tail_cons]
  dsimp' [← corec.F]
  rw [h]
  rfl

/-- Embed a list as a sequence -/
def ofList (l : List α) : Seqₓₓ α :=
  ⟨List.nth l, fun n h => by
    induction' l with a l IH generalizing n
    rfl
    dsimp' [← List.nth]
    cases' n with n <;> dsimp' [← List.nth]  at h
    · contradiction
      
    · apply IH _ h
      ⟩

instance coeList : Coe (List α) (Seqₓₓ α) :=
  ⟨ofList⟩

section Bisim

variable (R : Seqₓₓ α → Seqₓₓ α → Prop)

-- mathport name: «expr ~ »
local infixl:50 " ~ " => R

def BisimO : Option (Seq1 α) → Option (Seq1 α) → Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False

attribute [simp] bisim_o

def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.eq
  apply Streamₓ.eq_of_bisim fun x y => ∃ s s' : Seqₓₓ α, s.1 = x ∧ s'.1 = y ∧ R s s'
  dsimp' [← Streamₓ.IsBisimulation]
  intro t₁ t₂ e
  exact
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ => by
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id
          (fun r =>
            ⟨tail s, tail s', by
              cases s <;> rfl, by
              cases s' <;> rfl, r⟩)
          this
      have := bisim r
      revert r this
      apply cases_on s _ _ <;> intros <;> apply cases_on s' _ _ <;> intros <;> intro r this
      · constructor
        rfl
        assumption
        
      · rw [destruct_nil, destruct_cons] at this
        exact False.elim this
        
      · rw [destruct_nil, destruct_cons] at this
        exact False.elim this
        
      · rw [destruct_cons, destruct_cons] at this
        rw [head_cons, head_cons, tail_cons, tail_cons]
        cases' this with h1 h2
        constructor
        rw [h1]
        exact h2
        
  exact ⟨s₁, s₂, rfl, rfl, r⟩

end Bisim

theorem coinduction :
    ∀ {s₁ s₂ : Seqₓₓ α},
      head s₁ = head s₂ → (∀ (β : Type u) (fr : Seqₓₓ α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
  | ⟨f₁, a₁⟩, ⟨f₂, a₂⟩, hh, ht => Subtype.eq (Streamₓ.coinduction hh fun β fr => ht β fun s => fr s.1)

theorem coinduction2 (s) (f g : Seqₓₓ α → Seqₓₓ β)
    (H : ∀ s, BisimO (fun s1 s2 : Seqₓₓ β => ∃ s : Seqₓₓ α, s1 = f s ∧ s2 = g s) (destruct (f s)) (destruct (g s))) :
    f s = g s := by
  refine' eq_of_bisim (fun s1 s2 => ∃ s, s1 = f s ∧ s2 = g s) _ ⟨s, rfl, rfl⟩
  intro s1 s2 h
  rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]
  apply H

/-- Embed an infinite stream as a sequence -/
def ofStream (s : Streamₓ α) : Seqₓₓ α :=
  ⟨s.map some, fun n h => by
    contradiction⟩

instance coeStream : Coe (Streamₓ α) (Seqₓₓ α) :=
  ⟨ofStream⟩

/-- Embed a `lazy_list α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `lazy_list`s created by meta constructions. -/
def ofLazyList : LazyList α → Seqₓₓ α :=
  corec fun l =>
    match l with
    | LazyList.nil => none
    | LazyList.cons a l' => some (a, l' ())

instance coeLazyList : Coe (LazyList α) (Seqₓₓ α) :=
  ⟨ofLazyList⟩

/-- Translate a sequence into a `lazy_list`. Since `lazy_list` and `list`
  are isomorphic as non-meta types, this function is necessarily meta. -/
unsafe def to_lazy_list : Seqₓₓ α → LazyList α
  | s =>
    match destruct s with
    | none => LazyList.nil
    | some (a, s') => LazyList.cons a (to_lazy_list s')

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def force_to_list (s : Seqₓₓ α) : List α :=
  (to_lazy_list s).toList

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : Seqₓₓ ℕ :=
  Streamₓ.nats

@[simp]
theorem nats_nth (n : ℕ) : nats.nth n = some n :=
  rfl

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : Seqₓₓ α) : Seqₓₓ α :=
  @corec α (Seqₓₓ α × Seqₓₓ α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)

/-- Map a function over a sequence. -/
def map (f : α → β) : Seqₓₓ α → Seqₓₓ β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun n => by
      dsimp' [← Streamₓ.map, ← Streamₓ.nth]
      induction' e : s n with <;> intro
      · rw [al e]
        assumption
        
      · contradiction
        ⟩

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : Seqₓₓ (Seq1 α) → Seqₓₓ α :=
  corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')

/-- Remove the first `n` elements from the sequence. -/
def drop (s : Seqₓₓ α) : ℕ → Seqₓₓ α
  | 0 => s
  | n + 1 => tail (drop n)

attribute [simp] drop

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Seqₓₓ α → List α
  | 0, s => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def splitAt : ℕ → Seqₓₓ α → List α × Seqₓₓ α
  | 0, s => ([], s)
  | n + 1, s =>
    match destruct s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := split_at n s'
      (List.cons x l, r)

section ZipWith

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) : Seqₓₓ α → Seqₓₓ β → Seqₓₓ γ
  | ⟨f₁, a₁⟩, ⟨f₂, a₂⟩ =>
    ⟨fun n =>
      match f₁ n, f₂ n with
      | some a, some b => some (f a b)
      | _, _ => none,
      fun n => by
      induction' h1 : f₁ n with
      · intro H
        simp only [← a₁ h1]
        rfl
        
      induction' h2 : f₂ n with <;> dsimp' [← Seqₓₓ.ZipWith._match1] <;> intro H
      · rw [a₂ h2]
        cases f₁ (n + 1) <;> rfl
        
      · rw [h1, h2] at H
        contradiction
        ⟩

variable {s : Seqₓₓ α} {s' : Seqₓₓ β} {n : ℕ}

theorem zip_with_nth_some {a : α} {b : β} (s_nth_eq_some : s.nth n = some a) (s_nth_eq_some' : s'.nth n = some b)
    (f : α → β → γ) : (zipWith f s s').nth n = some (f a b) := by
  cases' s with st
  have : st n = some a := s_nth_eq_some
  cases' s' with st'
  have : st' n = some b := s_nth_eq_some'
  simp only [← zip_with, ← Seqₓₓ.nth, *]

theorem zip_with_nth_none (s_nth_eq_none : s.nth n = none) (f : α → β → γ) : (zipWith f s s').nth n = none := by
  cases' s with st
  have : st n = none := s_nth_eq_none
  cases' s' with st'
  cases st'_nth_eq : st' n <;> simp only [← zip_with, ← Seqₓₓ.nth, *]

theorem zip_with_nth_none' (s'_nth_eq_none : s'.nth n = none) (f : α → β → γ) : (zipWith f s s').nth n = none := by
  cases' s' with st'
  have : st' n = none := s'_nth_eq_none
  cases' s with st
  cases st_nth_eq : st n <;> simp only [← zip_with, ← Seqₓₓ.nth, *]

end ZipWith

/-- Pair two sequences into a sequence of pairs -/
def zip : Seqₓₓ α → Seqₓₓ β → Seqₓₓ (α × β) :=
  zipWith Prod.mk

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Seqₓₓ (α × β)) : Seqₓₓ α × Seqₓₓ β :=
  (map Prod.fst s, map Prod.snd s)

/-- Convert a sequence which is known to terminate into a list -/
def toList (s : Seqₓₓ α) (h : ∃ n, ¬(nth s n).isSome) : List α :=
  take (Nat.findₓ h) s

/-- Convert a sequence which is known not to terminate into a stream -/
def toStream (s : Seqₓₓ α) (h : ∀ n, (nth s n).isSome) : Streamₓ α := fun n => Option.getₓ (h n)

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def toListOrStream (s : Seqₓₓ α) [Decidable (∃ n, ¬(nth s n).isSome)] : Sum (List α) (Streamₓ α) :=
  if h : ∃ n, ¬(nth s n).isSome then Sum.inl (toList s h)
  else Sum.inr (toStream s fun n => Decidable.by_contradiction fun hn => h ⟨n, hn⟩)

@[simp]
theorem nil_append (s : Seqₓₓ α) : append nil s = s := by
  apply coinduction2
  intro s
  dsimp' [← append]
  rw [corec_eq]
  dsimp' [← append]
  apply cases_on s _ _
  · trivial
    
  · intro x s
    rw [destruct_cons]
    dsimp'
    exact ⟨rfl, s, rfl, rfl⟩
    

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  destruct_eq_cons <| by
    dsimp' [← append]
    rw [corec_eq]
    dsimp' [← append]
    rw [destruct_cons]
    dsimp' [← append]
    rfl

@[simp]
theorem append_nil (s : Seqₓₓ α) : append s nil = s := by
  apply coinduction2 s
  intro s
  apply cases_on s _ _
  · trivial
    
  · intro x s
    rw [cons_append, destruct_cons, destruct_cons]
    dsimp'
    exact ⟨rfl, s, rfl, rfl⟩
    

@[simp]
theorem append_assoc (s t u : Seqₓₓ α) : append (append s t) u = append s (append t u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        apply cases_on s <;> simp
        · apply cases_on t <;> simp
          · apply cases_on u <;> simp
            · intro x u
              refine' ⟨nil, nil, u, _, _⟩ <;> simp
              
            
          · intro x t
            refine' ⟨nil, t, u, _, _⟩ <;> simp
            
          
        · intro x s
          exact ⟨s, t, u, rfl, rfl⟩
          
    
  · exact ⟨s, t, u, rfl, rfl⟩
    

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq <;> dsimp' [← cons, ← map] <;> rw [Streamₓ.map_cons] <;> rfl

@[simp]
theorem map_id : ∀ s : Seqₓₓ α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.eq <;> dsimp' [← map]
    rw [Option.map_id, Streamₓ.map_id] <;> rfl

@[simp]
theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq <;> dsimp' [← tail, ← map] <;> rw [Streamₓ.map_tail] <;> rfl

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Seqₓₓ α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq <;> dsimp' [← map]
    rw [Streamₓ.map_map]
    apply congr_arg fun f : _ → Option γ => Streamₓ.map f s
    ext ⟨⟩ <;> rfl

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) := by
  apply eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _ ⟨s, t, rfl, rfl⟩
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      apply cases_on s <;> simp
      · apply cases_on t <;> simp
        · intro x t
          refine' ⟨nil, t, _, _⟩ <;> simp
          
        
      · intro x s
        refine' ⟨s, t, rfl, rfl⟩
        

@[simp]
theorem map_nth (f : α → β) : ∀ s n, nth (map f s) n = (nth s n).map f
  | ⟨s, al⟩, n => rfl

instance : Functor Seqₓₓ where map := @map

instance : IsLawfulFunctor Seqₓₓ where
  id_map := @map_id
  comp_map := @map_comp

@[simp]
theorem join_nil : join nil = (nil : Seqₓₓ α) :=
  destruct_eq_nil rfl

@[simp]
theorem join_cons_nil (a : α) (S) : join (cons (a, nil) S) = cons a (join S) :=
  destruct_eq_cons <| by
    simp [← join]

@[simp]
theorem join_cons_cons (a b : α) (s S) : join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
  destruct_eq_cons <| by
    simp [← join]

@[simp]
theorem join_cons (a : α) (s S) : join (cons (a, s) S) = cons a (append s (join S)) := by
  apply
    eq_of_bisim (fun s1 s2 => s1 = s2 ∨ ∃ a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S))) _
      (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, Or.inl <| Eq.refl s => by
      apply cases_on s
      · trivial
        
      · intro x s
        rw [destruct_cons]
        exact ⟨rfl, Or.inl rfl⟩
        
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      apply cases_on s
      · simp
        
      · intro x s
        simp
        refine' Or.inr ⟨x, s, S, rfl, rfl⟩
        

@[simp]
theorem join_append (S T : Seqₓₓ (Seq1 α)) : join (append S T) = append (join S) (join T) := by
  apply eq_of_bisim fun s1 s2 => ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        apply cases_on s <;> simp
        · apply cases_on S <;> simp
          · apply cases_on T
            · simp
              
            · intro s T
              cases' s with a s <;> simp
              refine' ⟨s, nil, T, _, _⟩ <;> simp
              
            
          · intro s S
            cases' s with a s <;> simp
            exact ⟨s, S, T, rfl, rfl⟩
            
          
        · intro x s
          exact ⟨s, S, T, rfl, rfl⟩
          
    
  · refine' ⟨nil, S, T, _, _⟩ <;> simp
    

@[simp]
theorem of_list_nil : ofList [] = (nil : Seqₓₓ α) :=
  rfl

@[simp]
theorem of_list_cons (a : α) (l) : ofList (a :: l) = cons a (ofList l) := by
  ext (_ | n) : 2 <;> simp [← of_list, ← cons, ← Streamₓ.nth, ← Streamₓ.cons]

@[simp]
theorem of_stream_cons (a : α) (s) : ofStream (a :: s) = cons a (ofStream s) := by
  apply Subtype.eq <;> simp [← of_stream, ← cons] <;> rw [Streamₓ.map_cons]

@[simp]
theorem of_list_append (l l' : List α) : ofList (l ++ l') = append (ofList l) (ofList l') := by
  induction l <;> simp [*]

@[simp]
theorem of_stream_append (l : List α) (s : Streamₓ α) : ofStream (l ++ₛ s) = append (ofList l) (ofStream s) := by
  induction l <;> simp [*, ← Streamₓ.nil_append_stream, ← Streamₓ.cons_append_stream]

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def toList' {α} (s : Seqₓₓ α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Seqₓₓ α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a :: l, s'))
    ([], s)

theorem dropn_add (s : Seqₓₓ α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add n)

theorem dropn_tail (s : Seqₓₓ α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [add_commₓ] <;> symm <;> apply dropn_add

theorem nth_tail : ∀ (s : Seqₓₓ α) (n), nth (tail s) n = nth s (n + 1)
  | ⟨f, al⟩, n => rfl

@[ext]
protected theorem ext (s s' : Seqₓₓ α) (hyp : ∀ n : ℕ, s.nth n = s'.nth n) : s = s' := by
  let ext := fun s s' : Seqₓₓ α => ∀ n, s.nth n = s'.nth n
  apply Seqₓₓ.eq_of_bisim ext _ hyp
  -- we have to show that ext is a bisimulation
  clear hyp s s'
  intro s s'(hyp : ext s s')
  unfold Seqₓₓ.destruct
  rw [hyp 0]
  cases s'.nth 0
  · simp [← Seqₓₓ.BisimO]
    
  -- option.none
  · -- option.some
    suffices ext s.tail s'.tail by
      simpa
    intro n
    simp only [← Seqₓₓ.nth_tail _ n, ← hyp <| n + 1]
    

@[simp]
theorem head_dropn (s : Seqₓₓ α) (n) : head (drop s n) = nth s n := by
  induction' n with n IH generalizing s
  · rfl
    
  rw [Nat.succ_eq_add_one, ← nth_tail, ← dropn_tail]
  apply IH

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seqₓₓ α}, a ∈ s → f a ∈ map f s
  | ⟨g, al⟩ => Streamₓ.mem_map (Option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seqₓₓ α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
  | ⟨g, al⟩, h => by
    let ⟨o, om, oe⟩ := Streamₓ.exists_of_mem_map h
    cases' o with a <;> injection oe with h' <;> exact ⟨a, om, h'⟩

theorem of_mem_append {s₁ s₂ : Seqₓₓ α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  have := h
  revert this
  generalize e : append s₁ s₂ = ss
  intro h
  revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  apply s₁.cases_on _ fun c t₁ => _ <;> intro m e <;> have := congr_arg destruct e
  · apply Or.inr
    simpa using m
    
  · cases'
      show a = c ∨ a ∈ append t₁ s₂ by
        simpa using m with
      e' m
    · rw [e']
      exact Or.inl (mem_cons _ _)
      
    · cases'
        show c = b ∧ append t₁ s₂ = s' by
          simpa with
        i1 i2
      cases' o with e' IH
      · simp [← i1, ← e']
        
      · exact Or.imp_left (mem_cons_of_mem _) (IH m i2)
        
      
    

theorem mem_append_left {s₁ s₂ : Seqₓₓ α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ := by
  apply mem_rec_on h <;> intros <;> simp [*]

end Seqₓₓ

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Seqₓₓ

/-- Convert a `seq1` to a sequence. -/
def toSeq : Seq1 α → Seqₓₓ α
  | (a, s) => cons a s

instance coeSeq : Coe (Seq1 α) (Seqₓₓ α) :=
  ⟨toSeq⟩

/-- Map a function on a `seq1` -/
def map (f : α → β) : Seq1 α → Seq1 β
  | (a, s) => (f a, Seqₓₓ.map f s)

theorem map_id : ∀ s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by
    simp [← map]

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Seq1 (Seq1 α) → Seq1 α
  | ((a, s), S) =>
    match destruct s with
    | none => (a, Seqₓₓ.join S)
    | some s' => (a, Seqₓₓ.join (cons s' S))

@[simp]
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Seqₓₓ.join S) :=
  rfl

@[simp]
theorem join_cons (a b : α) (s S) : join ((a, cons b s), S) = (a, Seqₓₓ.join (cons (b, s) S)) := by
  dsimp' [← join] <;> rw [destruct_cons] <;> rfl

/-- The `return` operator for the `seq1` monad,
  which produces a singleton sequence. -/
def ret (a : α) : Seq1 α :=
  (a, nil)

instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨ret default⟩

/-- The `bind` operator for the `seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Seq1 α) (f : α → Seq1 β) : Seq1 β :=
  join (map f s)

@[simp]
theorem join_map_ret (s : Seqₓₓ α) : Seqₓₓ.join (Seqₓₓ.map ret s) = s := by
  apply coinduction2 s <;> intro s <;> apply cases_on s <;> simp [← ret]

@[simp]
theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
  | ⟨a, s⟩ => by
    dsimp' [← bind, ← map]
    change fun x => ret (f x) with ret ∘ f
    rw [map_comp]
    simp [← Function.comp, ← ret]

@[simp]
theorem ret_bind (a : α) (f : α → Seq1 β) : bind (ret a) f = f a := by
  simp [← ret, ← bind, ← map]
  cases' f a with a s
  apply cases_on s <;> intros <;> simp

@[simp]
theorem map_join' (f : α → β) (S) : Seqₓₓ.map f (Seqₓₓ.join S) = Seqₓₓ.join (Seqₓₓ.map (map f) S) := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S, s1 = append s (Seqₓₓ.map f (Seqₓₓ.join S)) ∧ s2 = append s (Seqₓₓ.join (Seqₓₓ.map (map f) S))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        apply cases_on s <;> simp
        · apply cases_on S <;> simp
          · intro x S
            cases' x with a s <;> simp [← map]
            exact ⟨_, _, rfl, rfl⟩
            
          
        · intro x s
          refine' ⟨s, S, rfl, rfl⟩
          
    
  · refine' ⟨nil, S, _, _⟩ <;> simp
    

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by
    apply cases_on s <;> intros <;> simp [← map]

@[simp]
theorem join_join (SS : Seqₓₓ (Seq1 (Seq1 α))) : Seqₓₓ.join (Seqₓₓ.join SS) = Seqₓₓ.join (Seqₓₓ.map join SS) := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s SS, s1 = Seqₓₓ.append s (Seqₓₓ.join (Seqₓₓ.join SS)) ∧ s2 = Seqₓₓ.append s (Seqₓₓ.join (Seqₓₓ.map join SS))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, SS, rfl, rfl⟩ => by
        apply cases_on s <;> simp
        · apply cases_on SS <;> simp
          · intro S SS
            cases' S with s S <;> cases' s with x s <;> simp [← map]
            apply cases_on s <;> simp
            · exact ⟨_, _, rfl, rfl⟩
              
            · intro x s
              refine' ⟨cons x (append s (Seqₓₓ.join S)), SS, _, _⟩ <;> simp
              
            
          
        · intro x s
          exact ⟨s, SS, rfl, rfl⟩
          
    
  · refine' ⟨nil, SS, _, _⟩ <;> simp
    

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  cases' s with a s
  simp [← bind, ← map]
  rw [← map_comp]
  change fun x => join (map g (f x)) with join ∘ map g ∘ f
  rw [map_comp _ join]
  generalize Seqₓₓ.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  apply cases_on s <;> intros <;> apply cases_on S <;> intros <;> simp
  · cases' x with x t
    apply cases_on t <;> intros <;> simp
    
  · cases' x_1 with y t <;> simp
    

instance : Monadₓ Seq1 where
  map := @map
  pure := @ret
  bind := @bind

instance : IsLawfulMonad Seq1 where
  id_map := @map_id
  bind_pure_comp_eq_map := @bind_ret
  pure_bind := @ret_bind
  bind_assoc := @bind_assoc

end Seq1

