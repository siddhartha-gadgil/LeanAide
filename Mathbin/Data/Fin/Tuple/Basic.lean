/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Data.Pi.Lex

/-!
# Operation on tuples

We interpret maps `Π i : fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `vector`s.

We define the following operations:

* `fin.tail` : the tail of an `n+1` tuple, i.e., its last `n` entries;
* `fin.cons` : adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple;
* `fin.init` : the beginning of an `n+1` tuple, i.e., its first `n` entries;
* `fin.snoc` : adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc`
  comes from `cons` (i.e., adding an element to the left of a tuple) read in reverse order.
* `fin.insert_nth` : insert an element to a tuple at a given position.
* `fin.find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.

-/


universe u v

namespace Finₓ

variable {m n : ℕ}

open Function

section Tuple

/-- There is exactly one tuple of size zero. -/
example (α : Finₓ 0 → Sort u) : Unique (∀ i : Finₓ 0, α i) := by
  infer_instance

@[simp]
theorem tuple0_le {α : ∀ i : Finₓ 0, Type _} [∀ i, Preorderₓ (α i)] (f g : ∀ i, α i) : f ≤ g :=
  finZeroElim

variable {α : Finₓ (n + 1) → Type u} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Finₓ n, α i.succ) (i : Finₓ n) (y : α i.succ)
  (z : α 0)

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail (q : ∀ i, α i) : ∀ i : Finₓ n, α i.succ := fun i => q i.succ

theorem tail_def {n : ℕ} {α : Finₓ (n + 1) → Type _} {q : ∀ i, α i} :
    (tail fun k : Finₓ (n + 1) => q k) = fun k : Finₓ n => q k.succ :=
  rfl

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons (x : α 0) (p : ∀ i : Finₓ n, α i.succ) : ∀ i, α i := fun j => Finₓ.cases x p j

@[simp]
theorem tail_cons : tail (cons x p) = p := by
  simp [← tail, ← cons]

@[simp]
theorem cons_succ : cons x p i.succ = p i := by
  simp [← cons]

@[simp]
theorem cons_zero : cons x p 0 = x := by
  simp [← cons]

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp]
theorem cons_update : cons x (update p i y) = update (cons x p) i.succ y := by
  ext j
  by_cases' h : j = 0
  · rw [h]
    simp [← Ne.symm (succ_ne_zero i)]
    
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ]
    by_cases' h' : j' = i
    · rw [h']
      simp
      
    · have : j'.succ ≠ i.succ := by
        rwa [Ne.def, succ_inj]
      rw [update_noteq h', update_noteq this, cons_succ]
      
    

/-- As a binary function, `fin.cons` is injective. -/
theorem cons_injective2 : Function.Injective2 (@cons n α) := fun x₀ y₀ x y h =>
  ⟨congr_fun h 0,
    funext fun i => by
      simpa using congr_fun h (Finₓ.succ i)⟩

@[simp]
theorem cons_eq_cons {x₀ y₀ : α 0} {x y : ∀ i : Finₓ n, α i.succ} : cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y :=
  cons_injective2.eq_iff

theorem cons_left_injective (x : ∀ i : Finₓ n, α i.succ) : Function.Injective fun x₀ => cons x₀ x :=
  cons_injective2.left _

theorem cons_right_injective (x₀ : α 0) : Function.Injective (cons x₀) :=
  cons_injective2.right _

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_cons_zero : update (cons x p) 0 z = cons z p := by
  ext j
  by_cases' h : j = 0
  · rw [h]
    simp
    
  · simp only [← h, ← update_noteq, ← Ne.def, ← not_false_iff]
    let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ, cons_succ]
    

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem cons_self_tail : cons (q 0) (tail q) = q := by
  ext j
  by_cases' h : j = 0
  · rw [h]
    simp
    
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, tail, cons_succ]
    

/-- Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple. -/
@[elab_as_eliminator]
def consInduction {P : (∀ i : Finₓ n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Finₓ.cons x₀ x))
    (x : ∀ i : Finₓ n.succ, α i) : P x :=
  cast
      (by
        rw [cons_self_tail]) <|
    h (x 0) (tail x)

@[simp]
theorem cons_induction_cons {P : (∀ i : Finₓ n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Finₓ.cons x₀ x)) (x₀ : α 0)
    (x : ∀ i : Finₓ n, α i.succ) : @consInduction _ _ _ h (cons x₀ x) = h x₀ x := by
  rw [cons_induction, cast_eq]
  congr
  exact tail_cons _ _

@[simp]
theorem forall_fin_zero_pi {α : Finₓ 0 → Sort _} {P : (∀ i, α i) → Prop} : (∀ x, P x) ↔ P finZeroElim :=
  ⟨fun h => h _, fun h x => Subsingleton.elimₓ finZeroElim x ▸ h⟩

@[simp]
theorem exists_fin_zero_pi {α : Finₓ 0 → Sort _} {P : (∀ i, α i) → Prop} : (∃ x, P x) ↔ P finZeroElim :=
  ⟨fun ⟨x, h⟩ => Subsingleton.elimₓ x finZeroElim ▸ h, fun h => ⟨_, h⟩⟩

theorem forall_fin_succ_pi {P : (∀ i, α i) → Prop} : (∀ x, P x) ↔ ∀ a v, P (Finₓ.cons a v) :=
  ⟨fun h a v => h (Finₓ.cons a v), consInduction⟩

theorem exists_fin_succ_pi {P : (∀ i, α i) → Prop} : (∃ x, P x) ↔ ∃ a v, P (Finₓ.cons a v) :=
  ⟨fun ⟨x, h⟩ => ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨a, v, h⟩ => ⟨_, h⟩⟩

/-- Updating the first element of a tuple does not change the tail. -/
@[simp]
theorem tail_update_zero : tail (update q 0 z) = tail q := by
  ext j
  simp [← tail, ← Finₓ.succ_ne_zero]

/-- Updating a nonzero element and taking the tail commute. -/
@[simp]
theorem tail_update_succ : tail (update q i.succ y) = update (tail q) i y := by
  ext j
  by_cases' h : j = i
  · rw [h]
    simp [← tail]
    
  · simp [← tail, ← (Finₓ.succ_injective n).Ne h, ← h]
    

theorem comp_cons {α : Type _} {β : Type _} (g : α → β) (y : α) (q : Finₓ n → α) : g ∘ cons y q = cons (g y) (g ∘ q) :=
  by
  ext j
  by_cases' h : j = 0
  · rw [h]
    rfl
    
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ, comp_app, cons_succ]
    

theorem comp_tail {α : Type _} {β : Type _} (g : α → β) (q : Finₓ n.succ → α) : g ∘ tail q = tail (g ∘ q) := by
  ext j
  simp [← tail]

theorem le_cons [∀ i, Preorderₓ (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Finₓ n, α i.succ} :
    q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
  forall_fin_succ.trans <|
    and_congr Iff.rfl <|
      forall_congrₓ fun j => by
        simp [← tail]

theorem cons_le [∀ i, Preorderₓ (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Finₓ n, α i.succ} :
    cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
  @le_cons _ (fun i => (α i)ᵒᵈ) _ x q p

theorem cons_le_cons [∀ i, Preorderₓ (α i)] {x₀ y₀ : α 0} {x y : ∀ i : Finₓ n, α i.succ} :
    cons x₀ x ≤ cons y₀ y ↔ x₀ ≤ y₀ ∧ x ≤ y :=
  forall_fin_succ.trans <|
    and_congr_right' <| by
      simp only [← cons_succ, ← Pi.le_def]

theorem pi_lex_lt_cons_cons {x₀ y₀ : α 0} {x y : ∀ i : Finₓ n, α i.succ} (s : ∀ {i : Finₓ n.succ}, α i → α i → Prop) :
    Pi.Lex (· < ·) (@s) (Finₓ.cons x₀ x) (Finₓ.cons y₀ y) ↔
      s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex (· < ·) (fun i : Finₓ n => @s i.succ) x y :=
  by
  simp_rw [Pi.Lex, Finₓ.exists_fin_succ, Finₓ.cons_succ, Finₓ.cons_zero, Finₓ.forall_fin_succ]
  simp [← and_assoc, ← exists_and_distrib_left]

@[simp]
theorem range_cons {α : Type _} {n : ℕ} (x : α) (b : Finₓ n → α) :
    Set.Range (Finₓ.cons x b : Finₓ n.succ → α) = insert x (Set.Range b) := by
  ext y
  simp only [← Set.mem_range, ← Set.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    refine' cases (Or.inl (cons_zero _ _)) (fun i => Or.inr ⟨i, _⟩) i
    rw [cons_succ]
    
  · rintro (rfl | ⟨i, hi⟩)
    · exact ⟨0, Finₓ.cons_zero _ _⟩
      
    · refine' ⟨i.succ, _⟩
      rw [cons_succ, hi]
      
    

/-- `fin.append ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`.  `ho` provides control of definitional equality
for the vector length. -/
def append {α : Type _} {o : ℕ} (ho : o = m + n) (u : Finₓ m → α) (v : Finₓ n → α) : Finₓ o → α := fun i =>
  if h : (i : ℕ) < m then u ⟨i, h⟩ else v ⟨(i : ℕ) - m, (tsub_lt_iff_left (le_of_not_ltₓ h)).2 (ho ▸ i.property)⟩

@[simp]
theorem fin_append_apply_zero {α : Type _} {o : ℕ} (ho : o + 1 = m + 1 + n) (u : Finₓ (m + 1) → α) (v : Finₓ n → α) :
    Finₓ.append ho u v 0 = u 0 :=
  rfl

end Tuple

section TupleRight

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `fin (n+1)` is constructed
inductively from `fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/


variable {α : Finₓ (n + 1) → Type u} (x : α (last n)) (q : ∀ i, α i) (p : ∀ i : Finₓ n, α i.cast_succ) (i : Finₓ n)
  (y : α i.cast_succ) (z : α (last n))

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init (q : ∀ i, α i) (i : Finₓ n) : α i.cast_succ :=
  q i.cast_succ

theorem init_def {n : ℕ} {α : Finₓ (n + 1) → Type _} {q : ∀ i, α i} :
    (init fun k : Finₓ (n + 1) => q k) = fun k : Finₓ n => q k.cast_succ :=
  rfl

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc (p : ∀ i : Finₓ n, α i.cast_succ) (x : α (last n)) (i : Finₓ (n + 1)) : α i :=
  if h : i.val < n then
    cast
      (by
        rw [Finₓ.cast_succ_cast_lt i h])
      (p (castLt i h))
  else
    cast
      (by
        rw [eq_last_of_not_lt h])
      x

@[simp]
theorem init_snoc : init (snoc p x) = p := by
  ext i
  have h' := Finₓ.cast_lt_cast_succ i i.is_lt
  simp [← init, ← snoc, ← i.is_lt, ← h']
  convert cast_eq rfl (p i)

@[simp]
theorem snoc_cast_succ : snoc p x i.cast_succ = p i := by
  have : i.cast_succ.val < n := i.is_lt
  have h' := Finₓ.cast_lt_cast_succ i i.is_lt
  simp [← snoc, ← this, ← h']
  convert cast_eq rfl (p i)

@[simp]
theorem snoc_comp_cast_succ {n : ℕ} {α : Sort _} {a : α} {f : Finₓ n → α} :
    (snoc f a : Finₓ (n + 1) → α) ∘ cast_succ = f :=
  funext fun i => by
    rw [Function.comp_app, snoc_cast_succ]

@[simp]
theorem snoc_last : snoc p x (last n) = x := by
  simp [← snoc]

@[simp]
theorem snoc_comp_nat_add {n m : ℕ} {α : Sort _} (f : Finₓ (m + n) → α) (a : α) :
    (snoc f a : Finₓ _ → α) ∘ (natAdd m : Finₓ (n + 1) → Finₓ (m + n + 1)) = snoc (f ∘ natAdd m) a := by
  ext i
  refine' Finₓ.lastCases _ (fun i => _) i
  · simp only [← Function.comp_app]
    rw [snoc_last, nat_add_last, snoc_last]
    
  · simp only [← Function.comp_app]
    rw [snoc_cast_succ, nat_add_cast_succ, snoc_cast_succ]
    

@[simp]
theorem snoc_cast_add {α : Finₓ (n + m + 1) → Type _} (f : ∀ i : Finₓ (n + m), α (castSucc i)) (a : α (last (n + m)))
    (i : Finₓ n) : (snoc f a) (castAdd (m + 1) i) = f (castAdd m i) :=
  dif_pos _

@[simp]
theorem snoc_comp_cast_add {n m : ℕ} {α : Sort _} (f : Finₓ (n + m) → α) (a : α) :
    (snoc f a : Finₓ _ → α) ∘ castAdd (m + 1) = f ∘ castAdd m :=
  funext (snoc_cast_add f a)

/-- Updating a tuple and adding an element at the end commute. -/
@[simp]
theorem snoc_update : snoc (update p i y) x = update (snoc p x) i.cast_succ y := by
  ext j
  by_cases' h : j.val < n
  · simp only [← snoc, ← h, ← dif_pos]
    by_cases' h' : j = cast_succ i
    · have C1 : α i.cast_succ = α j := by
        rw [h']
      have E1 : update (snoc p x) i.cast_succ y j = _root_.cast C1 y := by
        have : update (snoc p x) j (_root_.cast C1 y) j = _root_.cast C1 y := by
          simp
        convert this
        · exact h'.symm
          
        · exact heq_of_cast_eq (congr_arg α (Eq.symm h')) rfl
          
      have C2 : α i.cast_succ = α (cast_succ (cast_lt j h)) := by
        rw [cast_succ_cast_lt, h']
      have E2 : update p i y (cast_lt j h) = _root_.cast C2 y := by
        have : update p (cast_lt j h) (_root_.cast C2 y) (cast_lt j h) = _root_.cast C2 y := by
          simp
        convert this
        · simp [← h, ← h']
          
        · exact heq_of_cast_eq C2 rfl
          
      rw [E1, E2]
      exact eq_rec_compose _ _ _
      
    · have : ¬cast_lt j h = i := by
        intro E
        apply h'
        rw [← E, cast_succ_cast_lt]
      simp [← h', ← this, ← snoc, ← h]
      
    
  · rw [eq_last_of_not_lt h]
    simp [← Ne.symm (ne_of_ltₓ (cast_succ_lt_last i))]
    

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_snoc_last : update (snoc p x) (last n) z = snoc p z := by
  ext j
  by_cases' h : j.val < n
  · have : j ≠ last n := ne_of_ltₓ h
    simp [← h, ← update_noteq, ← this, ← snoc]
    
  · rw [eq_last_of_not_lt h]
    simp
    

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem snoc_init_self : snoc (init q) (q (last n)) = q := by
  ext j
  by_cases' h : j.val < n
  · have : j ≠ last n := ne_of_ltₓ h
    simp [← h, ← update_noteq, ← this, ← snoc, ← init, ← cast_succ_cast_lt]
    have A : cast_succ (cast_lt j h) = j := cast_succ_cast_lt _ _
    rw [← cast_eq rfl (q j)]
    congr 1 <;> rw [A]
    
  · rw [eq_last_of_not_lt h]
    simp
    

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp]
theorem init_update_last : init (update q (last n) z) = init q := by
  ext j
  simp [← init, ← ne_of_ltₓ, ← cast_succ_lt_last]

/-- Updating an element and taking the beginning commute. -/
@[simp]
theorem init_update_cast_succ : init (update q i.cast_succ y) = update (init q) i y := by
  ext j
  by_cases' h : j = i
  · rw [h]
    simp [← init]
    
  · simp [← init, ← h]
    

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem tail_init_eq_init_tail {β : Type _} (q : Finₓ (n + 2) → β) : tail (init q) = init (tail q) := by
  ext i
  simp [← tail, ← init, ← cast_succ_fin_succ]

/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem cons_snoc_eq_snoc_cons {β : Type _} (a : β) (q : Finₓ n → β) (b : β) :
    @cons n.succ (fun i => β) a (snoc q b) = snoc (cons a q) b := by
  ext i
  by_cases' h : i = 0
  · rw [h]
    rfl
    
  set j := pred i h with ji
  have : i = j.succ := by
    rw [ji, succ_pred]
  rw [this, cons_succ]
  by_cases' h' : j.val < n
  · set k := cast_lt j h' with jk
    have : j = k.cast_succ := by
      rw [jk, cast_succ_cast_lt]
    rw [this, ← cast_succ_fin_succ]
    simp
    
  rw [eq_last_of_not_lt h', succ_last]
  simp

theorem comp_snoc {α : Type _} {β : Type _} (g : α → β) (q : Finₓ n → α) (y : α) : g ∘ snoc q y = snoc (g ∘ q) (g y) :=
  by
  ext j
  by_cases' h : j.val < n
  · have : j ≠ last n := ne_of_ltₓ h
    simp [← h, ← this, ← snoc, ← cast_succ_cast_lt]
    
  · rw [eq_last_of_not_lt h]
    simp
    

theorem comp_init {α : Type _} {β : Type _} (g : α → β) (q : Finₓ n.succ → α) : g ∘ init q = init (g ∘ q) := by
  ext j
  simp [← init]

end TupleRight

section InsertNth

variable {α : Finₓ (n + 1) → Type u} {β : Type v}

/-- Define a function on `fin (n + 1)` from a value on `i : fin (n + 1)` and values on each
`fin.succ_above i j`, `j : fin n`. This version is elaborated as eliminator and works for
propositions, see also `fin.insert_nth` for a version without an `@[elab_as_eliminator]`
attribute. -/
@[elab_as_eliminator]
def succAboveCases {α : Finₓ (n + 1) → Sort u} (i : Finₓ (n + 1)) (x : α i) (p : ∀ j : Finₓ n, α (i.succAbove j))
    (j : Finₓ (n + 1)) : α j :=
  if hj : j = i then Eq.ndrec x hj.symm
  else
    if hlt : j < i then Eq.recOnₓ (succ_above_cast_lt hlt) (p _)
    else Eq.recOnₓ (succ_above_pred <| (Ne.lt_or_lt hj).resolve_left hlt) (p _)

theorem forall_iff_succ_above {p : Finₓ (n + 1) → Prop} (i : Finₓ (n + 1)) :
    (∀ j, p j) ↔ p i ∧ ∀ j, p (i.succAbove j) :=
  ⟨fun h => ⟨h _, fun j => h _⟩, fun h => succAboveCases i h.1 h.2⟩

/-- Insert an element into a tuple at a given position. For `i = 0` see `fin.cons`,
for `i = fin.last n` see `fin.snoc`. See also `fin.succ_above_cases` for a version elaborated
as an eliminator. -/
def insertNth (i : Finₓ (n + 1)) (x : α i) (p : ∀ j : Finₓ n, α (i.succAbove j)) (j : Finₓ (n + 1)) : α j :=
  succAboveCases i x p j

@[simp]
theorem insert_nth_apply_same (i : Finₓ (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) : insertNth i x p i = x := by
  simp [← insert_nth, ← succ_above_cases]

@[simp]
theorem insert_nth_apply_succ_above (i : Finₓ (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) (j : Finₓ n) :
    insertNth i x p (i.succAbove j) = p j := by
  simp only [← insert_nth, ← succ_above_cases, ← dif_neg (succ_above_ne _ _)]
  by_cases' hlt : j.cast_succ < i
  · rw [dif_pos ((succ_above_lt_iff _ _).2 hlt)]
    apply eq_of_heq ((eq_rec_heq _ _).trans _)
    rw [cast_lt_succ_above hlt]
    
  · rw [dif_neg (mt (succ_above_lt_iff _ _).1 hlt)]
    apply eq_of_heq ((eq_rec_heq _ _).trans _)
    rw [pred_succ_above (le_of_not_ltₓ hlt)]
    

@[simp]
theorem succ_above_cases_eq_insert_nth : @succAboveCases.{u + 1} = @insertNth.{u} :=
  rfl

@[simp]
theorem insert_nth_comp_succ_above (i : Finₓ (n + 1)) (x : β) (p : Finₓ n → β) : insertNth i x p ∘ i.succAbove = p :=
  funext <| insert_nth_apply_succ_above i x p

theorem insert_nth_eq_iff {i : Finₓ (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p = q ↔ q i = x ∧ p = fun j => q (i.succAbove j) := by
  simp [← funext_iff, ← forall_iff_succ_above i, ← eq_comm]

theorem eq_insert_nth_iff {i : Finₓ (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q = i.insertNth x p ↔ q i = x ∧ p = fun j => q (i.succAbove j) :=
  eq_comm.trans insert_nth_eq_iff

theorem insert_nth_apply_below {i j : Finₓ (n + 1)} (h : j < i) (x : α i) (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = Eq.recOnₓ (succ_above_cast_lt h) (p <| j.cast_lt _) := by
  rw [insert_nth, succ_above_cases, dif_neg h.ne, dif_pos h]

theorem insert_nth_apply_above {i j : Finₓ (n + 1)} (h : i < j) (x : α i) (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = Eq.recOnₓ (succ_above_pred h) (p <| j.pred _) := by
  rw [insert_nth, succ_above_cases, dif_neg h.ne', dif_neg h.not_lt]

theorem insert_nth_zero (x : α 0) (p : ∀ j : Finₓ n, α (succAbove 0 j)) :
    insertNth 0 x p = cons x fun j => cast (congr_arg α (congr_fun succ_above_zero j)) (p j) := by
  refine'
    insert_nth_eq_iff.2
      ⟨by
        simp , _⟩
  ext j
  convert (cons_succ _ _ _).symm

@[simp]
theorem insert_nth_zero' (x : β) (p : Finₓ n → β) : @insertNth _ (fun _ => β) 0 x p = cons x p := by
  simp [← insert_nth_zero]

theorem insert_nth_last (x : α (last n)) (p : ∀ j : Finₓ n, α ((last n).succAbove j)) :
    insertNth (last n) x p = snoc (fun j => cast (congr_arg α (succ_above_last_apply j)) (p j)) x := by
  refine'
    insert_nth_eq_iff.2
      ⟨by
        simp , _⟩
  ext j
  apply eq_of_heq
  trans snoc (fun j => _root_.cast (congr_arg α (succ_above_last_apply j)) (p j)) x j.cast_succ
  · rw [snoc_cast_succ]
    exact (cast_heq _ _).symm
    
  · apply congr_arg_heq
    rw [succ_above_last]
    

@[simp]
theorem insert_nth_last' (x : β) (p : Finₓ n → β) : @insertNth _ (fun _ => β) (last n) x p = snoc p x := by
  simp [← insert_nth_last]

@[simp]
theorem insert_nth_zero_right [∀ j, Zero (α j)] (i : Finₓ (n + 1)) (x : α i) : i.insertNth x 0 = Pi.single i x :=
  insert_nth_eq_iff.2 <| by
    simp [← succ_above_ne, ← Pi.zero_def]

theorem insert_nth_binop (op : ∀ j, α j → α j → α j) (i : Finₓ (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    (i.insertNth (op i x y) fun j => op _ (p j) (q j)) = fun j => op j (i.insertNth x p j) (i.insertNth y q j) :=
  insert_nth_eq_iff.2 <| by
    simp

@[simp]
theorem insert_nth_mul [∀ j, Mul (α j)] (i : Finₓ (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x * y) (p * q) = i.insertNth x p * i.insertNth y q :=
  insert_nth_binop (fun _ => (· * ·)) i x y p q

@[simp]
theorem insert_nth_add [∀ j, Add (α j)] (i : Finₓ (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x + y) (p + q) = i.insertNth x p + i.insertNth y q :=
  insert_nth_binop (fun _ => (· + ·)) i x y p q

@[simp]
theorem insert_nth_div [∀ j, Div (α j)] (i : Finₓ (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x / y) (p / q) = i.insertNth x p / i.insertNth y q :=
  insert_nth_binop (fun _ => (· / ·)) i x y p q

@[simp]
theorem insert_nth_sub [∀ j, Sub (α j)] (i : Finₓ (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x - y) (p - q) = i.insertNth x p - i.insertNth y q :=
  insert_nth_binop (fun _ => Sub.sub) i x y p q

@[simp]
theorem insert_nth_sub_same [∀ j, AddGroupₓ (α j)] (i : Finₓ (n + 1)) (x y : α i) (p : ∀ j, α (i.succAbove j)) :
    i.insertNth x p - i.insertNth y p = Pi.single i (x - y) := by
  simp_rw [← insert_nth_sub, ← insert_nth_zero_right, Pi.sub_def, sub_self, Pi.zero_def]

variable [∀ i, Preorderₓ (α i)]

theorem insert_nth_le_iff {i : Finₓ (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p ≤ q ↔ x ≤ q i ∧ p ≤ fun j => q (i.succAbove j) := by
  simp [← Pi.le_def, ← forall_iff_succ_above i]

theorem le_insert_nth_iff {i : Finₓ (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q ≤ i.insertNth x p ↔ q i ≤ x ∧ (fun j => q (i.succAbove j)) ≤ p := by
  simp [← Pi.le_def, ← forall_iff_succ_above i]

open Set

theorem insert_nth_mem_Icc {i : Finₓ (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q₁ q₂ : ∀ j, α j} :
    i.insertNth x p ∈ Icc q₁ q₂ ↔
      x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (fun j => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j) :=
  by
  simp only [← mem_Icc, ← insert_nth_le_iff, ← le_insert_nth_iff, ← And.assoc, ← And.left_comm]

theorem preimage_insert_nth_Icc_of_mem {i : Finₓ (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j} (hx : x ∈ Icc (q₁ i) (q₂ i)) :
    i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j) :=
  Set.ext fun p => by
    simp only [← mem_preimage, ← insert_nth_mem_Icc, ← hx, ← true_andₓ]

theorem preimage_insert_nth_Icc_of_not_mem {i : Finₓ (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext fun p => by
    simp only [← mem_preimage, ← insert_nth_mem_Icc, ← hx, ← false_andₓ, ← mem_empty_eq]

end InsertNth

section Find

/-- `find p` returns the first index `n` where `p n` is satisfied, and `none` if it is never
satisfied. -/
def find : ∀ {n : ℕ} (p : Finₓ n → Prop) [DecidablePred p], Option (Finₓ n)
  | 0, p, _ => none
  | n + 1, p, _ => by
    skip <;>
      exact
        Option.casesOn (@find n (fun i => p (i.cast_lt (Nat.lt_succ_of_ltₓ i.2))) _)
          (if h : p (Finₓ.last n) then some (Finₓ.last n) else none) fun i => some (i.cast_lt (Nat.lt_succ_of_ltₓ i.2))

/-- If `find p = some i`, then `p i` holds -/
theorem find_spec : ∀ {n : ℕ} (p : Finₓ n → Prop) [DecidablePred p] {i : Finₓ n} (hi : i ∈ Finₓ.find p), p i
  | 0, p, I, i, hi => Option.noConfusion hi
  | n + 1, p, I, i, hi => by
    dsimp' [← find]  at hi
    skip
    cases' h : find fun i : Finₓ n => p (i.cast_lt (Nat.lt_succ_of_ltₓ i.2)) with j
    · rw [h] at hi
      dsimp'  at hi
      split_ifs  at hi with hl hl
      · exact hi ▸ hl
        
      · exact hi.elim
        
      
    · rw [h] at hi
      rw [← Option.some_inj.1 hi]
      exact find_spec _ h
      

/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
theorem is_some_find_iff : ∀ {n : ℕ} {p : Finₓ n → Prop} [DecidablePred p], (find p).isSome ↔ ∃ i, p i
  | 0, p, _ => iff_of_false (fun h => Bool.noConfusion h) fun ⟨i, _⟩ => finZeroElim i
  | n + 1, p, _ =>
    ⟨fun h => by
      rw [Option.is_some_iff_exists] at h
      cases' h with i hi
      exact ⟨i, find_spec _ hi⟩, fun ⟨⟨i, hin⟩, hi⟩ => by
      skip
      dsimp' [← find]
      cases' h : find fun i : Finₓ n => p (i.cast_lt (Nat.lt_succ_of_ltₓ i.2)) with j
      · split_ifs with hl hl
        · exact Option.is_some_some
          
        · have :=
            (@is_some_find_iff n (fun x => p (x.cast_lt (Nat.lt_succ_of_ltₓ x.2))) _).2
              ⟨⟨i,
                  lt_of_le_of_neₓ (Nat.le_of_lt_succₓ hin) fun h => by
                    clear_aux_decl <;> cases h <;> exact hl hi⟩,
                hi⟩
          rw [h] at this
          exact this
          
        
      · simp
        ⟩

/-- `find p` returns `none` if and only if `p i` never holds. -/
theorem find_eq_none_iff {n : ℕ} {p : Finₓ n → Prop} [DecidablePred p] : find p = none ↔ ∀ i, ¬p i := by
  rw [← not_exists, ← is_some_find_iff] <;> cases find p <;> simp

/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
theorem find_min :
    ∀ {n : ℕ} {p : Finₓ n → Prop} [DecidablePred p] {i : Finₓ n} (hi : i ∈ Finₓ.find p) {j : Finₓ n} (hj : j < i), ¬p j
  | 0, p, _, i, hi, j, hj, hpj => Option.noConfusion hi
  | n + 1, p, _, i, hi, ⟨j, hjn⟩, hj, hpj => by
    skip
    dsimp' [← find]  at hi
    cases' h : find fun i : Finₓ n => p (i.cast_lt (Nat.lt_succ_of_ltₓ i.2)) with k
    · rw [h] at hi
      split_ifs  at hi with hl hl
      · subst hi
        rw [find_eq_none_iff] at h
        exact h ⟨j, hj⟩ hpj
        
      · exact hi.elim
        
      
    · rw [h] at hi
      dsimp'  at hi
      obtain rfl := Option.some_inj.1 hi
      exact find_min h (show (⟨j, lt_transₓ hj k.2⟩ : Finₓ n) < k from hj) hpj
      

theorem find_min' {p : Finₓ n → Prop} [DecidablePred p] {i : Finₓ n} (h : i ∈ Finₓ.find p) {j : Finₓ n} (hj : p j) :
    i ≤ j :=
  le_of_not_gtₓ fun hij => find_min h hij hj

theorem nat_find_mem_find {p : Finₓ n → Prop} [DecidablePred p] (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
    (⟨Nat.findₓ h, (Nat.find_specₓ h).fst⟩ : Finₓ n) ∈ find p := by
  let ⟨i, hin, hi⟩ := h
  cases' hf : find p with f
  · rw [find_eq_none_iff] at hf
    exact (hf ⟨i, hin⟩ hi).elim
    
  · refine' Option.some_inj.2 (le_antisymmₓ _ _)
    · exact find_min' hf (Nat.find_specₓ h).snd
      
    · exact
        Nat.find_min'ₓ _
          ⟨f.2, by
            convert find_spec p hf <;> exact Finₓ.eta _ _⟩
      
    

theorem mem_find_iff {p : Finₓ n → Prop} [DecidablePred p] {i : Finₓ n} : i ∈ Finₓ.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
  ⟨fun hi => ⟨find_spec _ hi, fun _ => find_min' hi⟩, by
    rintro ⟨hpi, hj⟩
    cases hfp : Finₓ.find p
    · rw [find_eq_none_iff] at hfp
      exact (hfp _ hpi).elim
      
    · exact Option.some_inj.2 (le_antisymmₓ (find_min' hfp hpi) (hj _ (find_spec _ hfp)))
      ⟩

theorem find_eq_some_iff {p : Finₓ n → Prop} [DecidablePred p] {i : Finₓ n} :
    Finₓ.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j :=
  mem_find_iff

theorem mem_find_of_unique {p : Finₓ n → Prop} [DecidablePred p] (h : ∀ i j, p i → p j → i = j) {i : Finₓ n}
    (hi : p i) : i ∈ Finₓ.find p :=
  mem_find_iff.2 ⟨hi, fun j hj => le_of_eqₓ <| h i j hi hj⟩

end Find

end Finₓ

