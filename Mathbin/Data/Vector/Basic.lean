/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Leanbin.Data.Vector
import Mathbin.Data.List.Nodup
import Mathbin.Data.List.OfFn
import Mathbin.Control.Applicative
import Mathbin.Meta.Univs

/-!
# Additional theorems and definitions about the `vector` type

This file introduces the infix notation `::ᵥ` for `vector.cons`.
-/


universe u

variable {n : ℕ}

namespace Vector

variable {α : Type _}

-- mathport name: «expr ::ᵥ »
infixr:67 " ::ᵥ " => Vector.cons

attribute [simp] head_cons tail_cons

instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩

theorem to_list_injective : Function.Injective (@toList α n) :=
  Subtype.val_injective

/-- Two `v w : vector α n` are equal iff they are equal at every single index. -/
@[ext]
theorem ext : ∀ {v w : Vector α n} (h : ∀ m : Finₓ n, Vector.nth v m = Vector.nth w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq
      (List.ext_le
        (by
          rw [hv, hw])
        fun m hm hn => h ⟨m, hv ▸ hm⟩)

/-- The empty `vector` is a `subsingleton`. -/
instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Finₓ.elim0 m⟩

@[simp]
theorem cons_val (a : α) : ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl

@[simp]
theorem cons_head (a : α) : ∀ v : Vector α n, (a ::ᵥ v).head = a
  | ⟨_, _⟩ => rfl

@[simp]
theorem cons_tail (a : α) : ∀ v : Vector α n, (a ::ᵥ v).tail = v
  | ⟨_, _⟩ => rfl

@[simp]
theorem to_list_of_fn : ∀ {n} (f : Finₓ n → α), toList (ofFn f) = List.ofFnₓ f
  | 0, f => rfl
  | n + 1, f => by
    rw [of_fn, List.of_fn_succ, to_list_cons, to_list_of_fn]

@[simp]
theorem mk_to_list : ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨l, h₁⟩, h₂ => rfl

@[simp]
theorem length_coe (v : Vector α n) : ((coe : { l : List α // l.length = n } → List α) v).length = n :=
  v.2

@[simp]
theorem to_list_map {β : Type _} (v : Vector α n) (f : α → β) : (v.map f).toList = v.toList.map f := by
  cases v <;> rfl

theorem nth_eq_nth_le :
    ∀ (v : Vector α n) (i),
      nth v i =
        v.toList.nthLe i.1
          (by
            rw [to_list_length] <;> exact i.2)
  | ⟨l, h⟩, i => rfl

@[simp]
theorem nth_repeat (a : α) (i : Finₓ n) : (Vector.repeat a n).nth i = a := by
  apply List.nth_le_repeat

@[simp]
theorem nth_map {β : Type _} (v : Vector α n) (f : α → β) (i : Finₓ n) : (v.map f).nth i = f (v.nth i) := by
  simp [← nth_eq_nth_le]

@[simp]
theorem nth_of_fn {n} (f : Finₓ n → α) (i) : nth (ofFn f) i = f i := by
  rw [nth_eq_nth_le, ← List.nth_le_of_fn f] <;> congr <;> apply to_list_of_fn

@[simp]
theorem of_fn_nth (v : Vector α n) : ofFn (nth v) = v := by
  rcases v with ⟨l, rfl⟩
  apply to_list_injective
  change nth ⟨l, Eq.refl _⟩ with fun i => nth ⟨l, rfl⟩ i
  simpa only [← to_list_of_fn] using List.of_fn_nth_le _

/-- The natural equivalence between length-`n` vectors and functions from `fin n`. -/
def _root_.equiv.vector_equiv_fin (α : Type _) (n : ℕ) : Vector α n ≃ (Finₓ n → α) :=
  ⟨Vector.nth, Vector.ofFn, Vector.of_fn_nth, fun f => funext <| Vector.nth_of_fn f⟩

theorem nth_tail (x : Vector α n) (i) : x.tail.nth i = x.nth ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ := by
  rcases x with ⟨_ | _, h⟩ <;> rfl

@[simp]
theorem nth_tail_succ : ∀ (v : Vector α n.succ) (i : Finₓ n), nth (tail v) i = nth v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by
    simp [← nth_eq_nth_le] <;> rfl

@[simp]
theorem tail_val : ∀ v : Vector α n.succ, v.tail.val = v.val.tail
  | ⟨a :: l, e⟩ => rfl

/-- The `tail` of a `nil` vector is `nil`. -/
@[simp]
theorem tail_nil : (@nil α).tail = nil :=
  rfl

/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp]
theorem singleton_tail (v : Vector α 1) : v.tail = Vector.nil := by
  simp only [cons_head_tail, ← eq_iff_true_of_subsingleton]

@[simp]
theorem tail_of_fn {n : ℕ} (f : Finₓ n.succ → α) : tail (ofFn f) = ofFn fun i => f i.succ :=
  (of_fn_nth _).symm.trans <| by
    congr
    funext i
    cases i
    simp

/-- The list that makes up a `vector` made up of a single element,
retrieved via `to_list`, is equal to the list of that single element. -/
@[simp]
theorem to_list_singleton (v : Vector α 1) : v.toList = [v.head] := by
  rw [← v.cons_head_tail]
  simp only [← to_list_cons, ← to_list_nil, ← cons_head, ← eq_self_iff_true, ← and_selfₓ, ← singleton_tail]

/-- Mapping under `id` does not change a vector. -/
@[simp]
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _
    (by
      simp only [← List.map_id, ← Vector.to_list_map])

theorem mem_iff_nth {a : α} {v : Vector α n} : a ∈ v.toList ↔ ∃ i, v.nth i = a := by
  simp only [← List.mem_iff_nth_le, ← Finₓ.exists_iff, ← Vector.nth_eq_nth_le] <;>
    exact
      ⟨fun ⟨i, hi, h⟩ =>
        ⟨i, by
          rwa [to_list_length] at hi, h⟩,
        fun ⟨i, hi, h⟩ =>
        ⟨i, by
          rwa [to_list_length], h⟩⟩

theorem nodup_iff_nth_inj {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.nth := by
  cases' v with l hl
  subst hl
  simp only [← List.nodup_iff_nth_le_inj]
  constructor
  · intro h i j hij
    cases i
    cases j
    ext
    apply h
    simpa
    
  · intro h i j hi hj hij
    have := @h ⟨i, hi⟩ ⟨j, hj⟩
    simp [← nth_eq_nth_le] at *
    tauto
    

@[simp]
theorem nth_mem (i : Finₓ n) (v : Vector α n) : v.nth i ∈ v.toList := by
  rw [nth_eq_nth_le] <;> exact List.nth_le_mem _ _ _

theorem head'_to_list : ∀ v : Vector α n.succ, (toList v).head' = some (head v)
  | ⟨a :: l, e⟩ => rfl

/-- Reverse a vector. -/
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by
    simp ⟩

/-- The `list` of a vector after a `reverse`, retrieved by `to_list` is equal
to the `list.reverse` after retrieving a vector's `to_list`. -/
theorem to_list_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse :=
  rfl

@[simp]
theorem reverse_reverse {v : Vector α n} : v.reverse.reverse = v := by
  cases v
  simp [← Vector.reverse]

@[simp]
theorem nth_zero : ∀ v : Vector α n.succ, nth v 0 = head v
  | ⟨a :: l, e⟩ => rfl

@[simp]
theorem head_of_fn {n : ℕ} (f : Finₓ n.succ → α) : head (ofFn f) = f 0 := by
  rw [← nth_zero, nth_of_fn]

@[simp]
theorem nth_cons_zero (a : α) (v : Vector α n) : nth (a ::ᵥ v) 0 = a := by
  simp [← nth_zero]

/-- Accessing the `nth` element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
theorem nth_cons_nil {ix : Finₓ 1} (x : α) : nth (x ::ᵥ nil) ix = x := by
  convert nth_cons_zero x nil

@[simp]
theorem nth_cons_succ (a : α) (v : Vector α n) (i : Finₓ n) : nth (a ::ᵥ v) i.succ = nth v i := by
  rw [← nth_tail_succ, tail_cons]

/-- The last element of a `vector`, given that the vector is at least one element. -/
def last (v : Vector α (n + 1)) : α :=
  v.nth (Finₓ.last n)

/-- The last element of a `vector`, given that the vector is at least one element. -/
theorem last_def {v : Vector α (n + 1)} : v.last = v.nth (Finₓ.last n) :=
  rfl

/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
theorem reverse_nth_zero {v : Vector α (n + 1)} : v.reverse.head = v.last := by
  have : 0 = v.to_list.length - 1 - n := by
    simp only [← Nat.add_succ_sub_one, ← add_zeroₓ, ← to_list_length, ← tsub_self, ← List.length_reverse]
  rw [← nth_zero, last_def, nth_eq_nth_le, nth_eq_nth_le]
  simp_rw [to_list_reverse, Finₓ.val_eq_coe, Finₓ.coe_last, Finₓ.coe_zero, this]
  rw [List.nth_le_reverse]

section Scan

variable {β : Type _}

variable (f : β → α → β) (b : β)

variable (v : Vector α n)

/-- Construct a `vector β (n + 1)` from a `vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `fin.last n`, using `b : β` as the starting value.
-/
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by
    rw [List.length_scanl, to_list_length]⟩

/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp]
theorem scanl_nil : scanl f b nil = b ::ᵥ nil :=
  rfl

/-- The recursive step of `scanl` splits a vector `x ::ᵥ v : vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_nth`.
-/
@[simp]
theorem scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v := by
  simpa only [← scanl, ← to_list_cons]

/-- The underlying `list` of a `vector` after a `scanl` is the `list.scanl`
of the underlying `list` of the original `vector`.
-/
@[simp]
theorem scanl_val : ∀ {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val
  | ⟨l, hl⟩ => rfl

/-- The `to_list` of a `vector` after a `scanl` is the `list.scanl`
of the `to_list` of the original `vector`.
-/
@[simp]
theorem to_list_scanl : (scanl f b v).toList = List.scanl f b v.toList :=
  rfl

/-- The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : vector α 1` into a `vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp]
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil := by
  rw [← cons_head_tail v]
  simp only [← scanl_cons, ← scanl_nil, ← cons_head, ← singleton_tail]

/-- The first element of `scanl` of a vector `v : vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
theorem scanl_head : (scanl f b v).head = b := by
  cases n
  · have : v = nil := by
      simp only [← eq_iff_true_of_subsingleton]
    simp only [← this, ← scanl_nil, ← cons_head]
    
  · rw [← cons_head_tail v]
    simp only [nth_zero, ← nth_eq_nth_le, ← to_list_scanl, ← to_list_cons, ← List.scanl, ← Finₓ.val_zero', ← List.nthLe]
    

/-- For an index `i : fin n`, the `nth` element of `scanl` of a
vector `v : vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `i.cast_succ` element of
`scanl f b v` and `nth v i`.

This lemma is the `nth` version of `scanl_cons`.
-/
@[simp]
theorem scanl_nth (i : Finₓ n) : (scanl f b v).nth i.succ = f ((scanl f b v).nth i.cast_succ) (v.nth i) := by
  cases n
  · exact finZeroElim i
    
  induction' n with n hn generalizing b
  · have i0 : i = 0 := by
      simp only [← eq_iff_true_of_subsingleton]
    simpa only [← scanl_singleton, ← i0, ← nth_zero]
    
  · rw [← cons_head_tail v, scanl_cons, nth_cons_succ]
    refine' Finₓ.cases _ _ i
    · simp only [← nth_zero, ← scanl_head, ← Finₓ.cast_succ_zero, ← cons_head]
      
    · intro i'
      simp only [← hn, ← Finₓ.cast_succ_fin_succ, ← nth_cons_succ]
      
    

end Scan

/-- Monadic analog of `vector.of_fn`.
Given a monadic function on `fin n`, return a `vector α n` inside the monad. -/
def mOfFnₓ {m} [Monadₓ m] {α : Type u} : ∀ {n}, (Finₓ n → m α) → m (Vector α n)
  | 0, f => pure nil
  | n + 1, f => do
    let a ← f 0
    let v ← m_of_fn fun i => f i.succ
    pure (a ::ᵥ v)

theorem m_of_fn_pure {m} [Monadₓ m] [IsLawfulMonad m] {α} :
    ∀ {n} (f : Finₓ n → α), (@mOfFnₓ m _ _ _ fun i => pure (f i)) = pure (ofFn f)
  | 0, f => rfl
  | n + 1, f => by
    simp [← m_of_fn, ← @m_of_fn_pure n, ← of_fn]

/-- Apply a monadic function to each component of a vector,
returning a vector inside the monad. -/
def mmapₓ {m} [Monadₓ m] {α} {β : Type u} (f : α → m β) : ∀ {n}, Vector α n → m (Vector β n)
  | 0, xs => pure nil
  | n + 1, xs => do
    let h' ← f xs.head
    let t' ← @mmap n xs.tail
    pure (h' ::ᵥ t')

@[simp]
theorem mmap_nil {m} [Monadₓ m] {α β} (f : α → m β) : mmapₓ f nil = pure nil :=
  rfl

@[simp]
theorem mmap_cons {m} [Monadₓ m] {α β} (f : α → m β) (a) :
    ∀ {n} (v : Vector α n),
      mmapₓ f (a ::ᵥ v) = do
        let h' ← f a
        let t' ← mmapₓ f v
        pure (h' ::ᵥ t')
  | _, ⟨l, rfl⟩ => rfl

/-- Define `C v` by induction on `v : vector α n`.

This function has two arguments: `h_nil` handles the base case on `C nil`,
and `h_cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

This can be used as `induction v using vector.induction_on`. -/
@[elab_as_eliminator]
def inductionOn {C : ∀ {n : ℕ}, Vector α n → Sort _} {n : ℕ} (v : Vector α n) (h_nil : C nil)
    (h_cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) : C v := by
  induction' n with n ih generalizing v
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
    
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    apply @h_cons n _ ⟨v, (add_left_injₓ 1).mp v_property⟩
    apply ih
    

-- check that the above works with `induction ... using`
example (v : Vector α n) : True := by
  induction v using Vector.inductionOn <;> trivial

variable {β γ : Type _}

/-- Define `C v w` by induction on a pair of vectors `v : vector α n` and `w : vector β n`. -/
@[elab_as_eliminator]
def inductionOn₂ {C : ∀ {n}, Vector α n → Vector β n → Sort _} (v : Vector α n) (w : Vector β n) (h_nil : C nil nil)
    (h_cons : ∀ {n a b} {x : Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) : C v w := by
  induction' n with n ih generalizing v w
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
    
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, _⟩
    cases w_property
    apply @h_cons n _ _ ⟨v, (add_left_injₓ 1).mp v_property⟩ ⟨w, (add_left_injₓ 1).mp w_property⟩
    apply ih
    

/-- Define `C u v w` by induction on a triplet of vectors
`u : vector α n`, `v : vector β n`, and `w : vector γ b`. -/
@[elab_as_eliminator]
def inductionOn₃ {C : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort _} (u : Vector α n) (v : Vector β n)
    (w : Vector γ n) (h_nil : C nil nil nil)
    (h_cons : ∀ {n a b c} {x : Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) : C u v w := by
  induction' n with n ih generalizing u v w
  · rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
    
  · rcases u with ⟨_ | ⟨a, u⟩, _⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, _⟩
    cases v_property
    rcases w with ⟨_ | ⟨c, w⟩, _⟩
    cases w_property
    apply
      @h_cons n _ _ _ ⟨u, (add_left_injₓ 1).mp u_property⟩ ⟨v, (add_left_injₓ 1).mp v_property⟩
        ⟨w, (add_left_injₓ 1).mp w_property⟩
    apply ih
    

/-- Cast a vector to an array. -/
def toArray : Vector α n → Arrayₓ n α
  | ⟨xs, h⟩ =>
    cast
      (by
        rw [h])
      xs.toArray

section InsertNth

variable {a : α}

/-- `v.insert_nth a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
def insertNth (a : α) (i : Finₓ (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertNth i a, by
    rw [List.length_insert_nth, v.2]
    rw [v.2, ← Nat.succ_le_succ_iff]
    exact i.2⟩

theorem insert_nth_val {i : Finₓ (n + 1)} {v : Vector α n} : (v.insertNth a i).val = v.val.insertNth i.1 a :=
  rfl

@[simp]
theorem remove_nth_val {i : Finₓ n} : ∀ {v : Vector α n}, (removeNth i v).val = v.val.removeNth i
  | ⟨l, hl⟩ => rfl

theorem remove_nth_insert_nth {v : Vector α n} {i : Finₓ (n + 1)} : removeNth i (insertNth a i v) = v :=
  Subtype.eq <| List.remove_nth_insert_nth i.1 v.1

theorem remove_nth_insert_nth' {v : Vector α (n + 1)} :
    ∀ {i : Finₓ (n + 1)} {j : Finₓ (n + 2)},
      removeNth (j.succAbove i) (insertNth a j v) = insertNth a (i.predAbove j) (removeNth i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ => by
    dsimp' [← insert_nth, ← remove_nth, ← Finₓ.succAbove, ← Finₓ.predAbove]
    simp only [← Subtype.mk_eq_mk]
    split_ifs
    · convert (List.insert_nth_remove_nth_of_ge i (j - 1) _ _ _).symm
      · convert (Nat.succ_pred_eq_of_posₓ _).symm
        exact lt_of_le_of_ltₓ (zero_le _) h
        
      · apply remove_nth_val
        
      · convert hi
        exact v.2
        
      · exact Nat.le_pred_of_ltₓ h
        
      
    · convert (List.insert_nth_remove_nth_of_le i j _ _ _).symm
      · apply remove_nth_val
        
      · convert hi
        exact v.2
        
      · simpa using h
        
      

theorem insert_nth_comm (a b : α) (i j : Finₓ (n + 1)) (h : i ≤ j) :
    ∀ v : Vector α n, (v.insertNth a i).insertNth b j.succ = (v.insertNth b j).insertNth a i.cast_succ
  | ⟨l, hl⟩ => by
    refine' Subtype.eq _
    simp only [← insert_nth_val, ← Finₓ.coe_succ, ← Finₓ.castSucc, ← Finₓ.val_eq_coe, ← Finₓ.coe_cast_add]
    apply List.insert_nth_comm
    · assumption
      
    · rw [hl]
      exact Nat.le_of_succ_le_succₓ j.2
      

end InsertNth

section UpdateNth

/-- `update_nth v n a` replaces the `n`th element of `v` with `a` -/
def updateNth (v : Vector α n) (i : Finₓ n) (a : α) : Vector α n :=
  ⟨v.1.updateNth i.1 a, by
    rw [List.update_nth_length, v.2]⟩

@[simp]
theorem to_list_update_nth (v : Vector α n) (i : Finₓ n) (a : α) : (v.updateNth i a).toList = v.toList.updateNth i a :=
  rfl

@[simp]
theorem nth_update_nth_same (v : Vector α n) (i : Finₓ n) (a : α) : (v.updateNth i a).nth i = a := by
  cases v <;> cases i <;> simp [← Vector.updateNth, ← Vector.nth_eq_nth_le]

theorem nth_update_nth_of_ne {v : Vector α n} {i j : Finₓ n} (h : i ≠ j) (a : α) : (v.updateNth i a).nth j = v.nth j :=
  by
  cases v <;>
    cases i <;>
      cases j <;> simp [← Vector.updateNth, ← Vector.nth_eq_nth_le, ← List.nth_le_update_nth_of_ne (Finₓ.vne_of_ne h)]

theorem nth_update_nth_eq_if {v : Vector α n} {i j : Finₓ n} (a : α) :
    (v.updateNth i a).nth j = if i = j then a else v.nth j := by
  split_ifs <;>
    try
        simp [*] <;>
      try
          rw [nth_update_nth_of_ne] <;>
        assumption

@[to_additive]
theorem prod_update_nth [Monoidₓ α] (v : Vector α n) (i : Finₓ n) (a : α) :
    (v.updateNth i a).toList.Prod = (v.take i).toList.Prod * a * (v.drop (i + 1)).toList.Prod := by
  refine' (List.prod_update_nth v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_leₓ i.2 (le_of_eqₓ v.2.symm)
  simp_all

@[to_additive]
theorem prod_update_nth' [CommGroupₓ α] (v : Vector α n) (i : Finₓ n) (a : α) :
    (v.updateNth i a).toList.Prod = v.toList.Prod * (v.nth i)⁻¹ * a := by
  refine' (List.prod_update_nth' v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_leₓ i.2 (le_of_eqₓ v.2.symm)
  simp [← this, ← nth_eq_nth_le, ← mul_assoc]

end UpdateNth

end Vector

namespace Vector

section Traverse

variable {F G : Type u → Type u}

variable [Applicativeₓ F] [Applicativeₓ G]

open Applicativeₓ Functor

open List (cons)

open Nat

private def traverse_aux {α β : Type u} (f : α → F β) : ∀ x : List α, F (Vector β x.length)
  | [] => pure Vector.nil
  | x :: xs => Vector.cons <$> f x <*> traverse_aux xs

/-- Apply an applicative function to each component of a vector. -/
protected def traverse {α β : Type u} (f : α → F β) : Vector α n → F (Vector β n)
  | ⟨v, Hv⟩ =>
    cast
        (by
          rw [Hv]) <|
      traverseAux f v

section

variable {α β : Type u}

@[simp]
protected theorem traverse_def (f : α → F β) (x : α) :
    ∀ xs : Vector α n, (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩ <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem id_traverse : ∀ x : Vector α n, x.traverse id.mk = x := by
  rintro ⟨x, rfl⟩
  dsimp' [← Vector.traverse, ← cast]
  induction' x with x xs IH
  · rfl
    
  simp [← IH]
  rfl

end

open Function

variable [IsLawfulApplicative F] [IsLawfulApplicative G]

variable {α β γ : Type u}

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- We need to turn off the linter here as
-- the `is_lawful_traversable` instance below expects a particular signature.
@[nolint unused_arguments]
protected theorem comp_traverse (f : β → F γ) (g : α → G β) :
    ∀ x : Vector α n,
      Vector.traverse (comp.mk ∘ Functor.map f ∘ g) x = Comp.mk (Vector.traverse f <$> Vector.traverse g x) :=
  by
  rintro ⟨x, rfl⟩ <;>
    dsimp' [← Vector.traverse, ← cast] <;>
      induction' x with x xs <;> simp' [← cast, *] with functor_norm <;> [rfl, simp [← (· ∘ ·)]]

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem traverse_eq_map_id {α β} (f : α → β) : ∀ x : Vector α n, x.traverse (id.mk ∘ f) = id.mk (map f x) :=
  by
  rintro ⟨x, rfl⟩ <;> simp <;> induction x <;> simp' [*] with functor_norm <;> rfl

variable (η : ApplicativeTransformation F G)

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem naturality {α β : Type _} (f : α → F β) :
    ∀ x : Vector α n, η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  rintro ⟨x, rfl⟩ <;> simp [← cast] <;> induction' x with x xs IH <;> simp' [*] with functor_norm

end Traverse

instance : Traversable.{u} (flip Vector n) where
  traverse := @Vector.traverse n
  map := fun α β => @Vector.map.{u, u} α β n

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
instance : IsLawfulTraversable.{u} (flip Vector n) where
  id_traverse := @Vector.id_traverse n
  comp_traverse := @Vector.comp_traverse n
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := @Vector.naturality n
  id_map := by
    intros <;> cases x <;> simp [← (· <$> ·)]
  comp_map := by
    intros <;> cases x <;> simp [← (· <$> ·)]

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]
-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]
unsafe instance reflect [reflected_univ.{u}] {α : Type u} [has_reflect α] [reflected _ α] {n : ℕ} :
    has_reflect (Vector α n) := fun v =>
  @Vector.inductionOn α (fun n => reflected _) n v
    ((by
          trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]" :
          reflected _ @Vector.nil.{u}).subst
      (quote.1 α))
    fun n x xs ih =>
    (by
          trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]" :
          reflected _ @Vector.cons.{u}).subst₄
      (quote.1 α) (quote.1 n) (quote.1 x) ih

end Vector

