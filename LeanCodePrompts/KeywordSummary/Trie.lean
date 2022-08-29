inductive Trie (α : Type _) (β : Type _)
  | mk : α → Option β → List (Trie α β) → Trie α β
  deriving Inhabited, BEq

namespace Trie

partial def isWellFormed : Trie α β → Bool
  | mk _ none [] => false
  | mk _  _ l => l.all isWellFormed

def isTerminus : Trie α β → Bool
  | mk _ (some _) _ => true
  | mk _ none _ => false

def label : Trie α β → α
  | mk a _ _ => a

def data? : Trie α β → Option β
  | mk _ b? _ => b?

def data : (tr : Trie α β) → tr.isTerminus → β
  | mk _ (some b) _, _ => b
  | mk _ none _, h => by 
    dsimp [isTerminus] at h
    contradiction

def find? [DecidableEq α] : Trie α β → α → Option (Trie α β)
  | mk _ _ l, a => l.find? (·.label = a)

instance [DecidableEq α] : GetElem (Trie α β) α (Trie α β) (Option.toBool <| ·.find? ·) where
  getElem := λ tr a h =>
    match tr.find? a, h with
      | some tr', _ => tr'
      | none, h => by 
        dsimp [Option.toBool] at h
        contradiction

def fromList [DecidableEq α] : List ((List α) × β) → Trie α β := fun l =>
  let lg := l.groupBy (λ ⟨l₁, _⟩ ⟨l₂, _⟩ => l₁.head? = l₂.head?)
  sorry

def keyword? [DecidableEq α] (tr : Trie α β) (p : List α) : List α → (List α × List α × Option β)
  | [] => (p, [], tr.data?)
  | w :: ws => 
    match tr.find? w with
      | some tr' => keyword? tr' (p.concat w) ws
      | none => (p, w :: ws, tr.data?)

theorem keyword?.decompose [DecidableEq α] (tr : Trie α β) (p l : List α) : 
  let (k, l', _) := keyword? tr p l 
  p ++ l = k ++ l' :=
    match l with
      | [] => rfl
      | w :: ws => by
        simp [keyword?]
        cases tr.find? w
        · rfl
        · have : p ++ w :: ws = (p.concat w) ++ ws := by rw [List.concat_eq_append, List.append_assoc]; rfl
          rw [this]
          apply keyword?.decompose

def keyword?.length [DecidableEq α] (tr : Trie α β) (p : List α) : List α → Nat
    | [] => .zero
    | w :: ws =>
      match tr.find? w with
        | some tr' => .succ $ keyword?.length tr' (p.concat w) ws
        | none => .zero

theorem keyword?.eq_drop_length [DecidableEq α] (tr : Trie α β) (p l : List α) :
  let (_, l', _) := keyword? tr p l
  l' = l.drop (keyword?.length tr p l) :=
  match l with
    | [] => rfl
    | w :: ws => by
      simp [keyword?, keyword?.length]
      cases tr.find? w
      · rfl
      · dsimp [List.drop]
        apply keyword?.eq_drop_length

def keywords [DecidableEq α] (tr : Trie α β) (l : List α) : List ((List α) × β) :=
  match tr.keyword? [] l with
    | (kw, l', some b) => (kw, b) :: keywords tr l'
    | (_, l', none) => keywords tr l'
decreasing_by sorry

end Trie