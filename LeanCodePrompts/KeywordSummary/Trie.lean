inductive Trie (α : Type _) (β : Type _)
  | terminus : β → Trie α β
  | node : α → List (Trie α β) → Trie α β
  deriving Inhabited, BEq

namespace Trie

def isterminus? : Trie α β → Bool
  | terminus _ => true
  | node _ _ => false

def isnode? : Trie α β → Bool
  | node _ _ => true
  | terminus _ => false

def label? : Trie α β → Option α
  | node a _ => some a
  | terminus _ => none

def label! [Inhabited α] : Trie α β → α
  | node a _ => a
  | terminus _ => panic! "Trie is a terminus."

def find? [DecidableEq α] : Trie α β → α → Option (Trie α β)
  | node _ l, a => l.find? (·.label? = some a)
  | terminus _, _ => none

instance [DecidableEq α] : GetElem (Trie α β) α (Trie α β) (Option.toBool <| ·.find? ·) where
  getElem := λ tr a h =>
    match tr.find? a, h with
      | some tr', _ => tr'
      | none, h => by 
        dsimp [Option.toBool] at h
        contradiction
        
def end? : Trie α β → Option (Trie α β)
  | terminus b => some <| terminus b
  | node _ l => l.find? isterminus? -- the assumption here is that there is 
                                    -- at most one terminus in this list

def keyword? [DecidableEq α] : Trie α β → List α → List α → (List α × Option ((List α) × β))
  | terminus b, p, ws => (ws, (p, b))
  | node _ _, _, [] => ([], none)
  | node a l, p, w :: ws => 
    match (node a l)[w]? with
      | some tr => keyword? tr (p.concat a) ws
      | none =>
      match l.find? isterminus? with
        | some (terminus b) => (ws, (p.concat a, b))
        | _ => (w :: ws, none)

end Trie