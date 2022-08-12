/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathbin.Data.Rbtree.Init

universe u v w

def RbmapLt {α : Type u} {β : Type v} (lt : α → α → Prop) (a b : α × β) : Prop :=
  lt a.1 b.1

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option auto_param.check_exists
set_option auto_param.check_exists false

def Rbmap (α : Type u) (β : Type v)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Type max u v :=
  Rbtree (α × β) (RbmapLt lt)

def mkRbmap (α : Type u) (β : Type v)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Rbmap α β lt :=
  mkRbtree (α × β) (RbmapLt lt)

namespace Rbmap

variable {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop}

def empty (m : Rbmap α β lt) : Bool :=
  m.Empty

def toList (m : Rbmap α β lt) : List (α × β) :=
  m.toList

def min (m : Rbmap α β lt) : Option (α × β) :=
  m.min

def max (m : Rbmap α β lt) : Option (α × β) :=
  m.max

def fold (f : α → β → δ → δ) (m : Rbmap α β lt) (d : δ) : δ :=
  m.fold (fun e => f e.1 e.2) d

def revFold (f : α → β → δ → δ) (m : Rbmap α β lt) (d : δ) : δ :=
  m.revFold (fun e => f e.1 e.2) d

/-
We don't assume β is inhabited when in membership predicate `mem` and
function find_entry to make this module more convenient to use.
If we had assumed β to be inhabited we could use the following simpler
definition: (k, default) ∈ m
-/
protected def Mem (k : α) (m : Rbmap α β lt) : Prop :=
  match m.val with
  | Rbnode.leaf => False
  | Rbnode.red_node _ e _ => Rbtree.Mem (k, e.2) m
  | Rbnode.black_node _ e _ => Rbtree.Mem (k, e.2) m

instance : HasMem α (Rbmap α β lt) :=
  ⟨Rbmap.Mem⟩

instance [HasRepr α] [HasRepr β] : HasRepr (Rbmap α β lt) :=
  ⟨fun t => "rbmap_of " ++ reprₓ t.toList⟩

def rbmapLtDec [h : DecidableRel lt] : DecidableRel (@RbmapLt α β lt) := fun a b => h a.1 b.1

variable [DecidableRel lt]

def insert (m : Rbmap α β lt) (k : α) (v : β) : Rbmap α β lt :=
  @Rbtree.insert _ _ rbmapLtDec m (k, v)

def findEntry (m : Rbmap α β lt) (k : α) : Option (α × β) :=
  match m.val with
  | Rbnode.leaf => none
  | Rbnode.red_node _ e _ => @Rbtree.find _ _ rbmapLtDec m (k, e.2)
  | Rbnode.black_node _ e _ => @Rbtree.find _ _ rbmapLtDec m (k, e.2)

def toValue : Option (α × β) → Option β
  | none => none
  | some e => some e.2

def find (m : Rbmap α β lt) (k : α) : Option β :=
  toValue (m.findEntry k)

def contains (m : Rbmap α β lt) (k : α) : Bool :=
  (findEntry m k).isSome

def fromList (l : List (α × β))
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Rbmap α β lt :=
  l.foldl (fun m p => insert m p.1 p.2) (mkRbmap α β lt)

end Rbmap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β))
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Rbmap α β lt :=
  Rbmap.fromList l lt

