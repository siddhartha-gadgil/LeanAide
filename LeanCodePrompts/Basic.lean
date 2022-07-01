import Mathlib.Init.Set
import Mathbin.All
/-  Basic definitions to allow syntax matching -/

infix:50 " ⊂ " => Subset.subset

/-
def Set.supset (s₁ s₂ : Set α) : Prop := s₂ ⊂ s₁

infix:50 " ⊃ " => Subset.supset
infix:50 " ⊇ " => Subset.supset

@[reducible] class SMul (α : Type u) (β : Type v)  where
  sMul : α → β → β 

infixl:70 " • "   =>  SMul.sMul

class HasNorm (α : Type u) (k : Type v) where
  norm : α → k

def Norm.norm {α : Type u} {k : Type v} [c: HasNorm α k] : α → k :=
  c.norm

notation " ∥ " α " ∥ " =>  Norm.norm α
-/

