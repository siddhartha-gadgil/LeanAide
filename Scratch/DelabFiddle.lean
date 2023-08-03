import Lean

open Lean Meta PrettyPrinter 
def delabView (name: Name) : MetaM String := 
    do
    let info ←  getConstInfo name
    let term := info.value?.get! 
    let stx ←  delab term
    let _ := stx.raw.reprint
    let fmt ←  formatTerm stx
    return fmt.pretty 

def egComp {α β γ α' : Type} (f : α' → β → γ) (g : (a : α) → α')
    (a : α) (b : β) :=  f (g a) b

#print egComp /- def egComp : {α β γ α' : Type} → (α' → β → γ) → (α → α') → α → β → γ :=
-- fun {α β γ α'} f g a b => f (g a) b -/

#eval delabView `egComp -- "fun {α β γ α'} f g a b => f g a b" 

def delabSyntax (name: Name) : MetaM Syntax := 
    do
    let info ←  getConstInfo name
    let term := info.value?.get! 
    delab term

#eval delabSyntax `egComp 