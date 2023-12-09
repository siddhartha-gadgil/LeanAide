import Lean
import LeanAide.PremiseData

open Lean Meta PrettyPrinter
def delabView (name: Name) : MetaM String :=
    do
    let info ←  getConstInfo name
    let term := info.value?.get!
    let stx ←  delab term
    let _ := stx.raw.reprint
    let fmt ←  ppTerm stx
    return fmt.pretty

def delabViewType (name: Name) : MetaM String :=
    do
    let info ←  getConstInfo name
    let term := info.type
    let stx ←  delab term
    let _ := stx.raw.reprint
    let fmt ←  ppTerm stx
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

#eval delabViewType `RingHom.map_sum

open BigOperators in
#eval delabViewType `RingHom.map_sum

def openDecls : CoreM <| List OpenDecl := do
    let ctx ← read
    return ctx.openDecls

def kindsViewType (name: Name) : MetaM <| List Name :=
    do
    let info ←  getConstInfo name
    let term := info.type
    let stx ←  delab term
    let tks ← termKindsIn stx.raw
    return tks.eraseDups




#eval kindsViewType `RingHom.map_sum

#eval openDecls

open BigOperators in
#eval kindsViewType `RingHom.map_sum

open BigOperators in
#eval openDecls
