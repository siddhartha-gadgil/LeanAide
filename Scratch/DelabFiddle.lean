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

def openDecls : MetaM <| List OpenDecl := do
    getOpenDecls

def kindsViewType (name: Name) : MetaM <| List Name :=
    do
    let info ←  getConstInfo name
    let term := info.type
    let stx ←  delab term
    let tks ← termKindsIn stx.raw
    return tks.eraseDups

def kindsViewTypeDoc (name: Name) :
    MetaM <| Array (Name × String) :=
    do
    let info ←  getConstInfo name
    let term := info.type
    let stx ←  delab term
    let tks ← termKindsIn stx.raw
    let env ← getEnv
    let tks := tks.eraseDups
    let mut withDocs := #[]
    for tk in tks do
        let doc? ←  findDocString? env tk
        match doc? with
        | none => pure ()
        | some doc =>
         withDocs := withDocs.push (tk, doc)
    return withDocs



#eval kindsViewTypeDoc `RingHom.map_sum

#eval openDecls

open BigOperators in
#eval kindsViewTypeDoc `RingHom.map_sum

open BigOperators
#eval openDecls

#check termKindList

def termKindDocList : MetaM <| Array (Name × String) :=
    do
    let env ← getEnv
    let mut withDocs := #[]
    for tk in ← termKindList do
        let doc? ←  findDocString? env tk
        match doc? with
        | none => pure ()
        | some doc =>
         withDocs := withDocs.push (tk, doc)
    return withDocs

#eval termKindDocList

def termKindDocCount : MetaM <| (Nat × Nat) :=
    do
    let mut withDocs := 0
    let mut withoutDocs := 0
    let env ← getEnv
    for tk in ← termKindList do
        let doc? ←  findDocString? env tk
        match doc? with
        | none => withoutDocs := withoutDocs + 1
        | some _ =>
         withDocs := withDocs + 1
    return (withDocs, withoutDocs)

open Topology Manifold in
#eval termKindDocCount

open Json
def termKindDocJson : MetaM Json :=
    do
    let mut withDocs : Array Json := #[]
    let env ← getEnv
    for tk in ← termKindList do
        let doc? ←  findDocString? env tk
        match doc? with
        | none => pure ()
        | some doc =>
         withDocs := withDocs.push <| mkObj <| [("name",  tk.toString), ("doc", doc)]
    return Json.arr withDocs

#eval termKindDocJson
#check IO.FS.writeFile
#check Json.pretty

def writeTermKindDocJson : MetaM Unit :=
    do
    let json ← termKindDocJson
    let jsonStr := Json.pretty json
    IO.FS.writeFile ("data" / "termKindDoc.json") jsonStr
#eval writeTermKindDocJson
