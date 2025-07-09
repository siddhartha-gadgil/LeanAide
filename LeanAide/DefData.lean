import Lean
import LeanAide.Aides
import LeanAide.StatementSyntax
open Lean Meta Elab Term Parser PrettyPrinter Lean.Parser.Term

namespace LeanAide

def foldContext (type: Syntax.Term) : List Syntax → CoreM (Syntax.Term)
| [] => return type
| x :: ys => do
    let tailType ← foldContext type ys
    match x with
    | `(letDecl|$n:ident : $type := $val) => do
        `(let $n : $type := $val; $tailType)
    | `(funBinder|($n:ident : $type:term)) => do
        `(($n : $type) → $tailType)
    | `(funImplicitBinder |{$n:ident : $type:term}) => do
        `({$n : $type} → $tailType)
    | `(funBinder|(_ : $type:term)) => do
        `((_ : $type) → $tailType)
    | `(funImplicitBinder|{_ : $type:term}) => do
        `({_ : $type} → $tailType)
    | `(instBinder|[$n:ident : $type:term]) => do
        `([$n : $type] → $tailType)
    | `(instBinder|[$type:term]) => do
        `([$type] → $tailType)
    | `(bracketedBinderF|⦃$n:ident : $type:term⦄) => do
        `(($n : $type) → $tailType)
    | `(bracketedBinderF|($n:ident : $type:term)) => do
        `(($n : $type) → $tailType)
    | _ =>
        IO.println s!"foldContext: {x}, i.e., {x.reprint.get!} could not be folded"
        return type

/--
Data associated to a definition. This was originally intended to be used for tracking premises but is also used ignoring a few parameters as *syntax* data for a definition.
-/
structure DefData where
    name : Name
    type : Syntax.Term
    value : Syntax.Term
    isProp : Bool
    isNoncomputable : Bool
    doc? : Option String := none
    deriving Inhabited,  Repr

#print DefinitionVal

#check addAndCompile

structure DefDataRepr where
    name: Name
    type: String
    isProp : Bool
    isNoncomputable : Bool
    doc? : Option String
    value? : Option String
    statement : String
    deriving Repr, ToJson, FromJson


namespace DefData


def statement (data: DefData)(omitProofs: Bool := true) :
        CoreM String := do
    let value? := if omitProofs && data.isProp then none else some data.value
    match data.doc? with
    | none =>
      mkStatement (some data.name) data.type value? data.isProp (isNoncomputable := data.isNoncomputable)
    | some doc =>
      mkStatementWithDoc (some data.name) data.type value? data.isProp true doc data.isNoncomputable

def statementWithDoc (data: DefData)(doc: String)
    (omitProofs: Bool := true)(useExample: Bool := true) :
        CoreM String := do
    let value? := if omitProofs && data.isProp then none else some data.value
    mkStatementWithDoc
        (some data.name) data.type value? data.isProp useExample doc data.isNoncomputable

def statementStx (data: DefData)(omitProofs: Bool := true) :
        CoreM Syntax.Command := do
    let value? := if omitProofs && data.isProp then none else some data.value
    match data.doc? with
    | none =>
      mkStatementStx (some data.name) data.type value? data.isProp (isNoncomputable := data.isNoncomputable)
    | some doc =>
      mkStatementWithDocStx (some data.name) data.type value? data.isProp true doc data.isNoncomputable

-- incorrect
-- def relType (xs:  List (TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder])) (type: Syntax.Term) : MetaM Syntax.Term := do
--     match xs with
--     | [] => return type
--     | h :: t =>
--         let prev ← relType t type
--         `(h → $prev)

open Elab Term  in
def toDeclaration (data: DefData) : TermElabM Declaration := do
    let typeExpr ← elabType data.type
    let valueExpr ← elabTerm data.value typeExpr
    let valueExpr ← instantiateMVars valueExpr
    let typeExpr ← instantiateMVars typeExpr
    Term.synthesizeSyntheticMVarsNoPostponing
    -- logInfo s!"toDeclaration: {data.name} : {← PrettyPrinter.ppExpr typeExpr} := {← PrettyPrinter.ppExpr valueExpr}"
    -- logInfo s!"Mvar? : {valueExpr.hasExprMVar}, {valueExpr.hasLevelMVar}"
    -- logInfo s!"{repr valueExpr}"
    let decl ← match data.isProp with
    | true => do
        let decl := .thmDecl {
            name := data.name,
            type := typeExpr,
            value := valueExpr,
            levelParams := []
        }
        return decl
    | false => do
        let decl := Declaration.defnDecl {
            name := data.name,
            levelParams := [],
            type := typeExpr,
            value := valueExpr,
            hints := ReducibilityHints.abbrev,
            safety := DefinitionSafety.safe
        }
        -- logInfo s!"toDeclaration: {data.name} : {data.type} := {data.value}"
        return decl

def addDeclaration (data: DefData) : TermElabM Unit := do
    let decl ← data.toDeclaration
    addAndCompile decl


def ofSyntax? (stx: Syntax) : MetaM <| Option DefData := do
    match stx with
    | `(command| def $n:ident $xs* : $type := $val) => do
        let xs := xs.toList
        let xs := xs.map fun stx => stx.raw
        let type ← foldContext type xs
        let name := n.getId
        let type := type
        let value := val
        let isProp := false
        return some ⟨name, type, value, isProp, false, none⟩
    | `(command| noncomputable def $n:ident $xs* : $type := $val) => do
        let xs := xs.toList
        let xs := xs.map fun stx => stx.raw
        let type ← foldContext type xs
        let name := n.getId
        let type := type
        let value := val
        let isProp := false
        return some ⟨name, type, value, isProp, true, none⟩
    | `(command| theorem $n:ident $xs* : $type := $val) =>
        let xs := xs.toList
        let xs := xs.map fun stx => stx.raw
        let type ← foldContext type xs
        let name := n.getId
        let type := type
        let value := val
        let isProp := true
        return some ⟨name, type, value, isProp, false, none⟩
    | _ => return none

def repr (data: DefData) : MetaM DefDataRepr := do
    let statement ← data.statement
    return {name := data.name, type := (← ppTerm data.type).pretty, isProp := data.isProp, isNoncomputable := data.isNoncomputable, doc? := data.doc?, value? := (← ppTerm data.value).pretty, statement := statement}

def jsonView (data: DefData) : MetaM Json := do
    return Json.mkObj [("name", toJson data.name),
    ("type", toJson (← ppTerm data.type).pretty),
    ("value", toJson (← ppTerm data.value).pretty),
    ("isProp", toJson data.isProp)]

def ofNameM (name: Name) : MetaM DefData := do
    let decl ← getConstInfo name
    let type ← instantiateMVars decl.type
    let value ← instantiateMVars decl.value!
    let typeStx ← delab type
    let valueStx ← delab value
    let nc := Lean.isNoncomputable (← getEnv) name
    let isProp := match decl with
    | ConstantInfo.defnInfo _ => false
    | ConstantInfo.thmInfo _ => true
    | _ => false
    let doc? ← findDocString? (← getEnv) name
    return {name := name, type := typeStx, value := valueStx, isProp := isProp, isNoncomputable := nc, doc? := doc?}

end DefData

def DefDataRepr.withDoc (dfn: DefDataRepr) : String :=
  match dfn.doc? with
  | some doc => s!"/-- {doc} -/\n{dfn.statement}"
  | none => dfn.statement
