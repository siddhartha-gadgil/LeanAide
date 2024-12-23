import Lean

open Lean Meta Elab Parser PrettyPrinter

abbrev ContextTerm := TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]

abbrev ContextSyn := Array Syntax

open Lean.Parser.Term

partial def arrowHeads (type: Syntax.Term)
    (accum: Array ContextTerm := #[]) :
        CoreM <| (Array ContextTerm) × Syntax.Term := do
    match type with
    | `(depArrow|$bb → $body) => do
        let accum := accum.push bb
        arrowHeads body accum
    | _ => return (accum, type)


def mkStatementStx (name?: Option Name)(type: Syntax.Term)
    (value?: Option Syntax.Term)(isProp: Bool)(useExample: Bool := false)(isNoncomputable: Bool := false) :
        CoreM (TSyntax `command) := do
    let (ctxs, tailType) ← arrowHeads type
    let value := value?.getD (← `(by sorry))
    if name?.isNone && useExample then
        if isNoncomputable
        then
            `(command| noncomputable example $ctxs* : $tailType := $value)
        else
            `(command| example $ctxs* : $tailType := $value)
    else
        let hash := hash type.raw.reprint
        let inner_name :=
            Name.mkSimple s!"aux_{hash}"
        let name := mkIdent <| name?.getD inner_name
        if isProp
        then
            `(command| theorem $name $ctxs* : $tailType := $value)
        else
            if isNoncomputable
            then
                `(command| noncomputable def $name:ident $ctxs* : $tailType := $value)
            else
            `(command| def $name:ident $ctxs* : $tailType := $value)

#check PrettyPrinter.ppCommand

def mkStatement (name?: Option Name)(type: Syntax.Term)
    (value?: Option Syntax.Term)(isProp: Bool) (isNoncomputable: Bool := false) :
        CoreM String := do
    let stx ← mkStatementStx name? type value? isProp (isNoncomputable := isNoncomputable)
    let fmt ← ppCommand stx
    return fmt.pretty

def mkTheoremWithDoc (name: Name)(thm: String)
    (doc: String) :
        CoreM String := do
    let type? := runParserCategory (← getEnv) `term thm |>.toOption
    match type? with
    | none => return ""
    | some type => do
        let type : Syntax.Term := ⟨type⟩
        let name := mkIdent name
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ " -/")]
        let stx ← `(command| $docs:docComment theorem $name : $type := by sorry)
        let fmt ← ppCategory `command stx
        return fmt.pretty

def mkStatementWithDocStx (name?: Option Name)(type: Syntax.Term)
        (value?: Option Syntax.Term)(isProp: Bool)
        (useExample: Bool := false)(doc: String) (isNoncomputable : Bool := false) : CoreM Syntax.Command := do
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ " -/")]
    let (ctxs, tailType) ← arrowHeads type
    let value := value?.getD (← `(by sorry))
    if name?.isNone && useExample then
        if isNoncomputable
        then
            `(command| $docs:docComment noncomputable example $ctxs* : $tailType := $value)
        else
            `(command| $docs:docComment example $ctxs* : $tailType := $value)
    else
        let hash := hash type.raw.reprint
        let inner_name :=
            Name.mkSimple s!"aux_{hash}"
        let name := mkIdent <| name?.getD inner_name
        if isProp
        then
            `(command| $docs:docComment theorem $name $ctxs* : $tailType := $value)
        else
            if isNoncomputable
            then
                `(command| $docs:docComment noncomputable def $name:ident $ctxs* : $tailType := $value)
            else
                `(command| $docs:docComment def $name:ident $ctxs* : $tailType := $value)

def mkStatementWithDoc (name?: Option Name)(type: Syntax.Term)
        (value?: Option Syntax.Term)(isProp: Bool)(useExample: Bool := false)
        (doc: String) (isNoncomputable : Bool := false) : CoreM String := do
    let stx ← mkStatementWithDocStx name? type value? isProp useExample doc (isNoncomputable := isNoncomputable)
    let fmt ← ppCategory `command stx
    return fmt.pretty
