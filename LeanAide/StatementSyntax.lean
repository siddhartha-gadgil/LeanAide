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
    (value?: Option Syntax.Term)(isProp: Bool) :
        CoreM (TSyntax `command) := do
    let (ctxs, tailType) ← arrowHeads type
    let value := value?.getD (← `(by sorry))
    let hash := hash type.raw.reprint
    let inner_name :=
        Name.num (Name.mkSimple "aux") hash.toNat
    let name := mkIdent <| name?.getD inner_name
    if isProp
    then
        `(command| theorem $name $ctxs* : $tailType := $value)
    else
        `(command| def $name:ident $ctxs* : $tailType := $value)

def mkStatement (name?: Option Name)(type: Syntax.Term)
    (value?: Option Syntax.Term)(isProp: Bool) :
        CoreM String := do
    let stx ← mkStatementStx name? type value? isProp
    let fmt ← ppCategory `command stx
    return fmt.pretty
