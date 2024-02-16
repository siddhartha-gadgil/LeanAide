import Lean

open Lean Meta Elab Term PrettyPrinter

def egStx₀  : MetaM Syntax := do
  let stx ← `(command| def three := 1 + 2)
  return stx

#eval egStx₀

open Lean.Parser.Term Parser
def bracketedBinderT : Parser := bracketedBinder true

def egStx (name: Name) : MetaM Syntax := do
  let id := mkIdent name
  let s : TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] := mkIdent `x
  let s' : TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] ← `(bracketedBinderF| (x : Y))
  let ss := #[s, s']
  let type := mkIdent ``Nat
  let stx ← `(command| def $id $ss* : $type := 1 + 2)
  return stx

def egFmt (name: Name) : MetaM Format := do
  logInfo m!"{name}"
  PrettyPrinter.ppCategory `command (← egStx name)

#check Lean.Parser.Command.optDeclSig
#check bracketedBinderF

#eval egFmt `three

#eval egFmt Name.anonymous

def egFmt₀  : MetaM Format := do
  let stx ← `(command| def three := 1 + 2)
  PrettyPrinter.ppCategory `command stx

#eval egFmt₀

#check mkIdent

#print Nat.add
