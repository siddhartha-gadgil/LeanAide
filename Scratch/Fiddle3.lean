import Lean

open Lean Meta Elab Term Parser Command Tactic

def egStx₀  : MetaM Syntax := do
  let stx ← `(command| def three := 1 + 2)
  return stx

#eval egStx₀

#check Lean.Environment.getModuleIdx?
#check Lean.Environment.getModuleIdxFor? -- (env : Environment) (moduleName : Name) : Option ModuleIdx

#check Lean.Environment.header
#check EnvironmentHeader.moduleData
#check EnvironmentHeader.mainModule
#check ModuleData.constants
#check sepBy1IndentSemicolon
#check MetaM

syntax commandSeq := sepBy1IndentSemicolon(command)

def commands : TSyntax `commandSeq → Array (TSyntax `command)
  | `(commandSeq| $cs*) => cs
  | _ => #[]

def toCommandSeq : Array (TSyntax `command) → CoreM (TSyntax `commandSeq)
  | cs => `(commandSeq| $cs*)

def myName: MetaM Name :=  do
  let env ← getEnv
  pure env.mainModule
#eval myName

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
#check Term.depArrow

#eval egFmt `three

#eval egFmt Name.anonymous

def egFmt₀  : MetaM Format := do
  let stx ← `(command| def three := 1 + 2)
  PrettyPrinter.ppCategory `command stx

#eval egFmt₀

#check mkIdent

#print Nat.add

def trivialEquality : Syntax → MetaM Bool
  | `($a = $b) => return a == b
  | _ => return false

#eval do
  let stx ← `(1 = 2)
  let b ← trivialEquality stx
  let stx' ← `(1 = 1)
  let b' ← trivialEquality stx'
  return (b, b')

open Tactic
