import Lean

open Lean Meta Elab Term

namespace LeanAide

structure TopCodeData where
  imports : List String
  codeLines : List String
deriving Inhabited

def TopCodeData.toString (tc : TopCodeData) : String :=
  let importsStr := String.intercalate "\n" tc.imports
  let codeStr := String.intercalate "\n" tc.codeLines
  s!"{importsStr}\n{codeStr}\n"

def topCodeData : TopCodeData :=
  { imports := ["import Mathlib"]
    codeLines := ["universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u₁ u₂ u₃",
                   "set_option maxHeartbeats 10000000",
                   "set_option linter.unreachableTactic false",
                   "open scoped Nat"] }

initialize topDataExt :
    SimpleScopedEnvExtension TopCodeData TopCodeData ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        n
    initial := topCodeData -- empty by default
  }

elab "#topCode" "[" imps:str,* "]" "[" lines:str,* "]" : command => Command.liftTermElabM do
    let imports := imps.getElems.map (·.getString)
    let codeLines := lines.getElems.map (·.getString)
    let newData := { imports := imports.toList, codeLines := codeLines.toList }
    topDataExt.add newData

def topCodeDataM : MetaM TopCodeData := do
  return topDataExt.getState (← getEnv)

def topCodeM : MetaM String := do
  let data ← topCodeDataM
  return data.toString

initialize pretranslateExt :
    SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        m.push n
    initial := #[] -- empty by default
  }

partial def fixSyntaxStep? (stx: Syntax) :
  MetaM <| Option Syntax := do
  let names := pretranslateExt.getState (← getEnv)
  let fns ← names.mapM fun n =>
    unsafe evalConst (Syntax → MetaM (Option Syntax)) n
  for fn in fns do
    match ← fn stx with
    | some newStx => return some newStx
    | none => continue
  return none

partial def fixSyntax (stx: Syntax.Term) : MetaM Syntax.Term := do
  let stx ← stx.raw.replaceM fixSyntaxStep?
  return ⟨stx⟩

syntax (name := pretranslate) "syntax_fix" : attr

initialize registerBuiltinAttribute {
  name := `pretranslate
  descr := "Prompt for trying to retranslate a theorem or definition."
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let expectedType ← mkArrow (mkConst ``Syntax) (← mkAppM ``MetaM #[(← mkAppM ``Option #[mkConst ``Syntax])])
    unless (← isDefEq declTy expectedType) do
      throwError s!"pretranslate attribute can only be applied to functions of type Syntax → MetaM (Option Syntax), type of {decl} is {declTy}"
    pretranslateExt.add decl
}

open Parser Tactic

initialize extraAutoTacticsExt :
    SimpleScopedEnvExtension (TSyntax ``tacticSeq) (Array (TSyntax ``tacticSeq)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        m.push n
    initial := #[] -- empty by default
  }

elab "#add_auto_tactics" "[" tacs:tacticSeq,* "]" : command => do
  for tac in tacs.getElems do
    extraAutoTacticsExt.add tac

def getAutoTactics : MetaM (Array (TSyntax ``tacticSeq)) := do
  return extraAutoTacticsExt.getState (← getEnv)

end LeanAide
