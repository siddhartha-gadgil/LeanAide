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

def levelNames :=
  [`u, `v, `u_1, `u_2, `u_3, `u_4, `u_5, `u_6, `u_7, `u_8, `u_9, `u_10, `u_11, `u₁, `u₂, `v₁, `v₂, `uι, `W₁, `W₂, `w₁, `w₂, `u', `v', `uu, `w, `w', `wE, `uE, `x]

def univLine : String := levelNames.foldl (fun s u => s!"{s} {u}") "universe"

def topCodeData : TopCodeData :=
  { imports := ["import Mathlib"]
    codeLines := [univLine,
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

initialize staticAutoTacticsExt :
    SimpleScopedEnvExtension (Nat × TSyntax ``tacticSeq) (Array (Nat × TSyntax ``tacticSeq)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        m.push n
    initial := #[] -- empty by default
  }

syntax "#add_auto_tactics" ("(level:=" num")")? "[" tacticSeq,* "]" : command

elab_rules : command
  | `(command| #add_auto_tactics (level:=$n:num) [ $tacs,* ]) => do
    for tac in tacs.getElems do
      staticAutoTacticsExt.add (n.getNat, tac)
  | `(command| #add_auto_tactics [ $tacs,* ]) => do
    for tac in tacs.getElems do
      staticAutoTacticsExt.add (0, tac)

def getStaticAutoTactics (maxLevel : Nat) : MetaM (Array (Nat × TSyntax ``tacticSeq)) := do
  return (staticAutoTacticsExt.getState (← getEnv)).filter (fun (level, _) => level ≤ maxLevel)

initialize dynamicAutoTacticsExt :
    SimpleScopedEnvExtension (Nat × Name) (Array (Nat × Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        m.push n
    initial := #[] -- empty by default
  }

initialize registerBuiltinAttribute {
  name := `auto_tactic_gen
  descr := "Register goal dependent dynamic auto tactics."
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let expectedType := Lean.Expr.forallE Lean.Name.anonymous (Lean.Expr.const `Lean.MVarId []) (Lean.Expr.forallE
    Lean.Name.anonymous
    (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `Lean.Name []))
    (Lean.Expr.app
      (Lean.Expr.const `Lean.Meta.MetaM [])
      (Lean.Expr.app
        (Lean.Expr.const `Lean.TSyntax [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Lean.SyntaxNodeKind []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Lean.Name.mkStr4 []) (Lean.Expr.lit (Lean.Literal.strVal "Lean")))
                  (Lean.Expr.lit (Lean.Literal.strVal "Parser")))
                (Lean.Expr.lit (Lean.Literal.strVal "Tactic")))
              (Lean.Expr.lit (Lean.Literal.strVal "tacticSeq"))))
          (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Lean.SyntaxNodeKind [])))))
    (Lean.BinderInfo.default)) (Lean.BinderInfo.default)

    unless (← withNewMCtxDepth <| isDefEqGuarded declTy expectedType) do
      throwError s!"auto_tactic_gen attribute can only be applied to functions of type {expectedType}, type of {decl} is {declTy}"
    let level := stx.toNat
    dynamicAutoTacticsExt.add (level, decl)
}

def getDynamicAutoTactics (goal : MVarId) (localNames: Array Name)(maxLevel : Nat) : MetaM (Array (Nat × TSyntax ``tacticSeq)) := do
  let dynTacs := (dynamicAutoTacticsExt.getState (← getEnv)).filter (fun (level, _) => level ≤ maxLevel)
  dynTacs.mapM fun (level, fn) => do
    let tac ← unsafe evalConst (MVarId → Array Name → MetaM (TSyntax ``tacticSeq)) fn
    let tacStx ← tac goal localNames
    return (level, tacStx)


end LeanAide
