import Lean

open Lean Meta Elab Parser

namespace LeanAide
/-!
Code from Lean 4 copied, simplified and customized. The main change is that instead of parsing the imports the current environment is used. In the entry point `simpleRunFrontend` the environment is passed as an argument.

In the `runFrontendM` function the environment is modified if the `modifyEnv` flag is set to true. The `elabFrontDefValueM` function is used to get the value of a definition in the environment. The `checkElabFrontM` function is used to check if the code has any errors.
-/

def simpleRunFrontend
    (input : String)
    (env: Environment)
    (opts : Options := {})
    (fileName : String := "<input>")
    : IO (Environment × MessageLog) := unsafe do
  let inputCtx := Parser.mkInputContext input fileName
  let commandState := Command.mkState env (opts := opts)
  let parserState: ModuleParserState := {}
  let s ← IO.processCommands inputCtx parserState commandState
  pure (s.commandState.env, s.commandState.messages)

def runFrontendM (input: String)(modifyEnv: Bool := false) : MetaM (Environment × MessageLog) := do
  let (env, chk) ← simpleRunFrontend input (← getEnv)
  if modifyEnv then setEnv env
  return (env, chk)

def elabFrontDefExprM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM Expr := do
  let (env, _) ← runFrontendM s modifyEnv
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => match seek.value? with
    | none => throwError "Definition has no value"
    | some val => return val

def elabFrontDefTypeValExprM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM <| Expr × Expr := do
  let (env, _) ← runFrontendM s modifyEnv
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => match seek.value? with
    | none => throwError "Definition has no value"
    | some val => return (seek.type, val)


def elabFrontThmExprM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM Expr := do
  let (env, msgs) ← runFrontendM s modifyEnv
  logInfo "Messages"
  for msg in msgs.toList do
    logInfo msg.data
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => return seek.type

def elabFrontDefsExprM(s: String)(ns: List Name)(modifyEnv: Bool := false) : MetaM <| List (Name × Expr) × MessageLog := do
  let (env, msgs) ← runFrontendM s modifyEnv
  let nameDefs := ns.filterMap fun n =>
    match env.find? n with
    | none => none
    | some c => c.value?.map (n, ·)
  return (nameDefs, msgs)

def elabFrontDefViewM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM String := do
  let val ← elabFrontDefExprM s n modifyEnv
  let fmt ←  ppExpr val
  return fmt.pretty

def elabFrontTheoremExprM (type: String) : MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"theorem {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings

-- #eval elabFrontTheoremExprM "∀ n: Nat, n ≤ n + 1"

def elabFrontTypeExprM(type: String) : MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"def {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings

def checkElabFrontM(s: String) : MetaM <| List String := do
  -- IO.eprintln  s!"Checking command elaboration for: {s}"
  let (env, log) ← runFrontendM  s
  let mut l := []
  for msg in log.toList do
    if msg.severity == MessageSeverity.error then
      let x ← msg.data.toString
      -- IO.eprintln s!"Error: {x}"
      -- IO.eprintln s!"imports : {env.allImportedModuleNames.size}"
      l := l.append [x]
  return l

def checkTypeElabFrontM(s: String) : MetaM <| List String := do
  checkElabFrontM s!"example : {s} := by sorry"

def checkTermElabFrontM(s: String) : MetaM <| List String := do
  checkElabFrontM s!"example := {s}"



-- #eval checkTermElabFrontM "(fun n => 3 : Nat → Nat)"

-- Not efficient, should generate per command if this is needed
def newDeclarations (s: String) : MetaM <| List Name := do
  let constants := (← getEnv).constants.map₁.toList.map (·.1)
  let (env, _) ← runFrontendM s
  let newConstants := env.constants.map₁.toList.map (·.1)
  return newConstants.filter (· ∉ constants)

-- #eval newDeclarations "def x : Nat := 0"

#check Elab.runFrontend
