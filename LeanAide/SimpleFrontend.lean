import Lean

open Lean Meta Elab Parser

/-!
Code from Lean 4 copied, simplified and customized. The main change is that instead of parsing the imports the current environment is used. In the entry point `simpleRunFrontend` the environment is passed as an argument.

In the `runFrontendM` function the environment is modified if the `modifyEnv` flag is set to true. The `elabFrontDefValueM` function is used to get the value of a definition in the environment. The `checkElabFrontM` function is used to check if the code has any errors.
-/

def simpleRunFrontend
    (input : String)
    (env: Environment)
    (opts : Options := {})
    (fileName : String := "<input>")
    : IO (Environment × MessageLog) := do
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

def elabFrontDefViewM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM String := do
  let val ← elabFrontDefExprM s n modifyEnv
  let fmt ←  ppExpr val
  return fmt.pretty

def checkElabFrontM(s: String) : MetaM <| List String := do
  let (_, log) ← runFrontendM s
  let mut l := []
  for msg in log.toList do
    if msg.severity == MessageSeverity.error then
      let x ← msg.data.toString
      l := l.append [x]
  return l

def codeBlock (code: String) (s: String) : String :=
  let fullSplit := s.splitOn s!"```{code}"
  let split := if fullSplit.length > 1
    then fullSplit.get! 1 else
    s.splitOn "```" |>.get! 1
  split.splitOn "```" |>.get! 0

def codeBlock? (code: String) (s: String) : Option String := do
  let split ←   s.splitOn s!"```{code}" |>.get? 1 |>.orElse fun _ =>
    s.splitOn "```" |>.get? 1
  split.splitOn "```" |>.get? 0


-- Not efficient, should generate per command if this is needed
def newDeclarations (s: String) : MetaM <| List Name := do
  let constants := (← getEnv).constants.map₁.toList.map (·.1)
  let (env, _) ← runFrontendM s
  let newConstants := env.constants.map₁.toList.map (·.1)
  return newConstants.filter (· ∉ constants)

-- #eval newDeclarations "def x : Nat := 0"
