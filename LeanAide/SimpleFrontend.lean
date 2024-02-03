import Lean

open Lean Meta Elab Parser

/-!
Code from Lean 4 copied, simplified and customized. The main change is that instead of parsing the imports the current environment is used. In the entry point `simpleRunFrontend` the environment is passed as an argument.

In the `runFrontendM` function the environment is modified if the `modifyEnv` flag is set to true. The `defFrontValueM` function is used to get the value of a definition in the environment. The `checkElabFrontM` function is used to check if the code has any errors.
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

def defFrontValueM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM String := do
  let (env, _) ← runFrontendM s modifyEnv
  let seek? : Option ConstantInfo :=  env.find? n
  let seek := seek?.get!
  let val := seek.value?.get!
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

-- Not efficient, should generate per command if this is needed
def newDeclarations (s: String) : MetaM <| List Name := do
  let constants := (← getEnv).constants.map₁.toList.map (·.1)
  let (env, _) ← runFrontendM s
  let newConstants := env.constants.map₁.toList.map (·.1)
  return newConstants.filter (· ∉ constants)

-- #eval newDeclarations "def x : Nat := 0"
