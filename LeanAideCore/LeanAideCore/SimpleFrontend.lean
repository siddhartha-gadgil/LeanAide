import Lean
import LeanAideCore.Aides
import LeanAideCore.Config
set_option linter.unusedSimpArgs false
open Lean Meta Elab Parser

namespace LeanAide
/-!
Code from Lean 4 copied, simplified and customized. The main change is that instead of parsing the imports the current environment is used. In the entry point `simpleRunFrontend` the environment is passed as an argument.

In the `runFrontendM` function the environment is modified if the `modifyEnv` flag is set to true. The `elabFrontDefValueM` function is used to get the value of a definition in the environment. The `checkElabFrontM` function is used to check if the code has any errors.
-/

def defaultTop : String := s!"{univLine}
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open scoped Nat
"

def simpleRunFrontend
    (input : String)
    (env: Environment)
    (opts : Options := {}) (top : String := defaultTop)
    (fileName : String := "<input>")
    : IO (Environment × MessageLog) := unsafe do
  let inputCtx := Parser.mkInputContext (top ++ input) fileName
  let commandState := Command.mkState env (opts := opts)
  let parserState: ModuleParserState := {}
  let s ← IO.processCommands inputCtx parserState commandState
  pure (s.commandState.env, s.commandState.messages)

def runFrontendM (input: String)(modifyEnv: Bool := false) (top : String := defaultTop) : MetaM (Environment × MessageLog) := do
  traceAide `leanaide.frontend.info s!"Running frontend on input:\n{input}"
  let (env, msgs) ← simpleRunFrontend input (← getEnv) (top := top)
  traceAide `leanaide.frontend.info s!"Frontend finished with {msgs.toList.length} messages"
  for msg in msgs.toList do
    traceAide `leanaide.frontend.debug s!"{← msg.toString}"
  if modifyEnv then setEnv env
  return (env, msgs)

def runFrontendSafeM (input: String) (top : String := defaultTop) : MetaM Bool := do
  traceAide `leanaide.frontend.info s!"Running frontend on input:\n{input}"
  let (env, msgs) ← simpleRunFrontend input (← getEnv) (top := top)
  traceAide `leanaide.frontend.info s!"Frontend finished with {msgs.toList.length} messages"
  let safe := msgs.toList.all (fun msg => msg.severity != MessageSeverity.error)
  traceAide `leanaide.frontend.info s!"Frontend safe: {safe}"
  for msg in msgs.toList do
    traceAide `leanaide.frontend.debug s!"{← msg.toString}"
  if safe then setEnv env
  else
    traceAide `leanAide.frontend.info s!"Error when running frontend:\n{input}\nMessages:"
    for msg in msgs.toList do
      traceAide `leanaide.frontend.info s!"{← msg.toString}"
  return safe

-- variable [LeanAideBaseDir]

def runFrontEndForMessages (input: String) (envHash? : Option UInt64) (top : String := defaultTop) : MetaM MessageLog := do
  let hashString := match envHash? with
  | none => ""
  | some h => s!"_{h}"
  let cacheFile := (← cachePath) / "frontend" / s!"{input.hash}{hashString}_{← leanToolchain}.json"
  if (← cacheFile.pathExists) then
    let content ← IO.FS.readFile cacheFile
    let json := Json.parse content
       match json with
       | Except.error err =>
         traceAide `leanaide.frontend.info s!"Could not parse frontend cache file {cacheFile}: {err}"
       | Except.ok j =>
         match fromJson? (α :=  List SerialMessage) j  with
         | .error e =>
           traceAide `leanaide.frontend.info s!"Could not decode frontend cache file {cacheFile}, error: {e}"
         | .ok ss =>
           let msgs := ss.foldl (fun log msg => log.add msg.toMessage) (MessageLog.empty)
           traceAide `leanaide.frontend.info s!"Frontend read from {cacheFile} with {msgs.toList.length} messages (from cache)"
           for msg in msgs.toList do
             traceAide `leanaide.frontend.debug s!"{← msg.toString}"
           return msgs
  traceAide `leanaide.frontend.info s!"Running frontend (no cache) on input:\n{input}"
  let (_, msgs) ← runFrontendM input (top := top)
  let serialMsgs ←  msgs.toList.mapM fun m => m.serialize
  let json := toJson serialMsgs
  IO.FS.writeFile cacheFile (json.pretty)
  traceAide `leanaide.frontend.info s!"Frontend wrote to {cacheFile} with {msgs.toList.length} messages"
  return msgs

def elabFrontDefExprM(s: String)(n: Name)(modifyEnv: Bool := false) (top : String := defaultTop) : MetaM Expr := do
  let (env, _) ← runFrontendM s modifyEnv (top := top)
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => match seek.value? with
    | none => throwError "Definition has no value"
    | some val => return val

def elabFrontDefTypeValExprM(s: String)(n: Name)(modifyEnv: Bool := false) (top : String := defaultTop) : MetaM <| Expr × Expr := do
  let (env, _) ← runFrontendM s modifyEnv (top := top)
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => match seek.value? with
    | none => throwError "Definition has no value"
    | some val => return (seek.type, val)


def elabFrontThmExprM(s: String)(n: Name)(modifyEnv: Bool := false) (top : String := defaultTop) : MetaM Expr := do
  let (env, msgs) ← runFrontendM s modifyEnv (top := top)
  logInfo "Messages"
  for msg in msgs.toList do
    logInfo msg.data
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => return seek.type

def elabFrontDefsExprM(s: String)(ns: List Name)(modifyEnv: Bool := false) (top : String := defaultTop) : MetaM <| List (Name × Expr) × MessageLog := do
  let (env, msgs) ← runFrontendM s modifyEnv (top := top)
  let nameDefs := ns.filterMap fun n =>
    match env.find? n with
    | none => none
    | some c => c.value?.map (n, ·)
  return (nameDefs, msgs)

def dropPrefixes : Name → Name
| .anonymous => .anonymous
| .str _ s => .str .anonymous s
| .num _ n => .num .anonymous n

  ---   #eval dropPrefixes `LeanAideCore.SimpleFrontend.elabFrontDefsExprAtM


def elabFrontDefsExprAtM(s: String)(pfx: Name)(modifyEnv: Bool := false) (top : String := defaultTop) : MetaM <| Array (Name × Expr) × MessageLog := do
  let (env, msgs) ← runFrontendM s modifyEnv (top := top)
  let decls := env.constants.map₁.toArray
  let ns := decls.filterMap (fun (n, _) => if pfx.isPrefixOf n then some n else none)
  logInfo "Looking for declarations with suffix `eg"
  for d in decls do
    if (`eg).isSuffixOf d.1 then
      logInfo s!"Found declaration: {d.1} with type {d.2.type}"
  let nameDefs := ns.filterMap fun n =>
    match env.find? n with
    | none => none
    | some c => c.value?.map (n, ·)
  logInfo "Messages"
  for msg in msgs.toList do
    logInfo msg.data
  logInfo s!"Found {ns.size} definitions with prefix {pfx}"
  return (nameDefs, msgs)

--    def egCodeAt := "namespace leanaide_scratch
--    def eg : True := by simp
--    end leanaide_scratch"

--    def egVal : MetaM (Array Name) := do
--      let res ← elabFrontDefsExprAtM egCodeAt `leanaide_scratch
--      return res.1.map (fun (n, _) => n)

--    #eval egVal

--    #eval (`leanaide_scratch).isPrefixOf `leanaide_scratch.eg

def elabFrontDefViewM(s: String)(n: Name)(modifyEnv: Bool := false) (top : String := defaultTop) : MetaM String := do
  let val ← elabFrontDefExprM s n modifyEnv (top := top)
  let fmt ←  ppExpr val
  return fmt.pretty


def elabFrontTheoremExprMStrict (type: String) (top : String := defaultTop) : MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"set_option autoImplicit true in\ntheorem {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s (top := top)
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings

def elabFrontTheoremExprM (type: String) (top : String := defaultTop) : MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"set_option autoImplicit true in\nnoncomputable def {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s (top := top)
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings


--    #eval elabFrontTheoremExprM "∀ n: Nat, n ≤ n + 1"

def elabFrontTypeExprM(type: String) (top : String := defaultTop) : MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"def {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s (top := top)
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings

def checkElabFrontM(s: String) (envHash? : Option UInt64) (top : String := defaultTop) : MetaM <| List String := do
  let log ← runFrontEndForMessages  s envHash? (top := top)
  let mut l := []
  for msg in log.toList do
    if msg.severity == MessageSeverity.error then
      let x ← msg.data.toString
      --    logToStdErr `leanaide.translate.info s!"Error: {x}"
      --    logToStdErr `leanaide.translate.info s!"imports : {env.allImportedModuleNames.size}"
      l := l.append [x]
  return l

def checkTypeElabFrontM(s: String) (envHash? : Option UInt64) (top : String := defaultTop) : MetaM <| List String := do
  checkElabFrontM s!"example : {s} := by sorry" envHash? (top := top)

def checkTermElabFrontM(s: String) (envHash? : Option UInt64) (top : String := defaultTop) : MetaM <| List String := do
  checkElabFrontM s!"example := {s}" envHash? (top := top)



--    #eval checkTermElabFrontM "(fun n => 3 : Nat → Nat)"

def newDeclarations (s: String) (top : String := defaultTop) : MetaM <| Array Name := do
  let constants := (← getEnv).constants
  let (env, _) ← runFrontendM s (top := top)
  let mut newConstants := #[]
  for (n, _) in env.constants do
    unless n.isInternal do
    if  !constants.contains n then
      newConstants := newConstants.push n
  return newConstants


def elabFrontDefsNewExprM(s: String)(top : String := defaultTop) : MetaM <| List (Name × Expr) × MessageLog := do
  let constants := (← getEnv).constants
  let (env, msgs) ← runFrontendM s (top := top)
  let mut nameDefs := #[]
  for (n, d) in env.constants do
    unless n.isInternal do
    if  !constants.contains n then
      match d.value? with
      | none => continue
      | some v => --    logToStdErr `leanaide.translate.info s!"Found new definition: {n} with
        nameDefs := nameDefs.push (n, v)
  return (nameDefs.toList, msgs)



end LeanAide
