import Lean
import LeanAideCore.Aides
import LeanAideCore.SimpleFrontend
import LeanAideCore.DefData
import LeanAideCore.PromptExampleBuilder
import LeanAideCore.ChatClient

open Lean Meta Elab Term
namespace LeanAide
-- variable [LeanAideBaseDir]

/--
Text source for a definition.
-/
structure DefSource where
  doc : String
  isProp : Bool
deriving ToJson, FromJson, Repr


/--
Error during elaboration.
-/
inductive ElabError : Type where
| unparsed (text parseError: String) (context? : Option String) : ElabError
| parsed (text elabError : String) (cmdErrors : List String)
    (context? : Option String) : ElabError
deriving Repr, ToJson, FromJson

def ElabError.text : ElabError → String
  | .unparsed text _ _ => text
  | .parsed text _ _ _ => text

def ElabError.error : ElabError → String
  | .unparsed _ parseError _ => parseError
  | .parsed _ _ cmdErrors _ =>
      if cmdErrors.isEmpty then
        "no front-end errors"
      else
        cmdErrors.foldr (· ++ "\n" ++ · ) ""

instance : ToMessageData (ElabError) where
  toMessageData (err) := match err with
  | .unparsed text parseError _ => m!"Parsing error: {parseError} for {text}"
  | .parsed text elabError cmdErrors _ =>
      m!"Elaboration errors : {elabError} for {text}; front-end errors: {cmdErrors}"

/--
A collection of elaboration errors during translation.
-/
structure ElabErrorData where
  source : String
  prompt? : Option Json
  elabErrors : Array ElabError
deriving FromJson, ToJson, Repr

/--
A collection of elaboration errors during translation, when elaboration is done by forming a command.
-/
inductive CmdElabError : Type where
| unparsed (text parseError: String) (context? : Option String) : CmdElabError
| parsed (text : String) (cmdErrors : List String)
    (context? : Option String) : CmdElabError
deriving Repr, ToJson, FromJson

def CmdElabError.text : CmdElabError → String
  | .unparsed text _ _ => text
  | .parsed text _ _ => text

def CmdElabError.fallback (errs : Array CmdElabError) :
    MetaM String := do
  let bestParsed? := errs.findSome? (fun e => do
    match e with
    | CmdElabError.parsed e .. => some e
    | _ => none)
  match bestParsed? with
  | some e => return e
  | none => match errs[0]? with
    | some e => return e.text
    | _ => throwError "no outputs found"

/--
Result of translating a definition.
-/
inductive DefTranslateResult : Type where
  | success (dfns : Array DefData) : DefTranslateResult
  | failure
    (progress : Array DefData) (error : Array CmdElabError) : DefTranslateResult

/--
Result of translating back a definition and comparing.
-/
inductive TranslateBackResult where
  | success (statement translation: String)
    (checks : Array Bool) (checksData : Array String) : TranslateBackResult
  | failure  : TranslateBackResult
  deriving Repr, ToJson, FromJson

def TranslateBackResult.checkFailed (r: TranslateBackResult) : Bool :=
  match r with
  | TranslateBackResult.success _ _ checks _ => checks.any id
  | TranslateBackResult.failure => true

/--
Result of elaborating a term, excluding the resulting expressions (to allow serialization).
-/
structure ElabSuccessBase where
  typeView : String
  allElaborated : Array String
  groups : Array (Array String)
  roundTripCheck? : Option Bool := none
  roundTripFailures : Array (String × Array (Bool × String)) := #[]
  deriving Repr, ToJson, FromJson

/--
Result of elaborating a term.
-/
structure ElabSuccessResult extends ElabSuccessBase where
  term : Expr
  allElaboratedExprs : Array Expr
  groupsExprs : Array (Array Expr)

def ElabSuccessResult.view (er: ElabSuccessResult) : MetaM String :=
  er.term.view

structure TranslateSuccessResult extends ElabSuccessResult where
  view : String

def ElabSuccessResult.withView (er: ElabSuccessResult) : MetaM TranslateSuccessResult := do
  return {er with view := (← er.view)}

abbrev TranslateResult := Except ElabErrorData ElabSuccessResult

structure LabelledTheorem where
  /-- Name of the theorem -/
  name : Name
  /-- LaTeX-style label for the theorem -/
  label : String
  /-- Statement of the theorem -/
  type : Expr
  /-- Whether the theorem is proved; need not be a complete proof, just to know if a proof is deferred -/
  isProved : Bool
  /-- source -/
  source: Json
deriving Repr

/--
State for translation. The main motivation for this was to avoid repeatedly loading embeddings.
-/
structure Translate.State where
  /-- Embeddings to preload -/
  embedMap : EmbedMap := Std.HashMap.emptyWithCapacity
  /-- Embedding response associated to the query -/
  queryEmbeddingCache : Std.HashMap String (Except String Json) := Std.HashMap.emptyWithCapacity 100000
  /-- Descriptions, docstrings etc -/
  descriptionMap : Std.HashMap Name Json := Std.HashMap.emptyWithCapacity 100000
  cmdPrelude : Array Syntax.Command := #[]
  /-- Relevant definitions to include in a prompt -/
  defs : Array (DefData) := #[]
  promptContext : Array String := #[]
  varPreludes : Array String := #[]
  outputFile : Option System.FilePath := none
  errorLog : Array ElabErrorData := #[]
  context : Option String := none
  labelledTheorems : Array LabelledTheorem := #[]
  recentTranslations: Array ChatPair := #[] -- (input, output)
  numRecentTranslationsToUse : Nat := 0
deriving Inhabited

/-- Monad with environment for translation -/
abbrev TranslateM := StateT Translate.State TermElabM

open Command in
instance : MonadEval TranslateM CommandElabM where
  monadEval := fun x => liftTermElabM <| x.run' {}

namespace Translate

def getEmbedMap : TranslateM EmbedMap := do
  return (← get).embedMap

def addEmbeddings (descField: String) (embeddings: EmbedData) : TranslateM Unit := do
  modify fun s => {s with embedMap := s.embedMap.insert descField embeddings}

def setEmbedMap (em : EmbedMap) : TranslateM Unit := do
  modify fun s => {s with embedMap := em}

def withEmbeddings (em : EmbedMap) (x: TranslateM α) :
    TranslateM α := do
  setEmbedMap em
  x

def setContext (ctx : String) : TranslateM Unit := do
  modify fun s => {s with context := some ctx}

def getContext : TranslateM <| Option String := do
  return (← get).context

def logError (source: String) (prompt?: Option Json) (errs: Array ElabError) : TranslateM Unit := do
  modify fun s => {s with errorLog := s.errorLog.push {source := source, prompt? := prompt?, elabErrors := errs}}

def getErrors : TranslateM <| Array ElabErrorData := do
  return (← get).errorLog

def printKeys : TranslateM Unit := do
  let em := (← getEmbedMap)
  logToStdErr `leanaide.translate.info s!"Loaded embeddings: {em.toList.map Prod.fst}"

def getDescMap : TranslateM (Std.HashMap Name Json) := do
  return (← get).descriptionMap

def addDescription (desc: Json) : TranslateM Unit := do
  match desc.getObjValAs? String "name" with
  | Except.ok name => do
    let m ← getDescMap
    let newDesc :=
      match m.get? name.toName with
      | some d => d.mergeObj desc
      | none =>  desc
    modify fun s =>
      {s with descriptionMap := s.descriptionMap.insert name.toName newDesc}
  | Except.error _ => return

def uploadDesciptions (file: System.FilePath) : TranslateM Unit := do
  let lines ← IO.FS.lines file
  for line in lines do
    match Json.parse line with
    | Except.ok desc =>
      Translate.addDescription desc
    | Except.error _ => continue

def preloadDescriptions : TranslateM Unit := do
  let resourcesDir ← getResourcesDir
  if (← (resourcesDir / "mathlib4-prompts.jsonl").pathExists) then
    uploadDesciptions <| resourcesDir / "mathlib4-prompts.jsonl"
  else
     let _ ← IO.Process.output {cmd:= "curl", args := #["--output", (resourcesDir / "mathlib4-prompts.jsonl").toString, "https://storage.googleapis.com/leanaide_data/mathlib4-prompts.jsonl"]}
     uploadDesciptions <| resourcesDir   / "mathlib4-prompts.jsonl"

  if (← (resourcesDir / "mathlib4-descs.jsonl").pathExists) then
    uploadDesciptions <| resourcesDir / "mathlib4-descs.jsonl"
  else
     let _ ← IO.Process.output {cmd:= "curl", args := #["--output", (resourcesDir / "mathlib4-descs.jsonl").toString, "https://storage.googleapis.com/leanaide_data/mathlib4-descs.jsonl"]}
     uploadDesciptions <| resourcesDir / "mathlib4-descs.jsonl"

def getDescriptionData (name: Name) : TranslateM <| Option Json := do
  let m ← getDescMap
  if m.isEmpty then preloadDescriptions
  let m ← getDescMap
  match m.get? name with
  | some desc => return desc
  | none => return none

open PrettyPrinter
def cmdPreludeBlob : TranslateM String := do
  let cmds := (← get).cmdPrelude
  let cmds ←
    cmds.mapM (fun cmd => PrettyPrinter.ppCommand cmd)
  let cmds := cmds.map (·.pretty)
  return cmds.foldr (· ++ "\n" ++ · ) "\n\n"

def commandNeededForFrontendPrelude (cmd : Syntax.Command) : TranslateM Bool := do
  match ← DefData.ofSyntax? cmd with
  -- TODO: This duplicate-declaration filter can be useful only because
  -- `runFrontendM` starts from the current environment. It is unsafe with the
  -- current frontend cache, whose key depends on the input string/toolchain but
  -- not on the current generated environment. Either include a generated-env
  -- fingerprint in the cache key, or run frontend checks from a fixed base
  -- environment with the full generated textual prelude.
  | some dfn => return (← getEnv).find? dfn.name |>.isNone
  | none => return true

def cmdPreludeForFrontendBlob? : TranslateM <| Option String := do
  let cmds := (← get).cmdPrelude
  let cmds ← cmds.filterM commandNeededForFrontendPrelude
  if cmds.isEmpty then return none
  let cmds ←
    cmds.mapM (fun cmd => PrettyPrinter.ppCommand cmd)
  let cmds := cmds.map (·.pretty)
  return some <| cmds.foldr (· ++ "\n" ++ · ) "\n\n"

def variablePreludeForFrontendBlob? : TranslateM <| Option String := do
  match ← variableCommandFromLocalContext? with
  | some cmd => return some (← PrettyPrinter.ppCommand cmd).pretty
  | none => return none

-- TODO(generation-check-homogeneous): Keep prompt-only declarations separate
-- from the frontend prelude. Validate the command prelude on its own before
-- appending `body`, and do not attribute prelude diagnostics to `body`. Any
-- declaration open in local free variables must be closed before it can enter
-- this global-command prelude; changing the order alone is not a complete fix.
def withCommandPrelude (body : String) : TranslateM String := do
  let preludes := #[
    ← cmdPreludeForFrontendBlob?,
    ← variablePreludeForFrontendBlob?
  ].filterMap id
  match preludes.toList with
  | [] => return body
  | prelude :: rest =>
      let prelude := rest.foldl (· ++ "\n" ++ ·) prelude
      return prelude ++ "\n" ++ body

def cmdPreludeBriefBlob? : TranslateM <| Option String := do
  let cmds := (← get).cmdPrelude
  if cmds.isEmpty then return none
  let cmds ←
    cmds.mapM (fun cmd => do
      let brief ← theoremsWithoutProofs cmd
      PrettyPrinter.ppCommand brief)
  let cmds := cmds.map (·.pretty)
  return some <| cmds.foldl (· ++ "\n" ++ · ) "import Mathlib\n"

-- TODO(generation-check-homogeneous): Make this operation transactional. Check
-- error-severity messages and update the environment/prelude only on success;
-- do not discard the `runFrontendM` result.
def runCommand (cmd: Syntax.Command) : TranslateM Unit := do
  discard <|  runFrontendM (← ppCommand cmd).pretty true
  modify fun s  => {s with cmdPrelude := s.cmdPrelude.push cmd}

def writeCommands  (cmds : Array <| TSyntax `command) : TranslateM Unit := do
  match (← get).outputFile with
  | none => return
  | some file => do
    let contents ← IO.FS.readFile file
    let mut lines : Array String := #[]
    for cmd in cmds do
      let cmdStr := (← ppCommand cmd).pretty
      lines := lines.push cmdStr
    IO.FS.writeFile file <| contents ++ (lines.foldr (· ++ "\n" ++ · ) "")

-- TODO(generation-check-homogeneous): Rename this state-only operation to
-- `addCommandToPrelude` (and its plural analogue accordingly). The current name
-- incorrectly suggests that the command is elaborated or run. Prompt-only
-- context needs a separate API and must not be added here.
def addCommand (cmd: Syntax.Command) : TranslateM Unit := do
  modify fun s  => {s with cmdPrelude := s.cmdPrelude.push cmd}

-- TODO(generation-check-homogeneous): Split this into clearly named validation
-- and commit operations (for example `runAndCommitCommands`). Elaborate the
-- complete sequence in saved state, collect errors, and perform the environment
-- update, output write, and prelude append atomically only after success. This
-- full-declaration check must also reject proof terms with unexpected universe
-- parameters and tactics appended after a goal-closing fallback.
def addCommands (cmds: TSyntax ``commandSeq) : TranslateM Unit := do
  let cmds := getCommands cmds
  for cmd in cmds do
    discard <| runFrontendM (← ppCommand cmd).pretty true
  writeCommands cmds
  modify fun s => {s with cmdPrelude := s.cmdPrelude ++ cmds}

def registerDefnEnv (dfn: DefData) : TranslateM Unit := do
  runCommand <| ← dfn.statementStx
  modify fun s => {s with defs := s.defs.push dfn}

def addDefn (dfn: DefData) : TranslateM Unit := do
  modify fun s => {s with defs := s.defs.push dfn}

def addRecentTranslation (input: String) (output: String) : TranslateM Unit := do
  modify fun s =>
    let newRecent := s.recentTranslations.push {user:= input, assistant := output}
    {s with recentTranslations := newRecent}

def getRecentTranslations : TranslateM <| Array ChatPair := do
  let n := (← get).numRecentTranslationsToUse
  let recent := (← get).recentTranslations
  if n == 0 then
    return #[]
  else
    if recent.size <= n then
      return recent
    else
      return recent.extract (recent.size - n) recent.size

def setNumRecentTranslationsToUse (n: Nat) : TranslateM Unit := do
  modify fun s => {s with numRecentTranslationsToUse := n}

def getDefs : TranslateM <| Array DefData := do
  return (← get).defs

def clearDefs : TranslateM Unit := do
  modify fun s => {s with defs := #[]}

def defsBlob : TranslateM <| Array String := do
  let defs := (← get).defs
  defs.mapM <| fun dfn => dfn.statement

def defsNames : TranslateM <| Array Name := do
  let defs := (← get).defs
  defs.mapM <| fun dfn => do pure dfn.name

def addPromptContext (p: String) : TranslateM Unit := do
  modify fun s =>
    if s.promptContext.contains p then
      s
    else
      -- logToStdErr `leanaide.translate.info s!"Adding prompt context: {p}"
    {s with promptContext := s.promptContext.push p}

def addVarPrelude (p: String) : TranslateM Unit := do
  let decl := if p.startsWith "inst" then s!"[{p}]" else
    match p.toUTF8[0]? with
    | some c => if (Char.ofUInt8 c).isLower then s!"({p})" else "{" ++ p ++ "}"
    | none => s!"({p})"
  let notCommand :=
    Parser.runParserCategory (← getEnv) `command ("variable " ++ decl) |>.toOption.isNone
  modify fun s =>
    if notCommand || s.varPreludes.contains decl then
      s
    else
      {s with varPreludes := s.varPreludes.push decl}

def clearPreludes : TranslateM Unit := do
  modify fun s => {s with promptContext := #[]}

def preludesBlob : TranslateM <| Array String := do
  let preludes := (← get).promptContext
  preludes.mapM <| fun p => do pure p

def withPreludes (s: String) : TranslateM String := do
  let prelude ← preludesBlob
  return prelude.foldr (· ++ "\n" ++ · ) s

def withVarPreludes (s: String) : TranslateM String := do
  let preludes := (← get).varPreludes
  return preludes.foldr (· ++ " → " ++ · ) s

def defsNameBlob : TranslateM <| Array <| Name × String := do
  let defs := (← get).defs
  defs.mapM <| fun dfn => do pure (dfn.name, ← dfn.statement)

def binderInfoContextString (binderInfo : BinderInfo) (name type : String) : String :=
  match binderInfo with
  | BinderInfo.default => s!"({name} : {type})"
  | BinderInfo.implicit => "{" ++ name ++ " : " ++ type ++ "}"
  | BinderInfo.strictImplicit => "⦃" ++ name ++ " : " ++ type ++ "⦄"
  | BinderInfo.instImplicit => "[" ++ name ++ " : " ++ type ++ "]"

def localDeclContextLine? (decl : LocalDecl) : TranslateM (Option String) := do
  if decl.isImplementationDetail then
    return none
  match decl with
  | .cdecl _ _ userName type binderInfo .. =>
      let typeStr := (← PrettyPrinter.ppExpr type).pretty
      return some <| binderInfoContextString binderInfo userName.toString typeStr
  | .ldecl _ _ userName type value .. =>
      let typeStr := (← PrettyPrinter.ppExpr type).pretty
      let valueStr := (← PrettyPrinter.ppExpr value).pretty
      return some s!"let {userName} : {typeStr} := {valueStr}"

def localContextLines : TranslateM (Array String) := do
  let mut lines : Array String := #[]
  for decl in (← getLCtx) do
    if let some line ← localDeclContextLine? decl then
      lines := lines.push line
  return lines

def availableVariablesBlob : TranslateM String := do
  let lines ← localContextLines
  let body :=
    if lines.isEmpty then
      "(none)"
    else
      lines.foldl (fun acc line => acc ++ line ++ "\n") ""
  return "Available variables:\n" ++ body

def availableVariablesBlob? : TranslateM (Option String) := do
  let lines ← localContextLines
  if lines.isEmpty then
    return none
  else
    let body := lines.foldl (fun acc line => acc ++ line ++ "\n") ""
    return some <| "Available variables:\n" ++ body

def defDataContextLine (dfn : DefData) : TranslateM String := do
  let typeStr := (← ppTerm dfn.type).pretty
  return s!"{dfn.name} : {typeStr}"

def availableDeclarationsBlob (defs : Array DefData) : TranslateM String := do
  let lines ← defs.mapM defDataContextLine
  let body :=
    if lines.isEmpty then
      "(none)"
    else
      lines.foldl (fun acc line => acc ++ line ++ "\n") ""
  return "Available previous declarations:\n" ++ body

def availableContextBlobWithDefs (defs : Array DefData) : TranslateM String := do
  let vars ← availableVariablesBlob
  let decls ← availableDeclarationsBlob defs
  return vars ++ "\n" ++ decls

def availableContextBlob : TranslateM String := do
  availableContextBlobWithDefs (← getDefs)

def addTheorem (thm: LabelledTheorem) : TranslateM Unit := do
  modify fun s => {s with labelledTheorems := s.labelledTheorems.push thm}
def getTheorems : TranslateM <| Array LabelledTheorem := do
  return (← get).labelledTheorems

def findTheorem? (label: String) : TranslateM <| Option LabelledTheorem := do
  let thms := (← get).labelledTheorems
  return thms.find? (fun thm => thm.label == label)

def allLabels : TranslateM <| Array String := do
  let thms := (← get).labelledTheorems
  return thms.map (·.label)

def updateToProved (labelledTheorem : String) : TranslateM Unit := do
  let newLabelledTheorems := (← get).labelledTheorems.map (fun thm =>
    if thm.label == labelledTheorem then
      {thm with isProved := true}
    else
      thm)
  modify fun s => {s with labelledTheorems := newLabelledTheorems}

def deferredTheoremNames : TranslateM <| Array Name := do
  let thms := (← get).labelledTheorems
  return thms.filter (fun thm => !thm.isProved) |>.map (·.name)

def openDeferredTheoremsStx? : TranslateM <| Option Syntax.Command := do
  let thms := (← deferredTheoremNames)
  if thms.isEmpty then
    return none
  else
    let idents := thms.map (mkIdent ·)
    let deferredId := mkIdent `deferred
    `(command| open $deferredId ($idents*))

def varDeferredTheoremsStx? : TranslateM <| Option Syntax.Command := do
  let thms := (← deferredTheoremNames)
  if thms.isEmpty then
    return none
  else
    let factId := mkIdent `Fact
    let bids ←  thms.mapM fun name =>
      let id := mkIdent <| name ++ `prop
      `(bracketedBinder| [$factId $id:ident])
    `(command| variable $bids* )

def deferredTheoremsHeaderStx : TranslateM <| Array Syntax.Command := do
  let openStx? ← openDeferredTheoremsStx?
  let varStx? ← varDeferredTheoremsStx?
  match openStx?, varStx? with
  | some openStx, some varStx =>
    return #[← `(section), openStx, varStx]
  | _, _ => return #[]

def withDeferredTheorems (x?: TranslateM (Option (TSyntax ``commandSeq))) : TranslateM (Option (TSyntax ``commandSeq)) := do
  let headerStx? ← deferredTheoremsHeaderStx
  match headerStx? with
  | #[] => x?
  | cmds =>
    for cmd in cmds do
      runCommand cmd
    let res? ← x? -- side-effect: the commands are run
    res?.mapM fun res => do
      let resCmds := getCommands res
      runCommand (← `(command| end))
      let fullCmds := cmds ++ resCmds.push (← `(command| end))
      `(commandSeq| $fullCmds*)

end Translate

namespace TranslateM
open Translate
def runWithEmbeddings (em : EmbedMap)
    (x: TranslateM α) : CoreM α := do
  let x :=
    withEmbeddings em do
      -- printKeys
      x
  x.run' {} |>.run'.run'


def runToCore (x: TranslateM α) (em?: Option EmbedMap := none) (outputFile?: Option System.FilePath := none) : CoreM α := do
  match em? with
  | some em => runWithEmbeddings em x
  | none =>
    match outputFile? with
    | some file => do
      IO.FS.writeFile file topCode
      x.run' {outputFile := some file} |>.run'.run'
    | none => x.run' {} |>.run'.run'

section Async
open Std.Internal.IO.Async Async
def runToAsync (x: TranslateM α) (em?: Option EmbedMap)
    (ctx : Core.Context) (env: Environment) : Async α := do
  let core := x.runToCore em?
  let res ← core.run' ctx {env := env} |>.runToIO'
  return res

def runBackground (t₀ : T)(x: T → TranslateM α)   (em?: Option EmbedMap)
    (ctx : Core.Context) (env: Environment) (callback : T →  α → IO Unit)(prio: Task.Priority := Task.Priority.default) : Async Unit :=
  background (prio := prio) do
    let res ← runToAsync (x t₀) em? ctx env
    callback t₀ res


def runBackgroundIO (t₀ : T)(x: T → TranslateM α)  (em?: Option EmbedMap)
    (ctx : Core.Context) (env: Environment)
    (callback : T →  α → IO Unit) (prio: Task.Priority := Task.Priority.default) : IO Unit := do
  AsyncTask.block <| ←
    Async.toIO do
      runBackground t₀ x em? ctx env callback prio
  return ()

partial def runBackgroundChain (t₀ : α)(x: α  → TranslateM α)   (em?: Option EmbedMap)
    (ctx : Core.Context) (env: Environment) (callback : α →  α → Async Unit)(chains : α → α → Array (α → TranslateM α)) (prios: α → Task.Priority := fun _ => Task.Priority.default) : Async Unit :=
  background (prio := prios t₀) do
    let res ← runToAsync (x t₀) em? ctx env
    callback t₀ res
    let offspringTasks := chains t₀ res
    for childTask in offspringTasks do
      runBackgroundChain res childTask em? ctx env callback chains prios

def runBackgroundChainIO (t₀ : α)(x: α  → TranslateM α)   (em?: Option EmbedMap)
    (ctx : Core.Context) (env: Environment) (callback : α →  α → Async Unit)(chains : α → α → Array (α → TranslateM α)) (prios: α → Task.Priority := fun _ => Task.Priority.default) : IO Unit := do
  AsyncTask.block <| ←
    Async.toIO do
      runBackgroundChain t₀ x em? ctx env callback chains prios

end Async
-- {"task" : "echo"}
end TranslateM

open Translate
def timedTest : TranslateM (Nat × Nat × Nat × Json × Json × Json) := do
  let t₀ ← IO.monoMsNow
  let d₁ ← getDescriptionData ``Nat.add_assoc
  let t₁ ← IO.monoMsNow
  let d₂ ← getDescriptionData ``Nat.add_comm
  let t₂ ← IO.monoMsNow
  let d₃ ← getDescriptionData ``Nat.mul_comm
  let t₃ ← IO.monoMsNow
  return (t₁ - t₀, t₂ - t₁, t₃ - t₂, d₁.getD Json.null, d₂.getD Json.null, d₃.getD Json.null)

-- #eval timedTest


structure Translate.SavedState where
  cmdPrelude : Array Syntax.Command
  defs : Array (DefData)
  promptContext : Array String
  context : Option String
  recentTranslations: Array ChatPair
  outputFile : Option System.FilePath

-- TODO(generation-check-homogeneous): This backtracking instance deliberately
-- saves only `Translate.State`; it does not restore the underlying Term/Meta
-- state or metavariable context. Rename/use a more explicit prompt-state scope,
-- and provide two separate contracts: a handler transaction that restores both
-- states when a candidate fails and commits only explicitly allowed state on
-- success, and an always-restore syntax-generation scope for callers that must
-- replay syntax on the original goal. A successful handler may retain allowed
-- Translate effects, while live `MVarId` helpers must commit successful
-- Term/Meta state because their results depend on it.
instance : MonadBacktrack Translate.SavedState TranslateM where
  saveState := fun σ  =>
    let saved : Translate.SavedState := {cmdPrelude := σ.cmdPrelude, defs := σ.defs, promptContext := σ.promptContext, context := σ.context, recentTranslations := σ.recentTranslations, outputFile := σ.outputFile}
    return (saved, σ)
  restoreState := fun ss => do
  modify fun s =>
      {s with cmdPrelude := ss.cmdPrelude, defs := ss.defs, promptContext := ss.promptContext, context := ss.context, recentTranslations := ss.recentTranslations, outputFile := ss.outputFile}

-- TODO(handler-backtracking): This is an always-restore scope and is appropriate
-- for recursive `proofCode` and other computations whose returned syntax/value
-- is independent of both saved states. Do not use it as the generic handler
-- retry transaction: it would discard intentional Translate effects from a
-- successful handler. Add a separate handler transaction that restores both
-- states on exception and defines its success policy explicitly (normally retain
-- allowed Translate effects while restoring speculative Term/Meta state for
-- replayable syntax).
def withoutModifyingTranslateAndTermState
    (x : TranslateM α) : TranslateM α := do
  let translateState ← get
  let termState ← Term.saveState
  try
    x
  finally
    termState.restore
    set translateState

structure CodeElabResult where
  declarations : List Name
  logs : List String
  sorries : List (Name × Expr)
  sorriesAfterPurge : List (Name × Expr)

def getSorriesFromJson (js: Json) : TermElabM (Name × Expr) := do
  let .ok declaration_name := js.getObjValAs? String "declaration_name" | throwError "no 'declaration_name' field"
  let .ok sorryTypeText := js.getObjValAs? String "sorry_type" | throwError "no 'sorry_type' field"
  let .ok stx := Parser.runParserCategory (← getEnv) `term sorryTypeText | throwError s!"could not parse sorry type: {sorryTypeText}"
  let expr ← elabType stx
  return (declaration_name.toName, expr)

def CodeElabResult.fromJson (js: Json) : TermElabM CodeElabResult := do
  let .ok declarations := js.getObjValAs? (List Name) "declarations" | throwError "no 'declarations' field"
  let .ok logs := js.getObjValAs? (List String) "logs" | throwError "no 'logs' field"
  let .ok sorriesJson := js.getObjValAs? (Array Json) "sorries" | throwError "no 'sorries' field"
  let sorries ← sorriesJson.mapM getSorriesFromJson
  let .ok sorriesAfterPurgeJson := js.getObjValAs? (Array Json) "sorries_after_purge" | throwError "no 'sorries_after_purge' field"
  let sorriesAfterPurge ← sorriesAfterPurgeJson.mapM getSorriesFromJson
  return { declarations := declarations, logs := logs, sorries := sorries.toList, sorriesAfterPurge := sorriesAfterPurge.toList }

end LeanAide
