import Lean
import LeanAideCore.Aides
import LeanAideCore.SimpleFrontend
import LeanAideCore.DefData
import LeanAideCore.PromptExampleBuilder
import LeanAideCore.ChatClient

open Lean Meta Elab Term
namespace LeanAide
variable [LeanAideBaseDir]

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
  /-- Whether the theorem is proved-/
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
  preludes : Array String := #[]
  varPreludes : Array String := #[]
  errorLog : Array ElabErrorData := #[]
  context : Option String := none
  labelledTheorems : Array LabelledTheorem := #[]
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
  IO.eprintln s!"Loaded embeddings: {em.toList.map Prod.fst}"

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
  if (← ((← resourcesDir) / "mathlib4-prompts.jsonl").pathExists) then
    uploadDesciptions <| (← resourcesDir) / "mathlib4-prompts.jsonl"
  else
     let _ ← IO.Process.output {cmd:= "curl", args := #["--output", ((← resourcesDir) / "mathlib4-prompts.jsonl").toString, "https://storage.googleapis.com/leanaide_data/mathlib4-prompts.jsonl"]}
     uploadDesciptions <| (← resourcesDir) / "mathlib4-prompts.jsonl"

  if (← ((← resourcesDir) / "mathlib4-descs.jsonl").pathExists) then
    uploadDesciptions <| (← resourcesDir) / "mathlib4-descs.jsonl"
  else
     let _ ← IO.Process.output {cmd:= "curl", args := #["--output", ((← resourcesDir) / "mathlib4-descs.jsonl").toString, "https://storage.googleapis.com/leanaide_data/mathlib4-descs.jsonl"]}
     uploadDesciptions <| (← resourcesDir) / "mathlib4-descs.jsonl"

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

def runCommand (cmd: Syntax.Command) : TranslateM Unit := do
  discard <|  runFrontendM (← ppCommand cmd).pretty true
  modify fun s  => {s with cmdPrelude := s.cmdPrelude.push cmd}

def addCommand (cmd: Syntax.Command) : TranslateM Unit := do
  modify fun s  => {s with cmdPrelude := s.cmdPrelude.push cmd}

def addCommands (cmds: TSyntax ``commandSeq) : TranslateM Unit := do
  let cmds := getCommands cmds
  modify fun s => {s with cmdPrelude := s.cmdPrelude ++ cmds}

def addDefn (dfn: DefData) : TranslateM Unit := do
  runCommand <| ← dfn.statementStx
  modify fun s => {s with defs := s.defs.push dfn}

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

def addPrelude (p: String) : TranslateM Unit := do
  modify fun s =>
    if s.preludes.contains p then
      s
    else
      -- IO.eprintln s!"Adding prelude: {p}"
    {s with preludes := s.preludes.push p}

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
  modify fun s => {s with preludes := #[]}

def preludesBlob : TranslateM <| Array String := do
  let preludes := (← get).preludes
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


def runToCore (x: TranslateM α) (em?: Option EmbedMap := none) : CoreM α := do
  match em? with
  | some em => runWithEmbeddings em x
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
    (ctx : Core.Context) (env: Environment) (callback : α →  α → IO Unit)(chains : α → α → Array (α → TranslateM α)) (prios: α → Task.Priority := fun _ => Task.Priority.default) : Async Unit :=
  background (prio := prios t₀) do
    let res ← runToAsync (x t₀) em? ctx env
    callback t₀ res
    let offspringTasks := chains t₀ res
    for childTask in offspringTasks do
      runBackgroundChain res childTask em? ctx env callback chains prios

def runBackgroundChainIO (t₀ : α)(x: α  → TranslateM α)   (em?: Option EmbedMap)
    (ctx : Core.Context) (env: Environment) (callback : α →  α → IO Unit)(chains : α → α → Array (α → TranslateM α)) (prios: α → Task.Priority := fun _ => Task.Priority.default) : IO Unit := do
  AsyncTask.block <| ←
    Async.toIO do
      runBackgroundChain t₀ x em? ctx env callback chains prios
  return ()

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
  cmdPrelude : Array Syntax.Command := #[]
  defs : Array (DefData) := #[]
  preludes : Array String := #[]
  context : Option String := none

instance : MonadBacktrack Translate.SavedState TranslateM where
  saveState := fun σ  =>
    let saved : Translate.SavedState := {cmdPrelude := σ.cmdPrelude, defs := σ.defs, preludes := σ.preludes, context := σ.context}
    return (saved, σ)
  restoreState := fun ss => do
  modify fun s =>
      {s with cmdPrelude := ss.cmdPrelude, defs := ss.defs, preludes := ss.preludes, context := ss.context}


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
