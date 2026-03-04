import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension
import LeanAideCore.Config
import Std

open Lean Meta Elab Parser Tactic

variable [LeanAideBaseDir]


-- def five  := 5

-- #eval show% five + 3



-- #eval cachePath

def reroutePath (fp : System.FilePath) : IO System.FilePath := do
  if ← fp.pathExists then
    return fp
  else
    return (← leanAidePath) / fp

def leanToolchain : IO String := do
  let inp ← IO.FS.readFile "lean-toolchain"
  return inp.trim.drop ("leanprover/lean4:".length)

-- #eval leanToolchain



def getDelabBound : MetaM UInt32 := do
   delab_bound.get

def setDelabBound (n: UInt32) : MetaM Unit := do
   delab_bound.set n

def picklePath (descField : String) : IO System.FilePath := do
  let name := if descField == "docString" then "prompts" else descField
  return (← baseDir)/".lake"/ "build" / "lib" /
    s!"mathlib4-{name}-embeddings-{← leanToolchain}.olean"


open System IO.FS
def appendFile (fname : FilePath) (content : String) : IO Unit := do
  let h ← Handle.mk fname Mode.append
  h.putStrLn content
  h.flush

open Std.Time.Timestamp in
def showDate : IO String := now.map (·.toPlainDateAssumingUTC.format "uuuu-MM-dd")


def appendLog (logFile: String) (content : Json) (force: Bool := false) : CoreM Unit := do
  if force then go logFile content
  else
    match (← leanAideLogging?) with
    | some "0" => return ()
    | some _ => go logFile content
    | none => return ()
  where go (logFile: String) (content: Json) : IO Unit := do
    let dir : System.FilePath := (← baseDir) / "leanaide_logs"
    if !(← dir.pathExists) then
      IO.FS.createDirAll dir
    let fname : System.FilePath := dir / (logFile ++ "-" ++ (← showDate) ++ ".jsonl")
    appendFile fname content.compress

def threadNum : IO Nat := do
  try
    let info ←  IO.FS.readFile <| System.mkFilePath ["/", "proc", "cpuinfo"]
    return (info.splitOn "processor" |>.length) - 1
  catch _ =>
    return 4

partial def List.batchesAux (l: List α)(size: Nat)(accum : List (List α)) : List (List α) :=
  match l with
  | [] => accum
  | _ =>
    let batch := l.take size
    let rest := l.drop size
    batchesAux rest size (batch::accum)

def List.batches (l: List α)(size: Nat) : List (List α) :=
  batchesAux l size []

def Array.batches (l: Array α)(size: Nat) : Array (Array α) :=
  (l.toList.batches size).map (fun l => l.toArray) |>.toArray

def List.batches' (l: List α)(numBatches: Nat) : List (List α) :=
  let size :=
    if l.length % numBatches = 0 then
      l.length / numBatches
    else
      l.length / numBatches + 1
  batchesAux l size []

def Array.batches' (l: Array α)(numBatches: Nat) : Array (Array α) :=
  (l.toList.batches' numBatches).map (fun l => l.toArray) |>.toArray

-- #check Json.compress

-- #check Option.mapM

@[inline] protected def Except.mapM [Monad m] (f : α → m β)
    (o : Except ε α) : m (Except ε β) := do
  match o with
  | Except.ok a => return Except.ok (← f a)
  | Except.error e => return Except.error e

def isBlackListed  (declName : Name) : MetaM  Bool := do
  let env ← getEnv
  return (declName.isInternal
  || isAuxRecursor env declName
  || isNoConfusion env declName
  || isRecCore env declName
  || isMatcherCore env declName)

def isAux (declName : Name) : MetaM  Bool := do
  let env ← getEnv
  return (isAuxRecursor env declName
          || isNoConfusion env declName)

def isNotAux  (declName : Name) : MetaM  Bool := do
  let nAux ← isAux declName
  return (not nAux)

def isWhiteListed (declName : Name) : MetaM Bool := do
  try
  let bl ← isBlackListed  declName
  return !bl
  catch _ => return false

def excludePrefixes := [`Lean,  `IO,
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO, `UInt8, ``UInt16, ``UInt32, ``UInt64, `Mathlib.Tactic, `Mathlib.Meta, `LeanAide, `Aesop, `Qq, `Plausible, `LeanSearchClient]


def excludeSuffixes := #[`dcasesOn, `recOn, `casesOn, `rawCast, `freeVar, `brec, `brecOn, `rec, `recOn, `cases, `casesOn, `dcases, `below, `ndrec]

def isMatchCase : Name → Bool
| name =>
  let last? := name.components.reverse.head?
  (last?.getD Name.anonymous).toString.startsWith "match_"

/-- This is a slight modification of `Parser.runParserCategory` due to Scott Morrison/Kim Liesinger. -/
def parseAsTacticSeq (env : Environment) (input : String) (fileName := "<input>") :
    Except String (TSyntax ``tacticSeq) :=
  let p := andthenFn whitespace Tactic.tacticSeq.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if (String.Pos.Raw.atEnd input) s.pos then
    Except.ok ⟨s.stxStack.back⟩
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)


/-- Parsing with a group, for example to extract context -/
def parseGroup (env : Environment) (input : String) (parsers: List Parser) (fileName := "<input>") :
    Except String Syntax :=
  match parsers with
  | [] => Except.error "no parsers"
  | head :: tail =>
  let p := tail.foldl (fun acc p => acc <|> p) head |>.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if (String.Pos.Raw.atEnd input) s.pos then
    Except.ok s.stxStack.back
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

def getName? (stx: Syntax) : Option Name :=
  match stx with
  | `($n:ident) => some n.getId
  | _ => none

def structuralTerm (stx: Syntax) : MetaM Bool := do
  match getName? stx with
  | none => pure false
  | some n =>
    let check := (``Eq).isPrefixOf n || (``Iff).isPrefixOf n
    -- IO.println s!"function with name: {n}; blocked: {check}"
    return check

def openAIKey? : IO (Option String) := IO.getEnv "OPENAI_API_KEY"

def openAIKey : IO String := do
  match ← openAIKey? with
      | some k => return k
      | none =>
          let path : System.FilePath := "private" / "OPENAI_API_KEY"
          if (← path.pathExists) then
            return (← IO.FS.readFile path).trim
          else
          let path : System.FilePath := "rawdata" / "OPENAI_API_KEY"
          if (← path.pathExists) then
            return (← IO.FS.readFile path).trim
          else
            IO.throwServerError "OPENAI_API_KEY not set"

def geminiAPIKey? : IO (Option String) := IO.getEnv "GEMINI_API_KEY"

def geminiAPIKey : IO String := do
  match ← geminiAPIKey? with
      | some k => return k
      | none =>
          let path : System.FilePath := "private" / "GEMINI_API_KEY"
          if (← path.pathExists) then
            return (← IO.FS.readFile path).trim
          else
            panic! "GEMINI_API_KEY not set"


def azureKey : IO (Option String) := IO.getEnv "AZURE_OPENAI_KEY"

def azureEndpoint : IO (Option String) := IO.getEnv "AZURE_OPENAI_ENDPOINT"

def azureURL (deployment: String := "GPT4TestDeployment") : IO String := do
  let endpoint ← azureEndpoint
  match endpoint with
  | none => throw <| IO.userError "AZURE_OPENAI_ENDPOINT not set"
  | some endpoint =>
    return s!"{endpoint}/openai/deployments/{deployment}/chat/completions?api-version=2023-05-15"

def openAIURL : IO String := do
  pure "https://api.openai.com/v1/chat/completions"

def projectID : IO String := do
  let id ← IO.getEnv "PROJECT_ID"
  match id with
  | none => throw <| IO.userError "PROJECT_ID not set"
  | some id => return id



def gitHash : IO String := do
  let hash ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short", "HEAD"] }
  return hash.stdout.trim


def codeBlock (code: String) (s: String) : String :=
  let fullSplit := s.splitOn s!"```{code}"
  let split := if fullSplit.length > 1
    then fullSplit[1]! else
    (s.splitOn "```")[1]!
  (split.splitOn "```")[0]!

def codeBlock? (code: String) (s: String) : Option String := do
  let split ←
    (s.splitOn s!"```{code}")[1]? |>.orElse fun _ =>
      (s.splitOn "```")[1]?
  (split.splitOn "```")[0]?

def extractLean (s: String) : String :=
  codeBlock? "lean" s |>.getD s

def extractJson (s: String) : Json :=
  let code := codeBlock? "json" s |>.getD s
  let code := code.trim
  let code' :=
    code.replace "\n" " " |>.replace "\t" " " |>.replace "\\" "\\\\"
  match Json.parse code' with
  | Except.ok j => j
  | Except.error _ => Json.str code

def partialParser  (parser : Parser) (input : String) (fileName := "<input>") : MetaM <| Except String (Syntax × String × String) := do
  let env ← getEnv
  -- let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let p := andthenFn whitespace parser.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  let stack := s.stxStack.toSubarray.array.filter fun s => !s.hasMissing
  if stack.isEmpty &&  s.hasError then
    return Except.error (s.toErrorMsg ictx)
  else
    let head := (String.Pos.Raw.extract input) 0 s.pos
    let stx := stack.back!
    return Except.ok (stx, head, input.drop head.length)

partial def polyParser (parser: Parser) (input: String) (fileName := "<input>") : MetaM <| Option  Syntax := do
  -- logInfo s!"parsing {input}"
  match (← partialParser parser input fileName) with
  | Except.ok (stx, _, _) =>
    -- logInfo s!"parsed {stx}"
    return some stx
  | Except.error _ =>
    let tail := input.dropWhile (fun c => c != '\n') |>.drop 1 |>.trim
    if tail.isEmpty then
      -- logInfo "no more input; tail empty"
      return none
    else
      return (← polyParser parser tail fileName)

partial def lineBlocks (input: String) : List String :=
  let tail := input.dropWhile (fun c => c != '\n') |>.drop 1
    if tail.isEmpty then
      [input]
    else
      let tailBlocks := lineBlocks tail
      let head := input.takeWhile (fun c => c != '\n')
      head :: (tailBlocks.map (fun b => head ++ "\n" ++ b)) ++ tailBlocks



def termKinds : MetaM <| SyntaxNodeKindSet :=  do
    let env ← getEnv
    let categories := (parserExtension.getState env).categories
    let termCat? := getCategory categories `term
    return termCat?.get!.kinds

def termKindList : MetaM <| List SyntaxNodeKind := do
    let s ← termKinds
    pure <| s.toList.map (·.1)

-- #check String.dropWhile

-- #check '\n'

abbrev EmbedData := Array <| (String × String × Bool × String) ×  FloatArray

abbrev EmbedMap := Std.HashMap String EmbedData

def freshDataHandle (fileNamePieces : List String)(clean: Bool := true) : IO IO.FS.Handle := do
    let path := System.mkFilePath <| [".", "rawdata"] ++ fileNamePieces
    let dir := System.mkFilePath <| [".", "rawdata"] ++
        fileNamePieces.take (fileNamePieces.length - 1)
    if !(← dir.pathExists) then
        IO.FS.createDirAll dir
    if clean then
        IO.eprintln s!"cleaning {path}"
        IO.FS.writeFile path ""
    else IO.eprintln s!"{path} already exists, adding to it"
    IO.FS.Handle.mk path IO.FS.Mode.append

def relLCtxAux (goal: Expr) (decls: List LocalDecl) : MetaM Expr := do
  match decls with
  | [] => return goal
  | (.ldecl _ _ name type value _ kind) :: tail =>
    withLetDecl name type value (kind := kind) fun x => do
      let inner ← relLCtxAux (goal.instantiate1 x) tail
      mkLetFVars #[x] inner
  | (.cdecl _ _ name type bi kind) :: tail =>
    logInfo m!"decl: {name}"
    withLocalDecl name bi type (kind := kind) fun x => do
      let inner ← relLCtxAux goal tail
      let inner := inner.instantiate1 x
      mkForallFVars #[x] inner


def relLCtx (mvarId : MVarId) : MetaM Expr :=
  mvarId.withContext do
    let decls := (← getLCtx).decls.toArray |>.filterMap id
    let decls := decls.filter fun decl =>
      !decl.isImplementationDetail
    relLCtxAux (← mvarId.getType) decls.toList

def relLCtx' (mvarId : MVarId) : MetaM Expr :=
  mvarId.withContext do
    let decls := (← getLCtx).decls.toArray |>.filterMap id
    relLCtxAux (← mvarId.getType) decls.toList

def groups := ["train", "test", "valid"]

def splitData (data: Array α) : IO <| Std.HashMap String (Array α) := do
    let mut img := Std.HashMap.ofList <| groups.map fun g => (g, #[])
    let mut count := 0
    for d in data do
        let group :=  match ← IO.rand 0 9 with
            | 0 => "test"
            | 1 => "valid"
            | _ => "train"
        img := img.insert group <| (img.getD group #[]).push d
        count := count + 1
        if count % 1000 = 0 then
            IO.println s!"split count: {count}"
    return img

partial def shrink (s: String) : String :=
    let step := s.replace "  " " " |>.replace "( " "("
                |>.replace " )" ")"
                |>.replace "{ " "{"
                |>.replace " }" "}"
                |>.replace "[ " "["
                |>.replace " ]" "]"
                |>.trim
    if step == s then s else shrink step


def runTacticToCore (mvarId: MVarId) (stx: Syntax)
    (ctx: Term.Context) (s : Term.State) (mctx : Meta.Context) (s' : Meta.State) : CoreM <| (List MVarId × Term.State) × Meta.State  :=
  MetaM.run (
    Elab.runTactic mvarId stx  {ctx with mayPostpone := false, errToSorry := false, declName? := some `_tacticCode} s) mctx s'

def evalTacticSafe (tacticCode: Syntax): TacticM (Bool × Nat) := do
  let mvarId ← getMainGoal
  let ctx ← readThe Term.Context
  let s ← getThe Term.State
  let mctx ← readThe Meta.Context
  let s' ← getThe Meta.State
  let state ← saveState
  let res ← Core.tryCatchRuntimeEx (do
      let res ← runTacticToCore mvarId tacticCode ctx s mctx s'
      pure <| Except.ok res
      ) (fun e => pure <| Except.error e)
  match res with
  | Except.ok ((mvarIds, s), ms) => do
    set ms
    set s
    replaceMainGoal mvarIds
    return (true, mvarIds.length)
  | Except.error e =>
    state.restore
    logWarning e.toMessageData
    return (false, 1)

def checkTacticSafe (mvarId: MVarId)(tacticCode: Syntax):
    TermElabM Bool := withoutModifyingState do
  let ctx ← readThe Term.Context
  let s ← getThe Term.State
  let mctx ← readThe Meta.Context
  let s' ← getThe Meta.State
  let state ← saveState
  let res ← Core.tryCatchRuntimeEx (do
      let res ← runTacticToCore mvarId tacticCode ctx s mctx s'
      pure <| Except.ok res
      ) (fun e => pure <| Except.error e)
  match res with
  | Except.ok ((mvarIds, s), ms) => do
    set ms
    set s
    return mvarIds.isEmpty
  | Except.error e =>
    state.restore
    logWarning e.toMessageData
    return false

-- from batteries
def List.scanl' (f : α → β → α) (a : α) : List β → List α
  | [] => [a]
  | b :: l => a :: scanl' f (f a b) l

def colEqSegments (s: String) : List String :=
  let pieces := s.splitOn ":="
  match pieces with
  | [] => []
  | head :: tail =>
    tail.scanl' (fun acc x => acc ++ ":=" ++ x) head |>.map (String.trim)

def splitColEqSegments (ss: Array String) : Array String :=
  ss.toList.flatMap colEqSegments |>.toArray

def trivialEquality : Syntax → CoreM Bool
  | `($a = $b) => return a == b
  | _ => return false


def checkName (name: Name) : CoreM Bool := do
    let l ← resolveGlobalName name
    return l.length > 0

def newName (base: Name) : CoreM Name := do
  let mut idx := 1
  let mut newName := base
  while (← checkName newName) do
    idx := idx + 1
    newName := Name.mkStr base s!"_{idx}"
  return newName

def extractJsonM (s: String) : CoreM Json :=
  let code := codeBlock? "json" s |>.getD s
  let code := code.trim
  match Json.parse code with
  | Except.ok j => do
    -- logInfo s!"parsed JSON: {j}"
    appendLog "json_parsed" j
    return j
  | Except.error e => do
    logWarning  m!"Error parsing JSON: {e}"
    appendLog "json_error" (Json.str code)
    appendLog "json_error" (Json.str e)
    return Json.str code


partial def identNames : Syntax → MetaM (List Name)
| Syntax.ident _ _ s .. => do
  if (← isWhiteListed s) &&
    !(excludeSuffixes.any fun sfx => sfx.isSuffixOf s) && !(excludePrefixes.any fun pfx => pfx.isPrefixOf s)
    then return [s] else return []
| Syntax.node _ _ ss => do
    let groups ← ss.toList.mapM identNames
    return groups.flatten.eraseDups
| _ => return []

namespace LeanAide

open Elab Term

elab "s%" s:term : term => do
  let t ← elabTerm s (mkConst ``String)
  let str ← unsafe evalExpr String (mkConst ``String) t
  let istr := s!"s!\"{str}\""
  logInfo m!"{istr}"
  let .ok stx := Parser.runParserCategory (← getEnv) `term istr
    | throwError "failed to parse {istr}"
  let res ← withoutErrToSorry do
    elabTerm stx (mkConst ``String)
  return res

class Proxy (α : Type) (β : outParam Type)[ToJson β][Repr β]  where
  toJsonInst : ToJson β := by apply inferInstance
  to : α → TermElabM β
  of : β → TermElabM α

-- Probably not needed (from before changes in `Proxy`), but keeping for now just in case.
class InverseProxy (β  : Type)  where
  α  : Type
  of : β → TermElabM α
  to : α → TermElabM β

def proxy {α β : Type}[ToJson β][Repr β][inst: Proxy α β] (a : α) : TermElabM β :=
  inst.to a

def unproxy {α β : Type} [ToJson β][Repr β]  [inst : Proxy α β] (b : β) : TermElabM α :=
  inst.of b

def proxyJson {α β : Type}[ToJson β][Repr β] [inst: Proxy α β] (a : α) : TermElabM Json := do
  let b   ← proxy a
  let _ : ToJson β := inst.toJsonInst
  return toJson b

def unproxyJson {α β : Type} [FromJson β][ToJson β][Repr β] [inst: Proxy α β] (j: Json) : TermElabM α := do
  let .ok (b : β) := fromJson? j | throwError s!"failed to parse {j}"
  unproxy b

class ReprM (α : Type u) where
  reprPrecM : α → Nat → TermElabM Format

instance {α : Type u}[Repr α] : ReprM α  where
  reprPrecM n x := return reprPrec n x

instance {α β : Type}[ToJson β][Repr β] [Proxy α β] : ReprM α where
  reprPrecM a x := do
    let b ← proxy a
    return reprPrec b x

def reprM {α : Type u}[ReprM α] (x : α) : TermElabM String := do
  let f ← ReprM.reprPrecM x 0
  return f.pretty

def reprPrecM {α : Type u}[ReprM α] (x : α) (prec : Nat) : TermElabM String := do
  let f ← ReprM.reprPrecM x prec
  return f.pretty

def showM {α : Type u}[ReprM α] (x : α) : TermElabM Format := do
  reprM x

macro "#aide_eval" t:term : command => do
  `(command| #eval showM ($t))

instance {α : Type}[ReprM α] : ReprM (TermElabM α) where
  reprPrecM x n := do
    let y ← x
    reprPrecM y n


-- #aide_eval 3

instance optProxy {α β : Type}[ToJson β][Repr β] [inst : Proxy α β]  : Proxy (Option α) (Option β) where
  toJsonInst := by apply inferInstance
  to
    | none => pure none
    | some a => do return some <| ←  inst.to a
  of
    | none => pure none
    | some b => do return some <| ←  inst.of b

def pythonPath : IO String := do
  let topFiles ←  ("." : FilePath).readDir
  let mut secondDirs : List FilePath := []
  for f in topFiles do -- includes venv
    if ← f.path.isDir then
      let subFiles ← f.path.readDir -- includes venv/bin
      for sf in subFiles do
        if ← sf.path.isDir then
          secondDirs := sf.path :: secondDirs
  let bins := secondDirs.filterMap fun f =>
    if f.fileName = some "bin" then
      pure f
    else
      none
  for bin in bins do
    let pyPath := bin / "python3"
    if (← pyPath.pathExists) then
      return pyPath.toString
    let files ← bin.readDir
    for f in files do
      if let some fname := f.path.fileName then
        if fname.startsWith "python" then
          return f.path.toString
  return "python3"

-- #eval pythonPath

end LeanAide
