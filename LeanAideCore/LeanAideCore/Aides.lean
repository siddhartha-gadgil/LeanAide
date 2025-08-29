import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension
import LeanAideCore.Config
import Std

open Lean Meta Elab Parser Tactic

variable [LeanAideBaseDir]

def Lean.Expr.view (expr: Expr) : MetaM String := do
  let expr ← instantiateMVars expr
  let fmt ← PrettyPrinter.ppExpr expr
  return fmt.pretty

partial def showSyntax : Syntax → String
| Syntax.node _ _ args =>
  (args.map <| fun s => showSyntax s).foldl (fun acc s => acc ++ " " ++ s) ""
| Lean.Syntax.atom _ val => val
| Lean.Syntax.ident _ _ val _ => val.toString
| _ => ""


def leanAidePath : IO System.FilePath := do
  return (← baseDir) / ".lake" /"packages" /"leanaide"

def cachePath : IO System.FilePath := do
  let path : System.FilePath := (← baseDir) /  ".leanaide_cache"
  if ← path.pathExists then
    return path
  else
    return (← leanAidePath) / path

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


namespace Lean.Json

def parseArrIO (s : String) : IO <| Array Json := do
  IO.ofExcept $ Json.parse s >>= Json.getArr?

def parseFile (path : System.FilePath) : IO <| Array Json :=
  IO.FS.readFile path >>= Json.parseArrIO

instance : GetElem Json String Json (λ j k => Except.toBool <| j.getObjVal? k) where
  getElem := λ j key h =>
    match j.getObjVal? key, h with
      | .ok j, _ => j
      | .error _, h => by simp [Except.toBool] at h

instance : GetElem Json Nat Json (λ j n => Except.toBool <| j.getArrVal? n) where
  getElem := λ j n h =>
    match j.getArrVal? n, h with
      | .ok j, _ => j
      | .error _, h => by simp [Except.toBool] at h

def getStr! (j : Json) : String :=
  j.getStr?.toOption.get!

end Lean.Json


def EIO.runToIO' (eio: EIO Exception α) : IO α  := do
  match ←  eio.toIO' with
  | Except.ok x =>
      pure x
  | Except.error e =>
      let msg ← e.toMessageData.toString
      IO.throwServerError msg

open Std.Internal.IO.Async Async in
def EIO.runToAsync (eio: EIO Exception α) : Async α := do
  return ←  eio.runToIO'

def EIO.spawnToIO (eio: EIO Exception α) : IO <| Task <| IO α  := do
  let task ←  eio.asTask (prio := Task.Priority.max)
  return task.map (fun eio =>
    match eio with
    | Except.ok x =>
        pure x
    | Except.error e => do
        let msg ←  e.toMessageData.toString
        IO.throwServerError msg)


-- code from Leo de Moura
def getTactics (s : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match s with
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]

def appendTactics (s t : TSyntax ``tacticSeq) :
  MetaM (TSyntax ``tacticSeq) := do
  let ts := getTactics t
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := t ++ ts
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := t ++ ts
      `(tacticSeq| $[$ts']*)
  | _ => pure t

def appendTactics' (ts : Array (TSyntax `tactic))
    (s : TSyntax ``tacticSeq) :
  MetaM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := ts ++ t
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := ts ++ t
      `(tacticSeq| $[$ts']*)
  | _ => `(tacticSeq| $[$ts]*)

def consTactics (h: TSyntax `tactic)(s : TSyntax ``tacticSeq):
  MetaM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := #[h] ++ t
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := #[h] ++ t
      `(tacticSeq| $[$ts']*)
  | _ => pure s

def endsWithDone (t: TSyntax ``tacticSeq) : MetaM Bool := do
  match getTactics t |>.back? with
  | some t =>
    let fmt ← PrettyPrinter.ppTactic t
    pure <| fmt.pretty.trim.endsWith "done"
  | _ => pure false

def threadNum : IO Nat := do
  try
    let info ←  IO.FS.readFile <| System.mkFilePath ["/", "proc", "cpuinfo"]
    return (info.splitOn "processor" |>.length) - 1
  catch _ =>
    return 4


def jsonLines [ToJson α] (jsl : Array α) : String :=
  let lines := jsl.map (fun j => Json.compress <| toJson j)
  lines.foldl (fun acc l => acc ++ l ++ "\n") ""

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

/-
Obtaining names of constants
-/
-- #check Name.isInternalDetail

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
  else if input.atEnd s.pos then
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
  else if input.atEnd s.pos then
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
            panic! "OPENAI_API_KEY not set"

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
    let head := input.extract 0 s.pos
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

partial def idents : Syntax → List String
| Syntax.ident _ s .. => [s.toString]
| Syntax.node _ _ ss => ss.toList.flatMap idents
| _ => []


def ppExprDetailed (e : Expr): MetaM String := do
  let fmtDetailed ← withOptions (fun o₁ =>
                    let o₂ := pp.motives.all.set o₁ true
                    let o₃ := pp.fieldNotation.set o₂ false
                    let o₄ := pp.proofs.set o₃ true
                    let o₅ := pp.deepTerms.set o₄ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.fullNames.set o₈ true
                    pp.unicode.fun.set o₉ true) do
    ppExpr e
  return fmtDetailed.pretty

instance : Repr Json where
  reprPrec js _ := js.pretty

-- test

elab "detailed" t:term : term => do
  let e ← Term.elabTerm t none
  let fmt ← ppExprDetailed e
  logInfo fmt
  logInfo m!"{← ppExpr e}"
  return e

-- #check detailed (fun (n : Nat) => n + 1)

def delabMatchless (e: Expr) : MetaM Syntax := withOptions (fun o₁ =>
                    -- let o₂ := pp.motives.all.set o₁ true
                    let o₃ := pp.fieldNotation.set o₁ false
                    let o₄ := pp.proofs.set o₃ true
                    let o₅ := pp.deepTerms.set o₄ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.match.set o₈ false
                    let o' := pp.fullNames.set o₉ false
                    pp.unicode.fun.set o' true) do
              PrettyPrinter.delab e

def delabDetailed (e: Expr) : MetaM Syntax.Term := withOptions (fun o₁ =>
                    -- let o₂ := pp.motives.all.set o₁ true
                    let o₃ := pp.fieldNotation.set o₁ false
                    let o₄ := pp.proofs.set o₃ true
                    let o₅ := pp.deepTerms.set o₄ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.coercions.types.set o₈ true
                    let o' := pp.motives.nonConst.set o₉ true
                    let o'' := pp.fullNames.set o' true
                    pp.unicode.fun.set o'' true) do
              PrettyPrinter.delab e


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

open PrettyPrinter in
/--
Definitions and theorems in an expression that are both present in its
syntax tree and are *used constants*. Allows for dot notation.
-/
def defsInExpr (expr: Expr) : MetaM <| Array Name := do
  let typeStx ← delab expr
  let defNames := idents typeStx |>.eraseDups |>.map String.toName
  let defNames := defNames.filter fun name =>
    (excludePrefixes.all fun pre => !pre.isPrefixOf name) &&
    (excludeSuffixes.all fun suff => !suff.isSuffixOf name)
  let tails := defNames.filterMap fun n =>
    n.componentsRev.head?
  let constsInType := expr.getUsedConstants
  let dotNames := constsInType.filter fun n =>
    match n.componentsRev.head? with
    | some t => tails.contains t || defNames.contains n
    | none => false
  return dotNames

def defsInTypeRec (name : Name) (type: Expr) (depth:Nat) :
    MetaM <| Array Name := do
  match depth with
  | 0 => if ← isProp type then return #[] else return #[name]
  | k + 1 =>
    let children ← defsInExpr type
    let childrenTypes ← children.filterMapM fun n => do
      let info ← getConstInfo n
      pure <| some (n, info.type)
    let childValueTypes ← children.filterMapM fun n => do
      let info ← getConstInfo n
      match info with
      | ConstantInfo.defnInfo val => pure <| some (n, val.value)
      | _ => return none
    let res ← (childrenTypes ++ childValueTypes).mapM fun (n, t) => defsInTypeRec n t k
    return res.foldl (· ++ ·) children |>.toList |>.eraseDups |>.toArray

def isDefn (name: Name) : MetaM Bool := do
  let info ←  getConstInfo name
  match info with
  | .defnInfo _ => return true
  | _ => return false

open Elab Term
def defsInTypeString? (name: Name)(typeStr: String) (depth: Nat):
    TermElabM <| Option (Array Name) := do
    let typeStx? := Parser.runParserCategory (← getEnv) `term typeStr
    match typeStx? with
    | .error _ => return none
    | .ok stx =>
      try
        let type ← elabType stx
        defsInTypeRec name type depth
      catch _ =>
        return none


partial def _root_.Lean.Syntax.size (stx: Syntax) : Nat :=
    match stx with
    | Syntax.ident _ _ _ _ => 1
    | Syntax.node _ _ args => args.foldl (fun acc x => acc + x.size) 0
    | _ => 1


def defsInConst (name: Name) (depth: Nat) :
    MetaM <| Array Name := do
  let info ← getConstInfo name
  let base ←  defsInTypeRec name info.type depth
  base.filterM isDefn

def weightedDefsInConsts (names: List Name) (depth: Nat)
  (weight: Float := 1.0) (decay: Float := 0.8) : MetaM (Array (Name × Float)) :=
  match names with
  | [] => return #[]
  | h :: ts => do
    let tailWtdConsts ← weightedDefsInConsts ts depth (weight * decay) decay
    let headConsts ← defsInConst h depth
    let tailConsts := tailWtdConsts.map (fun (x, _) => x)
    let novel := headConsts.filter fun x => !tailConsts.contains x
    let novelWtdConsts :=
      novel.map fun x => (x, weight)
    let unsorted := novelWtdConsts ++ (tailWtdConsts.map fun (x, w) =>
      (x, if headConsts.contains x then w + weight else w))
    return unsorted.qsort fun (_, w₁) (_, w₂) => w₁ > w₂

def bestDefsInConsts (n: Nat) (names: List Name) (depth: Nat)
  (weight: Float := 1.0) (decay: Float := 0.8) : MetaM <| Array Name := do
    let weighted ← weightedDefsInConsts names depth weight decay
    return weighted[0:n] |>.toArray.map fun (n, _) => n

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

/--
Get a key-value pair from a JSON object which is a single key-value pair.
-/
def Lean.Json.getKV? (js : Json) : Option (String × Json) :=
  match js with
  | Json.obj m =>
    match m.toArray with
    | #[⟨k, v⟩] => some (k, v)
    | _ => none
  | _ => none

/--
Get a key-value pair from a JSON object which is a single key-value pair or has a field "type".
-/
def Lean.Json.getKVorType? (js : Json) : Option (String × Json) :=
  match js with
  | Json.obj m =>
    match m.toArray with
    | #[⟨"type", .str key⟩] =>
        (key, json% {})
    | #[⟨k, v⟩] =>
      some (k, v)
    | jsArr =>
      let keys := jsArr.map (fun ⟨k, _⟩ => k)
      let keyVals := jsArr.map (fun ⟨k, v⟩ => (k, v))
      if keys.contains "type" then
        let purged := jsArr.filter (fun ⟨k, _⟩ => k != "type")
        let purged : Array (String × Json) :=
          purged.map fun ⟨k, v⟩ => (k, v)
        let typeVal? := keyVals.findSome? (fun (k, v) => if k == "type" then some v else none)
        match typeVal? with
          | some typeVal =>
            let type? := typeVal.getStr?.toOption
            type?.map fun type =>
              (type, Json.mkObj purged.toList)
          | none => none
      else
        none
  | _ => none


syntax commandSeq := sepBy1IndentSemicolon(command)

def commands : TSyntax `commandSeq → Array (TSyntax `command)
  | `(commandSeq| $cs*) => cs
  | _ => #[]

def toCommandSeq : Array (TSyntax `command) → CoreM (TSyntax `commandSeq)
  | cs => `(commandSeq| $cs*)

def flattenCommands (cs: Array <| TSyntax `commandSeq) :
  CoreM (TSyntax `commandSeq) :=
  toCommandSeq (cs.map commands |>.flatten)

def flattenTactics (tacs: Array <| TSyntax ``tacticSeq) :
  CoreM (TSyntax ``tacticSeq) := do
  let tacs := tacs.map getTactics |>.flatten
  `(tacticSeq| $tacs*)

partial def Lean.Expr.hasUnassignedExprMVar (e: Expr) : MetaM Bool := do
  let deps ← getMVars e
  for m in deps do
    match (← getExprMVarAssignment? m) with
    | some e  =>
      if ←  e.hasUnassignedExprMVar then
        return true
    | none => return true
  return false

-- def checkNoLoop : MetaM Bool := do
--   let mvar ← mkFreshExprMVar (mkConst ``Nat)
--   mvar.hasUnassignedExprMVar

-- #eval checkNoLoop

def getCommandName (stx: TSyntax `command) : Option Name :=
  match stx with
      | `(command| theorem $id:ident $_:declSig $_:declVal) => some id.getId
      | `(command| def $id:ident $_* : $_ := $_) => some id.getId
      | `(command| noncomputable def $id:ident $_* : $_ := $_) => some id.getId
      | _ => none

declare_syntax_cat commandSeqWrap

syntax commandSeq : commandSeqWrap

def getNamesFromCode (s: String) : MetaM (Array Name) := do
  let env ← getEnv
  let res := Parser.runParserCategory env `commandSeqWrap s
  match res with
  | .ok stx =>
    let stx'' := match stx with
      | `(commandSeqWrap| $cs:commandSeq) => cs
      | _ => panic! "Expected commandSeqWrap syntax"
    let stx' : TSyntax `commandSeq := ⟨ stx'' ⟩
    let cmds := commands stx'
    logInfo m!"Parsed commandSeq: {stx}"
    logInfo m!"Commands: {cmds}"
    return cmds.filterMap getCommandName
  | .error err =>
    logError m!"Error parsing commandSeq: {err}"
    return #[]

def parseCommands (s: String) : CoreM (TSyntax ``commandSeq) := do
  let env ← getEnv
  let res := Parser.runParserCategory env `commandSeqWrap s
  match res with
  | .ok stx =>
    match stx with
      | `(commandSeqWrap| $cs:commandSeq) => return cs
      | _ => throwError "Expected commandSeqWrap syntax"
  | .error err =>
    throwError m!"Error parsing commandSeq: {err}"

declare_syntax_cat tacticSeqWrap
syntax tacticSeq : tacticSeqWrap

def parseTactics (s: String) : CoreM <| TSyntax ``tacticSeq := do
  let env ← getEnv
  let res := Parser.runParserCategory env `tacticSeqWrap s
  match res with
  | .ok stx =>
    match stx with
      | `(tacticSeqWrap| $ts:tacticSeq) => return ts
      | _ => throwError "Expected tacticSeqWrap syntax"
  | .error err =>
    logError m!"Error parsing tacticSeq: {err}"
    throwError s!"Failed to parse tacticSeq : {err}"

-- #eval getNamesFromCode "def eg: Nat := 42
-- theorem test : eg = 42 := rfl"

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
