import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension
import LeanAide.Config

open Lean Meta Elab Parser Tactic

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

def leanAidePath : System.FilePath := "lake-packages/leanaide/"

def reroutePath (fp : System.FilePath) : IO System.FilePath := do
  if ← fp.pathExists then
    return fp
  else
    return leanAidePath / fp

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

def getDelabBound : MetaM UInt32 := do
   delab_bound.get

def setDelabBound (n: UInt32) : MetaM Unit := do
   delab_bound.set n

def Lean.MessageData.toCrudeString (msg: MessageData) : String :=
  match msg with
  | .compose l₁ l₂ => l₁.toCrudeString ++ l₂.toCrudeString
  | .nest _ l => l.toCrudeString
  | .withContext _ l => l.toCrudeString
  | .withNamingContext _ l => l.toCrudeString
  | .ofFormat m => s!"{m}"
  | .ofPPFormat _ => "ofPPFormat"
  | .tagged _ l => l.toCrudeString
  | .group l => l.toCrudeString
  | .trace _ s _ _ => s.toCrudeString
  | .ofGoal _ => "ofGoal"

def EIO.runToIO' (eio: EIO Exception α) : IO α  := do
  match ←  eio.toIO' with
  | Except.ok x =>
      pure x
  | Except.error e =>
      let msg ← e.toMessageData.toString
      IO.throwServerError msg

def EIO.spawnToIO (eio: EIO Exception α) : IO <| Task <| IO α  := do
  let task ←  eio.asTask (prio := Task.Priority.max)
  return task.map (fun eio => 
    match eio with
    | Except.ok x =>
        pure x
    | Except.error e => do
        let msg ←  e.toMessageData.toString
        IO.throwServerError msg)
    
def EIO.asyncIO (eio: EIO Exception α) : IO α  := do
  let task ← EIO.spawnToIO eio
  task.get

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

#check Array.append

def threadNum : IO Nat := do
  try
    let info ←  IO.FS.readFile <| System.mkFilePath ["/", "proc", "cpuinfo"]
    return (info.splitOn "processor" |>.length) - 1
  catch _ =>
    return 4

def jsonLines [ToJson α] (jsl : Array α) : String :=
  let lines := jsl.map (fun j => toJson j |>.pretty 10000000) 
      |>.filter (fun l =>  l.length < 9000000)
  lines.foldl (fun acc l => acc ++ "\n" ++ l) ""

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

#check Json.compress

#check Option.mapM

@[inline] protected def Except.mapM [Monad m] (f : α → m β) 
    (o : Except ε α) : m (Except ε β) := do
  match o with
  | Except.ok a => return Except.ok (← f a)
  | Except.error e => return Except.error e

/- 
Obtaining names of constants
-/

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

def excludePrefixes := [`Lean, `Std, `IO, 
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO, `UInt8, ``UInt16, ``UInt32, ``UInt64, `Mathlib.Tactic, `Mathlib.Meta, `LeanAide.Meta, `Aesop]

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

def openAIKey : IO (Option String) := IO.getEnv "OPENAI_API_KEY"

def azureKey : IO (Option String) := IO.getEnv "AZURE_API_KEY"