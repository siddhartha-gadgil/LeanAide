import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension

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

initialize
  registerTraceClass `Translate.info
  registerTraceClass `Translate.debug
  registerTraceClass `Translate.warning
  registerTraceClass `leanaide.proof.info

initialize delab_bound : IO.Ref UInt32 ← IO.mkRef 64

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

def EIO.runToIO (eio: EIO Exception α) : IO α  := do
  eio.toIO (fun e => IO.userError <| s!"Error: {e.toMessageData.toCrudeString}")


