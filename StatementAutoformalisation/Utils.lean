import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension

open Lean Meta Elab Parser Tactic

def Lean.Expr.view (expr : Expr) : MetaM String := do
  let expr ← instantiateMVars expr
  let fmt ← PrettyPrinter.ppExpr expr
  return fmt.pretty

partial def showSyntax : Syntax → String
| Syntax.node _ _ args => 
  (args.map <| fun s => showSyntax s).foldl (fun acc s => acc ++ " " ++ s) ""
| Lean.Syntax.atom _ val => val
| Lean.Syntax.ident _ _ val _ => val.toString
| _ => ""

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

def Array.joinWith (sep : String := " ") : Array String → String
  | ⟨[]⟩ => ""
  | ⟨a::as⟩ => Array.foldl (fun acc x => acc ++ sep ++ x) a ⟨as⟩

-- TODO Check where `Option.elim` is defined and use that instead
def Option.eliminate : Option α → (α → β) → β → β
  | some a, f, _ => f a
  | none, _, b => b

def Lean.Syntax.toString! : Lean.Syntax → String :=
  Option.get! ∘ Syntax.reprint

def Lean.TSyntax.toString! : Lean.TSyntax t → String
  | ⟨stx⟩ => stx.toString!

/-- The `kind` of a `ConstantInfo` term (`axiom`/`def`/`theorem`/...) as a `String`.-/
def Lean.ConstantInfo.kind? : Lean.ConstantInfo → Option String
  | axiomInfo  _ => "axiom"
  | defnInfo   _ => "def"
  | thmInfo    _ => "theorem"
  | opaqueInfo _ => "opaque"
  | quotInfo   _ =>  none
  | inductInfo _ => "inductive"
  | ctorInfo   _ =>  none
  | recInfo    _ => "rec"

def Lean.SMap.toArray [BEq α] [Hashable α] (m : SMap α β) : Array (α × β) :=
  m.fold (init := .empty) fun arr a b => arr.push (a, b)

def Array.partitionM [Monad M] (p : α → M Bool) (as : Array α) : M <| Array α × Array α := do
  let mut bs := #[]
  let mut cs := #[]

  for a in as do
    if ← p a then
      bs := bs.push a
    else
      cs := cs.push a

  return (bs, cs)

def Array.filterMapM' [Monad M] (as :Array α) (f : α → M (Except σ β)) : M (Array β) :=
  as.foldlM (init := #[]) fun bs a => do
    match ← f a with
      | .ok b => return bs.push b
      | .error _ => return bs

def Array.partitionExceptM {α β σ : Type} [Monad M] (p : α → M (Except σ β)) (as : Array α) : M <| Array (α × β) × Array (α × σ) := do
  let mut oks := #[]
  let mut errors := #[]

  for a in as do
    match ← p a with
      | .ok b => oks := oks.push (a, b)
      | .error s => errors := errors.push (a, s)

  return (oks, errors)

initialize
  registerTraceClass `Translate.info
  registerTraceClass `Translate.debug
  registerTraceClass `Translate.warning