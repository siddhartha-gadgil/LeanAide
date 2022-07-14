import Lean
import Lean.Meta
import Init.System
import Std
open Lean Meta Std Elab

set_option synthInstance.maxHeartbeats 1000000

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
  let bl ← isBlackListed  declName
  return !bl

def excludePrefixes := [`Lean, `Std, `IO, 
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO, `UInt8, ``UInt16, ``UInt32, ``UInt64]

/-- names of global constants -/
def constantNames  : MetaM (Array Name) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, _) => name 
  let names ← allNames.filterM (isWhiteListed)
  let names := names.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
  return names

def constantNamesCore : CoreM (Array Name) := 
  constantNames.run'

/-- names with types of global constants -/
def constantNameTypes  : MetaM (Array (Name ×  Expr)) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, dfn) => (name, dfn.type) 
  let names ← allNames.filterM (fun (name, _) => isWhiteListed name)
  return names

initialize exprRecCache : IO.Ref (HashMap Expr (Array Name)) ← IO.mkRef (HashMap.empty)

def getCached? (e : Expr) : IO (Option (Array Name)) := do
  let cache ← exprRecCache.get
  return cache.find? e

def cache (e: Expr) (offs : Array Name) : IO Unit := do
  let cache ← exprRecCache.get
  exprRecCache.set (cache.insert  e offs)
  return ()

/-- given name, optional expression of definition for the corresponding constant -/
def nameExpr? : Name → MetaM ( Option Expr) := 
  fun name => do
      let info := ((← getEnv).find? name)
      return Option.bind info ConstantInfo.value?

/-- optionally infer type of expression -/
def inferType?(e: Expr) : MetaM (Option Expr) := do
  try
    let type ← inferType e
    return some type
  catch _ => return none

/-- recursively find (whitelisted) names of constants in an expression; -/
partial def recExprNames: Expr → MetaM (Array Name) :=
  fun e =>
  do 
  let fmt ← PrettyPrinter.ppExpr e
  IO.println s!"expr : {fmt.pretty}"
  match ← getCached? e with
  | some offs => return offs
  | none =>
    IO.println "matching"
    let res ← match e with
      | Expr.bvar ..       => return #[]
      | Expr.const name _ _  =>
        do
        if ← (isWhiteListed name) 
          then return #[name] 
          else
          if ← (isNotAux name)  then
            match ←  nameExpr?  name with
            | some e => recExprNames e
            | none => return #[]
          else pure #[]        
      | Expr.app f a _ => 
          do  
            let ftype? ← inferType? f 
            let expl? := 
              ftype?.map $ fun ftype =>
              (ftype.data.binderInfo.isExplicit)
            let expl := expl?.getD true
            let s ←  
              if !expl then 
                match a with
                | Expr.const name _ _  =>
                    do
                    if ← (isWhiteListed name) 
                      then
                        return (← recExprNames f).push name
                      else recExprNames f 
                | _ =>   recExprNames f 
                else return (← recExprNames f) ++ (← recExprNames a)
            return s
      | Expr.lam _ _ b _ => 
          do
            return ← recExprNames b 
      | Expr.forallE _ _ b _ => do
          return  ← recExprNames b 
      | Expr.letE _ _ v b _ => 
            return (← recExprNames b) ++ (← recExprNames v)
      | _ => pure #[]
    cache e res
    return res

/-- names that are offspring of the constant with a given name -/
def offSpring? (name: Name) : MetaM (Option (Array Name)) := do
  let expr? ← nameExpr?  name
  match expr? with
  | some e => 
    return  some <| (← recExprNames e)
  | none => return none

initialize simplifyCache : IO.Ref (HashMap Expr Expr) ← IO.mkRef HashMap.empty

def Lean.Expr.simplify(e: Expr) : MetaM Expr := do 
  try 
  let cache ← simplifyCache.get
  match cache.find? e with
  | none => 
    let r ← simp e (← Simp.Context.mkDefault)
    simplifyCache.set (cache.insert e r.expr)
    return r.expr
  | some expr => return expr
  catch _ => return e

/-- 
Array of constants, names in their definition, and names in their type. 
-/
def offSpringShallowTriple(excludePrefixes: List Name := [])
              : MetaM (Array (Name × (Array Name) × (Array Name) )) :=
  do
  let keys ←  constantNameTypes  
  IO.println s!"Tokens: {keys.size}"
  let goodKeys := keys.filter fun (name, _) =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name))
  IO.println s!"Tokens considered (excluding system code): {goodKeys.size}"
  let kv : Array (Name × (Array Name) × (Array Name)) ←  (goodKeys).mapM $ 
      fun (n, type) => 
          do 
          IO.println s!"Token: {n}"
          let l := (← offSpring? n).getD #[]
          IO.println s!"Offspring: {l.size}"
          let type ← type.simplify
          IO.println "simplified"
          let l := l.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          let tl ←  recExprNames type
          IO.println s!"Type offspring: {tl.size}"
          let tl := tl.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
          -- IO.println s!"Type offspring (excluding system code): {tl.size}"
          return (n, l, tl)
  return kv

  
def offSpringShallowTripleCore: 
    CoreM (Array (Name × (Array Name) × (Array Name) )) := 
          (offSpringShallowTriple excludePrefixes).run' 
