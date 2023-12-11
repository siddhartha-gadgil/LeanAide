import Lean
import Lean.Meta
import Init.System
import LeanAide.Aides
open Lean Meta Elab

set_option synthInstance.maxHeartbeats 1000000

namespace LeanAide.Meta


/-- names of global constants -/
def constantNames  : MetaM (Array Name) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, _) => name
  let names ← allNames.filterM (isWhiteListed)
  let names := names.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
  return names

def constantNamesCore  : CoreM (Array Name) :=
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
partial def recExprNames (depth: Nat): Expr → MetaM (Array Name) :=
  fun e =>
  do
  match depth with
  | 0 => return #[]
  | k + 1 =>
  -- let fmt ← PrettyPrinter.ppExpr e
  -- IO.println s!"expr : {e}"
  match ← getCached? e with
  | some offs => return offs
  | none =>
    -- IO.println "matching"
    let res ← match e with
      | Expr.bvar ..       => return #[]
      | Expr.fvar ..       => return #[]
      | Expr.const name ..  =>
        do
        if ← (isWhiteListed name)
          then return #[name]
          else
          if ← (isNotAux name)  then
            match ←  nameExpr?  name with
            | some e => recExprNames k e
            | none => return #[]
          else pure #[]
      | Expr.app f a .. =>
          do
            -- IO.println "app"
            let ftype? ← inferType? f
            -- IO.println "got ftype"
            let expl? :=
              ftype?.map $ fun ftype =>
              (ftype.binderInfo.isExplicit)
            let expl := expl?.getD true
            -- IO.println s!"got expl: {expl}"
            let s ←
              if !expl then
                -- IO.println a
                match a with
                | Expr.const name ..  =>
                    do
                    if ← (isWhiteListed name)
                      then
                        return (← recExprNames k f).push name
                      else recExprNames k f
                | _ =>
                  -- IO.println s!"using only f: {f}"
                  recExprNames k f
                else return (← recExprNames k f) ++ (← recExprNames k a)
            return s
      | Expr.lam _ _ b _ =>
          do
            -- IO.println s!"lam; body: {b}"
            return ← recExprNames k b
      | Expr.forallE _ _ b _ => do
          return  ← recExprNames k b
      | Expr.letE _ _ v b _ =>
            return (← recExprNames k b) ++ (← recExprNames k v)
      | _ => pure #[]
    cache e res
    return res

/-- names that are offspring of the constant with a given name -/
def offSpring? (depth: Nat)(name: Name) : MetaM (Option (Array Name)) := do
  let expr? ← nameExpr?  name
  match expr? with
  | some e =>
    return  some <| (← recExprNames depth e)
  | none =>
    IO.println s!"no expr for {name}"
    return none

initialize simplifyCache : IO.Ref (HashMap Expr Expr) ← IO.mkRef HashMap.empty

def Lean.Expr.simplify(e: Expr) : MetaM Expr := do
  try
  let cache ← simplifyCache.get
  match cache.find? e with
  | none =>
    let ⟨r, _⟩ ← simp e (← Simp.Context.mkDefault)
    simplifyCache.set (cache.insert e r.expr)
    return r.expr
  | some expr => return expr
  catch _ => return e

def excludeSuffixes := #[`dcasesOn, `recOn, `casesOn, `rawCast, `freeVar]

-- #eval (`dcasesOn).isSuffixOf (`AlgebraicGeometry.IsAffine.dcasesOn)

/--
Array of constants, names in their definition, and names in their type.
-/
def offSpringShallowTriple(excludePrefixes: List Name := [])(depth: Nat)
              : MetaM (Unit) :=
  do
  let keys ←  constantNameTypes
  IO.println s!"Tokens: {keys.size}"
  let goodKeys := keys.filter fun (name, _) =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name))
  IO.println s!"Tokens considered (excluding system code): {goodKeys.size}"
  let depsFile := System.mkFilePath ["rawdata", "deps.yaml"]
  let h ← IO.FS.Handle.mk depsFile IO.FS.Mode.append
  let mut count := 0
  for (n, type) in  (goodKeys) do
      let l := (← offSpring? depth n).getD #[]
      -- let type ← type.simplify
      -- IO.println "simplified"
      let l := l.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf n))
      -- IO.println s!"Computing offspring for {type}"
      let tl ←  recExprNames depth type
      let tl := tl.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
      -- IO.println s!"Type offspring (excluding system code): {tl.size}"
      h.putStrLn s!"- name: {n}"
      h.putStrLn <| s!"  defn: " ++ ((s!"{l}").drop 1)
      h.putStrLn <| s!"  type: " ++ ((s!"{tl}").drop 1)
      h.putStrLn ""
      count := count + 1
      if count % 1000 = 0 then
        IO.println s!"Token: {n}"
        IO.println s!"Offspring: {l.size}"
        IO.println s!"Type offspring: {tl.size}"
        IO.println s!"Completed: {count} (out of {goodKeys.size})"
  return ()


def offSpringShallowTripleCore (depth: Nat):
    CoreM Unit :=
          (offSpringShallowTriple excludePrefixes depth).run'

/-- All constants in the environment with value and type. -/
def constantNameValueTypes  : MetaM (Array (Name × Expr ×   Expr × Option String)) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNamesCore := decls.filterMap <|
    fun (name, dfn) => dfn.value? |>.map fun t => (name, t, dfn.type)
  let allNames ← allNamesCore.mapM <|
    fun (name, value, type) => do
      pure <| (name, value, type, ← findDocString? env name )
  let names ← allNames.filterM (fun (name, _) => isWhiteListed name)
  let names := names.filter <|
    fun (name, _, _)  ↦ !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name))
  return names

def constantNameValueDocs  : MetaM (Array (Name × Expr ×  Option String)) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNamesCore := decls.map <|
    fun (name, dfn) => (name, dfn.type)
  let allNames ← allNamesCore.mapM <|
    fun (name,  type) => do
      pure <| (name,  type, ← findDocString? env name )
  let names ← allNames.filterM (fun (name, _) => isWhiteListed name)
  let names := names.filter <|
    fun (name, _, _)  ↦ !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name))
  return names

structure DefnTypes where
    name: Name
    type: String
    isProp : Bool
    docString? : Option String
    deriving Repr, ToJson, FromJson

def propMapFromDefns (dfns : Array DefnTypes) : MetaM <| HashMap Name String := do
    return HashMap.ofList <|
       dfns.filter (fun d => d.isProp)
        |>.toList.map fun d => (d.name, d.type)

def propMapFromDefnsStr (dfns : Array DefnTypes) : MetaM <| HashMap String String := do
    return HashMap.ofList <|
       dfns.filter (fun d => d.isProp)
        |>.toList.map fun d => (d.name.toString.trim, d.type)

def groups := ["train", "test", "valid"]

def splitData (data: Array α) : IO <| HashMap String (Array α) := do
    let mut img := HashMap.ofList <| groups.map fun g => (g, #[])
    for d in data do
        let group :=  match ← IO.rand 0 9 with
            | 0 => "test"
            | 1 => "valid"
            | _ => "train"
        img := img.insert group <| (img.findD group #[]) ++ #[d]
    return img
namespace DefnTypes
def getM : MetaM <| Array DefnTypes := do
    let cs ← constantNameValueTypes
    cs.filterMapM <| fun (name, term, type, doc?) => do
        let depth := type.approxDepth
        if depth > 60 then
          return none
        else
          let fmt ← Meta.ppExpr type
          pure
            (some ⟨name, fmt.pretty, ← isProof term, doc?⟩)

def writeM (dfns : Array DefnTypes)(name: String := "all.json") : MetaM Unit := do
    let jsonl := dfns.map toJson
    let jsonc := jsonl.map Json.compress
    let path := System.mkFilePath ["rawdata", "defn-types", name]
    let handle ←  IO.FS.Handle.mk path IO.FS.Mode.append
    for l in jsonc do
        handle.putStrLn l

/-- Saving to file and returning for convenience along with map -/
def getWriteSplitM : MetaM <| (Array DefnTypes) × (HashMap Name String) × HashMap String (Array DefnTypes) := do
    let dfns ← getM
    writeM dfns
    let split ← splitData dfns
    for group in groups do
        let path := System.mkFilePath ["rawdata", "defn-types", group ++ ".jsonl"]
        IO.FS.writeFile path (jsonLines <| split.findD group #[])
    let pm ← propMapFromDefns dfns
    return (dfns, pm, split)

def getWriteSplitCore : CoreM ((Array DefnTypes) × (HashMap Name String) × HashMap String (Array DefnTypes)) :=
    (getWriteSplitM).run'

def getWriteM : MetaM <| (Array DefnTypes) × (HashMap Name String) := do
    let dfns ← getM
    writeM dfns
    let pm ← propMapFromDefns dfns
    return (dfns, pm)

def getWriteCore : CoreM ((Array DefnTypes) × (HashMap Name String)) :=
    (getWriteM).run'

end DefnTypes

def writeDocsM : MetaM Unit := do
  let dfns ← DefnTypes.getM
  IO.println s!"Total: {dfns.size}"
  let dfns := dfns.filter (fun d => d.docString?.isSome)
  IO.println s!"Total: {dfns.size}"
  DefnTypes.writeM dfns "docs.jsonl"

def writeDocsCore : CoreM Unit :=
    (writeDocsM).run'

def getPropMap : MetaM <| HashMap Name String := do
    let dfns ← DefnTypes.getM
    propMapFromDefns dfns

partial def shrink (s: String) : String :=
    let step := s.replace "  " " " |>.replace "( " "("
                |>.replace " )" ")"
                |>.replace "{ " "{"
                |>.replace " }" "}"
                |>.replace "[ " "["
                |>.replace " ]" "]"
                |>.trim
    if step == s then s else shrink step

def getPropMapStr : MetaM <| HashMap String String := do
    let mut count := 0
    let mut skipped := 0
    let omittedPath :=
      System.mkFilePath ["CodeGen", "Omitted.lean"]
    IO.FS.writeFile omittedPath ""
    let mut propOmittedHandle ←
      IO.FS.Handle.mk omittedPath IO.FS.Mode.append
    propOmittedHandle.putStrLn "import Mathlib"
    let cs ← constantNameValueTypes
    let mut m : HashMap String String := HashMap.empty
    let mut dfs : Array DefnTypes := #[]
    for (name, value, type, doc?) in cs do
      if !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && type.approxDepth < 60 then
        let fmt ← ppExpr type
        let isProp ← isProof value
        let dfn : DefnTypes := ⟨name, fmt.pretty, isProp, doc?⟩
        dfs := dfs.push dfn
        if count % 1000 = 0 then
          IO.println s!"count: {count}"
          IO.println s!"skipped: {skipped}"
        if isProp then
          m := m.insert name.toString.trim fmt.pretty
        count := count + 1
      else
        if type.approxDepth >= 60 then
          skipped := skipped + 1
          propOmittedHandle.putStrLn s!"#check {name}"
          if skipped % 100 = 0 then
            let omittedPath :=
              System.mkFilePath ["CodeGen", s!"Omitted{skipped/100}.lean"]
            IO.FS.writeFile omittedPath ""
            propOmittedHandle ←
              IO.FS.Handle.mk omittedPath IO.FS.Mode.append
            propOmittedHandle.putStrLn "import Mathlib"

    let path := System.mkFilePath ["rawdata", "defn-types", "all.jsonl"]
    IO.FS.writeFile path <| jsonLines <| dfs
    return m

def propMapCore : CoreM (HashMap String String) :=
    (getPropMapStr).run'

def nameViewM? (name: Name) : MetaM <| Option String := do
  let exp? ←  nameExpr? name
  let fmt ← match exp? with
    | some exp => do
      let fmt ← ppExpr exp
      pure <| some <| shrink fmt.pretty
    | none => pure name.toString
  return fmt

def nameViewCore? (name: Name) : CoreM <| Option String :=
    (nameViewM? name).run'

end LeanAide.Meta
