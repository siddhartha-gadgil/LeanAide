import Lean
import Lean.Meta
import Init.System
import LeanAide.Aides
import LeanAide.StatementSyntax
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
  let names := names.filter fun (n, _) => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
  return names

/-- given name, optional expression of definition for the corresponding constant -/
def nameExpr? : Name → MetaM ( Option Expr) :=
  fun name => do
      let info := ((← getEnv).find? name)
      return info >>= ConstantInfo.value?

/-- optionally infer type of expression -/
def inferType?(e: Expr) : MetaM (Option Expr) := do
  try
    let type ← inferType e
    return some type
  catch _ => return none


partial def getSorryTypes (e: Expr) : MetaM (Array Expr) := do
  match e with
  | .app (.const ``sorryAx _) a => return #[a]
  | Expr.app f a  =>
    return (← getSorryTypes f) ++ (← getSorryTypes a)
  | Expr.lam .. =>
    lambdaTelescope e fun xs b => do
      let inner ← getSorryTypes b
      inner.mapM <| mkForallFVars xs
  | Expr.forallE .. =>
    forallTelescope e fun xs b => do
      let inner ← getSorryTypes b
      inner.mapM <| mkForallFVars xs
  | Expr.letE .. =>
      lambdaLetTelescope e fun xs b => do
      let inner ← getSorryTypes b
      inner.mapM <| mkForallFVars xs
  | .proj _ _ s => getSorryTypes s
  | _ => pure #[]

elab "show_sorries" t:term : term => do
  let value ← Term.elabTerm t none
  let value' ← reduce value
  logInfo s!"{← ppExpr value'}"
  let sorries ← getSorryTypes value'
  logInfo s!"{sorries.size} sorries in {← ppExpr value} with types:"
  for s in sorries do
    logInfo s!"{← ppExpr s}"
  return value

elab "show_sorries#" n:ident : term => do
  let env ← getEnv
  let value' :=
    (env.find? n.getId).get!.value!
  -- logInfo s!"{← ppExpr value'}"
  let sorries ← getSorryTypes value'
  logInfo s!"{sorries.size} sorries in {n} with types:"
  for s in sorries do
    logInfo s!"{← ppExpr s}"
  return value'

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def withSorry (n: Nat) : Nat := match n with
  | 0 => by sorry
  | k + 1 => by sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def withSorry' (n m: Nat) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ n ih => sorry


/-- names that are offspring of the constant with a given name -/
def offSpring? (name: Name) : MetaM (Option (Array Name)) := do
  let expr? ← nameExpr?  name
  match expr? with
  | some e =>
    let deps := e.getUsedConstants
    let deps ←  deps.filterM fun n => do
      pure !(← isBlackListed n)
    return  some deps
  | none =>
    IO.eprintln s!"no expr for {name}"
    return none

initialize simplifyCache : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef Std.HashMap.empty

def Lean.Expr.simplify(e: Expr) : MetaM Expr := do
  try
  let cache ← simplifyCache.get
  match cache.get? e with
  | none =>
    let ⟨r, _⟩ ← simp e (← Simp.Context.mkDefault)
    simplifyCache.set (cache.insert e r.expr)
    return r.expr
  | some expr => return expr
  catch _ => return e

def excludeSuffixes := #[`dcasesOn, `recOn, `casesOn, `rawCast, `freeVar, `brec, `brecOn, `rec, `recOn, `cases, `casesOn, `dcases, `below, `ndrec]

-- #eval (`dcasesOn).isSuffixOf (`AlgebraicGeometry.IsAffine.dcasesOn)

/--
Array of constants, names in their definition, and names in their type.
-/
def offSpringShallowTriple(excludePrefixes: List Name := [])
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
      let l := (← offSpring?  n).getD #[]
      let l := l.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf n))
      let tl := type.getUsedConstants
      let tl ← tl.filterM fun n => do
        pure !(← isBlackListed n)
      let tl := tl.filter fun n => !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n))
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


def offSpringShallowTripleCore:
    CoreM Unit :=
          (offSpringShallowTriple excludePrefixes).run'

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


def nameValueDocs (consts: Array Name) : MetaM (Array (Name × Expr ×  Option String)) := do
  let env ← getEnv
  let decls := consts.filterMap <|
    fun name => env.find? name |>.map fun dfn => (name, dfn)
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
    value : Option String
    statement : String
    deriving Repr, ToJson, FromJson

structure ConstructorTypes where
    name: Name
    induc : Name
    type: String
    docString? : Option String
    deriving Repr, ToJson, FromJson

structure InductiveTypes where
    name: Name
    type: String
    docString? : Option String
    deriving Repr, ToJson, FromJson

def propMapFromDefns (dfns : Array DefnTypes) : MetaM <| Std.HashMap Name (String × String) := do
    return Std.HashMap.ofList <|
       dfns.filter (fun d => d.isProp)
        |>.toList.map fun d => (d.name, (d.type, d.statement))


def groups := ["train", "test", "valid"]

def splitData (data: Array α) : IO <| Std.HashMap String (Array α) := do
    let mut img := Std.HashMap.ofList <| groups.map fun g => (g, #[])
    for d in data do
        let group :=  match ← IO.rand 0 9 with
            | 0 => "test"
            | 1 => "valid"
            | _ => "train"
        img := img.insert group <| (img.getD group #[]) ++ #[d]
    return img
namespace DefnTypes
def getM : MetaM <| Array DefnTypes := do
    let cs ← constantNameValueTypes
    IO.println s!"Total: {cs.size}"
    let mut count := 0
    let mut dfns : Array DefnTypes := #[]
    for (name, term, type, doc?) in cs do
        if count % 1000 = 0 then
          IO.println s!"count: {count}"
        count := count + 1
        let depth := type.approxDepth
        unless depth > 60 do
        try
          let fmt ← Meta.ppExpr type
          let isProp ← isProof term
          let v ← ppExpr term
          let value :=
            if isProp
              then none
              else some <| v.pretty
          let typeStx ← PrettyPrinter.delab type
          let valueStx ←  PrettyPrinter.delab term
          let valueStx? := if isProp then none else some valueStx
          let statement ←
            mkStatement (some name) typeStx valueStx? isProp
          dfns := dfns.push
            ⟨name, fmt.pretty, isProp, doc?, value, statement⟩
        catch e =>
          let msg := e.toMessageData
          IO.eprintln s!"Failed to process {name}; error {← msg.toString}"
    return dfns

def writeM (dfns : Array DefnTypes)(name: String := "all.json") : MetaM Unit := do
    let jsonl := dfns.map toJson
    let jsonc := jsonl.map Json.compress
    let path := System.mkFilePath ["rawdata", "defn-types", name]
    if ← path.pathExists then
        IO.FS.writeFile path ""
    let handle ←  IO.FS.Handle.mk path IO.FS.Mode.append
    for l in jsonc do
        handle.putStrLn l

/-- Saving to file and returning for convenience along with map -/
def getWriteSplitM : MetaM <| (Array DefnTypes) × (Std.HashMap Name (String × String)) × Std.HashMap String (Array DefnTypes) := do
    let dfns ← getM
    writeM dfns
    let split ← splitData dfns
    for group in groups do
        let path := System.mkFilePath ["rawdata", "defn-types", group ++ ".jsonl"]
        IO.FS.writeFile path (jsonLines <| split.getD group #[])
    let pm ← propMapFromDefns dfns
    return (dfns, pm, split)

def getWriteSplitCore : CoreM ((Array DefnTypes) × (Std.HashMap Name (String × String)) × Std.HashMap String (Array DefnTypes)) :=
    (getWriteSplitM).run'

def getWriteM : MetaM <| (Array DefnTypes) × (Std.HashMap Name (String × String)) := do
    let dfns ← getM
    writeM dfns
    let pm ← propMapFromDefns dfns
    return (dfns, pm)

def getWriteCore : CoreM ((Array DefnTypes) × (Std.HashMap Name (String × String))) :=
    (getWriteM).run'

def withDoc (dfn: DefnTypes) : String :=
  match dfn.docString? with
  | some doc => s!"/-- {doc} -/\n{dfn.statement}"
  | none => dfn.statement

def thmFromName? (name : Name) : MetaM <| Option DefnTypes := do
  let env ← getEnv
  let doc? ← findDocString? env name
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let fmt ← Meta.ppExpr type
        let isProp := true
        let value := none
        let typeStx ← PrettyPrinter.delab type
        let valueStx? := none
        let statement ←
          mkStatement (some name) typeStx valueStx? isProp
        return some ⟨name, fmt.pretty, isProp, doc?, value, statement⟩
    | _ => return none

def thmFromNameCore? (name : Name) : CoreM <| Option DefnTypes :=
    (thmFromName? name).run'

def defFromName? (name : Name) : MetaM <| Option DefnTypes := do
  let env ← getEnv
  let doc? ← findDocString? env name
  let info? := env.find? name
  match info? with
    | some (.defnInfo dfn) =>
        let term := dfn.value
        let type := dfn.type
        let fmt ← Meta.ppExpr type
        let isProp := false
        let value :=
            some <| (← Meta.ppExpr term).pretty
        let typeStx ← PrettyPrinter.delab type
        let valueStx ←  PrettyPrinter.delab term
        let valueStx? := if isProp then none else some valueStx
        let statement ←
          mkStatement (some name) typeStx valueStx? isProp
        return some ⟨name, fmt.pretty, isProp, doc?, value, statement⟩
    | _ => return none

end DefnTypes

def InductiveTypes.fromName? (name : Name) : MetaM <| Option InductiveTypes := do
  let env ← getEnv
  let doc? ← findDocString? env name
  let info? := env.find? name
  match info? with
    | some (.inductInfo dfn) =>
        let type := dfn.type
        let fmt ← Meta.ppExpr type
        return some ⟨name, fmt.pretty, doc?⟩
    | _ => return none

def ConstructorTypes.fromName? (name : Name) : MetaM <| Option ConstructorTypes := do
  let env ← getEnv
  let doc? ← findDocString? env name
  let info? := env.find? name
  match info? with
    | some (.ctorInfo dfn) =>
        let type := dfn.type
        let fmt ← Meta.ppExpr type
        let ind := dfn.induct
        return some ⟨name, ind, fmt.pretty, doc?⟩
    | _ => return none

def writeDocsM : MetaM <| Json := do
  IO.println "Getting defn types"
  let dfns ← DefnTypes.getM
  IO.println s!"Total: {dfns.size}"
  DefnTypes.writeM dfns
  let dfns := dfns.filter (fun d => d.docString?.isSome)
  IO.println s!"Total: {dfns.size}"
  DefnTypes.writeM dfns "docs.jsonl"
  return Json.arr <| dfns.map toJson

-- #check Json.mergeObj

def writeDocsCore : CoreM <| Json :=
    (writeDocsM).run'

def getPropMap : MetaM <| Std.HashMap Name (String × String) := do
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

def getPropMapStr : MetaM <| Std.HashMap String (String × String) := do
    let mut count := 0
    let mut skipped := 0
    let omittedPath :=
      System.mkFilePath ["CodeGen", "Omitted.lean"]
    IO.FS.writeFile omittedPath ""
    let mut propOmittedHandle ←
      IO.FS.Handle.mk omittedPath IO.FS.Mode.append
    propOmittedHandle.putStrLn "import Mathlib"
    let cs ← constantNameValueTypes
    let mut m : Std.HashMap String (String × String) := Std.HashMap.empty
    let mut dfs : Array DefnTypes := #[]
    for (name, value, type, doc?) in cs do
      if !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && type.approxDepth < 60 then
      try
        let fmt ← ppExpr type
        let isProp ← isProof value
        let v ← ppExpr value
        let value? := if isProp then none else some <| v.pretty
        let typeStx ← PrettyPrinter.delab type
        let valueStx ←  PrettyPrinter.delab value
        let valueStx? := if isProp then none else some valueStx
        let statement ←
            mkStatement (some name) typeStx valueStx? isProp

        let dfn : DefnTypes :=
          ⟨name, fmt.pretty, isProp, doc?, value?, statement⟩
        dfs := dfs.push dfn
        if count % 1000 = 0 then
          IO.println s!"count: {count}"
          IO.println s!"skipped: {skipped}"
        if isProp then
          m := m.insert name.toString.trim (fmt.pretty, statement)
        count := count + 1
      catch e =>
        let msg := e.toMessageData
        IO.eprintln s!"Failed to process {name}; error {← msg.toString}"
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

def propMapCore : CoreM (Std.HashMap String (String × String)) :=
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

end LeanAide.Meta
