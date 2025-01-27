import Lean
import Lean.Meta
import Init.System
import LeanAide.Aides
import LeanAide.StatementSyntax
import LeanAide.DefData
open Lean Meta Elab

set_option synthInstance.maxHeartbeats 1000000

namespace LeanAide.Meta


/-- names of global constants -/
def constantNames  : MetaM (Array Name) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.map $ fun (name, _) => name
  let names ← allNames.filterM (isWhiteListed)
  let names ←  names.filterM fun n => do pure <|
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf n)) && (← isWhiteListed n) && !(isMatchCase n)
  return names

def constantNamesCore  : CoreM (Array Name) :=
  constantNames.run'

def propNames : MetaM (Array Name) := do
  (← constantNames).filterM fun name => do
    let info? := ((← getEnv).find? name)
    let value? := info? >>= ConstantInfo.value?
    let check? ← value?.mapM isProof
    return check?.getD false

def propNamesCore : CoreM (Array Name) :=
  propNames.run'

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
  | Expr.lam name type body bi =>
    withLocalDecl name bi type fun x => do
      let body := body.instantiate1 x
      let inner ← getSorryTypes body
      inner.mapM <| mkForallFVars #[x]
  | Expr.letE name type value bdy nondep =>
      withLetDecl name type value fun x => do
        let bdy := bdy.instantiate1 x
        let inner ← getSorryTypes bdy
        inner.mapM <| fun type => do
          let y ←  mkLetFVars #[x] type
          pure <| .letE name type value y nondep
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

def propMapFromDefns (dfns : Array DefDataRepr) : MetaM <| Std.HashMap Name (String × String) := do
    return Std.HashMap.ofList <|
       dfns.filter (fun d => d.isProp)
        |>.toList.map fun d => (d.name, (d.type, d.statement))

namespace DefDataRepr
def getM : MetaM <| Array DefDataRepr := do
    let cs ← constantNameValueTypes
    IO.println s!"Total: {cs.size}"
    let mut count := 0
    let mut dfns : Array DefDataRepr := #[]
    for (name, value, type, doc?) in cs do
        if count % 1000 = 0 then
          IO.println s!"count: {count}"
        count := count + 1
        let depth := type.approxDepth
        unless depth > 60 do
        try
          let typeFmt ← Meta.ppExpr type
          let isProp ← isProof value
          let valueStr ←  do
            if isProp
              then pure none
              else
                pure <| some <| (← ppExpr value).pretty
          let typeStx ← PrettyPrinter.delab type
          let valueStx? ←
            if isProp then pure none
              else pure <| some (←  PrettyPrinter.delab value)
          let isNoncomputable := Lean.isNoncomputable (← getEnv) name
          let statement ←
            mkStatement (some name) typeStx valueStx? isProp (isNoncomputable := isNoncomputable)
          dfns := dfns.push
            ⟨name, typeFmt.pretty, isProp, isNoncomputable, doc?, valueStr, statement⟩
        catch e =>
          let msg := e.toMessageData
          IO.eprintln s!"Failed to process {name}; error {← msg.toString}"
    return dfns

def writeM (dfns : Array DefDataRepr)(name: String := "all.json") : MetaM Unit := do
    let jsonl := dfns.map toJson
    let jsonc := jsonl.map Json.compress
    let path := System.mkFilePath ["rawdata", "defn-types", name]
    if ← path.pathExists then
        IO.FS.writeFile path ""
    let handle ←  IO.FS.Handle.mk path IO.FS.Mode.append
    for l in jsonc do
        handle.putStrLn l

/-- Saving to file and returning for convenience along with map -/
def getWriteSplitM : MetaM <| (Array DefDataRepr) × (Std.HashMap Name (String × String)) × Std.HashMap String (Array DefDataRepr) := do
    let dfns ← getM
    writeM dfns
    let split ← splitData dfns
    for group in groups do
        let path := System.mkFilePath ["rawdata", "defn-types", group ++ ".jsonl"]
        IO.FS.writeFile path (jsonLines <| split.getD group #[])
    let pm ← propMapFromDefns dfns
    return (dfns, pm, split)

def getWriteSplitCore : CoreM ((Array DefDataRepr) × (Std.HashMap Name (String × String)) × Std.HashMap String (Array DefDataRepr)) :=
    (getWriteSplitM).run'

def getWriteM : MetaM <| (Array DefDataRepr) × (Std.HashMap Name (String × String)) := do
    let dfns ← getM
    writeM dfns
    let pm ← propMapFromDefns dfns
    return (dfns, pm)

def getWriteCore : CoreM ((Array DefDataRepr) × (Std.HashMap Name (String × String))) :=
    (getWriteM).run'


def thmFromName? (name : Name) : MetaM <| Option DefDataRepr := do
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
        let isNoncomputable := Lean.isNoncomputable (← getEnv) name
        let statement ←
          mkStatement (some name) typeStx valueStx? isProp (isNoncomputable := isNoncomputable)
        return some ⟨name, fmt.pretty, isProp, isNoncomputable, doc?, value, statement⟩
    | _ => return none

def thmFromNameCore? (name : Name) : CoreM <| Option DefDataRepr :=
    (thmFromName? name).run'

def defFromName? (name : Name) : MetaM <| Option DefDataRepr := do
  let env ← getEnv
  let doc? ← findDocString? env name
  let info? := env.find? name
  match info? with
    | some (.defnInfo dfn) =>
        let term := dfn.value
        let type := dfn.type
        let fmt ← PrettyPrinter.ppExpr type
        let isProp := false
        let value :=
            some <| (← PrettyPrinter.ppExpr term).pretty
        let typeStx ← PrettyPrinter.delab type
        let valueStx ←  PrettyPrinter.delab term
        let valueStx? := if isProp then none else some valueStx
        let isNoncomputable := Lean.isNoncomputable (← getEnv) name
        let statement ←
          mkStatement (some name) typeStx valueStx? isProp (isNoncomputable := isNoncomputable)
        return some ⟨name, fmt.pretty, isProp, isNoncomputable, doc?, value, statement⟩
    | _ => return none

end DefDataRepr

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
  let dfns ← DefDataRepr.getM
  IO.println s!"Total: {dfns.size}"
  DefDataRepr.writeM dfns
  let dfns := dfns.filter (fun d => d.doc?.isSome)
  IO.println s!"Total: {dfns.size}"
  DefDataRepr.writeM dfns "docs.jsonl"
  return Json.arr <| dfns.map toJson

-- #check Json.mergeObj

def writeDocsCore : CoreM <| Json :=
    (writeDocsM).run'

def getPropMap : MetaM <| Std.HashMap Name (String × String) := do
    let dfns ← DefDataRepr.getM
    propMapFromDefns dfns


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
    let mut dfs : Array DefDataRepr := #[]
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
        let isNoncomputable := Lean.isNoncomputable (← getEnv) name
        let statement ←
            mkStatement (some name) typeStx valueStx? isProp (isNoncomputable := isNoncomputable)

        let dfn : DefDataRepr :=
          ⟨name, fmt.pretty, isProp, isNoncomputable, doc?, value?, statement⟩
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


partial def termKindsInAux (stx: Syntax)(kinds: List SyntaxNodeKind) : MetaM <| List SyntaxNodeKind := do
    match stx with
    | .node _ k args  =>
        let prevs ← args.toList.mapM (fun a => termKindsInAux a kinds)
        let prevs := prevs.flatten
        if prevs.contains k then
            return prevs
        else
        if kinds.contains k then
            return k :: prevs
        else
            return prevs
    | _ =>
        let k := stx.getKind
        if kinds.contains k then
            return [k]
        else
            return []
open PrettyPrinter
def termKindsIn (stx: Syntax) : MetaM <| List SyntaxNodeKind := do
    let kinds ← termKindList
    termKindsInAux stx kinds

def termKindBestEgsM (choice: Nat := 3)(constantNameValueDocs  := constantNameValueDocs)(termKindList : MetaM <| List SyntaxNodeKind := termKindList) :
    MetaM <| Std.HashMap Name
        (Nat × (Array (Name × Nat × String × Bool ×  String)) ×
         Array (Name × Nat × String × Bool)) := do
    let cs ← constantNameValueDocs
    let kinds ← termKindList
    IO.eprintln s!"Found {cs.size} constants"
    let mut count := 0
    let mut m : Std.HashMap Name (Nat × (Array (Name × Nat × String × Bool × String)) ×
         Array (Name × Nat × String × Bool)) := Std.HashMap.empty
    for ⟨name, type, doc?⟩ in cs do
        count := count + 1
        if count % 400 == 0 then
            IO.eprintln s!"Processed {count} constants out of {cs.size}"
        let depth := type.approxDepth.toNat
        unless depth > 50 do
            try
            let stx ← PrettyPrinter.delab type
            let p ← isProp type
            let tks ← termKindsInAux stx.raw kinds
            let tks := tks.eraseDups
            for tk in tks do
                let (c, egs, noDocEgs) := m.getD tk ((0, #[], #[]))
                match doc? with
                | some doc =>
                  match egs.findIdx? (fun (_, d, _, p', _) =>
                    d > depth ∨ (¬p' ∧ p)) with
                  | some k =>
                    let egs := egs.insertIdx! k (name, depth, (← ppTerm stx).pretty, p, doc)
                    let egs := if egs.size > choice then egs.pop else egs
                    let noDocEgs :=
                        if egs.size + noDocEgs.size > choice then
                            noDocEgs.pop
                        else
                            noDocEgs
                    m := m.insert tk (c + 1, egs, noDocEgs)
                  | none =>
                    if egs.size < choice then
                        let egs := egs.push (name, depth, (← ppTerm stx).pretty, p, doc)
                        let noDocEgs :=
                            if egs.size + noDocEgs.size > choice then
                                noDocEgs.pop
                            else
                                noDocEgs
                        m := m.insert tk (c + 1, egs, noDocEgs)
                    else
                        m := m.insert tk (c + 1, egs, noDocEgs)
                | none =>
                    match noDocEgs.findIdx? (fun (_, d, _, p') =>
                    d > depth ∨ (¬p' ∧ p)) with
                    | some k =>
                        let noDocEgs := noDocEgs.insertIdx! k (name, depth, (← ppTerm stx).pretty, p)
                        let noDocEgs :=
                            if egs.size + noDocEgs.size > choice then
                                noDocEgs.pop
                            else
                                noDocEgs
                        m := m.insert tk (c + 1, egs, noDocEgs)
                    | none =>
                        if noDocEgs.size + egs.size < choice then
                            m := m.insert tk (c + 1, egs, noDocEgs.push (name, depth, (← ppTerm stx).pretty, p))
                        else
                            m := m.insert tk (c + 1, egs, noDocEgs)
            catch e =>
                IO.eprintln s!"Error {← e.toMessageData.toString} delaborating {name}"
    return m


def termKindExamplesM (choices: Nat := 3)(constantNameValueDocs  := constantNameValueDocs)(termKindList : MetaM <| List SyntaxNodeKind := termKindList) : MetaM <| List Json := do
    let egs ← termKindBestEgsM choices constantNameValueDocs termKindList
    IO.eprintln s!"Found {egs.size} term kinds"
    let examples := egs.toArray.qsort (
        fun (_, n, _, _) (_, m, _, _) => n > m
    ) |>.toList
    return examples.map (fun (k, n, v, v') => Json.mkObj [("kind", toJson k),
    ("count", n), ("examples",
        Json.arr <| v.map (fun (n, d, s, p, doc) =>
        Json.mkObj [("name", toJson n.toString), ("depth", d), ("type", toJson s), ("isProp", toJson p), ("doc", toJson doc)])),
        ("noDocExamples",
        Json.arr <| v'.map (fun (n, d, s, p) =>
        Json.mkObj [("name", toJson n.toString), ("depth", d), ("type", toJson s), ("isProp", toJson p)]))])


def termKindExamplesCore (choices: Nat := 3) : CoreM <| List Json := do
    termKindExamplesM choices |>.run' {}


end LeanAide.Meta
