import Lean
import LeanAideCore.Aides
import LeanAideCore.Syntax

/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `CodeGenerator`, an optional goal, a syntax category, and a JSON object, and returns the corresponding syntax or throws an error.
-/


open Lean Meta Elab LeanAide

initialize registerTraceClass `LeanAide.Codegen

namespace LeanAide

instance : Repr SyntaxNodeKinds where
  reprPrec kinds n :=
    let names : List Name := kinds
    Repr.reprPrec names n

instance : ToString SyntaxNodeKinds where
  toString kinds :=
    let names : List Name := kinds
    ToString.toString names

namespace Codegen

#logIO leanaide.codegen.info
#logFile leanaide.codegen.info

/--
Attribute for generating Lean code, more precisely Syntax of a given category, from JSON data. More precisely, we generate `TranslateM <| Option <| TSyntax Q` from a JSON object, with the matching key as part of the attribute. In some cases, no syntax is generated as the goal is purely to have a side-effect to modify the context.

As the same statement can generate different syntax categories (e.g. `def` and `let`) this is not specified in the attribute. Instead the target category is part of the signature of the function.
-/
syntax (name := codegen) "codegen" (str,*)? : attr

/-- Environment extension storing code generation lemmas -/
initialize codegenExt :
    SimpleScopedEnvExtension (Name × (Option String)) (Std.HashMap (Option String) (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key?) =>
        m.insert key? <| (m.getD key? #[] ).push n
    initial := {}
  }

/--
Extract the keys from the `codegen` attribute syntax. If no keys are provided, return `none`. If keys are provided, return an array of strings.
-/
def codegenKeyM (stx : Syntax) : CoreM <| Option (Array String) := do
  match stx with
  | `(attr|codegen) => do
    return none
  | `(attr|codegen $x) => do
    return #[x.getString]
  | `(attr|codegen $xs,*) => do
    let keys := xs.getElems
    return keys.map (·.getString)
  | _ => throwUnsupportedSyntax

/--
An environment extension for code generation functions. It stores the functions that can be used to generate code from JSON data. The key is a string that identifies the function, and the value is an array of names of the functions that can be used to generate code for that key.
-/
initialize registerBuiltinAttribute {
  name := `codegen
  descr := "Lean code generator"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    -- Obtained from Qq.
    let expectedType := Expr.forallE Name.anonymous (Expr.const `LeanAide.CodeGenerator [])
      (Expr.forallE Name.anonymous ((Expr.const `Option [Level.zero]).app (Expr.const `Lean.MVarId []))
        (Expr.forallE `kind (Expr.const `Lean.SyntaxNodeKinds [])
          (Expr.forallE Name.anonymous (Expr.const `Lean.Json [])
            ((Expr.const `LeanAide.TranslateM []).app
              ((Expr.const `Option [Level.zero]).app ((Expr.const `Lean.TSyntax []).app (Expr.bvar 1))))
            BinderInfo.default)
          BinderInfo.default)
        BinderInfo.default)
      BinderInfo.default
    unless ← isDefEq declTy expectedType do
      throwError -- replace with error
        s!"codegen: {decl} has type {declTy}, but expected {expectedType}"
    let keys ← codegenKeyM stx
    -- logInfo m!"codegen: {decl}; keys: {keys}"
    match keys with
    | none => do
      -- no keys, just add the name
      codegenExt.add (decl, none) kind
    | some keys =>
    for key in keys do
      codegenExt.add (decl, key) kind
}

/--
Get the code generation functions for a given key. The key is a string that identifies the function. If no function is found for the key, an error is thrown.
-/
def codegenMatches (key: String) : CoreM <| Array Name := do
  let allKeys := (codegenExt.getState (← getEnv)).toArray.map (fun (k, _) => k)
  let some fs :=
    (codegenExt.getState (← getEnv)).get? key | throwError
      s!"codegen: no function found for key '{key}' available keys are {allKeys.toList}"
  traceAide `leanaide.codegen.info s!"found {fs.size} functions for key {key}"
  if fs.isEmpty then
    traceAide `leanaide.codegen.info s!"no function found for key {key} in {allKeys.toList}"
  return fs

/--
Get the code generation functions that do not have a key associated with them. These functions are used when no key is found in the JSON object.
-/
def codegenKeyless : CoreM <| Array Name := do
  return (codegenExt.getState (← getEnv)).get? none |>.getD #[]

/--
Given a function *name*, a `CodeGenerator`, an optional goal, a syntax category, and a JSON object, this function evaluates the function in the environment and returns the corresponding syntax or throws an error if the function does not match the expected type.
-/
def codeFromFunc (goal? : Option MVarId) (translator: CodeGenerator) (f: Name) (kind : SyntaxNodeKinds) (source: Json) :
    TranslateM (Option (TSyntax kind)) := do
  let expectedType ← mkArrow (mkConst ``CodeGenerator) (← mkArrow (mkConst ``Option) (Expr.forallE `kind (Expr.const `Lean.SyntaxNodeKinds [])
  (Expr.forallE Name.anonymous (Expr.const `Lean.Json [])
    ((Expr.const `LeanAide.TranslateM []).app
      ((Expr.const `Option [Level.zero]).app ((Expr.const `Lean.TSyntax []).app (Expr.bvar 1))))
    BinderInfo.default)
  BinderInfo.default : Expr))
  let f := mkConst f
  let code ←
    unsafe evalExpr
      (CodeGenerator → Option MVarId  → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))) expectedType f
  code translator goal? kind source

/--
Given a JSON object, return the corresponding syntax by matching with `.getKVorType?` and then calling the function in the environment using `codeFromFunc`. The function is expected to return a `TranslateM (Option (TSyntax kind))`, where `kind` is the syntax category of the object.

The return value is an `Option (TSyntax kind)`, which is `none` if the action is purely side-effecting (e.g. modifying the context) and `some` if the action generates code.
-/
partial def getCode  (translator: CodeGenerator) (goal? : Option MVarId) (kind: SyntaxNodeKinds)
  (source: Json) :
    TranslateM (Option (TSyntax kind)) := do
  match source.getKVorType? with
  | some (key, source) => do
    let key := key.toLower
    let fs ←  codegenMatches key
    let mut accumErrors : Array String := #[]
    for f in fs do
      traceAide `leanaide.codegen.info s!"trying {f} for key {key}"
      try
        -- logInfo m!"codegen: trying {f} for key {key}"
        let code? ← codeFromFunc goal? translator f kind source
        traceAide `leanaide.codegen.info s!"{f} for key {key} worked; returned : {code?.isSome}"
        return code?
      catch e =>
        logWarning m!"codegen: error in {f} for key {key}: {← e.toMessageData.toString}"
        accumErrors := accumErrors.push s!"{f}: {← e.toMessageData.toString}"
        continue -- try next function
    let allErrors := accumErrors.toList.foldl (init := "") (fun acc e => acc ++ "\n" ++ e)
    throwError
      s!"codegen: no valid function found for key {key}\nTried functions: {fs}\nErrors in functions:\n{allErrors}\nsource:\n{source.pretty}"
  | none =>
    match source with
    | Json.arr sources =>
      let obj := Json.mkObj [("document", Json.arr sources)]
      getCode translator goal? kind obj
    | _ => do
    let fs ← codegenKeyless
    if fs.isEmpty then
      throwError
        s!"codegen: no key or type found in JSON object {source}, and no codegen functions registered"
    for f in fs.reverse do
      try
        let code? ← codeFromFunc goal? translator f kind source
        return code?
      catch _ =>
        continue -- try next function
    throwError
      s!"codegen: no key or type found in JSON object {source} and no codegen functions returned a result"
