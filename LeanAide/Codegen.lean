import Lean
import Qq
import LeanAide.Aides
import LeanAide.TranslateM

open Lean Meta Qq Elab

initialize registerTraceClass `LeanAide.Codegen

namespace LeanAide

namespace Codegen

/--
Attribute for generating Lean code, more precisely Syntax of a given category, from JSON data. More precisely, we generate `TranslateM <| Option <| TSyntax Q` from a JSON object, with the matching key as part of the attribute. In some cases, no syntax is generated as the goal is purely to have a side-effect to modify the context.

As the same statement can generate different syntax categories (e.g. `def` and `let`) this is not specified in the attribute. Instead the target category is part of the signature of the function.
-/
syntax (name := codegen) "codegen" str : attr

/-- Environment extension storing code generation lemmas -/
initialize codegenExt :
    SimpleScopedEnvExtension (Name × String) (Std.HashMap String Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key) => m.insert key n
    initial := {}
  }

def codegenKeyM (stx : Syntax) : CoreM String := do
  match stx with
  | `(attr|codegen $x) => do
    return x.getString
  | _ => throwUnsupportedSyntax


initialize registerBuiltinAttribute {
  name := `codegen
  descr := "Lean code generator"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let expectedType : Q(Type) :=
    q((kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)))
    unless ← isDefEq declTy expectedType do
      logWarning -- replace with error
        s!"codegen: {decl} has type {declTy}, but expected {expectedType}"
    let key ← codegenKeyM stx
    logInfo m!"codegen: {decl}; key: {key}"
    codegenExt.add (decl, key) kind
}

def codegenMatch (key: String) : CoreM Name := do
  let some f :=
    (codegenExt.getState (← getEnv)).get? key | throwError
      s!"codegen: no function found for key {key}"
  return f

def test : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| `term, js =>
  match js.getStr? with
  | .ok str => do
    let name := Syntax.mkStrLit str
    `($name)
  | .error _ => do
    `(sorry)
| `tactic, _ => `(tactic|sorry)
| _, _ => throwError
    s!"codegen: test does not work"

#eval test `term (Json.str "Nat.succ")

def codeFromFunc (f: Name) (kind : SyntaxNodeKinds) (source: Json) :
    TranslateM (Option (TSyntax kind)) := do
  let expectedType : Q(Type) :=
    q((kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)))
  let f := mkConst f
  let code ←
    unsafe evalExpr
      ((kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))) expectedType f
  code kind source

/--
Given a JSON object, return the corresponding syntax by matching with `.getKVorType?` and then calling the function in the environment using `codeFromFunc`. The function is expected to return a `TranslateM (Option (TSyntax kind))`, where `kind` is the syntax category of the object.
-/
def getCode (kind: SyntaxNodeKinds) (source: Json) :
    TranslateM (Option (TSyntax kind)) := do
  match source.getKVorType? with
  | some (key, source) => do
    let f ←  codegenMatch key
    let code ← codeFromFunc f kind source
    return code
  | none => do
    throwError
      s!"codegen: no key or type found in JSON object {source}"

#eval codeFromFunc ``test `term (Json.null)

end Codegen

end LeanAide
