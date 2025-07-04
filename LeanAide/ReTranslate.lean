import LeanCodePrompts.Translate
import Qq

namespace LeanAide

open Translate Lean Meta Elab Term Qq

/-- Environment extension storing retranslation patterns -/
initialize retranslateExt :
    SimpleScopedEnvExtension (Name × Bool) (Array (Name × Bool)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        m.push n
    initial := #[] -- empty by default
  }

syntax (name := retranslate) "retranslate" : attr

initialize registerBuiltinAttribute {
  name := `retranslate
  descr := "Prompt for trying to retranslate a theorem or definition."
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let expectedSimpleType : Q(Type) :=
      q(String → Option String) -- type of the prompt function
    let isSimple ← isDefEq declTy expectedSimpleType
    let expectedType : Q(Type) :=
      q(ElabError → Option String) -- type of the prompt function
    if !isSimple then
      unless ← isDefEq declTy expectedType do
        throwError
          s!"codegen: {decl} has type {declTy}, but expected {expectedSimpleType} or {expectedType}"
    retranslateExt.add (decl, isSimple)
}

#check Term.mkConst

def retranslateSimplePrompts : MetaM (Array (String → Option String)) := do
  let names := retranslateExt.getState (← getEnv)
  names.filterMapM fun (n, isSimple) => do
    if isSimple then
      let f := Lean.mkConst n
      unsafe evalExpr (String → Option String) q(String → Option String) f
    else
      pure none

def retranslatePrompts : MetaM (Array (ElabError → Option String)) := do
  let names := retranslateExt.getState (← getEnv)
  names.mapM fun (n, isSimple) => do
    if isSimple then
      let f := Lean.mkConst n
      let f ← unsafe evalExpr (String → Option String) q(String → Option String) f
      pure <| fun e => f e.text
    else
      let f := Lean.mkConst n
      unsafe evalExpr (ElabError → Option String) q(ElabError → Option String) f

def allRetranslatePrompts (s: String) : MetaM (Array String) := do
  let prompts ← retranslateSimplePrompts
  return prompts.filterMap fun prompt? => prompt? s

def retranslateFromStringsAux (ss: Array String) (prompts: Array (String → Option String)) (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  let mut errs := #[]
  for prompt in prompts do
    for s in ss do
      if let some fixPrompt := prompt s then
        let results ← translator.server.mathCompletions fixPrompt n
        match ← greedyBestExprWithErr? results with
        | Except.ok e =>
          return Except.ok e
        | Except.error err =>
          errs := errs.push err
      else
        continue
  return .error errs.flatten

def retranslateFromErrorsAux (ss: Array ElabError) (prompts: Array (ElabError → Option String)) (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  let mut errs := #[]
  for prompt in prompts do
    for s in ss do
      if let some fixPrompt := prompt s then
        let results ← translator.server.mathCompletions fixPrompt n
        match ← greedyBestExprWithErr? results with
        | Except.ok e =>
          return Except.ok e
        | Except.error err =>
          errs := errs.push err
      else
        continue
  return .error errs.flatten


def retranslateFromStrings (ss: Array String) (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  let prompts ← retranslateSimplePrompts
  retranslateFromStringsAux ss prompts translator n

/--
Attempt to fix the given errors by using the prompt function to generate a prompt for each error. The prompt is first to allow `evalUnsafe` to be used with target type.
-/
def retranslateFromErrors (errs: Array ElabError)  (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  retranslateFromErrorsAux errs (← retranslatePrompts) translator n


end LeanAide
