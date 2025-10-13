import LeanAideCore.TranslateM
import LeanAideCore.Translator
import Qq

namespace LeanAide
variable [LeanAideBaseDir]
open Translate Lean Meta Elab Term Qq

variable (translateFn? : Array String → TranslateM (Except (Array ElabError) Expr))

inductive RetranslateLevel
  | simple -- simple retranslate prompt, e.g. `String → Option String`
  | basic -- full retranslate prompt, e.g. `ElabError → Option String`
  | general -- general retranslate prompt, e.g. `ElabError → Translator → Except (Array ElabError) Expr` with a translator
deriving Inhabited, Repr, DecidableEq

/-- Environment extension storing retranslation patterns -/
initialize retranslateExt :
    SimpleScopedEnvExtension (Name × RetranslateLevel) (Array (Name × RetranslateLevel)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        m.push n
    initial := #[] -- empty by default
  }

syntax (name := retranslate) "retranslate" : attr

def retranslateFromBasicErrorsAux (err: ElabError) (prompt: ElabError → Option String) (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  if let some fixPrompt := prompt err then
    let results ← translator.server.mathCompletions fixPrompt n
    match ← translateFn? results with
    | Except.ok e =>
      return Except.ok e
    | Except.error err =>
      return .error err
  else
    return .error #[err]

def retranslateFromStringAux (text: String) (prompt: String → Option String) (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  if let some fixPrompt := prompt text then
    let results ← translator.server.mathCompletions fixPrompt n
    match ← translateFn? results with
    | Except.ok e =>
      return Except.ok e
    | Except.error err =>
      return .error err
  else
    return .error #[.unparsed text "<dummy>" none]


namespace RetranslateLevel

def defTypeExpr : RetranslateLevel → Q(Type)
  | .simple => q(String → Option String)
  | .basic => q(ElabError → Option String)
  | .general => q(ElabError → Translator → TranslateM (Except (Array ElabError) Expr))

def defType : RetranslateLevel → Type
  | .simple => String → Option String
  | .basic => ElabError → Option String
  | .general => ElabError → Translator → TranslateM (Except (Array ElabError) Expr)

def liftToGeneral : (level: RetranslateLevel) →
    level.defType → ElabError → Translator → TranslateM  (Except (Array ElabError) Expr)
  | .simple, f => fun e t => retranslateFromStringAux translateFn? e.text f t
  | .basic, f  => fun e t => retranslateFromBasicErrorsAux translateFn? e f t
  | .general, f => f

end RetranslateLevel

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
    let level :=
      if isSimple then
        RetranslateLevel.simple
      else
        RetranslateLevel.basic
    retranslateExt.add (decl, level)
}

def retranslators (useLLMs: Bool) : MetaM (Array (ElabError → Translator → TranslateM (Except (Array ElabError) Expr))) := do
  let names := retranslateExt.getState (← getEnv)
  let names :=
    if useLLMs then
      names
    else
      names.filter fun (_, level) => level ≠ .general
  names.mapM fun (n, level) => do
    let f := Lean.mkConst n
    let f ← unsafe evalExpr (RetranslateLevel.defType level) (RetranslateLevel.defTypeExpr level) f
    pure <| RetranslateLevel.liftToGeneral translateFn? level f

def retranslateFromErrorsAux (errors: Array ElabError) (attempts: Array (ElabError → Translator → TranslateM (Except (Array ElabError) Expr))) (translator: Translator := {}):
    TranslateM <| Except (Array ElabError) Expr := do
  let mut errs := #[]
  for attempt in attempts do
    for err in errors do
      match ←  attempt err translator with
      | Except.ok expr =>
        return .ok expr
      | Except.error err' =>
        errs := errs ++ err'
  return .error errs

def retranslateFromErrors (errs: Array ElabError)  (translator: Translator := {}) (useLLMs : Bool := true) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  retranslateFromErrorsAux errs (← retranslators translateFn? useLLMs) {translator with params := {translator.params with n := n}}

def iteratedRetranslateFromErrors (errs: Array ElabError)  (translator: Translator := {}) (n: Nat := 3) (withLLMs : Nat) (withoutLLMs : Nat) :
    TranslateM <| Except (Array ElabError) Expr := do
  match withLLMs, withoutLLMs with
  | 0, 0 => return .error errs
  | 0, k + 1 =>
    match ← retranslateFromErrors translateFn? errs translator false n with
    | .ok e => return .ok e
    | .error errs => iteratedRetranslateFromErrors errs translator n 0 k
  | k + 1, l =>
    match ← retranslateFromErrors translateFn? errs translator true n with
    | .ok e => return .ok e
    | .error errs => iteratedRetranslateFromErrors errs translator n k l

/-
Test code only below. Purge after testing.
-/
def retranslateSimplePrompts : MetaM (Array (String → Option String)) := do
  let names := retranslateExt.getState (← getEnv)
  names.filterMapM fun (n, level) => do
    if level = .simple then
      let f := Lean.mkConst n
      unsafe evalExpr (String → Option String) q(String → Option String) f
    else
      pure none

def allRetranslatePrompts (s: String) : MetaM (Array String) := do
  let prompts ← retranslateSimplePrompts
  return prompts.filterMap fun prompt? => prompt? s





def retranslateSpecialPrompts : MetaM (Array (ElabError → Option String)) := do
  let names := retranslateExt.getState (← getEnv)
  names.mapM fun (n, level) => do
    if level = .simple then
      let f := Lean.mkConst n
      let f ← unsafe evalExpr (String → Option String) q(String → Option String) f
      pure <| fun e => f e.text
    else
      let f := Lean.mkConst n
      unsafe evalExpr (ElabError → Option String) q(ElabError → Option String) f


def retranslateFromSpecilaErrorsAux (ss: Array ElabError) (prompts: Array (ElabError → Option String)) (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  let mut errs := #[]
  for prompt in prompts do
    for s in ss do
      if let some fixPrompt := prompt s then
        let results ← translator.server.mathCompletions fixPrompt n
        match ← translateFn? results with
        | Except.ok e =>
          return Except.ok e
        | Except.error err =>
          errs := errs.push err
      else
        continue
  return .error errs.flatten



/--
Attempt to fix the given errors by using the prompt function to generate a prompt for each error. The prompt is first to allow `evalUnsafe` to be used with target type.
-/
def retranslateFromSpecialErrors (errs: Array ElabError)  (translator: Translator := {}) (n: Nat := 3) :
    TranslateM <| Except (Array ElabError) Expr := do
  retranslateFromSpecilaErrorsAux translateFn? errs (← retranslateSpecialPrompts) translator n


end LeanAide
