import StatementAutoformalisation.Declaration
import Mathlib

set_option maxHeartbeats 10000000

open Lean Meta in
def checks : Array (Environment → Name → Bool) :=
  #[isAttribute,
    isAuxRecursor,
    isBRecOnRecursor,
    isCasesOnRecursor,
    isExtern,
    isExternC,
    isIOUnitBuiltinInitFn,
    isIOUnitInitFn,
    isIOUnitRegularInitFn,
    isMatcherCore,
    isPrivateNameFromImportedModule,
    isNoConfusion,
    isRecCore,
    isRecOnRecursor,
    fun _ => Name.isInternal,
    fun _ => Name.isImplementationDetail,
    fun _ => Name.isInaccessibleUserName]

open Lean in
def forbiddenPrefixes : Array Name :=
  #[`Lean,
    `_private,
    `_regBuiltin,
    `Std, 
    `IO, 
    `Char, 
    `String, 
    `ST,
    `System,
    `StateT,
    `Repr,
    `ReaderT,
    `EIO,
    `BaseIO,
    `Task,
    `UInt8,
    ``UInt16,
    ``UInt32,
    ``UInt64]

def blacklistFiles := [`StatementAutoformalisation.Declaration]

def outputFile : System.FilePath := "data/mathlib4-prompts.json"

open Lean in
def generatePrompts : MetaM Unit := do
  let env ← getEnv
  let consts := env.constants.map₁.toArray
  let blacklist : List Nat :=  blacklistFiles.filterMap env.getModuleIdx?
  let data ← consts.filterMapM fun ⟨nm, ci⟩ => do
    let some docstr ← findDocString? env nm | pure none
    let valid? : Option Unit := do
      let mod : Nat ← env.getModuleIdxFor? nm
      guard $ mod ∉ blacklist
      guard $ !checks.any (· env nm)
      guard $ !forbiddenPrefixes.any (·.isPrefixOf nm)
    valid?.mapM <| fun _ => do
      liftM <| IO.println nm.toString
      let decl ← Declaration.fromConstantInfo ci
      let decldoc : DeclarationWithDocstring := ⟨decl, docstr⟩
      return decldoc.toJson
  liftM <| IO.FS.writeFile outputFile (Json.arr data).pretty

open Lean
def main : IO Unit := do
  IO.println "Generating prompts..."
  initSearchPath (← Lean.findSysroot) ["lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/"]
  let env ← importModules [{module := `Mathlib}] {}
  Prod.fst <$> generatePrompts.toIO {fileName := "", fileMap := default, maxHeartbeats := 5000000} {env := env}
  IO.println s!"Output written to {outputFile}."