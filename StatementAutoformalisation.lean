import CodeAction.Interface
import StatementAutoformalisation.Config.Custom
import StatementAutoformalisation.Config.Informalisation
import StatementAutoformalisation.Config.SuggestName
import StatementAutoformalisation.Declaration

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

def outputFile : System.FilePath := "../data/mathlib4-prompts.json"

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
      let decl ← Declaration.fromConstantInfo ci
      let decldoc : DeclarationWithDocstring := ⟨decl, docstr⟩
      return decldoc.toJson
  liftM <| IO.FS.writeFile outputFile (Json.arr data).pretty

open Lean
def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) [".lake/build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/", "lake-packages/proofwidgets/build/lib" ]
  let env ← importModules #[{module := `Mathlib}] {}
  Prod.fst <$> generatePrompts.toIO 
    {fileName := "", 
     fileMap := default, 
     options := ⟨[(`maxHeartbeats, .ofNat 214920948329)]⟩, 
     maxHeartbeats := 712467123} {env}
