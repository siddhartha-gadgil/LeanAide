import Lean
import Lean.Meta
import Init.System
import Std
open Lean Meta Std Elab

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