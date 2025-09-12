import Lean
import LeanAideCore.Aides

/-!
Types for a discussion thread involving chatbots, humans and leanaide. Wrapper types for messages and an indexed inductive type for a discussion thread.
-/

namespace LeanAide

open Lean Meta

/-- A query message in a discussion thread. -/
structure Query where
  message : String
  queryParams : Json
deriving Inhabited, Repr, ToJson, FromJson

/-- A response message in a discussion thread. -/
structure Response where
  message : String
  responseParams : Json
deriving Inhabited, Repr, ToJson, FromJson

structure TheoremText where
  statement : String
deriving Inhabited, Repr, ToJson, FromJson

structure Document where
  content : String
deriving Inhabited, Repr, ToJson, FromJson

structure StructuredDocument where
  json: Json
deriving Inhabited, Repr, ToJson, FromJson

structure DocumentCode where
  code : TSyntax ``commandSeq
deriving Inhabited, Repr

structure Comment where
  message : String
  user : String
deriving Inhabited, Repr, ToJson, FromJson


end LeanAide
