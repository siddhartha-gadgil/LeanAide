import Lean
import LeanAideCore.Aides

/-!
Types for a discussion thread involving chatbots, humans and leanaide. Wrapper types for messages and an indexed inductive type for a discussion thread.

* The main line for the present code is
`TheoremText` → `TheoremCode` → `Document` → `StructuredDocument` → `TheoremCode`
* We may also upload a document or treat a response as a document (if the query is appropriate). But these will be *informal documents*.
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

structure TheoremCode where
  statement : String
  type : Expr
  code : TSyntax ``commandSeq
deriving Inhabited, Repr

structure DefinitionText where
  statement : String
deriving Inhabited, Repr, ToJson, FromJson

structure DefinitionCode where
  code : TSyntax ``commandSeq
deriving Inhabited, Repr

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

class Content (α : Type) where
  content : α → String

instance : Content Query where
  content q := q.message

instance : Content Response where
  content r := r.message

instance : Content Document where
  content d := d.content

instance : Content Comment where
  content c := c.message

inductive Discussion : Type → Type _ where
  | root (sysPrompt? : Option String) : Discussion Unit
  | query {α : Type} (q : Query) : Discussion α  → Discussion Query
  | response (r : Response) : Discussion Query → Discussion Response
  | digress {α : Type} (d : Discussion α) : Discussion Unit
  | translateTheoremQuery (tt : TheoremText) : Discussion Unit → Discussion TheoremText
  | theoremTranslation (tt : TheoremText) : Discussion TheoremText → Discussion TheoremCode
  | translateDefinitionQuery (dt : DefinitionText) : Discussion Unit → Discussion DefinitionText
  | definitionTranslation (dt : DefinitionText) : Discussion DefinitionText → Discussion DefinitionCode
  | comment (c : Comment) : Discussion α → Discussion Comment
  | proveTheoremQuery (tt : TheoremText) : Discussion TheoremText
  | proofDocument (doc : Document) (prompt? : Option String := none) : Discussion TheoremCode → Discussion Document
  | proofStructuredDocument (sdoc : StructuredDocument) (prompt? : Option String := none) (schema : Option Json := none) : Discussion Document → Discussion StructuredDocument
  | proofCode (tc : TheoremCode) : Discussion StructuredDocument → Discussion TheoremCode
  | rewrittenDocument {α} [Content α] (doc : Document) (prompt? : Option String := none) : Discussion α  → Discussion Document

end LeanAide
