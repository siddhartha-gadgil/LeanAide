import Lean
import LeanAideCore.Aides

/-!
Types for a discussion thread involving chatbots, humans and leanaide. Wrapper types for messages and an indexed inductive type for a discussion thread.

* The main line for the present code is
`TheoremText` → `TheoremCode` → `Document` → `StructuredDocument` → `TheoremCode`
* We may also upload a document or treat a response as a document (if the query is appropriate). But these will be *informal documents*.
-/

namespace LeanAide

open Lean Meta Elab Term

/-- A query message in a discussion thread. -/
structure Query where
  message : String
  queryParams : Json := Json.mkObj []
deriving Inhabited, Repr, ToJson, FromJson

/-- A response message in a discussion thread. -/
structure Response where
  message : String
  responseParams : Json := Json.mkObj []
deriving Inhabited, Repr, ToJson, FromJson

structure TheoremText where
  statement : String
deriving Inhabited, Repr, ToJson, FromJson

structure TheoremCode where
  statement : String
  name: Name
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

inductive ResponseType where
  | query | response | document | structuredDocument | code | comment | theoremText | theoremCode | definitionText | definitionCode | documentCode
deriving Repr, Inhabited

def ResponseType.toType : ResponseType → Type
| .query => Query
| .response => Response
| .document => Document
| .structuredDocument => StructuredDocument
| .code => DocumentCode
| .comment => Comment
| .theoremText => TheoremText
| .theoremCode => TheoremCode
| .definitionText => DefinitionText
| .definitionCode => DefinitionCode
| .documentCode => DocumentCode

instance (rt: ResponseType) : Repr rt.toType where
  reprPrec := by
    cases rt <;> simp [ResponseType.toType] <;> apply reprPrec

#check Repr Query

class ResponseType.OfType (α : Type)  where
  rt : ResponseType
  ofType : α → rt.toType := by exact fun x ↦ x
  eqn : rt.toType = α := by rfl

instance queryOfType : ResponseType.OfType Query where
  rt := .query

instance responseOfType : ResponseType.OfType Response where
  rt := .response

instance documentOfType : ResponseType.OfType Document where
  rt := .document

instance structuredDocumentOfType : ResponseType.OfType StructuredDocument where
  rt := .structuredDocument

instance codeOfType : ResponseType.OfType DocumentCode where
  rt := .code

instance commentOfType : ResponseType.OfType Comment where
  rt := .comment

instance theoremTextOfType : ResponseType.OfType TheoremText where
  rt := .theoremText

instance theoremCodeOfType : ResponseType.OfType TheoremCode where
  rt := .theoremCode

instance definitionTextOfType : ResponseType.OfType DefinitionText where
  rt := .definitionText

instance definitionCodeOfType : ResponseType.OfType DefinitionCode where
  rt := .definitionCode

instance documentCodeOfType : ResponseType.OfType DocumentCode where
  rt := .documentCode



inductive Discussion : Type → Type where
  | start {rt: ResponseType} (sysPrompt? : Option String) (elem: rt.toType) : Discussion rt.toType
  | query {rt: ResponseType} (init: Discussion rt.toType) (q : Query) : Discussion Query
  | response (init: Discussion Query) (r : Response) : Discussion Response
  | digress {a b : ResponseType}  (init: Discussion a.toType) (elem : b.toType): Discussion b.toType
  | translateTheoremQuery (init : Discussion Unit) (tt : TheoremText) : Discussion TheoremText
  | theoremTranslation (init : Discussion TheoremText) (tc : TheoremCode) :Discussion TheoremCode
  | translateDefinitionQuery (init : Discussion Unit) (dt : DefinitionText) : Discussion DefinitionText
  | definitionTranslation (init : Discussion DefinitionText) (dc : DefinitionCode) : Discussion DefinitionCode
  | comment {rt : ResponseType} (init: Discussion rt.toType) (c : Comment) : Discussion Comment
  | proveTheoremQuery (init: Discussion Unit) (tt : TheoremText) : Discussion TheoremText
  | proofDocument (init: Discussion TheoremCode) (doc : Document) (prompt? : Option String := none) :  Discussion Document
  | proofStructuredDocument (init: Discussion Document) (sdoc : StructuredDocument) (prompt? : Option String := none) (schema : Option Json := none) :  Discussion StructuredDocument
  | proofCode (init: Discussion StructuredDocument) (tc : DocumentCode) : Discussion DocumentCode
  | rewrittenDocument (init: Discussion Document ) (doc : Document) (prompt? : Option String := none) :  Discussion Document
  | edit {rt : ResponseType} (userName? : Option String := none) : Discussion rt.toType  → Discussion rt.toType
deriving Repr

namespace Discussion

def last {α} : Discussion α → α
| start _ elem => elem
| query _ q => q
| response _ r => r
| digress _ d => d
| translateTheoremQuery _ tt => tt
| theoremTranslation _ tc => tc
| translateDefinitionQuery _ d =>  d
| definitionTranslation _ d =>  d
| comment _ d => d
| proveTheoremQuery _ tt => tt
| proofDocument _ doc _  => doc
| proofStructuredDocument _ sdoc _ _ => sdoc
| proofCode _ tc => tc
| rewrittenDocument _ doc _ => doc
| edit _ d => d.last

def lastM {α} : TermElabM (Discussion α) → TermElabM α
| d => do return (← d).last

def init {α} [inst : ResponseType.OfType α ] (elem : α):
  Discussion α :=
  let disc := .start (rt := inst.rt) none (inst.ofType elem)
  inst.eqn ▸ disc

class GeneratorM (α β : Type) where
  generateM : (Discussion α) → TermElabM (Discussion β)

def generateM {α} (β : Type) [r : GeneratorM α β] (d : Discussion α) : TermElabM (Discussion β) :=
  r.generateM d

set_option synthInstance.checkSynthOrder false in
instance composition (α γ : Type) (β : outParam Type) [r1 : GeneratorM α β] [r2 : GeneratorM β γ] : GeneratorM α γ where
  generateM d := do
    let d' ← r1.generateM d
    r2.generateM d'

-- dummies for testing
instance queryResponse : GeneratorM Query Response where
  generateM d := do
    let q := d.last
    let res := { message := s!"This is a response to {q.message}", responseParams := Json.null }
    return Discussion.response d res

instance responseComment : GeneratorM Response Comment where
  generateM d := do
    let r := d.last
    let c := { message := s!"This is a comment on {r.message}", user := "user" }
    return Discussion.comment (rt := .response) d c

#synth GeneratorM Query Comment

def q : Discussion Query :=
  init { message := "What is 2+2?"}

#eval q.generateM Comment

end Discussion

end LeanAide
