import Lean
import LeanAideCore.Aides
namespace LeanAide
open Lean

local instance : Hashable Float where
  hash f := hash (f * 100).toUInt32

/--
  A `PromptExampleBuilder` is a way to specify how to generate a prompt
  for a given example. It can be a sequence of different builders, or a blend
  of different builders. The `embedSearch` builders use embeddings
  to search for a given field in the Lean 4 documentation. The `leansearch` and `moogle`
  builders use the `leansearch` and `moogle` endpoints respectively to search for a given
  field in the Lean 4 documentation. The `fixed` builder uses a fixed set of prompts.
-/
inductive PromptExampleBuilder where
| embedSearch (descField : String) (n: Nat) (penalty: Float := 1.0) : PromptExampleBuilder
| leansearch (descFields : List String)
  (preferDocs: Bool := false) (n: Nat) : PromptExampleBuilder
| moogle (descFields : List String)
  (preferDocs: Bool := false) (n: Nat) : PromptExampleBuilder
| generic (url: String) (baseData : Json) (headers : Array String) (n: Nat) : PromptExampleBuilder
| fixed (prompts : Array (String × Json)) : PromptExampleBuilder
| sequence : List PromptExampleBuilder → PromptExampleBuilder
| blend : List PromptExampleBuilder → PromptExampleBuilder
deriving  Repr, ToJson, FromJson, Hashable

/--
  A `SimpleDef` is a simple definition that can be used to generate a prompt.
  It has a name, a type, a docString, and a boolean indicating whether it is a proposition.
  It can also have a value.
-/
structure SimpleDef where
  name : String
  type : String
  docString : String
  isProp : Bool
  value : Option String := none
deriving Repr, FromJson, ToJson


namespace PromptExampleBuilder

/--
  A `PromptExampleBuilder` that uses embeddings to search for a given field in the Lean 4 documentation.
-/
def embedBuilder (numSim numConcise numDesc: Nat) : PromptExampleBuilder :=
  .blend [
    .embedSearch "docString" numSim,
    .embedSearch "concise-description" numConcise,
    .embedSearch "description" numDesc]

/--
  A `PromptExampleBuilder` that uses the `leansearch` and `moogle` endpoints to search for a given field in the Lean 4 documentation.
-/
def searchBuilder (numLeanSearch numMoogle: Nat) : PromptExampleBuilder :=
  .blend [.leansearch ["concise-description", "description"] true numLeanSearch,
      .moogle ["concise-description", "description"] true numMoogle]

def genericEmbedBuilder (url: String) (numSim numConcise numDesc: Nat)  (headers : Array String := #[]) : PromptExampleBuilder :=
  .blend [
    .generic url (Json.mkObj [("prompt_type", "docString")]) headers numSim,
    .generic url (Json.mkObj [("prompt_type", "concise-description")]) headers numConcise,
    .generic url (Json.mkObj [("prompt_type", "description")]) headers numDesc,
  ]

def mkEmbedBuilder (url?: Option String) (numSim numConcise numDesc: Nat)  (headers : Array String := #[]) : PromptExampleBuilder :=
  match url? with
  | some url => genericEmbedBuilder url numSim numConcise numDesc headers
  | none => embedBuilder numSim numConcise numDesc

/--
Append two `PromptExampleBuilder`s together.
-/
instance : Append PromptExampleBuilder :=
  {append := fun x y =>
    match x, y with
    | .sequence [], y => y
    | .blend [], y => y
    | .blend ps, .blend qs => .blend <| ps ++ qs
    | .sequence ps, .sequence qs => .sequence <| ps ++ qs
    | .blend ps, x => .blend <| ps ++ [x]
    | .sequence ps, x => .sequence <| ps ++ [x]
    | x, .sequence ps => .sequence <| x :: ps
    | x, y => .sequence [x, y]
  }

/--
The new default PromptExampleBuilder.
-/
def default :=
  PromptExampleBuilder.embedBuilder 8 4 4 ++ .searchBuilder 4 4

/--
The classic default PromptExampleBuilder (which seems to work better).
-/
def classicDefault :=
  PromptExampleBuilder.embedBuilder 20 2 2

instance : Inhabited PromptExampleBuilder := ⟨default⟩

partial def purge? (pb: PromptExampleBuilder) : Option PromptExampleBuilder :=
  match pb with
  | .sequence [] => none
  | .blend [] => none
  | .embedSearch _ 0 _ => none
  | .leansearch _ _ 0 => none
  | .moogle _ _ 0 => none
  | .sequence ps => some <| .sequence <| ps.filterMap purge?
  | .blend ps => some <| .blend <| ps.filterMap purge?
  | x => some x

/--
Prepend a fixed set of prompts to a `PromptExampleBuilder`.
-/
def prependFixed (pb: PromptExampleBuilder)
  (prompts: Array (String × Json)) : PromptExampleBuilder :=
  match pb with
  | .sequence (.fixed ps :: pbs) =>
      .sequence <| .fixed (prompts ++ ps) :: pbs
  | .sequence ps => .sequence <| .fixed prompts :: ps ++ [pb]
  | _ => .sequence [.fixed prompts, pb]

def prependSimpleDef (pb: PromptExampleBuilder)
  (sd: SimpleDef) : PromptExampleBuilder :=
  let pair := (sd.name, toJson sd)
  pb.prependFixed #[pair]

end PromptExampleBuilder

end LeanAide
