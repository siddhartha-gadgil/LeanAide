import Lean
import LeanAide.Aides
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
