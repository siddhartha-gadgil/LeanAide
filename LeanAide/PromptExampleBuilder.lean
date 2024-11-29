import Lean
import LeanAide.Aides
namespace LeanAide
open Lean

local instance : Hashable Float where
  hash f := hash (f * 100).toUInt32

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

structure SimpleDef where
  name : String
  type : String
  docString : String
  isProp : Bool
  value : Option String := none
deriving Repr, FromJson, ToJson


namespace PromptExampleBuilder

def embedBuilder (numSim numConcise numDesc: Nat) : PromptExampleBuilder :=
  .blend [
    .embedSearch "docString" numSim,
    .embedSearch "concise-description" numConcise,
    .embedSearch "description" numDesc]

def searchBuilder (numLeanSearch numMoogle: Nat) : PromptExampleBuilder :=
  .blend [.leansearch ["concise-description", "description"] true numLeanSearch,
      .moogle ["concise-description", "description"] true numMoogle]


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


def default :=
  PromptExampleBuilder.embedBuilder 8 4 4 ++ .searchBuilder 4 4

def classicDefault :=
  PromptExampleBuilder.embedBuilder 20 2 2

instance : Inhabited PromptExampleBuilder := ⟨default⟩

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
