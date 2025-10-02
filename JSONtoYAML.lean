import Lean.Data.Json.FromToJson
import Lean.Syntax
import Lean.Elab
import Lean.Parser
import Init.Prelude

open Lean Json

partial def readableJson (js: Json) : Json :=
   match js with
  | Json.obj m =>
   match m.toArray with
   | jsArr =>
     let keyVals := jsArr.map (fun ⟨k, v⟩ => (k, v))
     let purged := jsArr.filter (fun ⟨k, _⟩ => k != "type")
     let purged := purged.map fun ⟨k, v⟩ => (k, v)
     let typeVal? := keyVals.findSome? (fun (k, v) => if k == "type" then some v else none)
     match typeVal? with
     | some typeVal =>
       let type? := typeVal.getStr?.toOption
       match type? with
       | some type =>
          Json.mkObj [(type, readableJson (Json.mkObj purged.toList))]
       | none => js
     | none =>
       let keyValsModified := keyVals.map (fun (k,v) => (k, readableJson v))
       Json.mkObj keyValsModified.toList
  | Json.arr m => (m.map (fun x => readableJson x)).toJson
  | _ => js

#eval readableJson (json% {"type": "theorem-proof",
  "theorem": {"type": "val","win":"lose"},
  "proof" : "magic"
})

/-#eval json% {"theorem-proof":{
   "theorem": "hard",
   "proof" : "magic"
}}
-/

#eval readableJson (json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:even_prime",
        "claim": "The only even prime number is 2.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "An even number is any integer that is a multiple of 2."
          },
          {
            "type": "assert_statement",
            "claim": "A prime number is a natural number greater than 1 that has only two divisors: 1 and itself."
          },
          {
            "type": "assert_statement",
            "claim": "2 is even."
          },
          {
            "type": "assert_statement",
            "claim": "The only divisors of 2 are 1 and 2."
          },
          {
            "type": "assert_statement",
            "claim": "Therefore, 2 is prime."
          },
          {
            "type": "let_statement",
            "variable_name": "N",
            "variable_type": "integer",
            "properties": "even and greater than 2",
            "statement": "Let N be an even number greater than 2."
          },
          {
            "type": "assert_statement",
            "claim": "N is divisible by 2."
          },
          {
            "type": "assert_statement",
            "claim": "The divisors of N include 1, 2, and N."
          },
          {
            "type": "assert_statement",
            "claim": "Since N has at least three distinct divisors, it is not prime."
          },
          {
            "type": "conclude_statement",
            "claim": "2 is the only even prime number."
          }
        ]
      }
    ]
  }
})

/-YAML-like syntax for Lean-/
namespace Lean.YAML

/-YAML syntactic category-/
declare_syntax_cat yaml

/-YAML null syntax-/
syntax "null" : yaml

/-YAML true syntax-/
syntax "true" : yaml

/-YAML false syntax-/
syntax "false" : yaml

/-YAML string syntax-/
syntax str : yaml

/-YAML keys can be identifiers or strings-/
syntax yamlIdent := ident <|> str

/-YAML key-value pairs-/
syntax manyIndent(yamlIdent":" yaml linebreak): yaml

/-YAML syntax for lists-/
syntax manyIndent("-" yaml ppLine linebreak): yaml

/-Alternative YAML syntax for lists-/
syntax "[" yaml,* "]": yaml


def newstx : CoreM (Syntax) := `(yaml| -"key" : "val"
                                       - "key2" : "val2"
)

def stxprint : CoreM Format := do
  let stx ← newstx
  PrettyPrinter.ppCategory `yaml stx

#eval stxprint
