import ProofWidgets.Component.Plotly

open Lean Parser
open scoped ProofWidgets.Jsx ProofWidgets.Json

/-!
# Analysis of Premise Selection Data

This notebook requires the data to be saved locally in the main directory. 
To download the data, run the following commands from the root directory of this project:

```bash
wget math.iisc.ac.in/~gadgil/data/codet5_small_test.zip
unzip codet5_small_test.zip
```
-/

structure PremiseSelectionRecord where
  «theorem» : String
  identifiers : List Name
  generated : List Name
  target_size : Nat
  prediction_size : Nat
  correct : List Name
  missed : List Name
  coverage : Float
  efficiency : Float
deriving FromJson, ToJson, Inhabited, Repr

/- 
section JsonlParsing

  def Parsec.parse (ρ : Parsec α) (s : String) : Except String α :=
    match ρ s.mkIterator with
      | .success _ res => .ok res
      | .error it err => .error s!"offset {repr it.i.byteIdx}: {err}"

  declare_syntax_cat jsonl
  syntax jso* : jsonl

  open Parsec in
  def Jsonl.Parser.any : Parsec <| Array Json := do
    ws
    let res ← many Json.Parser.any
    eof
    return res

  def sample := "
  {\"name\": \"Gilbert\", \"wins\": [[\"straight\", \"7♣\"], [\"one pair\", \"10♥\"]]}
  {\"name\": \"Alexa\", \"wins\": [[\"two pair\", \"4♠\"], [\"two pair\", \"9♠\"]]}
  {\"name\": \"May\", \"wins\": []}
  {\"name\": \"Deloise\", \"wins\": [[\"three of a kind\", \"5♣\"]]}"

  #eval Parsec.parse Jsonl.Parser.any sample

  #check String.mkIterator

  #check ForIn

end JsonlParsing 
-/


def data : IO <| Array PremiseSelectionRecord := do
  let raw ← IO.FS.readFile "rawdata/premises/identifiers/test_data.jsonl"
  let lines := raw.trim.split (· = '\n') |>.toArray |>.extract 2 5
  IO.println lines
  IO.ofExcept <| lines.mapM <| fun line ↦ do
    let obj ← Json.parse line
    fromJson? obj


#plot {
  data: [{
    x: [1, 1, 1, 2, 2],
    type: "histogram"
  }]
}