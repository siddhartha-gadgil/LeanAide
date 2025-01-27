import ProofWidgets.Component.Plotly

open Lean 
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

set_option maxRecDepth 1000000000

/-- A custom structure for premise selection data. -/
structure PremiseSelectionRecord where
  «theorem»       : String
  identifiers     : List Name
  generated       : List Name
  target_size     : Nat
  prediction_size : Nat
  correct         : List Name
  missed          : List Name
  coverage        : Float
  efficiency      : Float
deriving FromJson, ToJson, Inhabited, Repr

open Parsec in
/-- A parser for `.jsonl` files. -/
def Jsonl.Parser.any : Parsec <| Array Json := do
  ws
  let res ← many Json.Parser.anyCore
  eof
  return res

/-- The premise selection data. -/
def premiseData : Array PremiseSelectionRecord :=
  Option.get! <| EStateM.run' (s := ()) <| do
    let data ← IO.FS.readFile "rawdata/premises/identifiers/test_data.jsonl"
    let .success _ objs := Jsonl.Parser.any data.mkIterator | IO.throwServerError "Failed to parse file"
    IO.ofExcept <| objs.mapM fromJson? 

/-!
A plot of the distribution of the number of premises in the training data.
-/

#plot {
  data: [{
    -- x: $(premiseData.map (·.identifiers.length)),
    x: [1, 1, 1, 2, 2, 2, 3],
    type: "histogram"
  }]
}