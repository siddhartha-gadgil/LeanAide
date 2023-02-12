import Lean
import LeanInk.Analysis.Basic

open Lean


def inputFile : System.FilePath := "lake-packages"/"mathlib"/"Mathlib"/"Data"/"Int"/"Dvd"/"Pow.lean"

#eval inputFile.pathExists

def tacticExtractionConfig : IO LeanInk.Configuration := return {
  inputFilePath := inputFile
  inputFileContents := ← IO.FS.readFile inputFile
  lakeFile := some $ "lake-packages"/"leanInk"/"lakefile.lean"
  verbose := true
  prettifyOutput := true
  experimentalTypeInfo := true
  experimentalDocString := false
  experimentalSemanticType := false
}

def tacticData : IO <| List LeanInk.Analysis.Sentence := do
  let config ← tacticExtractionConfig
  let result ← LeanInk.Analysis.analyzeInput.run config 
  return result.sentences

def tacticDataStrings : IO <| List String := do
  let tacs ← tacticData
  return tacs.map toString 
  -- TODO replace the default `toString` instance with a more descriptive one

#eval tacticDataStrings