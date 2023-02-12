import Lean
import LeanInk.Analysis.Basic

open Lean


def inputFile : System.FilePath := "lake-packages"/"mathlib"/"Mathlib"/"Data"/"Int"/"Basic.lean"  

def tacticExtractionConfig : IO LeanInk.Configuration := return {
  inputFilePath := inputFile
  inputFileContents := ← IO.FS.readFile inputFile
  lakeFile := some ("lake-packages"/"leanInk"/"lakefile.lean")
  verbose := true
  prettifyOutput := true
  experimentalTypeInfo := true
  experimentalDocString := false
  experimentalSemanticType := false
}

