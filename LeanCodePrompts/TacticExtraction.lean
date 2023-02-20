import Lean
import LeanInk.Analysis.Basic

open Lean Elab


def inputFile : System.FilePath := "LeanCodePrompts" / "TacticExtractionTest.lean"

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

-- modified from `LeanInk` source
open LeanInk in
def analyzeInput : AnalysisM Analysis.AnalysisResult := do
  let config ← tacticExtractionConfig 
  let context := Parser.mkInputContext config.inputFileContents config.inputFileName
  let (header, state, messages) ← Parser.parseHeader context
  -- doc-gen: Lake already configures us via LEAN_PATH
  -- initializeSearchPaths header config
    let options := Options.empty 
                    |>.setBool `trace.Elab.info true
                    |>.setBool `tactic.simp.trace true
  let (environment, messages) ← processHeader header options messages context 0
  logInfo s!"Header: {environment.header.mainModule}"
  logInfo s!"Header: {environment.header.moduleNames}"
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        let _ ← logError (← msg.toString)
    throw <| IO.userError "Errors during import; aborting"
  let commandState := Analysis.configureCommandState environment messages
  let s ← IO.processCommands context state commandState
  let result ← Analysis.resolveTacticList s.commandState.infoState.trees.toList
  let messages := s.commandState.messages.msgs.toList.filter (λ m => m.endPos.isSome )
  return ← result.insertMessages messages context.fileMap

def tacticData : IO <| List LeanInk.Analysis.Sentence := do
  let config ← tacticExtractionConfig
  let result ← analyzeInput.run config 
  return result.sentences

instance : ToString LeanInk.Analysis.Goal where
  toString goal := toString goal.conclusion

instance : ToString LeanInk.Analysis.Tactic where
  toString t := toString t.goalsAfter

instance (priority := high) : ToString LeanInk.Analysis.Sentence where
  toString
    | .tactic t => s!"[TACTIC:{t.headPos}-{t.tailPos}]" ++ toString t
    | .message m => "[MESSAGE]" ++ m.msg

def tacticDataStrings : IO <| List String := do
  let tacs ← tacticData
  return tacs.map toString 
  -- TODO replace the default `toString` instance with a more descriptive one