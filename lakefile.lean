import Lake
open Lake DSL

package leanaide {
  -- precompileModules := true
}

@[default_target]
lean_lib LeanAide {
}


@[default_target]
lean_lib LeanCodePrompts {
}

lean_lib StatementAutoformalisation {
}

-- lean_lib CodeAction {
-- }

lean_lib TacticExtraction {
}

lean_lib CodeGen

lean_lib notes {
}

lean_exe datagen{
  supportInterpreter := true
}

lean_exe elabdatagen{
  supportInterpreter := true
}

@[default_target]
lean_exe bulkelab {
  supportInterpreter := true
}

@[default_target]
lean_exe translate {
  supportInterpreter := true
}

lean_exe ctranslate {
  supportInterpreter := true
}

lean_exe chkelab {
  supportInterpreter := true
}

lean_exe promptsgen {
  supportInterpreter := true
}

lean_exe thmextract {
  supportInterpreter := true
}

lean_exe premiseless {
  supportInterpreter := true
}


lean_exe bulkchk{
  supportInterpreter := true
}

lean_exe extras.lib4chk{
  supportInterpreter := true
}

lean_exe pickle_embeddings

lean_exe batchcheck{
  supportInterpreter := true
}

lean_exe nearest_embeddings

@[default_target]
lean_exe nearest_embeddings_full

lean_exe fetch_embeddings

lean_exe nearest_embeddings_test

lean_exe benchmark_embeddings

lean_exe lemma_suggest{
  supportInterpreter := true
}

lean_exe getpremises{
  supportInterpreter := true
}

lean_exe props{
  supportInterpreter := true
}


lean_exe testpremises{
  supportInterpreter := true
}

lean_exe dedup

lean_exe getdefns{
  supportInterpreter := true
}

lean_exe moduledeps{
  supportInterpreter := true
}

lean_exe chkthms{
  supportInterpreter := true
}

lean_exe writedocs {
  supportInterpreter := true
}

lean_exe writedescs {
  supportInterpreter := true
}

lean_exe writedescs_docs {
  supportInterpreter := true
}

lean_exe rewritedescs {
  supportInterpreter := true
}

lean_exe descweb {
  supportInterpreter := true
}

lean_exe descdetails {
  supportInterpreter := true
}

lean_exe roundtrip {
  supportInterpreter := true
}

lean_exe codegen {
  supportInterpreter := true
}

lean_exe termexamples {
  supportInterpreter := true
}

lean_lib examples

lean_exe cubecode {
  supportInterpreter := true
}

lean_lib Scratch {
}

lean_lib Extras

lean_exe extras.constnames{
  supportInterpreter := true
}

lean_exe extras.depnames{
  supportInterpreter := true
}


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.11.0"

require LeanSearchClient from git
  "https://github.com/leanprover-community/LeanSearchClient"@"v4.11.0"
