import Lake
open Lake DSL

package leanaide {
  precompileModules := true
}

@[default_target]
lean_lib LeanAide {
}


@[default_target]
lean_lib LeanCodePrompts {
}

@[default_target]
lean_lib StatementAutoformalisation {
}

@[default_target]
lean_lib CodeAction {
}

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
lean_exe chkelab {
  supportInterpreter := true
}

@[default_target]
lean_exe promptsgen {
  supportInterpreter := true
}

lean_exe thmextract {
  supportInterpreter := true
}


lean_exe bulkchk{
  supportInterpreter := true
}

lean_exe lib4chk{
  supportInterpreter := true
}

lean_exe annotatekwds{
  supportInterpreter := false
}


lean_exe batchcheck{
  supportInterpreter := true
}

lean_exe constnames{
  supportInterpreter := true
}

lean_exe depnames{
  supportInterpreter := true
}

lean_exe getpremises{
  supportInterpreter := true
}

lean_exe testpremises{
  supportInterpreter := true
}

lean_exe getdefns{
  supportInterpreter := true
}

lean_exe moduledeps{
  supportInterpreter := true
}

@[default_target]
lean_exe chkthms{
  supportInterpreter := true
}

lean_lib examples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require leanInk from git
  "https://github.com/leanprover/LeanInk"@"main"

-- require aesop from git
--   "https://github.com/JLimperg/aesop.git"@"master"
