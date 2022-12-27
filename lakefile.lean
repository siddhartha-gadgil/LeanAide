import Lake
open Lake DSL

package leanaide {
  precompileModules := true
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

@[default_target]
lean_exe chkthms{
  supportInterpreter := true
}

lean_lib examples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"415530d447d2fc6557f3ed00caf409dd391e0756"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"120d183ebd8c91a7ebbcb754d49aa1d7f696ee48"

require aesop from git
  "https://github.com/JLimperg/aesop.git"@"3fa339ad9365fd3f42d452b65fb3c409c7623017"
