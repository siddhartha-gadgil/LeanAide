import Lake
open Lake DSL

package LeanCodePrompts{
  precompileModules := true
}

@[default_target]
lean_lib LeanCodePrompts {
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
  "https://github.com/leanprover-community/mathlib4.git"@"7e81227d4766fa23e798ac82f36f935aea6d4251"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"16d6ffd0bf9d2300388c11b7c3c8be1e7c3e73a3"

require aesop from git
  "https://github.com/JLimperg/aesop.git"@"3fa339ad9365fd3f42d452b65fb3c409c7623017"
