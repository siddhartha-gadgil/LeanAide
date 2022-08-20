import Lake
open Lake DSL

package LeanCodePrompts{
  precompileModules := true
}

lean_exe datagen{
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

@[defaultTarget]
lean_exe batchcheck{
  supportInterpreter := true
}

lean_exe constnames{
  supportInterpreter := true
}

lean_exe depnames{
  supportInterpreter := true
}


@[defaultTarget]
lean_exe chkthms{
  supportInterpreter := true
}

@[defaultTarget]
lean_lib examples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"master"

require aesop from git
  "https://github.com/JLimperg/aesop.git"@"master"
