import Lake
open Lake DSL

package LeanCodePrompts

lean_exe datagen{
  supportInterpreter := true
}

lean_exe bulkchk{
  supportInterpreter := true
}

lean_exe lib4chk{
  supportInterpreter := true
}


@[defaultTarget]
lean_exe batchcheck{
  supportInterpreter := true
}

lean_exe constnames{
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
