import Lake
open Lake DSL

package LeanCodePrompts{
  precompileModules := true
}

lean_lib LeanCodePrompts {
}

lean_exe datagen{
  supportInterpreter := true
}

lean_exe elabdatagen{
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
  "https://github.com/leanprover-community/mathlib4.git"@"aa176e5da516f57b502ebdfb633f39b392dda333"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"1749724b7917aeea55830be63bdc0aee6587451c"
