import Lake
open Lake DSL

package LeanCodePrompts{
  precompileModules := true
}

@[defaultTarget]
lean_lib LeanCodePrompts {
}

lean_exe datagen{
  supportInterpreter := true
}

lean_exe elabdatagen{
  supportInterpreter := true
}

@[defaultTarget]
lean_exe bulkelab {
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

@[defaultTarget]
lean_exe chkthms{
  supportInterpreter := true
}

lean_lib examples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"380fbe124708314e7dcd6c3b8f41adffd5046c44"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"04ead7ffe5221b7c752fd2a7256244d61b01ac83"
