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
  "https://github.com/leanprover-community/mathlib4.git"@"3d525b8da3d7db985860a51a3b8d050ad62f5207"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"cce383df712a48f0c773a10e8c3295164fbb9f57"
