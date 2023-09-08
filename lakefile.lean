import Lake
open Lake DSL

package leanaide {
  -- precompileModules := true
}

@[default_target]
lean_lib LeanAide {
}


@[default_target]
lean_exe bulkelab {
  supportInterpreter := true
}

lean_exe premiseless {
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



require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"
