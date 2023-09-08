import Lake
open Lake DSL

package leanaide

@[default_target]
lean_lib LeanAide {
}


@[default_target]
lean_lib LeanCodePrompts {
}



@[default_target]
lean_exe bulkelab {
  supportInterpreter := true
}


lean_exe pickle_embeddings 

lean_exe nearest_embeddings

@[default_target]
lean_exe nearest_embeddings_full


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
