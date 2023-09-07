import Lake
open Lake DSL

package leanaide {
  -- precompileModules := true
}

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


lean_exe thmextract {
  supportInterpreter := true
}

lean_exe premiseless {
  supportInterpreter := true
}


lean_exe bulkchk{
  supportInterpreter := true
}

lean_exe extras.lib4chk{
  supportInterpreter := true
}

lean_exe pickle_embeddings 

lean_exe batchcheck{
  supportInterpreter := true
}

lean_exe nearest_embeddings

@[default_target]
lean_exe nearest_embeddings_full

lean_exe nearest_embeddings_test

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


lean_lib examples

lean_lib LeanAideScratch

lean_lib Extras

lean_exe extras.constnames{
  supportInterpreter := true
}

lean_exe extras.depnames{
  supportInterpreter := true
}


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require «lean-slides» from git "https://github.com/0art0/lean-slides"@"master"
