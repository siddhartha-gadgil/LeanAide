import LeanAideCore.Aides.Toml

open Lean

namespace LeanAide

#eval loadTomlAsJson? "lakefile.toml"

#eval loadTomlAsJson? "leanaide.toml"

end LeanAide
