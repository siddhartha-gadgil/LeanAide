import Lake
open Lake DSL

package LeanCodePrompts{
  supportInterpreter := true
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require mathlib3port from git
  "https://github.com/leanprover-community/mathlib3port.git"@"master"
