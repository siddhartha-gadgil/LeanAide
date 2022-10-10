import Lean
import LeanCodePrompts.TexToUnicode
open Lean

def egTeX := "A formula is $\\alpha \\to \\beta := \\unknown$"

#eval teXToUnicode egTeX 

