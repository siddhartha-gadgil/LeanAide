import LeanCodePrompts.TexToUnicode

def egTeX := "A formula is $\\alpha \\to \\beta := \\unknown$"

#eval teXToUnicode egTeX 

def checkTC : IO Nat := do
  let c ← teXCommands
  return c.size 

#eval checkTC
