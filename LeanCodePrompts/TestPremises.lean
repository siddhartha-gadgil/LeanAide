import LeanCodePrompts.Premises
import Mathlib
open Lean Meta

#check Nat.exists_infinite_primes
#check Nat.minFac_le_div

def test : MetaM Unit := do
  let names := [``Nat.exists_infinite_primes, ``Nat.minFac_le_div]
  CorePremiseData.writeTest names

-- times out, should run from command line