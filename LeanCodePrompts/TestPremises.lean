import LeanAide.Premises
import Mathlib
open Lean Meta

#check Nat.exists_infinite_primes
#check Nat.minFac_le_div

def test : MetaM Unit := do
  let names := [``Nat.exists_infinite_primes, ``Nat.minFac_le_div]
  CorePremiseData.writeTest names


#eval depths ``Nat.totient_eq_card_lt_and_coprime

#eval depths ``Nat.succ

-- #eval propList

-- times out, should run from command line