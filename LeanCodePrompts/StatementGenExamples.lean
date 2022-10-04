import Mathbin.All

import LeanCodePrompts.StatementGen

def statement := "Every subgroup of a group is normal."

#eval showContinuationExprs statement "(G: Type u)[group G]"

#eval showLogs 1

def statement2 := "Every two prime numbers are coprime."

#eval showContinuationExprs statement2 "(n m: Nat)(h: nat.prime n)"

#eval showLogs 1

#eval showContinuationExprs statement2 "(n m: Nat)(h: nat.prime n) (h' : nat.prime m)"

#eval showContinuationExprs statement2 "(n m: Nat)(h: nat.prime n) (h' : odd m)"

#eval showDocContinuationExprs statement2 

#eval showLogs 1

#eval showDocContinuationExprs statement

def egThm := "{a b c : ℕ} (hp : nat.prime a) (habc : a * b * c = 1) : b * c = 1 "

#eval polyElabThmTrans egThm

#eval showSectionContinuationExprs statement2 "(n m: Nat)(h: nat.prime n) (h' : nat.prime m)"


