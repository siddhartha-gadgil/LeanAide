import LeanCodePrompts.Session
import Mathlib
open LeanAide.Translate Session

#check Session

#session pt144 := do
  addDefByName ``Multiset.esymm
  addDefByName ``iSup
  addDefByName ``SupSet.sSup
  consider "Let  $s_k (a_1, a_2, \\dots, a_n)$ denote the $k$-th elementary  symmetric function. Show that the supremum $M_k$  of $$\\frac{s_k (a_1, a_2, \\dots, a_n)}{(s_1 (a_1, a_2, \\dots, a_n))^k}$$ across all $n$-tuples $(a_1, a_2, \\dots, a_n)$ s is $\\frac{1}{k!}$."
  let translator ← getTranslator
  let (msgs, _) ← translator.getMessages (← text)
  -- say msgs
  translateText

open Parser

-- open Lean Meta Elab Term
-- def expandExists (stx: Syntax) :
--   MetaM <| Option Syntax := do
--   match stx with
--   | `(∃! ($xs* : $type), $value) =>
--     let xs' := xs.toList
--     let x := xs'[0]!
--     let eg ←
--       `(bracketedBinder|($x : $type))
--     sorry
--   | _  => return none
