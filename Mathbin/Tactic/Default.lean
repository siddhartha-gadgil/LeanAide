/-
This file imports many useful tactics ("the kitchen sink").

You can use `import tactic` at the beginning of your file to get everything.
(Although you may want to strip things down when you're polishing.)

Because this file imports some complicated tactics, it has many transitive dependencies
(which of course may not use `import tactic`, and must import selectively).

As (non-exhaustive) examples, these includes things like:
* algebra.group_power
* algebra.order.ring
* data.rat
* data.nat.prime
* data.list.perm
* data.set.lattice
* data.equiv.encodable.basic
* order.complete_lattice
-/
import Mathbin.Tactic.Basic
import Mathbin.Tactic.Abel
import Mathbin.Tactic.RingExp
import Mathbin.Tactic.NoncommRing
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.Omega.Default
import Mathbin.Tactic.Tfae
import Mathbin.Tactic.ApplyFun
import Mathbin.Tactic.IntervalCases
import Mathbin.Tactic.ReassocAxiom
import Mathbin.Tactic.Slice
import Mathbin.Tactic.SubtypeInstance
import Mathbin.Tactic.DeriveFintype
import Mathbin.Tactic.Group
import Mathbin.Tactic.CancelDenoms
import Mathbin.Tactic.Zify
import Mathbin.Tactic.Transport
import Mathbin.Tactic.UnfoldCases
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.LinearCombination
import Mathbin.Tactic.Polyrith

-- ensure basic tactics are available
-- ensure basic tactics are available
-- most likely useful only for category_theory
-- most likely useful only for category_theory
