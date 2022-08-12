/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oliver Nash
-/
import Mathbin.Tactic.Abel

namespace Tactic

namespace Interactive

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A tactic for simplifying identities in not-necessarily-commutative rings.

An example:
```lean
example {R : Type*} [ring R] (a b c : R) : a * (b + c + c - b) = 2*a*c :=
by noncomm_ring
```
-/
unsafe def noncomm_ring :=
  sorry

-- Expand everything out.
-- Right associate all products.
-- Expand powers to numerals.
-- Replace multiplication by numerals with `zsmul`.
-- Pull `zsmul n` out the front so `abel` can see them.
-- Pull out negations.
add_tactic_doc
  { Name := "noncomm_ring", category := DocCategory.tactic, declNames := [`tactic.interactive.noncomm_ring],
    tags := ["arithmetic", "simplification", "decision procedure"] }

end Interactive

end Tactic

