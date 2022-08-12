/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Basic
import Mathbin.Data.Multiset.Basic
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Lemmas about group actions on big operators

Note that analogous lemmas for `module`s like `finset.sum_smul` appear in other files.
-/


variable {α β γ : Type _}

open BigOperators

section

variable [Monoidₓ α] [AddMonoidₓ β] [DistribMulAction α β]

theorem List.smul_sum {r : α} {l : List β} : r • l.Sum = (l.map ((· • ·) r)).Sum :=
  (DistribMulAction.toAddMonoidHom β r).map_list_sum l

end

section

variable [Monoidₓ α] [Monoidₓ β] [MulDistribMulAction α β]

theorem List.smul_prod {r : α} {l : List β} : r • l.Prod = (l.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_list_prod l

end

section

variable [Monoidₓ α] [AddCommMonoidₓ β] [DistribMulAction α β]

theorem Multiset.smul_sum {r : α} {s : Multiset β} : r • s.Sum = (s.map ((· • ·) r)).Sum :=
  (DistribMulAction.toAddMonoidHom β r).map_multiset_sum s

theorem Finset.smul_sum {r : α} {f : γ → β} {s : Finset γ} : (r • ∑ x in s, f x) = ∑ x in s, r • f x :=
  (DistribMulAction.toAddMonoidHom β r).map_sum f s

end

section

variable [Monoidₓ α] [CommMonoidₓ β] [MulDistribMulAction α β]

theorem Multiset.smul_prod {r : α} {s : Multiset β} : r • s.Prod = (s.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_multiset_prod s

theorem Finset.smul_prod {r : α} {f : γ → β} {s : Finset γ} : (r • ∏ x in s, f x) = ∏ x in s, r • f x :=
  (MulDistribMulAction.toMonoidHom β r).map_prod f s

end

