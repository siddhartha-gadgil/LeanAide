/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Finite.Basic
import Mathbin.Data.Set.Finite

/-!
# Lemmas about `finite` and `set`s

In this file we prove two lemmas about `finite` and `set`s.

## Tags

finiteness, finite sets
-/


open Set

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w}

theorem Finite.Set.finite_of_finite_image (s : Set α) {f : α → β} (h : s.InjOn f) [Finite (f '' s)] : Finite s :=
  Finite.of_equiv _ (Equivₓ.ofBijective _ h.bij_on_image.Bijective).symm

theorem Finite.of_injective_finite_range {f : ι → α} (hf : Function.Injective f) [Finite (Range f)] : Finite ι :=
  Finite.of_injective (Set.rangeFactorization f) (hf.codRestrict _)

