/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathbin.RingTheory.Localization.AtPrime
import Mathbin.RingTheory.DiscreteValuationRing

/-!
# Dedekind domains

This file defines an equivalent notion of a Dedekind domain (or Dedekind ring),
namely a Noetherian integral domain where the localization at all nonzero prime ideals is a DVR
(TODO: and shows that it is equivalent to the main definition).

## Main definitions

 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is Noetherian, and the localization at every nonzero prime ideal is a DVR.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type _) [CommRingₓ R] [CommRingₓ A] [IsDomain A] [Field K]

open nonZeroDivisors Polynomial

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (P «expr ≠ » («expr⊥»() : ideal A))
/-- A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure IsDedekindDomainDvr : Prop where
  IsNoetherianRing : IsNoetherianRing A
  is_dvr_at_nonzero_prime : ∀ (P) (_ : P ≠ (⊥ : Ideal A)), P.IsPrime → DiscreteValuationRing (Localization.AtPrime P)

