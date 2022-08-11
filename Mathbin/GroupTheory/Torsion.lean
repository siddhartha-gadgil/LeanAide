/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.GroupTheory.Exponent
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.GroupTheory.PGroup
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.GroupTheory.Submonoid.Operations

/-!
# Torsion groups

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `monoid.is_torsion` a predicate asserting `G` is torsion, i.e. that all
  elements are of finite order.
* `comm_group.torsion G`, the torsion subgroup of an abelian group `G`
* `comm_monoid.torsion G`, the above stated for commutative monoids
* `monoid.is_torsion_free`, asserting no nontrivial elements have finite order in `G`
* `add_monoid.is_torsion` and `add_monoid.is_torsion_free` the additive versions of the above

## Implementation

All torsion monoids are really groups (which is proven here as `monoid.is_torsion.group`), but since
the definition can be stated on monoids it is implemented on `monoid` to match other declarations in
the group theory library.

## Tags

periodic group, aperiodic group, torsion subgroup, torsion abelian group

## Future work

* generalize to π-torsion(-free) groups for a set of primes π
* free, free solvable and free abelian groups are torsion free
* complete direct and free products of torsion free groups are torsion free
* groups which are residually finite p-groups with respect to 2 distinct primes are torsion free
-/


variable {G H : Type _}

namespace Monoidₓ

variable (G) [Monoidₓ G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def IsTorsion :=
  ∀ g : G, IsOfFinOrder g

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[simp, to_additive "An additive monoid is not a torsion monoid if it has an element of infinite order."]
theorem not_is_torsion_iff : ¬IsTorsion G ↔ ∃ g : G, ¬IsOfFinOrder g := by
  rw [is_torsion, not_forall]

end Monoidₓ

open Monoidₓ

/-- Torsion monoids are really groups. -/
@[to_additive "Torsion additive monoids are really additive groups"]
noncomputable def IsTorsion.group [Monoidₓ G] (tG : IsTorsion G) : Groupₓ G :=
  { ‹Monoidₓ G› with inv := fun g => g ^ (orderOf g - 1),
    mul_left_inv := fun g => by
      erw [← pow_succ'ₓ, tsub_add_cancel_of_le, pow_order_of_eq_one]
      exact order_of_pos' (tG g) }

section Groupₓ

variable [Groupₓ G] {N : Subgroup G} [Groupₓ H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
theorem IsTorsion.subgroup (tG : IsTorsion G) (H : Subgroup G) : IsTorsion H := fun h =>
  (is_of_fin_order_iff_coe H.toSubmonoid h).mpr <| tG h

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive AddIsTorsion.of_surjective "The image of a surjective additive torsion group homomorphism is torsion."]
theorem IsTorsion.of_surjective {f : G →* H} (hf : Function.Surjective f) (tG : IsTorsion G) : IsTorsion H := fun h =>
  by
  obtain ⟨g, hg⟩ := hf h
  rw [← hg]
  exact f.is_of_fin_order (tG g)

/-- Torsion groups are closed under extensions. -/
@[to_additive AddIsTorsion.extension_closed "Additive torsion groups are closed under extensions."]
theorem IsTorsion.extension_closed {f : G →* H} (hN : N = f.ker) (tH : IsTorsion H) (tN : IsTorsion N) : IsTorsion G :=
  fun g =>
  (is_of_fin_order_iff_pow_eq_one _).mpr <| by
    obtain ⟨ngn, ngnpos, hngn⟩ := (is_of_fin_order_iff_pow_eq_one _).mp (tH <| f g)
    have hmem := f.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
    lift g ^ ngn to N using hN.symm ▸ hmem with gn
    obtain ⟨nn, nnpos, hnn⟩ := (is_of_fin_order_iff_pow_eq_one _).mp (tN gn)
    exact
      ⟨ngn * nn, mul_pos ngnpos nnpos, by
        rw [pow_mulₓ, ← h, ← Subgroup.coe_pow, hnn, Subgroup.coe_one]⟩

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive AddIsTorsion.quotient_iff "The image of a quotient is additively torsion iff the group is torsion."]
theorem IsTorsion.quotient_iff {f : G →* H} (hf : Function.Surjective f) (hN : N = f.ker) (tN : IsTorsion N) :
    IsTorsion H ↔ IsTorsion G :=
  ⟨fun tH => IsTorsion.extension_closed hN tH tN, fun tG => IsTorsion.of_surjective hf tG⟩

/-- If a group exponent exists, the group is torsion. -/
@[to_additive ExponentExists.is_add_torsion "If a group exponent exists, the group is additively torsion."]
theorem ExponentExists.is_torsion (h : ExponentExists G) : IsTorsion G := fun g => by
  obtain ⟨n, npos, hn⟩ := h
  exact (is_of_fin_order_iff_pow_eq_one g).mpr ⟨n, npos, hn g⟩

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive IsAddTorsion.exponent_exists "The group exponent exists for any bounded additive torsion group."]
theorem IsTorsion.exponent_exists (tG : IsTorsion G) (bounded : (Set.Range fun g : G => orderOf g).Finite) :
    ExponentExists G :=
  exponent_exists_iff_ne_zero.mpr <|
    (exponent_ne_zero_iff_range_order_of_finite fun g => order_of_pos' (tG g)).mpr bounded

/-- Finite groups are torsion groups. -/
@[to_additive is_add_torsion_of_fintype "Finite additive groups are additive torsion groups."]
theorem is_torsion_of_fintype [Fintype G] : IsTorsion G :=
  ExponentExists.is_torsion <| exponent_exists_iff_ne_zero.mpr exponent_ne_zero_of_fintype

end Groupₓ

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type _) [AddCommMonoidₓ M]

namespace AddMonoidₓ

/-- A module whose scalars are additively torsion is additively torsion. -/
theorem IsTorsion.module_of_torsion [Semiringₓ R] [Module R M] (tR : IsTorsion R) : IsTorsion M := fun f =>
  (is_of_fin_add_order_iff_nsmul_eq_zero _).mpr <| by
    obtain ⟨n, npos, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero _).mp (tR 1)
    exact
      ⟨n, npos, by
        simp only [← nsmul_eq_smul_cast R _ f, nsmul_one, ← hn, ← zero_smul]⟩

/-- A module with a finite ring of scalars is additively torsion. -/
theorem IsTorsion.module_of_fintype [Ringₓ R] [Fintype R] [Module R M] : IsTorsion M :=
  (is_add_torsion_of_fintype : IsTorsion R).module_of_torsion _ _

end AddMonoidₓ

end Module

section CommMonoidₓ

variable (G) [CommMonoidₓ G]

namespace CommMonoidₓ

/-- The torsion submonoid of a commutative monoid.

(Note that by `monoid.is_torsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive add_torsion "The torsion submonoid of an additive commutative monoid."]
def torsion : Submonoid G where
  Carrier := { x | IsOfFinOrder x }
  one_mem' := is_of_fin_order_one
  mul_mem' := fun _ _ hx hy => hx.mul hy

variable {G}

/-- Torsion submonoids are torsion. -/
@[to_additive "Additive torsion submonoids are additively torsion."]
theorem torsion.is_torsion : is_torsion <| torsion G := fun ⟨_, n, npos, hn⟩ =>
  ⟨n, npos,
    Subtype.ext <| by
      rw [mul_left_iterate, _root_.mul_one, Submonoid.coe_pow, Subtype.coe_mk, Submonoid.coe_one,
        (is_periodic_pt_mul_iff_pow_eq_one _).mp hn]⟩

variable (G) (p : ℕ) [hp : Fact p.Prime]

include hp

/-- The `p`-primary component is the submonoid of elements with order prime-power of `p`. -/
@[to_additive "The `p`-primary component is the submonoid of elements with additive order prime-power of `p`.", simps]
def primaryComponent : Submonoid G where
  Carrier := { g | ∃ n : ℕ, orderOf g = p ^ n }
  one_mem' :=
    ⟨0, by
      rw [pow_zeroₓ, order_of_one]⟩
  mul_mem' := fun g₁ g₂ hg₁ hg₂ =>
    exists_order_of_eq_prime_pow_iff.mpr <| by
      obtain ⟨m, hm⟩ := exists_order_of_eq_prime_pow_iff.mp hg₁
      obtain ⟨n, hn⟩ := exists_order_of_eq_prime_pow_iff.mp hg₂
      exact
        ⟨m + n, by
          rw [mul_powₓ, pow_addₓ, pow_mulₓ, hm, one_pow, Monoidₓ.one_mul, mul_comm, pow_mulₓ, hn, one_pow]⟩

variable {G} {p}

/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive "Elements of the `p`-primary component have additive order `p^n` for some `n`"]
theorem primaryComponent.exists_order_of_eq_prime_pow (g : CommMonoidₓ.primaryComponent G p) :
    ∃ n : ℕ, orderOf g = p ^ n := by
  simpa [← primary_component] using g.property

/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive "The `p`- and `q`-primary components are disjoint for `p ≠ q`."]
theorem primaryComponent.disjoint {p' : ℕ} [hp' : Fact p'.Prime] (hne : p ≠ p') :
    Disjoint (CommMonoidₓ.primaryComponent G p) (CommMonoidₓ.primaryComponent G p') :=
  Submonoid.disjoint_def.mpr fun g hgp hgp' => by
    obtain ⟨n, hn⟩ := primary_component.exists_order_of_eq_prime_pow ⟨g, set_like.mem_coe.mp hgp⟩
    obtain ⟨n', hn'⟩ := primary_component.exists_order_of_eq_prime_pow ⟨g, set_like.mem_coe.mp hgp'⟩
    have := mt (eq_of_prime_pow_eq (nat.prime_iff.mp hp.out) (nat.prime_iff.mp hp'.out))
    simp only [← not_forall, ← exists_prop, ← not_ltₓ, ← le_zero_iff, ← and_imp] at this
    rw [← order_of_submonoid, SetLike.coe_mk] at hn hn'
    have hnzero := this (hn.symm.trans hn') hne
    rwa [hnzero, pow_zeroₓ, order_of_eq_one_iff] at hn

end CommMonoidₓ

open CommMonoidₓ (torsion)

namespace Monoidₓ.IsTorsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[simp, to_additive "The additive torsion submonoid of an additive torsion monoid is `⊤`."]
theorem torsion_eq_top (tG : IsTorsion G) : torsion G = ⊤ := by
  ext <;> tauto

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive "An additive torsion monoid is isomorphic to its torsion submonoid.", simps]
def torsionMulEquiv (tG : IsTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv

end Monoidₓ.IsTorsion

/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[simp,
  to_additive AddCommMonoidₓ.Torsion.ofTorsion
      "Additive torsion submonoids of an additive torsion submonoid are isomorphic to the submonoid."]
def Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  Monoidₓ.IsTorsion.torsionMulEquiv CommMonoidₓ.torsion.is_torsion

end CommMonoidₓ

section CommGroupₓ

variable (G) [CommGroupₓ G]

namespace CommGroupₓ

/-- The torsion subgroup of an abelian group. -/
@[to_additive "The torsion subgroup of an additive abelian group."]
def torsion : Subgroup G :=
  { CommMonoidₓ.torsion G with inv_mem' := fun x => IsOfFinOrder.inv }

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive add_torsion_eq_add_torsion_submonoid
      "The additive torsion submonoid of an abelian group equals the torsion subgroup as a submonoid."]
theorem torsion_eq_torsion_submonoid : CommMonoidₓ.torsion G = (torsion G).toSubmonoid :=
  rfl

variable (p : ℕ) [hp : Fact p.Prime]

include hp

/-- The `p`-primary component is the subgroup of elements with order prime-power of `p`. -/
@[to_additive "The `p`-primary component is the subgroup of elements with additive order prime-power of `p`.", simps]
def primaryComponent : Subgroup G :=
  { CommMonoidₓ.primaryComponent G p with inv_mem' := fun g ⟨n, hn⟩ => ⟨n, (order_of_inv g).trans hn⟩ }

variable {G} {p}

/-- The `p`-primary component is a `p` group. -/
theorem primaryComponent.is_p_group : IsPGroup p <| primaryComponent G p := fun g =>
  (propext exists_order_of_eq_prime_pow_iff.symm).mpr (CommMonoidₓ.primaryComponent.exists_order_of_eq_prime_pow g)

end CommGroupₓ

end CommGroupₓ

namespace Monoidₓ

variable (G) [Monoidₓ G]

/-- A predicate on a monoid saying that only 1 is of finite order. -/
@[to_additive "A predicate on an additive monoid saying that only 0 is of finite order."]
def IsTorsionFree :=
  ∀ g : G, g ≠ 1 → ¬IsOfFinOrder g

/-- A nontrivial monoid is not torsion-free if any nontrivial element has finite order. -/
@[simp, to_additive "An additive monoid is not torsion free if any nontrivial element has finite order."]
theorem not_is_torsion_free_iff : ¬IsTorsionFree G ↔ ∃ g : G, g ≠ 1 ∧ IsOfFinOrder g := by
  simp_rw [is_torsion_free, Ne.def, not_forall, not_not, exists_prop]

end Monoidₓ

section Groupₓ

open Monoidₓ

variable [Groupₓ G]

/-- A nontrivial torsion group is not torsion-free. -/
@[to_additive AddMonoidₓ.IsTorsion.not_torsion_free "A nontrivial additive torsion group is not torsion-free."]
theorem IsTorsion.not_torsion_free [hN : Nontrivial G] : IsTorsion G → ¬IsTorsionFree G := fun tG =>
  (not_is_torsion_free_iff _).mpr <| by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, hx, tG x⟩

/-- A nontrivial torsion-free group is not torsion. -/
@[to_additive AddMonoidₓ.IsTorsionFree.not_torsion "A nontrivial torsion-free additive group is not torsion."]
theorem IsTorsionFree.not_torsion [hN : Nontrivial G] : IsTorsionFree G → ¬IsTorsion G := fun tfG =>
  (not_is_torsion_iff _).mpr <| by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, (tfG x) hx⟩

/-- Subgroups of torsion-free groups are torsion-free. -/
@[to_additive "Subgroups of additive torsion-free groups are additively torsion-free."]
theorem IsTorsionFree.subgroup (tG : IsTorsionFree G) (H : Subgroup G) : IsTorsionFree H := fun h hne =>
  (is_of_fin_order_iff_coe H.toSubmonoid h).Not.mpr <|
    tG h <| by
      norm_cast <;> simp [← hne, ← not_false_iff]

/-- Direct products of torsion free groups are torsion free. -/
@[to_additive AddMonoidₓ.IsTorsionFree.prod "Direct products of additive torsion free groups are torsion free."]
theorem IsTorsionFree.prod {η : Type _} {Gs : η → Type _} [∀ i, Groupₓ (Gs i)] (tfGs : ∀ i, IsTorsionFree (Gs i)) :
    is_torsion_free <| ∀ i, Gs i := fun w hne h =>
  hne <| funext fun i => not_not.mp <| mt (tfGs i (w i)) <| not_not.mpr <| h.apply i

end Groupₓ

section CommGroupₓ

open Monoidₓ (IsTorsionFree)

open CommGroupₓ (torsion)

variable (G) [CommGroupₓ G]

/-- Quotienting a group by its torsion subgroup yields a torsion free group. -/
@[to_additive AddIsTorsionFree.quotient_torsion
      "Quotienting a group by its additive torsion subgroup yields an additive torsion free group."]
theorem IsTorsionFree.quotient_torsion : is_torsion_free <| G ⧸ torsion G := fun g hne hfin =>
  hne <| by
    induction g using QuotientGroup.induction_on'
    obtain ⟨m, mpos, hm⟩ := (is_of_fin_order_iff_pow_eq_one _).mp hfin
    obtain ⟨n, npos, hn⟩ := (is_of_fin_order_iff_pow_eq_one _).mp ((QuotientGroup.eq_one_iff _).mp hm)
    exact
      (QuotientGroup.eq_one_iff g).mpr
        ((is_of_fin_order_iff_pow_eq_one _).mpr ⟨m * n, mul_pos mpos npos, (pow_mulₓ g m n).symm ▸ hn⟩)

end CommGroupₓ

