/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathbin.Tactic.Ring
import Mathbin.Tactic.DocCommands

/-!
# `group`

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`zpow` which takes a group element and an
integer), then simplify the exponents using the `ring` tactic. The process needs to be repeated
since `ring` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

## Tags

group_theory
-/


-- The next four lemmas are not general purpose lemmas, they are intended for use only by
-- the `group` tactic.
@[to_additive]
theorem Tactic.Group.zpow_trick {G : Type _} [Groupₓ G] (a b : G) (n m : ℤ) : a * b ^ n * b ^ m = a * b ^ (n + m) := by
  rw [mul_assoc, ← zpow_add]

@[to_additive]
theorem Tactic.Group.zpow_trick_one {G : Type _} [Groupₓ G] (a b : G) (m : ℤ) : a * b * b ^ m = a * b ^ (m + 1) := by
  rw [mul_assoc, mul_self_zpow]

@[to_additive]
theorem Tactic.Group.zpow_trick_one' {G : Type _} [Groupₓ G] (a b : G) (n : ℤ) : a * b ^ n * b = a * b ^ (n + 1) := by
  rw [mul_assoc, mul_zpow_self]

@[to_additive]
theorem Tactic.Group.zpow_trick_sub {G : Type _} [Groupₓ G] (a b : G) (n m : ℤ) :
    a * b ^ n * b ^ -m = a * b ^ (n - m) := by
  rw [mul_assoc, ← zpow_add] <;> rfl

namespace Tactic

setup_tactic_parser

open Tactic.SimpArgType Interactive Tactic.Group

/-- Auxiliary tactic for the `group` tactic. Calls the simplifier only. -/
unsafe def aux_group₁ (locat : Loc) : tactic Unit :=
  simp_core {  } skip true
      [expr (pquote.1 commutator_element_def), expr (pquote.1 mul_oneₓ), expr (pquote.1 one_mulₓ),
        expr (pquote.1 one_pow), expr (pquote.1 one_zpow), expr (pquote.1 sub_self), expr (pquote.1 add_neg_selfₓ),
        expr (pquote.1 neg_add_selfₓ), expr (pquote.1 neg_negₓ), expr (pquote.1 tsub_self),
        expr (pquote.1 Int.coe_nat_add), expr (pquote.1 Int.coe_nat_mul), expr (pquote.1 Int.coe_nat_zero),
        expr (pquote.1 Int.coe_nat_one), expr (pquote.1 Int.coe_nat_bit0), expr (pquote.1 Int.coe_nat_bit1),
        expr (pquote.1 Int.mul_neg_eq_neg_mul_symm), expr (pquote.1 Int.neg_mul_eq_neg_mul_symm),
        symm_expr (pquote.1 zpow_coe_nat), symm_expr (pquote.1 zpow_neg_one), symm_expr (pquote.1 zpow_mul),
        symm_expr (pquote.1 zpow_add_one), symm_expr (pquote.1 zpow_one_add), symm_expr (pquote.1 zpow_add),
        expr (pquote.1 mul_zpow_neg_one), expr (pquote.1 zpow_zero), expr (pquote.1 mul_zpow),
        symm_expr (pquote.1 mul_assoc), expr (pquote.1 zpow_trick), expr (pquote.1 zpow_trick_one),
        expr (pquote.1 zpow_trick_one'), expr (pquote.1 zpow_trick_sub), expr (pquote.1 Tactic.Ring.hornerₓ)]
      [] locat >>
    skip

/-- Auxiliary tactic for the `group` tactic. Calls `ring_nf` to normalize exponents. -/
unsafe def aux_group₂ (locat : Loc) : tactic Unit :=
  ring_nf none Tactic.Ring.NormalizeMode.raw locat

end Tactic

namespace Tactic.Interactive

setup_tactic_parser

open Tactic

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h, -- normalizes `h` which becomes `h : c = d`
  rw h,       -- the goal is now `a*d*d⁻¹ = a`
  group,      -- which then normalized and closed
end
```
-/
unsafe def group (locat : parse location) : tactic Unit := do
  when locat sorry
  try (aux_group₁ locat)
  repeat (andthen (aux_group₂ locat) (aux_group₁ locat))

end Tactic.Interactive

add_tactic_doc
  { Name := "group", category := DocCategory.tactic, declNames := [`tactic.interactive.group],
    tags := ["decision procedure", "simplification"] }

