/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.Complement
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.Index

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
-/


open BigOperators

variable {G : Type _} [Groupₓ G] {H : Subgroup G} {A : Type _} [CommGroupₓ A] (ϕ : H →* A)

namespace Subgroup

namespace LeftTransversals

open Finset MulAction

open Pointwise

variable (R S T : LeftTransversals (H : Set G)) [Fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
  let α := MemLeftTransversals.toEquiv S.2
  let β := MemLeftTransversals.toEquiv T.2
  ∏ q,
    ϕ
      ⟨(α q)⁻¹ * β q,
        QuotientGroup.left_rel_apply.mp <| Quotientₓ.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive]
theorem diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
  prod_mul_distrib.symm.trans
    (prod_congr rfl fun q hq =>
      (ϕ.map_mul _ _).symm.trans
        (congr_arg ϕ
          (by
            simp_rw [Subtype.ext_iff, coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left])))

@[to_additive]
theorem diff_self : diff ϕ T T = 1 :=
  mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive]
theorem diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
  inv_eq_of_mul_eq_one_right <| (diff_mul_diff ϕ S T S).trans <| diff_self ϕ S

@[to_additive]
theorem smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
  prod_bij' (fun q _ => g⁻¹ • q) (fun _ _ => mem_univ _)
    (fun _ _ =>
      congr_arg ϕ
        (by
          simp_rw [coe_mk, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc,
            inv_mul_cancel_leftₓ]))
    (fun q _ => g • q) (fun _ _ => mem_univ _) (fun q _ => smul_inv_smul g q) fun q _ => inv_smul_smul g q

end LeftTransversals

end Subgroup

namespace MonoidHom

variable [Fintype (G ⧸ H)]

open Subgroup Subgroup.LeftTransversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive
      "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,\nthe transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer : G →* A :=
  let T : LeftTransversals (H : Set G) := Inhabited.default
  { toFun := fun g => diff ϕ T (g • T),
    map_one' := by
      rw [one_smul, diff_self],
    map_mul' := fun g h => by
      rw [mul_smul, ← diff_mul_diff, smul_diff_smul] }

variable (T : LeftTransversals (H : Set G))

@[to_additive]
theorem transfer_def (g : G) : transfer ϕ g = diff ϕ T (g • T) := by
  rw [transfer, ← diff_mul_diff, ← smul_diff_smul, mul_comm, diff_mul_diff] <;> rfl

end MonoidHom

