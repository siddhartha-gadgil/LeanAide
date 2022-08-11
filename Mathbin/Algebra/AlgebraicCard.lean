/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.Data.Polynomial.Cardinal
import Mathbin.RingTheory.Algebraic

/-!
### Cardinality of algebraic numbers

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `# polynomial R * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `liouville.is_transcendental`.
-/


universe u v

open Cardinal Polynomial

open Cardinal

namespace Algebraic

theorem aleph_0_le_cardinal_mk_of_char_zero (R A : Type _) [CommRingₓ R] [IsDomain R] [Ringₓ A] [Algebra R A]
    [CharZero A] : ℵ₀ ≤ # { x : A // IsAlgebraic R x } :=
  @mk_le_of_injective (ULift ℕ) { x : A | IsAlgebraic R x } (fun n => ⟨_, is_algebraic_nat n.down⟩) fun m n hmn => by
    simpa using hmn

section lift

variable (R : Type u) (A : Type v) [CommRingₓ R] [CommRingₓ A] [IsDomain A] [Algebra R A] [NoZeroSmulDivisors R A]

theorem cardinal_mk_lift_le_mul :
    Cardinal.lift.{u, v} (# { x : A // IsAlgebraic R x }) ≤ Cardinal.lift.{v, u} (# (Polynomial R)) * ℵ₀ := by
  rw [← mk_ulift, ← mk_ulift]
  let g : ULift.{u} { x : A | IsAlgebraic R x } → ULift.{v} (Polynomial R) := fun x => ULift.up (Classical.some x.1.2)
  apply Cardinal.mk_le_mk_mul_of_mk_preimage_le g fun f => _
  suffices Fintype (g ⁻¹' {f}) by
    exact @mk_le_aleph_0 _ (@Fintype.toEncodable _ this)
  by_cases' hf : f.1 = 0
  · convert Set.fintypeEmpty
    apply Set.eq_empty_iff_forall_not_mem.2 fun x hx => _
    simp only [← Set.mem_preimage, ← Set.mem_singleton_iff] at hx
    apply_fun ULift.down  at hx
    rw [hf] at hx
    exact (Classical.some_spec x.1.2).1 hx
    
  let h : g ⁻¹' {f} → f.down.root_set A := fun x =>
    ⟨x.1.1.1,
      (mem_root_set_iff hf x.1.1.1).2
        (by
          have key' : g x = f := x.2
          simp_rw [← key']
          exact (Classical.some_spec x.1.1.2).2)⟩
  apply Fintype.ofInjective h fun _ _ H => _
  simp only [← Subtype.val_eq_coe, ← Subtype.mk_eq_mk] at H
  exact Subtype.ext (ULift.down_injective (Subtype.ext H))

theorem cardinal_mk_lift_le_max :
    Cardinal.lift.{u, v} (# { x : A // IsAlgebraic R x }) ≤ max (Cardinal.lift.{v, u} (# R)) ℵ₀ :=
  (cardinal_mk_lift_le_mul R A).trans <|
    (mul_le_mul_right' (lift_le.2 cardinal_mk_le_max) _).trans <| by
      simp [← le_totalₓ]

theorem cardinal_mk_lift_le_of_infinite [Infinite R] :
    Cardinal.lift.{u, v} (# { x : A // IsAlgebraic R x }) ≤ Cardinal.lift.{v, u} (# R) :=
  (cardinal_mk_lift_le_max R A).trans <| by
    simp

variable [Encodable R]

@[simp]
theorem countable_of_encodable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← mk_set_le_aleph_0, ← lift_le]
  apply (cardinal_mk_lift_le_max R A).trans
  simp

@[simp]
theorem cardinal_mk_of_encodable_of_char_zero [CharZero A] [IsDomain R] : # { x : A // IsAlgebraic R x } = ℵ₀ :=
  le_antisymmₓ
    (by
      simp )
    (aleph_0_le_cardinal_mk_of_char_zero R A)

end lift

section NonLift

variable (R A : Type u) [CommRingₓ R] [CommRingₓ A] [IsDomain A] [Algebra R A] [NoZeroSmulDivisors R A]

theorem cardinal_mk_le_mul : # { x : A // IsAlgebraic R x } ≤ # (Polynomial R) * ℵ₀ := by
  rw [← lift_id (# _), ← lift_id (# (Polynomial R))]
  exact cardinal_mk_lift_le_mul R A

theorem cardinal_mk_le_max : # { x : A // IsAlgebraic R x } ≤ max (# R) ℵ₀ := by
  rw [← lift_id (# _), ← lift_id (# R)]
  exact cardinal_mk_lift_le_max R A

theorem cardinal_mk_le_of_infinite [Infinite R] : # { x : A // IsAlgebraic R x } ≤ # R :=
  (cardinal_mk_le_max R A).trans <| by
    simp

end NonLift

end Algebraic

