import Mathlib
import LeanAide.CheckedSorry
universe u v u_1
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false

theorem eg :
    ∀ {n : Type u} {α : Type v} [inst : CommRing α] [inst_1 : DecidableEq n] [inst_2 : Fintype n] {A : Matrix n n α},
      A ^ 3 = 1 → A.IsDiag :=
  by
  have : ∀ {A : Type u} [inst : Ring A] (a : A), a ^ 3 - 1 = 0 → Polynomial.eval a (Polynomial.X ^ 3 - 1) = 0 := by
    aesop (add
        unsafe
          90%
            (by
                omega)) (add
        unsafe
          90%
            (by
                ring)) (add
        unsafe
          90%
            (by
                linarith)) (add
        unsafe
          90%
            (by
                norm_num)) (add
        unsafe
          90%
            (by
                positivity)) (add
        unsafe
          90%
            (by
                gcongr)) (add
        unsafe 90% (by contradiction)) (add unsafe 90% (by tauto)) (add unsafe 50% (by checked_sorry))
  have : {K : Type u} → [inst : Field K] → [inst_1 : CharZero K] → sorryAx (Sort u) := by
    aesop (add
        unsafe
          90%
            (by
                omega)) (add
        unsafe
          90%
            (by
                ring)) (add
        unsafe
          90%
            (by
                linarith)) (add
        unsafe
          90%
            (by
                norm_num)) (add
        unsafe
          90%
            (by
                positivity)) (add
        unsafe
          90%
            (by
                gcongr)) (add
        unsafe 90% (by contradiction)) (add unsafe 90% (by tauto)) (add unsafe 50% (by checked_sorry))
  have :
    ∀ {K : Type u_1} [inst : Field K] {ω : K},
      ω ≠ 1 ∧ ω ^ 3 = 1 → ∀ {x y z : K}, [1, ω, ω ^ 2] = sorry → x ≠ y ∧ y ≠ z ∧ x ≠ z :=
    by
    aesop (add
        unsafe
          90%
            (by
                omega)) (add
        unsafe
          90%
            (by
                ring)) (add
        unsafe
          90%
            (by
                linarith)) (add
        unsafe
          90%
            (by
                norm_num)) (add
        unsafe
          90%
            (by
                positivity)) (add
        unsafe
          90%
            (by
                gcongr)) (add
        unsafe 90% (by contradiction)) (add unsafe 90% (by tauto)) (add unsafe 50% (by checked_sorry))
    repeat (sorry)
  have :
    ∀ {A : Type u} [inst : CommRing A] [inst_1 : Algebra A (Polynomial A)] (x : A),
      IsIntegral A x → minpoly A x ∣ Polynomial.X ^ 3 - 1 ∧ (minpoly A x).Separable :=
    by
    aesop (add
        unsafe
          90%
            (by
                omega)) (add
        unsafe
          90%
            (by
                ring)) (add
        unsafe
          90%
            (by
                linarith)) (add
        unsafe
          90%
            (by
                norm_num)) (add
        unsafe
          90%
            (by
                positivity)) (add
        unsafe
          90%
            (by
                gcongr)) (add
        unsafe 90% (by contradiction)) (add unsafe 90% (by tauto)) (add unsafe 50% (by checked_sorry))
  repeat (sorry)
