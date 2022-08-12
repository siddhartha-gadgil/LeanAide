/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.NumberTheory.ClassNumber.AdmissibleCardPowDegree
import Mathbin.NumberTheory.ClassNumber.Finite
import Mathbin.NumberTheory.FunctionField

/-!
# Class numbers of function fields

This file defines the class number of a function field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `function_field.class_number`: the class number of a function field is the (finite)
cardinality of the class group of its ring of integers
-/


namespace FunctionField

open Polynomial

variable (Fq F : Type) [Field Fq] [Fintype Fq] [Field F]

variable [Algebra Fq[X] F] [Algebra (Ratfunc Fq) F]

variable [IsScalarTower Fq[X] (Ratfunc Fq) F]

variable [FunctionField Fq F] [IsSeparable (Ratfunc Fq) F]

open Classical

namespace RingOfIntegers

open FunctionField

noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F) F) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (Ratfunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] ℤ))

end RingOfIntegers

/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F) F)

/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
theorem class_number_eq_one_iff : classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_class_group_eq_one_iff

end FunctionField

