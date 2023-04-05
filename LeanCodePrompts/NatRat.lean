import Mathlib

attribute [-instance] instSubNat
attribute [-instance] Nat.instDivNat


namespace lean3
scoped instance (priority := high)[Coe α ℚ][Coe β ℚ]  : HDiv α β  ℚ := ⟨fun a b => a * (b : ℚ)⁻¹⟩   
scoped instance (priority := high)[Coe α ℚ][Coe β ℚ] : HMul α β ℚ := ⟨fun a b => a * b⟩   
-- scoped instance (priority := high) : HMul ℕ ℚ  ℚ := ⟨fun a b => a * b⟩   
scoped instance (priority := high) [Coe α ℚ][Coe β ℚ] : HSub α β ℚ := ⟨fun a b => a - b⟩ 
scoped instance (priority := high) [Coe α ℚ] : HPow α ℕ ℚ := ⟨fun a b => (a : ℚ) ^ b⟩   
scoped instance (priority := high) : HPow ℤ ℕ ℚ := ⟨fun a b => a ^ b⟩   
end lean3

open lean3


instance : Coe ℕ ℚ := ⟨fun n : ℕ   ↦ (n : ℚ)⟩
instance : Coe ℕ ℤ  := ⟨fun n : ℕ   ↦ (n : ℤ )⟩


class SafeHSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a - b` computes the difference of `a` and `b`.
  The meaning of this notation is type-dependent.
  * For natural numbers, this operator saturates at 0: `a - b = 0` when `a ≤ b`. -/
  hSub : α → β → γ

instance (α : Type u) (β : Type v) (γ : outParam (Type w))[hs : HSub α β γ] : SafeHSub α β γ := ⟨hs.hSub⟩

infix:71 (priority := high) " * " => Mul.mul
infix:66 (priority := high) " - " => SafeHSub.hSub
infix:71 (priority := high) " / " => Div.div
infix:66 (priority := high) " + " => Add.add   



set_option pp.all true in
#check fun x y : ℕ => (x : ℚ)  / y


instance  subNatNatInt [Coe α ℤ][Coe β ℤ ] : SafeHSub α β  ℤ := ⟨fun a b => (a : ℤ) - (b : ℤ)⟩
-- instance  subNatIntInt : SafeHSub ℤ  ℕ ℤ := ⟨fun a b => (a : ℤ) - (b : ℤ)⟩
-- instance  subIntNatInt : SafeHSub ℕ ℤ ℤ := ⟨fun a b => (a : ℤ) - (b : ℤ)⟩
-- instance subIntIntInt : SafeHSub ℤ ℤ ℤ := ⟨fun a b => (a : ℤ) - (b : ℤ)⟩
instance  subNatIntRat [Coe α ℤ] : SafeHSub ℤ α ℚ := ⟨fun a b => (a : ℤ) - (b : ℤ)⟩
instance  subIntNatRat [Coe α ℤ] : SafeHSub α  ℤ ℚ := ⟨fun a b => (a : ℤ) - (b : ℤ)⟩
instance subIntIntRat : SafeHSub ℤ ℤ ℚ := ⟨fun a b => (a : ℤ) - (b : ℤ)⟩
instance subRatIntRat : SafeHSub ℚ ℤ ℚ := ⟨fun a b => (a : ℚ) - (b : ℚ)⟩
 

example (n : ℕ) : ℚ := ((4 : ℚ) *(n*(n-1)/2)^3-(n*(n-1)/2)^2)/3
example (n : ℕ) : ℚ := (4*(n*(n-1)/2)^3 + (n*(n-1)/2)^2)/3


-- set_option pp.all true in
#check fun n : ℕ   ↦ (n * (n - 1)/2)^3 - 1
