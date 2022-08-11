/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/

/-!
# Binary representation of integers using inductive types

Note: Unlike in Coq, where this representation is preferred because of
the reliance on kernel reduction, in Lean this representation is discouraged
in favor of the "Peano" natural numbers `nat`, and the purpose of this
collection of theorems is to show the equivalence of the different approaches.
-/


/-- The type of positive binary numbers.

     13 = 1101(base 2) = bit1 (bit0 (bit1 one)) -/
inductive PosNum : Type
  | one : PosNum
  | bit1 : PosNum → PosNum
  | bit0 : PosNum → PosNum
  deriving has_reflect, DecidableEq

instance : One PosNum :=
  ⟨PosNum.one⟩

instance : Inhabited PosNum :=
  ⟨1⟩

/-- The type of nonnegative binary numbers, using `pos_num`.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one))) -/
inductive Num : Type
  | zero : Num
  | Pos : PosNum → Num
  deriving has_reflect, DecidableEq

instance : Zero Num :=
  ⟨Num.zero⟩

instance : One Num :=
  ⟨Num.pos 1⟩

instance : Inhabited Num :=
  ⟨0⟩

/-- Representation of integers using trichotomy around zero.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
     -13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one))) -/
inductive Znum : Type
  | zero : Znum
  | Pos : PosNum → Znum
  | neg : PosNum → Znum
  deriving has_reflect, DecidableEq

instance : Zero Znum :=
  ⟨Znum.zero⟩

instance : One Znum :=
  ⟨Znum.pos 1⟩

instance : Inhabited Znum :=
  ⟨0⟩

namespace PosNum

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`.
  -/
def bit (b : Bool) : PosNum → PosNum :=
  cond b bit1 bit0

/-- The successor of a `pos_num`.
  -/
def succ : PosNum → PosNum
  | 1 => bit0 one
  | bit1 n => bit0 (succ n)
  | bit0 n => bit1 n

/-- Returns a boolean for whether the `pos_num` is `one`.
  -/
def isOne : PosNum → Bool
  | 1 => true
  | _ => false

/-- Addition of two `pos_num`s.
  -/
protected def add : PosNum → PosNum → PosNum
  | 1, b => succ b
  | a, 1 => succ a
  | bit0 a, bit0 b => bit0 (add a b)
  | bit1 a, bit1 b => bit0 (succ (add a b))
  | bit0 a, bit1 b => bit1 (add a b)
  | bit1 a, bit0 b => bit1 (add a b)

instance : Add PosNum :=
  ⟨PosNum.add⟩

/-- The predecessor of a `pos_num` as a `num`.
  -/
def pred' : PosNum → Num
  | 1 => 0
  | bit0 n => Num.pos (Num.casesOn (pred' n) 1 bit1)
  | bit1 n => Num.pos (bit0 n)

/-- The predecessor of a `pos_num` as a `pos_num`. This means that `pred 1 = 1`.
  -/
def pred (a : PosNum) : PosNum :=
  Num.casesOn (pred' a) 1 id

/-- The number of bits of a `pos_num`, as a `pos_num`.
  -/
def size : PosNum → PosNum
  | 1 => 1
  | bit0 n => succ (size n)
  | bit1 n => succ (size n)

/-- The number of bits of a `pos_num`, as a `nat`.
  -/
def natSize : PosNum → Nat
  | 1 => 1
  | bit0 n => Nat.succ (nat_size n)
  | bit1 n => Nat.succ (nat_size n)

/-- Multiplication of two `pos_num`s.
  -/
protected def mul (a : PosNum) : PosNum → PosNum
  | 1 => a
  | bit0 b => bit0 (mul b)
  | bit1 b => bit0 (mul b) + a

instance : Mul PosNum :=
  ⟨PosNum.mul⟩

/-- `of_nat_succ n` is the `pos_num` corresponding to `n + 1`.
  -/
def ofNatSucc : ℕ → PosNum
  | 0 => 1
  | Nat.succ n => succ (of_nat_succ n)

/-- `of_nat n` is the `pos_num` corresponding to `n`, except for `of_nat 0 = 1`.
  -/
def ofNat (n : ℕ) : PosNum :=
  ofNatSucc (Nat.pred n)

open Ordering

/-- Ordering of `pos_num`s.
  -/
def cmp : PosNum → PosNum → Ordering
  | 1, 1 => Eq
  | _, 1 => Gt
  | 1, _ => lt
  | bit0 a, bit0 b => cmp a b
  | bit0 a, bit1 b => Ordering.casesOn (cmp a b) lt lt Gt
  | bit1 a, bit0 b => Ordering.casesOn (cmp a b) lt Gt Gt
  | bit1 a, bit1 b => cmp a b

instance : LT PosNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE PosNum :=
  ⟨fun a b => ¬b < a⟩

instance decidableLt : @DecidableRel PosNum (· < ·)
  | a, b => by
    dsimp' [← (· < ·)] <;> infer_instance

instance decidableLe : @DecidableRel PosNum (· ≤ ·)
  | a, b => by
    dsimp' [← (· ≤ ·)] <;> infer_instance

end PosNum

section

variable {α : Type _} [One α] [Add α]

/-- `cast_pos_num` casts a `pos_num` into any type which has `1` and `+`.
  -/
def castPosNum : PosNum → α
  | 1 => 1
  | PosNum.bit0 a => bit0 (castPosNum a)
  | PosNum.bit1 a => bit1 (castPosNum a)

/-- `cast_num` casts a `num` into any type which has `0`, `1` and `+`.
  -/
def castNum [z : Zero α] : Num → α
  | 0 => 0
  | Num.pos p => castPosNum p

-- see Note [coercion into rings]
instance (priority := 900) posNumCoe : CoeTₓ PosNum α :=
  ⟨castPosNum⟩

-- see Note [coercion into rings]
instance (priority := 900) numNatCoe [z : Zero α] : CoeTₓ Num α :=
  ⟨castNum⟩

instance : HasRepr PosNum :=
  ⟨fun n => reprₓ (n : ℕ)⟩

instance : HasRepr Num :=
  ⟨fun n => reprₓ (n : ℕ)⟩

end

namespace Num

open PosNum

/-- The successor of a `num` as a `pos_num`.
  -/
def succ' : Num → PosNum
  | 0 => 1
  | Pos p => succ p

/-- The successor of a `num` as a `num`.
  -/
def succ (n : Num) : Num :=
  pos (succ' n)

/-- Addition of two `num`s.
  -/
protected def add : Num → Num → Num
  | 0, a => a
  | b, 0 => b
  | Pos a, Pos b => pos (a + b)

instance : Add Num :=
  ⟨Num.add⟩

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`.
  -/
protected def bit0 : Num → Num
  | 0 => 0
  | Pos n => pos (PosNum.bit0 n)

/-- `bit1 n` appends a `1` to the end of `n`, where `bit1 n = n1`.
  -/
protected def bit1 : Num → Num
  | 0 => 1
  | Pos n => pos (PosNum.bit1 n)

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`.
  -/
def bit (b : Bool) : Num → Num :=
  cond b Num.bit1 Num.bit0

/-- The number of bits required to represent a `num`, as a `num`. `size 0` is defined to be `0`.
  -/
def size : Num → Num
  | 0 => 0
  | Pos n => pos (PosNum.size n)

/-- The number of bits required to represent a `num`, as a `nat`. `size 0` is defined to be `0`.
  -/
def natSize : Num → Nat
  | 0 => 0
  | Pos n => PosNum.natSize n

/-- Multiplication of two `num`s.
  -/
protected def mul : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | Pos a, Pos b => pos (a * b)

instance : Mul Num :=
  ⟨Num.mul⟩

open Ordering

/-- Ordering of `num`s.
  -/
def cmp : Num → Num → Ordering
  | 0, 0 => Eq
  | _, 0 => Gt
  | 0, _ => lt
  | Pos a, Pos b => PosNum.cmp a b

instance : LT Num :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE Num :=
  ⟨fun a b => ¬b < a⟩

instance decidableLt : @DecidableRel Num (· < ·)
  | a, b => by
    dsimp' [← (· < ·)] <;> infer_instance

instance decidableLe : @DecidableRel Num (· ≤ ·)
  | a, b => by
    dsimp' [← (· ≤ ·)] <;> infer_instance

/-- Converts a `num` to a `znum`.
  -/
def toZnum : Num → Znum
  | 0 => 0
  | Pos a => Znum.pos a

/-- Converts `x : num` to `-x : znum`.
  -/
def toZnumNeg : Num → Znum
  | 0 => 0
  | Pos a => Znum.neg a

/-- Converts a `nat` to a `num`.
  -/
def ofNat' : ℕ → Num :=
  Nat.binaryRec 0 fun b n => cond b Num.bit1 Num.bit0

end Num

namespace Znum

open PosNum

/-- The negation of a `znum`.
  -/
def zneg : Znum → Znum
  | 0 => 0
  | Pos a => neg a
  | neg a => pos a

instance : Neg Znum :=
  ⟨zneg⟩

/-- The absolute value of a `znum` as a `num`.
  -/
def abs : Znum → Num
  | 0 => 0
  | Pos a => Num.pos a
  | neg a => Num.pos a

/-- The successor of a `znum`.
  -/
def succ : Znum → Znum
  | 0 => 1
  | Pos a => pos (PosNum.succ a)
  | neg a => (PosNum.pred' a).toZnumNeg

/-- The predecessor of a `znum`.
  -/
def pred : Znum → Znum
  | 0 => neg 1
  | Pos a => (PosNum.pred' a).toZnum
  | neg a => neg (PosNum.succ a)

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`.
  -/
protected def bit0 : Znum → Znum
  | 0 => 0
  | Pos n => pos (PosNum.bit0 n)
  | neg n => neg (PosNum.bit0 n)

/-- `bit1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x + 1`.
  -/
protected def bit1 : Znum → Znum
  | 0 => 1
  | Pos n => pos (PosNum.bit1 n)
  | neg n => neg (Num.casesOn (pred' n) 1 PosNum.bit1)

/-- `bitm1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x - 1`.
  -/
protected def bitm1 : Znum → Znum
  | 0 => neg 1
  | Pos n => pos (Num.casesOn (pred' n) 1 PosNum.bit1)
  | neg n => neg (PosNum.bit1 n)

/-- Converts an `int` to a `znum`.
  -/
def ofInt' : ℤ → Znum
  | (n : ℕ) => Num.toZnum (Num.ofNat' n)
  | -[1+ n] => Num.toZnumNeg (Num.ofNat' (n + 1))

end Znum

namespace PosNum

open Znum

/-- Subtraction of two `pos_num`s, producing a `znum`.
  -/
def sub' : PosNum → PosNum → Znum
  | a, 1 => (pred' a).toZnum
  | 1, b => (pred' b).toZnumNeg
  | bit0 a, bit0 b => (sub' a b).bit0
  | bit0 a, bit1 b => (sub' a b).bitm1
  | bit1 a, bit0 b => (sub' a b).bit1
  | bit1 a, bit1 b => (sub' a b).bit0

/-- Converts a `znum` to `option pos_num`, where it is `some` if the `znum` was positive and `none`
  otherwise.
  -/
def ofZnum' : Znum → Option PosNum
  | Znum.pos p => some p
  | _ => none

/-- Converts a `znum` to a `pos_num`, mapping all out of range values to `1`.
  -/
def ofZnum : Znum → PosNum
  | Znum.pos p => p
  | _ => 1

/-- Subtraction of `pos_num`s, where if `a < b`, then `a - b = 1`.
  -/
protected def sub (a b : PosNum) : PosNum :=
  match sub' a b with
  | Znum.pos p => p
  | _ => 1

instance : Sub PosNum :=
  ⟨PosNum.sub⟩

end PosNum

namespace Num

/-- The predecessor of a `num` as an `option num`, where `ppred 0 = none`
  -/
def ppred : Num → Option Num
  | 0 => none
  | Pos p => some p.pred'

/-- The predecessor of a `num` as a `num`, where `pred 0 = 0`.
  -/
def pred : Num → Num
  | 0 => 0
  | Pos p => p.pred'

/-- Divides a `num` by `2`
  -/
def div2 : Num → Num
  | 0 => 0
  | 1 => 0
  | Pos (PosNum.bit0 p) => pos p
  | Pos (PosNum.bit1 p) => pos p

/-- Converts a `znum` to an `option num`, where `of_znum' p = none` if `p < 0`.
  -/
def ofZnum' : Znum → Option Num
  | 0 => some 0
  | Znum.pos p => some (pos p)
  | Znum.neg p => none

/-- Converts a `znum` to an `option num`, where `of_znum p = 0` if `p < 0`.
  -/
def ofZnum : Znum → Num
  | Znum.pos p => pos p
  | _ => 0

/-- Subtraction of two `num`s, producing a `znum`.
  -/
def sub' : Num → Num → Znum
  | 0, 0 => 0
  | Pos a, 0 => Znum.pos a
  | 0, Pos b => Znum.neg b
  | Pos a, Pos b => a.sub' b

/-- Subtraction of two `num`s, producing an `option num`.
  -/
def psub (a b : Num) : Option Num :=
  ofZnum' (sub' a b)

/-- Subtraction of two `num`s, where if `a < b`, `a - b = 0`.
  -/
protected def sub (a b : Num) : Num :=
  ofZnum (sub' a b)

instance : Sub Num :=
  ⟨Num.sub⟩

end Num

namespace Znum

open PosNum

/-- Addition of `znum`s.
  -/
protected def add : Znum → Znum → Znum
  | 0, a => a
  | b, 0 => b
  | Pos a, Pos b => pos (a + b)
  | Pos a, neg b => sub' a b
  | neg a, Pos b => sub' b a
  | neg a, neg b => neg (a + b)

instance : Add Znum :=
  ⟨Znum.add⟩

/-- Multiplication of `znum`s.
  -/
protected def mul : Znum → Znum → Znum
  | 0, a => 0
  | b, 0 => 0
  | Pos a, Pos b => pos (a * b)
  | Pos a, neg b => neg (a * b)
  | neg a, Pos b => neg (a * b)
  | neg a, neg b => pos (a * b)

instance : Mul Znum :=
  ⟨Znum.mul⟩

open Ordering

/-- Ordering on `znum`s.
  -/
def cmp : Znum → Znum → Ordering
  | 0, 0 => Eq
  | Pos a, Pos b => PosNum.cmp a b
  | neg a, neg b => PosNum.cmp b a
  | Pos _, _ => Gt
  | neg _, _ => lt
  | _, Pos _ => lt
  | _, neg _ => Gt

instance : LT Znum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE Znum :=
  ⟨fun a b => ¬b < a⟩

instance decidableLt : @DecidableRel Znum (· < ·)
  | a, b => by
    dsimp' [← (· < ·)] <;> infer_instance

instance decidableLe : @DecidableRel Znum (· ≤ ·)
  | a, b => by
    dsimp' [← (· ≤ ·)] <;> infer_instance

end Znum

namespace PosNum

/-- Auxiliary definition for `pos_num.divmod`. -/
def divmodAux (d : PosNum) (q r : Num) : Num × Num :=
  match Num.ofZnum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)

/-- `divmod x y = (y / x, y % x)`.
  -/
def divmod (d : PosNum) : PosNum → Num × Num
  | bit0 n =>
    let (q, r₁) := divmod n
    divmodAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divmod n
    divmodAux d q (Num.bit1 r₁)
  | 1 => divmodAux d 0 1

/-- Division of `pos_num`,
  -/
def div' (n d : PosNum) : Num :=
  (divmod d n).1

/-- Modulus of `pos_num`s.
  -/
def mod' (n d : PosNum) : Num :=
  (divmod d n).2

/-
  private def sqrt_aux1 (b : pos_num) (r n : num) : num × num :=
  match num.of_znum' (n.sub' (r + num.pos b)) with
  | some n' := (r.div2 + num.pos b, n')
  | none := (r.div2, n)
  end

  private def sqrt_aux : pos_num → num → num → num
  | b@(bit0 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | b@(bit1 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | 1           r n := (sqrt_aux1 1 r n).1
  -/
/-

def sqrt_aux : ℕ → ℕ → ℕ → ℕ
| b r n := if b0 : b = 0 then r else
  let b' := shiftr b 2 in
  have b' < b, from sqrt_aux_dec b0,
  match (n - (r + b : ℕ) : ℤ) with
  | (n' : ℕ) := sqrt_aux b' (div2 r + b) n'
  | _ := sqrt_aux b' (div2 r) n
  end

/-- `sqrt n` is the square root of a natural number `n`. If `n` is not a
  perfect square, it returns the largest `k:ℕ` such that `k*k ≤ n`. -/
def sqrt (n : ℕ) : ℕ :=
match size n with
| 0      := 0
| succ s := sqrt_aux (shiftl 1 (bit0 (div2 s))) 0 n
end
-/
end PosNum

namespace Num

/-- Division of `num`s, where `x / 0 = 0`.
  -/
def div : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | Pos n, Pos d => PosNum.div' n d

/-- Modulus of `num`s.
  -/
def mod : Num → Num → Num
  | 0, _ => 0
  | n, 0 => n
  | Pos n, Pos d => PosNum.mod' n d

instance : Div Num :=
  ⟨Num.div⟩

instance : Mod Num :=
  ⟨Num.mod⟩

/-- Auxiliary definition for `num.gcd`. -/
def gcdAux : Nat → Num → Num → Num
  | 0, a, b => b
  | Nat.succ n, 0, b => b
  | Nat.succ n, a, b => gcd_aux n (b % a) a

/-- Greatest Common Divisor (GCD) of two `num`s.
  -/
def gcd (a b : Num) : Num :=
  if a ≤ b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a

end Num

namespace Znum

/-- Division of `znum`, where `x / 0 = 0`.
  -/
def div : Znum → Znum → Znum
  | 0, _ => 0
  | _, 0 => 0
  | Pos n, Pos d => Num.toZnum (PosNum.div' n d)
  | Pos n, neg d => Num.toZnumNeg (PosNum.div' n d)
  | neg n, Pos d => neg (PosNum.pred' n / Num.pos d).succ'
  | neg n, neg d => pos (PosNum.pred' n / Num.pos d).succ'

/-- Modulus of `znum`s.
  -/
def mod : Znum → Znum → Znum
  | 0, d => 0
  | Pos n, d => Num.toZnum (Num.pos n % d.abs)
  | neg n, d => d.abs.sub' (PosNum.pred' n % d.abs).succ

instance : Div Znum :=
  ⟨Znum.div⟩

instance : Mod Znum :=
  ⟨Znum.mod⟩

/-- Greatest Common Divisor (GCD) of two `znum`s.
  -/
def gcd (a b : Znum) : Num :=
  a.abs.gcd b.abs

end Znum

section

variable {α : Type _} [Zero α] [One α] [Add α] [Neg α]

/-- `cast_znum` casts a `znum` into any type which has `0`, `1`, `+` and `neg`
  -/
def castZnum : Znum → α
  | 0 => 0
  | Znum.pos p => p
  | Znum.neg p => -p

-- see Note [coercion into rings]
instance (priority := 900) znumCoe : CoeTₓ Znum α :=
  ⟨castZnum⟩

instance : HasRepr Znum :=
  ⟨fun n => reprₓ (n : ℤ)⟩

end

