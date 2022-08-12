/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathbin.Tactic.Ring
import Mathbin.Data.Pnat.Prime

/-!
# Euclidean algorithm for ℕ

This file sets up a version of the Euclidean algorithm that only works with natural numbers.
Given `0 < a, b`, it computes the unique `(w, x, y, z, d)` such that the following identities hold:
* `a = (w + x) d`
* `b = (y + z) d`
* `w * z = x * y + 1`
`d` is then the gcd of `a` and `b`, and `a' := a / d = w + x` and `b' := b / d = y + z` are coprime.

This story is closely related to the structure of SL₂(ℕ) (as a free monoid on two generators) and
the theory of continued fractions.

## Main declarations

* `xgcd_type`: Helper type in defining the gcd. Encapsulates `(wp, x, y, zp, ap, bp)`. where `wp`
  `zp`, `ap`, `bp` are the variables getting changed through the algorithm.
* `is_special`: States `wp * zp = x * y + 1`
* `is_reduced`: States `ap = a ∧ bp = b`

## Notes

See `nat.xgcd` for a very similar algorithm allowing values in `ℤ`.
-/


open Nat

namespace Pnat

/-- A term of xgcd_type is a system of six naturals.  They should
 be thought of as representing the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 together with the vector [a, b] = [ap + 1, bp + 1].
-/
structure XgcdType where
  (wp x y zp ap bp : ℕ)
  deriving Inhabited

namespace XgcdType

variable (u : XgcdType)

instance : SizeOf XgcdType :=
  ⟨fun u => u.bp⟩

/-- The has_repr instance converts terms to strings in a way that
 reflects the matrix/vector interpretation as above. -/
instance : HasRepr XgcdType :=
  ⟨fun u =>
    "[[[" ++ reprₓ (u.wp + 1) ++ ", " ++ reprₓ u.x ++ "], [" ++ reprₓ u.y ++ ", " ++ reprₓ (u.zp + 1) ++ "]], [" ++
            reprₓ (u.ap + 1) ++
          ", " ++
        reprₓ (u.bp + 1) ++
      "]]"⟩

def mk' (w : ℕ+) (x : ℕ) (y : ℕ) (z : ℕ+) (a : ℕ+) (b : ℕ+) : XgcdType :=
  mk w.val.pred x y z.val.pred a.val.pred b.val.pred

def w : ℕ+ :=
  succPnat u.wp

def z : ℕ+ :=
  succPnat u.zp

def a : ℕ+ :=
  succPnat u.ap

def b : ℕ+ :=
  succPnat u.bp

def r : ℕ :=
  (u.ap + 1) % (u.bp + 1)

def q : ℕ :=
  (u.ap + 1) / (u.bp + 1)

def qp : ℕ :=
  u.q - 1

/-- The map v gives the product of the matrix
 [[w, x], [y, z]] = [[wp + 1, x], [y, zp + 1]]
 and the vector [a, b] = [ap + 1, bp + 1].  The map
 vp gives [sp, tp] such that v = [sp + 1, tp + 1].
-/
def vp : ℕ × ℕ :=
  ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩

def v : ℕ × ℕ :=
  ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩

def succ₂ (t : ℕ × ℕ) : ℕ × ℕ :=
  ⟨t.1.succ, t.2.succ⟩

theorem v_eq_succ_vp : u.V = succ₂ u.vp := by
  ext <;>
    dsimp' [← v, ← vp, ← w, ← z, ← a, ← b, ← succ₂] <;>
      repeat'
          rw [Nat.succ_eq_add_one] <;>
        ring

/-- is_special holds if the matrix has determinant one. -/
def IsSpecial : Prop :=
  u.wp + u.zp + u.wp * u.zp = u.x * u.y

def IsSpecial' : Prop :=
  u.w * u.z = succPnat (u.x * u.y)

theorem is_special_iff : u.IsSpecial ↔ u.IsSpecial' := by
  dsimp' [← is_special, ← is_special']
  constructor <;> intro h
  · apply Eq
    dsimp' [← w, ← z, ← succ_pnat]
    rw [← h]
    repeat'
      rw [Nat.succ_eq_add_one]
    ring
    
  · apply Nat.succ.injₓ
    replace h := congr_arg (coe : ℕ+ → ℕ) h
    rw [mul_coe, w, z] at h
    repeat'
      rw [succ_pnat_coe, Nat.succ_eq_add_one] at h
    repeat'
      rw [Nat.succ_eq_add_one]
    rw [← h]
    ring
    

/-- is_reduced holds if the two entries in the vector are the
 same.  The reduction algorithm will produce a system with this
 property, whose product vector is the same as for the original
 system. -/
def IsReduced : Prop :=
  u.ap = u.bp

def IsReduced' : Prop :=
  u.a = u.b

theorem is_reduced_iff : u.IsReduced ↔ u.IsReduced' :=
  ⟨congr_arg succPnat, succ_pnat_inj⟩

def flip : XgcdType where
  wp := u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap

@[simp]
theorem flip_w : (flip u).w = u.z :=
  rfl

@[simp]
theorem flip_x : (flip u).x = u.y :=
  rfl

@[simp]
theorem flip_y : (flip u).y = u.x :=
  rfl

@[simp]
theorem flip_z : (flip u).z = u.w :=
  rfl

@[simp]
theorem flip_a : (flip u).a = u.b :=
  rfl

@[simp]
theorem flip_b : (flip u).b = u.a :=
  rfl

theorem flip_is_reduced : (flip u).IsReduced ↔ u.IsReduced := by
  dsimp' [← is_reduced, ← flip]
  constructor <;> intro h <;> exact h.symm

theorem flip_is_special : (flip u).IsSpecial ↔ u.IsSpecial := by
  dsimp' [← is_special, ← flip]
  rw [mul_comm u.x, mul_comm u.zp, add_commₓ u.zp]

theorem flip_v : (flip u).V = u.V.swap := by
  dsimp' [← v]
  ext
  · simp only
    ring
    
  · simp only
    ring
    

/-- Properties of division with remainder for a / b.  -/
theorem rq_eq : u.R + (u.bp + 1) * u.q = u.ap + 1 :=
  Nat.mod_add_divₓ (u.ap + 1) (u.bp + 1)

theorem qp_eq (hr : u.R = 0) : u.q = u.qp + 1 := by
  by_cases' hq : u.q = 0
  · let h := u.rq_eq
    rw [hr, hq, mul_zero, add_zeroₓ] at h
    cases h
    
  · exact (Nat.succ_pred_eq_of_posₓ (Nat.pos_of_ne_zeroₓ hq)).symm
    

/-- The following function provides the starting point for
 our algorithm.  We will apply an iterative reduction process
 to it, which will produce a system satisfying is_reduced.
 The gcd can be read off from this final system.
-/
def start (a b : ℕ+) : XgcdType :=
  ⟨0, 0, 0, 0, a - 1, b - 1⟩

theorem start_is_special (a b : ℕ+) : (start a b).IsSpecial := by
  dsimp' [← start, ← is_special]
  rfl

theorem start_v (a b : ℕ+) : (start a b).V = ⟨a, b⟩ := by
  dsimp' [← start, ← v, ← xgcd_type.a, ← xgcd_type.b, ← w, ← z]
  rw [one_mulₓ, one_mulₓ, zero_mul, zero_mul, zero_addₓ, add_zeroₓ]
  rw [← Nat.pred_eq_sub_one, ← Nat.pred_eq_sub_one]
  rw [Nat.succ_pred_eq_of_posₓ a.pos, Nat.succ_pred_eq_of_posₓ b.pos]

def finish : XgcdType :=
  XgcdType.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp

theorem finish_is_reduced : u.finish.IsReduced := by
  dsimp' [← is_reduced]
  rfl

theorem finish_is_special (hs : u.IsSpecial) : u.finish.IsSpecial := by
  dsimp' [← is_special, ← finish]  at hs⊢
  rw [add_mulₓ _ _ u.y, add_commₓ _ (u.x * u.y), ← hs]
  ring

theorem finish_v (hr : u.R = 0) : u.finish.V = u.V := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  rw [hr, zero_addₓ] at ha
  ext
  · change (u.wp + 1) * u.b + ((u.wp + 1) * u.qp + u.x) * u.b = u.w * u.a + u.x * u.b
    have : u.wp + 1 = u.w := rfl
    rw [this, ← ha, u.qp_eq hr]
    ring
    
  · change u.y * u.b + (u.y * u.qp + u.z) * u.b = u.y * u.a + u.z * u.b
    rw [← ha, u.qp_eq hr]
    ring
    

/-- This is the main reduction step, which is used when u.r ≠ 0, or
 equivalently b does not divide a. -/
def step : XgcdType :=
  XgcdType.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.R - 1)

/-- We will apply the above step recursively.  The following result
 is used to ensure that the process terminates. -/
theorem step_wf (hr : u.R ≠ 0) : sizeof u.step < sizeof u := by
  change u.r - 1 < u.bp
  have h₀ : u.r - 1 + 1 = u.r := Nat.succ_pred_eq_of_posₓ (Nat.pos_of_ne_zeroₓ hr)
  have h₁ : u.r < u.bp + 1 := Nat.mod_ltₓ (u.ap + 1) u.bp.succ_pos
  rw [← h₀] at h₁
  exact lt_of_succ_lt_succ h₁

theorem step_is_special (hs : u.IsSpecial) : u.step.IsSpecial := by
  dsimp' [← is_special, ← step]  at hs⊢
  rw [mul_addₓ, mul_comm u.y u.x, ← hs]
  ring

/-- The reduction step does not change the product vector. -/
theorem step_v (hr : u.R ≠ 0) : u.step.V = u.V.swap := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  let hr : u.r - 1 + 1 = u.r := (add_commₓ _ 1).trans (add_tsub_cancel_of_le (Nat.pos_of_ne_zeroₓ hr))
  ext
  · change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : ℕ) = u.y * u.a + u.z * u.b
    rw [← ha, hr]
    ring
    
  · change ((u.w * u.q + u.x) * u.b + u.w * (u.r - 1 + 1) : ℕ) = u.w * u.a + u.x * u.b
    rw [← ha, hr]
    ring
    

/-- We can now define the full reduction function, which applies
 step as long as possible, and then applies finish. Note that the
 "have" statement puts a fact in the local context, and the
 equation compiler uses this fact to help construct the full
 definition in terms of well-founded recursion.  The same fact
 needs to be introduced in all the inductive proofs of properties
 given below. -/
def reduce : XgcdType → XgcdType
  | u =>
    dite (u.R = 0) (fun h => u.finish) fun h =>
      have : sizeof u.step < sizeof u := u.step_wf h
      flip (reduce u.step)

theorem reduce_a {u : XgcdType} (h : u.R = 0) : u.reduce = u.finish := by
  rw [reduce]
  simp only
  rw [if_pos h]

theorem reduce_b {u : XgcdType} (h : u.R ≠ 0) : u.reduce = u.step.reduce.flip := by
  rw [reduce]
  simp only
  rw [if_neg h, step]

theorem reduce_reduced : ∀ u : XgcdType, u.reduce.IsReduced
  | u =>
    dite (u.R = 0)
      (fun h => by
        rw [reduce_a h]
        exact u.finish_is_reduced)
      fun h => by
      have : sizeof u.step < sizeof u := u.step_wf h
      rw [reduce_b h, flip_is_reduced]
      apply reduce_reduced

theorem reduce_reduced' (u : XgcdType) : u.reduce.IsReduced' :=
  (is_reduced_iff _).mp u.reduce_reduced

theorem reduce_special : ∀ u : XgcdType, u.IsSpecial → u.reduce.IsSpecial
  | u =>
    dite (u.R = 0)
      (fun h hs => by
        rw [reduce_a h]
        exact u.finish_is_special hs)
      fun h hs => by
      have : sizeof u.step < sizeof u := u.step_wf h
      rw [reduce_b h]
      exact (flip_is_special _).mpr (reduce_special _ (u.step_is_special hs))

theorem reduce_special' (u : XgcdType) (hs : u.IsSpecial) : u.reduce.IsSpecial' :=
  (is_special_iff _).mp (u.reduce_special hs)

theorem reduce_v : ∀ u : XgcdType, u.reduce.V = u.V
  | u =>
    dite (u.R = 0)
      (fun h => by
        rw [reduce_a h, finish_v u h])
      fun h => by
      have : sizeof u.step < sizeof u := u.step_wf h
      rw [reduce_b h, flip_v, reduce_v (step u), step_v u h, Prod.swap_swap]

end XgcdType

section Gcd

variable (a b : ℕ+)

def xgcd : XgcdType :=
  (XgcdType.start a b).reduce

def gcdD : ℕ+ :=
  (xgcd a b).a

def gcdW : ℕ+ :=
  (xgcd a b).w

def gcdX : ℕ :=
  (xgcd a b).x

def gcdY : ℕ :=
  (xgcd a b).y

def gcdZ : ℕ+ :=
  (xgcd a b).z

def gcdA' : ℕ+ :=
  succPnat ((xgcd a b).wp + (xgcd a b).x)

def gcdB' : ℕ+ :=
  succPnat ((xgcd a b).y + (xgcd a b).zp)

theorem gcd_a'_coe : (gcdA' a b : ℕ) = gcdW a b + gcdX a b := by
  dsimp' [← gcd_a', ← gcd_x, ← gcd_w, ← xgcd_type.w]
  rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, add_right_commₓ]

theorem gcd_b'_coe : (gcdB' a b : ℕ) = gcdY a b + gcdZ a b := by
  dsimp' [← gcd_b', ← gcd_y, ← gcd_z, ← xgcd_type.z]
  rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, add_assocₓ]

theorem gcd_props :
    let d := gcdD a b
    let w := gcdW a b
    let x := gcdX a b
    let y := gcdY a b
    let z := gcdZ a b
    let a' := gcdA' a b
    let b' := gcdB' a b
    w * z = succPnat (x * y) ∧
      a = a' * d ∧
        b = b' * d ∧
          z * a' = succPnat (x * b') ∧ w * b' = succPnat (y * a') ∧ (z * a : ℕ) = x * b + d ∧ (w * b : ℕ) = y * a + d :=
  by
  intros
  let u := xgcd_type.start a b
  let ur := u.reduce
  have ha : d = ur.a := rfl
  have hb : d = ur.b := u.reduce_reduced'
  have ha' : (a' : ℕ) = w + x := gcd_a'_coe a b
  have hb' : (b' : ℕ) = y + z := gcd_b'_coe a b
  have hdet : w * z = succ_pnat (x * y) := u.reduce_special' rfl
  constructor
  exact hdet
  have hdet' : (w * z : ℕ) = x * y + 1 := by
    rw [← mul_coe, hdet, succ_pnat_coe]
  have huv : u.v = ⟨a, b⟩ := xgcd_type.start_v a b
  let hv : Prod.mk (w * d + x * ur.b : ℕ) (y * d + z * ur.b : ℕ) = ⟨a, b⟩ := u.reduce_v.trans (xgcd_type.start_v a b)
  rw [← hb, ← add_mulₓ, ← add_mulₓ, ← ha', ← hb'] at hv
  have ha'' : (a : ℕ) = a' * d := (congr_arg Prod.fst hv).symm
  have hb'' : (b : ℕ) = b' * d := (congr_arg Prod.snd hv).symm
  constructor
  exact Eq ha''
  constructor
  exact Eq hb''
  have hza' : (z * a' : ℕ) = x * b' + 1 := by
    rw [ha', hb', mul_addₓ, mul_addₓ, mul_comm (z : ℕ), hdet']
    ring
  have hwb' : (w * b' : ℕ) = y * a' + 1 := by
    rw [ha', hb', mul_addₓ, mul_addₓ, hdet']
    ring
  constructor
  · apply Eq
    rw [succ_pnat_coe, Nat.succ_eq_add_one, mul_coe, hza']
    
  constructor
  · apply Eq
    rw [succ_pnat_coe, Nat.succ_eq_add_one, mul_coe, hwb']
    
  rw [ha'', hb'']
  repeat'
    rw [← mul_assoc]
  rw [hza', hwb']
  constructor <;> ring

theorem gcd_eq : gcdD a b = gcd a b := by
  rcases gcd_props a b with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩
  apply dvd_antisymm
  · apply dvd_gcd
    exact Dvd.intro (gcd_a' a b) (h₁.trans (mul_comm _ _)).symm
    exact Dvd.intro (gcd_b' a b) (h₂.trans (mul_comm _ _)).symm
    
  · have h₇ : (gcd a b : ℕ) ∣ gcd_z a b * a := (Nat.gcd_dvd_leftₓ a b).trans (dvd_mul_left _ _)
    have h₈ : (gcd a b : ℕ) ∣ gcd_x a b * b := (Nat.gcd_dvd_rightₓ a b).trans (dvd_mul_left _ _)
    rw [h₅] at h₇
    rw [dvd_iff]
    exact (Nat.dvd_add_iff_right h₈).mpr h₇
    

theorem gcd_det_eq : gcdW a b * gcdZ a b = succPnat (gcdX a b * gcdY a b) :=
  (gcd_props a b).1

theorem gcd_a_eq : a = gcdA' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.1

theorem gcd_b_eq : b = gcdB' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.1

theorem gcd_rel_left' : gcdZ a b * gcdA' a b = succPnat (gcdX a b * gcdB' a b) :=
  (gcd_props a b).2.2.2.1

theorem gcd_rel_right' : gcdW a b * gcdB' a b = succPnat (gcdY a b * gcdA' a b) :=
  (gcd_props a b).2.2.2.2.1

theorem gcd_rel_left : (gcdZ a b * a : ℕ) = gcdX a b * b + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.1

theorem gcd_rel_right : (gcdW a b * b : ℕ) = gcdY a b * a + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.2

end Gcd

end Pnat

