/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.Algebra.GroupWithZero.Power
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Algebra.Ring.Equiv

/-!
# The perfect closure of a field
-/


universe u v

open Function

section Defs

variable (R : Type u) [CommSemiringₓ R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- A perfect ring is a ring of characteristic p that has p-th root. -/
class PerfectRing : Type u where
  pthRoot' : R → R
  frobenius_pth_root' : ∀ x, frobenius R p (pth_root' x) = x
  pth_root_frobenius' : ∀ x, pth_root' (frobenius R p x) = x

/-- Frobenius automorphism of a perfect ring. -/
def frobeniusEquiv [PerfectRing R p] : R ≃+* R :=
  { frobenius R p with invFun := PerfectRing.pthRoot' p, left_inv := PerfectRing.pth_root_frobenius',
    right_inv := PerfectRing.frobenius_pth_root' }

/-- `p`-th root of an element in a `perfect_ring` as a `ring_hom`. -/
def pthRoot [PerfectRing R p] : R →+* R :=
  (frobeniusEquiv R p).symm

end Defs

section

variable {R : Type u} [CommSemiringₓ R] {S : Type v} [CommSemiringₓ S] (f : R →* S) (g : R →+* S) {p : ℕ} [Fact p.Prime]
  [CharP R p] [PerfectRing R p] [CharP S p] [PerfectRing S p]

@[simp]
theorem coe_frobenius_equiv : ⇑(frobeniusEquiv R p) = frobenius R p :=
  rfl

@[simp]
theorem coe_frobenius_equiv_symm : ⇑(frobeniusEquiv R p).symm = pthRoot R p :=
  rfl

@[simp]
theorem frobenius_pth_root (x : R) : frobenius R p (pthRoot R p x) = x :=
  (frobeniusEquiv R p).apply_symm_apply x

@[simp]
theorem pth_root_pow_p (x : R) : pthRoot R p x ^ p = x :=
  frobenius_pth_root x

@[simp]
theorem pth_root_frobenius (x : R) : pthRoot R p (frobenius R p x) = x :=
  (frobeniusEquiv R p).symm_apply_apply x

@[simp]
theorem pth_root_pow_p' (x : R) : pthRoot R p (x ^ p) = x :=
  pth_root_frobenius x

theorem left_inverse_pth_root_frobenius : LeftInverse (pthRoot R p) (frobenius R p) :=
  pth_root_frobenius

theorem right_inverse_pth_root_frobenius : Function.RightInverse (pthRoot R p) (frobenius R p) :=
  frobenius_pth_root

theorem commute_frobenius_pth_root : Function.Commute (frobenius R p) (pthRoot R p) := fun x =>
  (frobenius_pth_root x).trans (pth_root_frobenius x).symm

theorem eq_pth_root_iff {x y : R} : x = pthRoot R p y ↔ frobenius R p x = y :=
  (frobeniusEquiv R p).toEquiv.eq_symm_apply

theorem pth_root_eq_iff {x y : R} : pthRoot R p x = y ↔ x = frobenius R p y :=
  (frobeniusEquiv R p).toEquiv.symm_apply_eq

theorem MonoidHom.map_pth_root (x : R) : f (pthRoot R p x) = pthRoot S p (f x) :=
  eq_pth_root_iff.2 <| by
    rw [← f.map_frobenius, frobenius_pth_root]

theorem MonoidHom.map_iterate_pth_root (x : R) (n : ℕ) : f ((pthRoot R p^[n]) x) = (pthRoot S p^[n]) (f x) :=
  Semiconj.iterate_right f.map_pth_root n x

theorem RingHom.map_pth_root (x : R) : g (pthRoot R p x) = pthRoot S p (g x) :=
  g.toMonoidHom.map_pth_root x

theorem RingHom.map_iterate_pth_root (x : R) (n : ℕ) : g ((pthRoot R p^[n]) x) = (pthRoot S p^[n]) (g x) :=
  g.toMonoidHom.map_iterate_pth_root x n

variable (p)

theorem injective_pow_p {x y : R} (hxy : x ^ p = y ^ p) : x = y :=
  left_inverse_pth_root_frobenius.Injective hxy

end

section

variable (K : Type u) [CommRingₓ K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `perfect_closure K p` is the quotient by this relation. -/
@[mk_iff]
inductive PerfectClosure.R : ℕ × K → ℕ × K → Prop
  | intro : ∀ n x, PerfectClosure.R (n, x) (n + 1, frobenius K p x)

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
def PerfectClosure : Type u :=
  Quot (PerfectClosure.R K p)

end

namespace PerfectClosure

variable (K : Type u)

section Ringₓ

variable [CommRingₓ K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Constructor for `perfect_closure`. -/
def mk (x : ℕ × K) : PerfectClosure K p :=
  Quot.mk (R K p) x

@[simp]
theorem quot_mk_eq_mk (x : ℕ × K) : (Quot.mk (R K p) x : PerfectClosure K p) = mk K p x :=
  rfl

variable {K p}

/-- Lift a function `ℕ × K → L` to a function on `perfect_closure K p`. -/
@[elab_as_eliminator]
def liftOn {L : Type _} (x : PerfectClosure K p) (f : ℕ × K → L) (hf : ∀ x y, R K p x y → f x = f y) : L :=
  Quot.liftOn x f hf

@[simp]
theorem lift_on_mk {L : Sort _} (f : ℕ × K → L) (hf : ∀ x y, R K p x y → f x = f y) (x : ℕ × K) :
    (mk K p x).liftOn f hf = f x :=
  rfl

@[elab_as_eliminator]
theorem induction_on (x : PerfectClosure K p) {q : PerfectClosure K p → Prop} (h : ∀ x, q (mk K p x)) : q x :=
  Quot.induction_on x h

variable (K p)

private theorem mul_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p^[y.1]) x1.2 * (frobenius K p^[x1.1]) y.2) =
      mk K p (x2.1 + y.1, (frobenius K p^[y.1]) x2.2 * (frobenius K p^[x2.1]) y.2) :=
  match x1, x2, H with
  | _, _, r.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ', iterate_succ', ← frobenius_mul, Nat.succ_add] <;> apply r.intro

private theorem mul_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p^[y1.1]) x.2 * (frobenius K p^[x.1]) y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p^[y2.1]) x.2 * (frobenius K p^[x.1]) y2.2) :=
  match y1, y2, H with
  | _, _, r.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ', iterate_succ', ← frobenius_mul] <;> apply r.intro

instance : Mul (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift (fun y : ℕ × K => mk K p (x.1 + y.1, (frobenius K p^[y.1]) x.2 * (frobenius K p^[x.1]) y.2))
          (mul_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) => funext fun e => (Quot.induction_on e) fun y => mul_aux_left K p x1 x2 y H⟩

@[simp]
theorem mk_mul_mk (x y : ℕ × K) :
    mk K p x * mk K p y = mk K p (x.1 + y.1, (frobenius K p^[y.1]) x.2 * (frobenius K p^[x.1]) y.2) :=
  rfl

instance : CommMonoidₓ (PerfectClosure K p) :=
  { (inferInstance : Mul (PerfectClosure K p)) with
    mul_assoc := fun e f g =>
      (Quot.induction_on e) fun ⟨m, x⟩ =>
        (Quot.induction_on f) fun ⟨n, y⟩ =>
          (Quot.induction_on g) fun ⟨s, z⟩ =>
            congr_arg (Quot.mk _) <| by
              simp only [← add_assocₓ, ← mul_assoc, ← RingHom.iterate_map_mul, iterate_add_apply, ← add_commₓ, ←
                add_left_commₓ],
    one := mk K p (0, 1),
    one_mul := fun e =>
      Quot.induction_on e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [← RingHom.iterate_map_one, ← iterate_zero_apply, ← one_mulₓ, ← zero_addₓ],
    mul_one := fun e =>
      Quot.induction_on e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [← RingHom.iterate_map_one, ← iterate_zero_apply, ← mul_oneₓ, ← add_zeroₓ],
    mul_comm := fun e f =>
      Quot.induction_on e fun ⟨m, x⟩ =>
        Quot.induction_on f fun ⟨n, y⟩ =>
          congr_arg (Quot.mk _) <| by
            simp only [← add_commₓ, ← mul_comm] }

theorem one_def : (1 : PerfectClosure K p) = mk K p (0, 1) :=
  rfl

instance : Inhabited (PerfectClosure K p) :=
  ⟨1⟩

private theorem add_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p^[y.1]) x1.2 + (frobenius K p^[x1.1]) y.2) =
      mk K p (x2.1 + y.1, (frobenius K p^[y.1]) x2.2 + (frobenius K p^[x2.1]) y.2) :=
  match x1, x2, H with
  | _, _, r.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ', iterate_succ', ← frobenius_add, Nat.succ_add] <;> apply r.intro

private theorem add_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p^[y1.1]) x.2 + (frobenius K p^[x.1]) y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p^[y2.1]) x.2 + (frobenius K p^[x.1]) y2.2) :=
  match y1, y2, H with
  | _, _, r.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ', iterate_succ', ← frobenius_add] <;> apply r.intro

instance : Add (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift (fun y : ℕ × K => mk K p (x.1 + y.1, (frobenius K p^[y.1]) x.2 + (frobenius K p^[x.1]) y.2))
          (add_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) => funext fun e => (Quot.induction_on e) fun y => add_aux_left K p x1 x2 y H⟩

@[simp]
theorem mk_add_mk (x y : ℕ × K) :
    mk K p x + mk K p y = mk K p (x.1 + y.1, (frobenius K p^[y.1]) x.2 + (frobenius K p^[x.1]) y.2) :=
  rfl

instance : Neg (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => mk K p (x.1, -x.2)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, r.intro n x =>
        Quot.sound <| by
          rw [← frobenius_neg] <;> apply r.intro⟩

@[simp]
theorem neg_mk (x : ℕ × K) : -mk K p x = mk K p (x.1, -x.2) :=
  rfl

instance : Zero (PerfectClosure K p) :=
  ⟨mk K p (0, 0)⟩

theorem zero_def : (0 : PerfectClosure K p) = mk K p (0, 0) :=
  rfl

@[simp]
theorem mk_zero_zero : mk K p (0, 0) = 0 :=
  rfl

theorem mk_zero (n : ℕ) : mk K p (n, 0) = 0 := by
  induction' n with n ih <;> [rfl, rw [← ih]] <;>
    symm <;> apply Quot.sound <;> have := r.intro n (0 : K) <;> rwa [frobenius_zero K p] at this

theorem R.sound (m n : ℕ) (x y : K) (H : (frobenius K p^[m]) x = y) : mk K p (n, x) = mk K p (m + n, y) := by
  subst H <;>
    induction' m with m ih <;> [simp only [← zero_addₓ, ← iterate_zero_apply], rw [ih, Nat.succ_add, iterate_succ']] <;>
      apply Quot.sound <;> apply r.intro

instance : AddCommGroupₓ (PerfectClosure K p) :=
  { (inferInstance : Add (PerfectClosure K p)), (inferInstance : Neg (PerfectClosure K p)) with
    add_assoc := fun e f g =>
      (Quot.induction_on e) fun ⟨m, x⟩ =>
        (Quot.induction_on f) fun ⟨n, y⟩ =>
          (Quot.induction_on g) fun ⟨s, z⟩ =>
            congr_arg (Quot.mk _) <| by
              simp only [← RingHom.iterate_map_add, iterate_add_apply, ← add_assocₓ, ← add_commₓ s _],
    zero := 0,
    zero_add := fun e =>
      Quot.induction_on e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [← RingHom.iterate_map_zero, ← iterate_zero_apply, ← zero_addₓ],
    add_zero := fun e =>
      Quot.induction_on e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [← RingHom.iterate_map_zero, ← iterate_zero_apply, ← add_zeroₓ],
    sub_eq_add_neg := fun a b => rfl,
    add_left_neg := fun e =>
      Quot.induction_on e fun ⟨n, x⟩ => by
        simp only [← quot_mk_eq_mk, ← neg_mk, ← mk_add_mk, ← RingHom.iterate_map_neg, ← add_left_negₓ, ← mk_zero],
    add_comm := fun e f =>
      Quot.induction_on e fun ⟨m, x⟩ =>
        Quot.induction_on f fun ⟨n, y⟩ =>
          congr_arg (Quot.mk _) <| by
            simp only [← add_commₓ] }

instance : CommRingₓ (PerfectClosure K p) :=
  { PerfectClosure.addCommGroup K p, AddMonoidWithOneₓ.unary, (inferInstance : CommMonoidₓ (PerfectClosure K p)) with
    left_distrib := fun e f g =>
      (Quot.induction_on e) fun ⟨m, x⟩ =>
        (Quot.induction_on f) fun ⟨n, y⟩ =>
          (Quot.induction_on g) fun ⟨s, z⟩ =>
            show Quot.mk _ _ = Quot.mk _ _ by
              simp only [← add_assocₓ, ← add_commₓ, ← add_left_commₓ] <;>
                apply r.sound <;>
                  simp only [← RingHom.iterate_map_mul, ← RingHom.iterate_map_add, iterate_add_apply, ← mul_addₓ, ←
                    add_commₓ, ← add_left_commₓ],
    right_distrib := fun e f g =>
      (Quot.induction_on e) fun ⟨m, x⟩ =>
        (Quot.induction_on f) fun ⟨n, y⟩ =>
          (Quot.induction_on g) fun ⟨s, z⟩ =>
            show Quot.mk _ _ = Quot.mk _ _ by
              simp only [← add_assocₓ, ← add_commₓ _ s, ← add_left_commₓ _ s] <;>
                apply r.sound <;>
                  simp only [← RingHom.iterate_map_mul, ← RingHom.iterate_map_add, iterate_add_apply, ← add_mulₓ, ←
                    add_commₓ, ← add_left_commₓ] }

theorem eq_iff' (x y : ℕ × K) :
    mk K p x = mk K p y ↔ ∃ z, (frobenius K p^[y.1 + z]) x.2 = (frobenius K p^[x.1 + z]) y.2 := by
  constructor
  · intro H
    replace H := Quot.exact _ H
    induction H
    case eqv_gen.rel x y H =>
      cases' H with n x
      exact ⟨0, rfl⟩
    case eqv_gen.refl H =>
      exact ⟨0, rfl⟩
    case eqv_gen.symm x y H ih =>
      cases' ih with w ih
      exact ⟨w, ih.symm⟩
    case eqv_gen.trans x y z H1 H2 ih1 ih2 =>
      cases' ih1 with z1 ih1
      cases' ih2 with z2 ih2
      exists z2 + (y.1 + z1)
      rw [← add_assocₓ, iterate_add_apply, ih1]
      rw [← iterate_add_apply, add_commₓ, iterate_add_apply, ih2]
      rw [← iterate_add_apply]
      simp only [← add_commₓ, ← add_left_commₓ]
    
  intro H
  cases' x with m x
  cases' y with n y
  cases' H with z H
  dsimp' only  at H
  rw [r.sound K p (n + z) m x _ rfl, r.sound K p (m + z) n y _ rfl, H]
  rw [add_assocₓ, add_commₓ, add_commₓ z]

theorem nat_cast (n x : ℕ) : (x : PerfectClosure K p) = mk K p (n, x) := by
  induction' n with n ih
  · induction' x with x ih
    · simp
      
    rw [Nat.cast_succₓ, Nat.cast_succₓ, ih]
    rfl
    
  rw [ih]
  apply Quot.sound
  conv => congr skip skip rw [← frobenius_nat_cast K p x]
  apply r.intro

theorem int_cast (x : ℤ) : (x : PerfectClosure K p) = mk K p (0, x) := by
  induction x <;> simp only [← Int.cast_of_nat, ← Int.cast_neg_succ_of_nat, ← nat_cast K p 0] <;> rfl

theorem nat_cast_eq_iff (x y : ℕ) : (x : PerfectClosure K p) = y ↔ (x : K) = y := by
  constructor <;> intro H
  · rw [nat_cast K p 0, nat_cast K p 0, eq_iff'] at H
    cases' H with z H
    simpa only [← zero_addₓ, ← iterate_fixed (frobenius_nat_cast K p _)] using H
    
  rw [nat_cast K p 0, nat_cast K p 0, H]

instance : CharP (PerfectClosure K p) p := by
  constructor
  intro x
  rw [← CharP.cast_eq_zero_iff K]
  rw [← Nat.cast_zeroₓ, nat_cast_eq_iff, Nat.cast_zeroₓ]

theorem frobenius_mk (x : ℕ × K) :
    (frobenius (PerfectClosure K p) p : PerfectClosure K p → PerfectClosure K p) (mk K p x) = mk _ _ (x.1, x.2 ^ p) :=
  by
  simp only [← frobenius_def]
  cases' x with n x
  dsimp' only
  suffices ∀ p' : ℕ, mk K p (n, x) ^ p' = mk K p (n, x ^ p') by
    apply this
  intro p
  induction' p with p ih
  case nat.zero =>
    apply r.sound
    rw [(frobenius _ _).iterate_map_one, pow_zeroₓ]
  case nat.succ =>
    rw [pow_succₓ, ih]
    symm
    apply r.sound
    simp only [← pow_succₓ, ← (frobenius _ _).iterate_map_mul]

/-- Embedding of `K` into `perfect_closure K p` -/
def of : K →+* PerfectClosure K p where
  toFun := fun x => mk _ _ (0, x)
  map_one' := rfl
  map_mul' := fun x y => rfl
  map_zero' := rfl
  map_add' := fun x y => rfl

theorem of_apply (x : K) : of K p x = mk _ _ (0, x) :=
  rfl

end Ringₓ

theorem eq_iff [CommRingₓ K] [IsDomain K] (p : ℕ) [Fact p.Prime] [CharP K p] (x y : ℕ × K) :
    Quot.mk (R K p) x = Quot.mk (R K p) y ↔ (frobenius K p^[y.1]) x.2 = (frobenius K p^[x.1]) y.2 :=
  (eq_iff' K p x y).trans
    ⟨fun ⟨z, H⟩ =>
      (frobenius_inj K p).iterate z <| by
        simpa only [← add_commₓ, ← iterate_add] using H,
      fun H => ⟨0, H⟩⟩

section Field

variable [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

instance : Inv (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => Quot.mk (R K p) (x.1, x.2⁻¹)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, r.intro n x =>
        Quot.sound <| by
          simp only [← frobenius_def]
          rw [← inv_pow]
          apply r.intro⟩

instance : Field (PerfectClosure K p) :=
  { (inferInstance : Inv (PerfectClosure K p)), (inferInstance : CommRingₓ (PerfectClosure K p)) with
    exists_pair_ne := ⟨0, 1, fun H => zero_ne_one ((eq_iff _ _ _ _).1 H)⟩,
    mul_inv_cancel := fun e =>
      (induction_on e) fun ⟨m, x⟩ H =>
        have := mt (eq_iff _ _ _ _).2 H
        (eq_iff _ _ _ _).2
          (by
            simp only [← (frobenius _ _).iterate_map_one, ← (frobenius K p).iterate_map_zero, ← iterate_zero_apply,
                (frobenius _ p).iterate_map_mul] at this⊢ <;>
              rw [mul_inv_cancel this, (frobenius _ _).iterate_map_one]),
    inv_zero :=
      congr_arg (Quot.mk (R K p))
        (by
          rw [inv_zero]) }

instance : PerfectRing (PerfectClosure K p) p where
  pthRoot' := fun e =>
    liftOn e (fun x => mk K p (x.1 + 1, x.2)) fun x y H =>
      match x, y, H with
      | _, _, r.intro n x => Quot.sound (R.intro _ _)
  frobenius_pth_root' := fun e =>
    induction_on e fun ⟨n, x⟩ => by
      simp only [← lift_on_mk, ← frobenius_mk]
      exact (Quot.sound <| r.intro _ _).symm
  pth_root_frobenius' := fun e =>
    induction_on e fun ⟨n, x⟩ => by
      simp only [← lift_on_mk, ← frobenius_mk]
      exact (Quot.sound <| r.intro _ _).symm

theorem eq_pth_root (x : ℕ × K) : mk K p x = (pthRoot (PerfectClosure K p) p^[x.1]) (of K p x.2) := by
  rcases x with ⟨m, x⟩
  induction' m with m ih
  · rfl
    
  rw [iterate_succ_apply', ← ih] <;> rfl

/-- Given a field `K` of characteristic `p` and a perfect ring `L` of the same characteristic,
any homomorphism `K →+* L` can be lifted to `perfect_closure K p`. -/
def lift (L : Type v) [CommSemiringₓ L] [CharP L p] [PerfectRing L p] : (K →+* L) ≃ (PerfectClosure K p →+* L) := by
  have := left_inverse_pth_root_frobenius.iterate
  refine_struct { .. }
  field to_fun =>
    intro f
    refine_struct { .. }
    field to_fun =>
      refine' fun e => lift_on e (fun x => (pthRoot L p^[x.1]) (f x.2)) _
      rintro a b ⟨n⟩
      simp only [← f.map_frobenius, ← iterate_succ_apply, ← pth_root_frobenius]
    field map_one' =>
      exact f.map_one
    field map_zero' =>
      exact f.map_zero
    field map_mul' =>
      rintro ⟨x⟩ ⟨y⟩
      simp only [← quot_mk_eq_mk, ← lift_on_mk, ← mk_mul_mk, ← RingHom.map_iterate_frobenius, ← RingHom.iterate_map_mul,
        ← RingHom.map_mul]
      rw [iterate_add_apply, this _ _, add_commₓ, iterate_add_apply, this _ _]
    field map_add' =>
      rintro ⟨x⟩ ⟨y⟩
      simp only [← quot_mk_eq_mk, ← lift_on_mk, ← mk_add_mk, ← RingHom.map_iterate_frobenius, ← RingHom.iterate_map_add,
        ← RingHom.map_add]
      rw [iterate_add_apply, this _ _, add_commₓ x.1, iterate_add_apply, this _ _]
  field inv_fun =>
    exact fun f => f.comp (of K p)
  field left_inv =>
    intro f
    ext x
    rfl
  field right_inv =>
    intro f
    ext ⟨x⟩
    simp only [← RingHom.coe_mk, ← quot_mk_eq_mk, ← RingHom.comp_apply, ← lift_on_mk]
    rw [eq_pth_root, RingHom.map_iterate_pth_root]

end Field

end PerfectClosure

/-- A reduced ring with prime characteristic and surjective frobenius map is perfect. -/
noncomputable def PerfectRing.ofSurjective (k : Type _) [CommRingₓ k] [IsReduced k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (h : Function.Surjective <| frobenius k p) : PerfectRing k p where
  pthRoot' := Function.surjInv h
  frobenius_pth_root' := Function.surj_inv_eq h
  pth_root_frobenius' := fun x => frobenius_inj _ _ <| Function.surj_inv_eq h _

