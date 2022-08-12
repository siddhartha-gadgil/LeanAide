/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.RingTheory.WittVector.InitTail

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.

## Main declarations

- `truncated_witt_vector`: the underlying type of the ring of truncated Witt vectors
- `truncated_witt_vector.comm_ring`: the ring structure on truncated Witt vectors
- `witt_vector.truncate`: the quotient homomorphism that truncates a Witt vector,
  to obtain a truncated Witt vector
- `truncated_witt_vector.truncate`: the homomorphism that truncates
  a truncated Witt vector of length `n` to one of length `m` (for some `m ≤ n`)
- `witt_vector.lift`: the unique ring homomorphism into the ring of Witt vectors
  that is compatible with a family of ring homomorphisms to the truncated Witt vectors:
  this realizes the ring of Witt vectors as projective limit of the rings of truncated Witt vectors

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


open Function (Injective Surjective)

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime] (n : ℕ) (R : Type _)

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

/-- A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`truncated_witt_vector p n R` takes a parameter `p : ℕ` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `truncated_witt_vector p n R`.
(`truncated_witt_vector p₁ n R` and `truncated_witt_vector p₂ n R` are definitionally
equal as types but will have different ring operations.)
-/
-- type as `\bbW`
@[nolint unused_arguments]
def TruncatedWittVector (p : ℕ) (n : ℕ) (R : Type _) :=
  Finₓ n → R

instance (p n : ℕ) (R : Type _) [Inhabited R] : Inhabited (TruncatedWittVector p n R) :=
  ⟨fun _ => default⟩

variable {n R}

namespace TruncatedWittVector

variable (p)

/-- Create a `truncated_witt_vector` from a vector `x`. -/
def mk (x : Finₓ n → R) : TruncatedWittVector p n R :=
  x

variable {p}

/-- `x.coeff i` is the `i`th entry of `x`. -/
def coeff (i : Finₓ n) (x : TruncatedWittVector p n R) : R :=
  x i

@[ext]
theorem ext {x y : TruncatedWittVector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
  funext h

theorem ext_iff {x y : TruncatedWittVector p n R} : x = y ↔ ∀ i, x.coeff i = y.coeff i :=
  ⟨fun h i => by
    rw [h], ext⟩

@[simp]
theorem coeff_mk (x : Finₓ n → R) (i : Finₓ n) : (mk p x).coeff i = x i :=
  rfl

@[simp]
theorem mk_coeff (x : TruncatedWittVector p n R) : (mk p fun i => x.coeff i) = x := by
  ext i
  rw [coeff_mk]

variable [CommRingₓ R]

/-- We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out (x : TruncatedWittVector p n R) : 𝕎 R :=
  (WittVector.mk p) fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]
theorem coeff_out (x : TruncatedWittVector p n R) (i : Finₓ n) : x.out.coeff i = x.coeff i := by
  rw [out, WittVector.coeff_mk, dif_pos i.is_lt, Finₓ.eta]

theorem out_injective : Injective (@out p n R _) := by
  intro x y h
  ext i
  rw [WittVector.ext_iff] at h
  simpa only [← coeff_out] using h ↑i

end TruncatedWittVector

namespace WittVector

variable {p} (n)

section

/-- `truncate_fun n x` uses the first `n` entries of `x` to construct a `truncated_witt_vector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `witt_vector.truncate` -/
def truncateFun (x : 𝕎 R) : TruncatedWittVector p n R :=
  (TruncatedWittVector.mk p) fun i => x.coeff i

end

variable {n}

@[simp]
theorem coeff_truncate_fun (x : 𝕎 R) (i : Finₓ n) : (truncateFun n x).coeff i = x.coeff i := by
  rw [truncate_fun, TruncatedWittVector.coeff_mk]

variable [CommRingₓ R]

@[simp]
theorem out_truncate_fun (x : 𝕎 R) : (truncateFun n x).out = init n x := by
  ext i
  dsimp' [← TruncatedWittVector.out, ← init, ← select]
  split_ifs with hi
  swap
  · rfl
    
  rw [coeff_truncate_fun, Finₓ.coe_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRingₓ R]

@[simp]
theorem truncate_fun_out (x : TruncatedWittVector p n R) : x.out.truncateFun n = x := by
  simp only [← WittVector.truncateFun, ← coeff_out, ← mk_coeff]

open WittVector

variable (p n R)

include hp

instance : Zero (TruncatedWittVector p n R) :=
  ⟨truncateFun n 0⟩

instance : One (TruncatedWittVector p n R) :=
  ⟨truncateFun n 1⟩

instance : HasNatCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩

instance : HasIntCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩

instance : Add (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out + y.out)⟩

instance : Mul (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out * y.out)⟩

instance : Neg (TruncatedWittVector p n R) :=
  ⟨fun x => truncateFun n (-x.out)⟩

instance : Sub (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out - y.out)⟩

instance hasNatScalar : HasSmul ℕ (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩

instance hasIntScalar : HasSmul ℤ (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩

instance hasNatPow : Pow (TruncatedWittVector p n R) ℕ :=
  ⟨fun x m => truncateFun n (x.out ^ m)⟩

@[simp]
theorem coeff_zero (i : Finₓ n) : (0 : TruncatedWittVector p n R).coeff i = 0 := by
  show coeff i (truncate_fun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncate_fun, WittVector.zero_coeff]

end TruncatedWittVector

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A macro tactic used to prove that `truncate_fun` respects ring operations. -/
unsafe def tactic.interactive.witt_truncate_fun_tac : tactic Unit :=
  sorry

namespace WittVector

variable (p n R)

variable [CommRingₓ R]

theorem truncate_fun_surjective : Surjective (@truncateFun p n R) :=
  Function.RightInverse.surjective TruncatedWittVector.truncate_fun_out

include hp

@[simp]
theorem truncate_fun_zero : truncateFun n (0 : 𝕎 R) = 0 :=
  rfl

@[simp]
theorem truncate_fun_one : truncateFun n (1 : 𝕎 R) = 1 :=
  rfl

variable {p R}

@[simp]
theorem truncate_fun_add (x y : 𝕎 R) : truncateFun n (x + y) = truncateFun n x + truncateFun n y := by
  witt_truncate_fun_tac
  rw [init_add]

@[simp]
theorem truncate_fun_mul (x y : 𝕎 R) : truncateFun n (x * y) = truncateFun n x * truncateFun n y := by
  witt_truncate_fun_tac
  rw [init_mul]

theorem truncate_fun_neg (x : 𝕎 R) : truncateFun n (-x) = -truncateFun n x := by
  witt_truncate_fun_tac
  rw [init_neg]

theorem truncate_fun_sub (x y : 𝕎 R) : truncateFun n (x - y) = truncateFun n x - truncateFun n y := by
  witt_truncate_fun_tac
  rw [init_sub]

theorem truncate_fun_nsmul (x : 𝕎 R) (m : ℕ) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncate_fun_tac
  rw [init_nsmul]

theorem truncate_fun_zsmul (x : 𝕎 R) (m : ℤ) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncate_fun_tac
  rw [init_zsmul]

theorem truncate_fun_pow (x : 𝕎 R) (m : ℕ) : truncateFun n (x ^ m) = truncateFun n x ^ m := by
  witt_truncate_fun_tac
  rw [init_pow]

theorem truncate_fun_nat_cast (m : ℕ) : truncateFun n (m : 𝕎 R) = m :=
  rfl

theorem truncate_fun_int_cast (m : ℤ) : truncateFun n (m : 𝕎 R) = m :=
  rfl

end WittVector

namespace TruncatedWittVector

open WittVector

variable (p n R)

variable [CommRingₓ R]

include hp

instance : CommRingₓ (TruncatedWittVector p n R) :=
  (truncate_fun_surjective p n R).CommRing _ (truncate_fun_zero p n R) (truncate_fun_one p n R) (truncate_fun_add n)
    (truncate_fun_mul n) (truncate_fun_neg n) (truncate_fun_sub n) (truncate_fun_nsmul n) (truncate_fun_zsmul n)
    (truncate_fun_pow n) (truncate_fun_nat_cast n) (truncate_fun_int_cast n)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (n)

variable [CommRingₓ R]

include hp

/-- `truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `truncated_witt_vector`, which has the same base `p` as `x`. -/
noncomputable def truncate : 𝕎 R →+* TruncatedWittVector p n R where
  toFun := truncateFun n
  map_zero' := truncate_fun_zero p n R
  map_add' := truncate_fun_add n
  map_one' := truncate_fun_one p n R
  map_mul' := truncate_fun_mul n

variable (p n R)

theorem truncate_surjective : Surjective (truncate n : 𝕎 R → TruncatedWittVector p n R) :=
  truncate_fun_surjective p n R

variable {p n R}

@[simp]
theorem coeff_truncate (x : 𝕎 R) (i : Finₓ n) : (truncate n x).coeff i = x.coeff i :=
  coeff_truncate_fun _ _

variable (n)

theorem mem_ker_truncate (x : 𝕎 R) : x ∈ (@truncate p _ n R _).ker ↔ ∀, ∀ i < n, ∀, x.coeff i = 0 := by
  simp only [← RingHom.mem_ker, ← truncate, ← truncate_fun, ← RingHom.coe_mk, ← TruncatedWittVector.ext_iff, ←
    TruncatedWittVector.coeff_mk, ← coeff_zero]
  exact Subtype.forall

variable (p)

@[simp]
theorem truncate_mk (f : ℕ → R) : truncate n (mk p f) = TruncatedWittVector.mk _ fun k => f k := by
  ext i
  rw [coeff_truncate, coeff_mk, TruncatedWittVector.coeff_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRingₓ R]

include hp

/-- A ring homomorphism that truncates a truncated Witt vector of length `m` to
a truncated Witt vector of length `n`, for `n ≤ m`.
-/
def truncate {m : ℕ} (hm : n ≤ m) : TruncatedWittVector p m R →+* TruncatedWittVector p n R :=
  RingHom.liftOfRightInverse (WittVector.truncate m) out truncate_fun_out
    ⟨WittVector.truncate n, by
      intro x
      simp only [← WittVector.mem_ker_truncate]
      intro h i hi
      exact h i (lt_of_lt_of_leₓ hi hm)⟩

@[simp]
theorem truncate_comp_witt_vector_truncate {m : ℕ} (hm : n ≤ m) :
    (@truncate p _ n R _ m hm).comp (WittVector.truncate m) = WittVector.truncate n :=
  RingHom.lift_of_right_inverse_comp _ _ _ _

@[simp]
theorem truncate_witt_vector_truncate {m : ℕ} (hm : n ≤ m) (x : 𝕎 R) :
    truncate hm (WittVector.truncate m x) = WittVector.truncate n x :=
  RingHom.lift_of_right_inverse_comp_apply _ _ _ _ _

@[simp]
theorem truncate_truncate {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) (x : TruncatedWittVector p n₃ R) :
    (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n₃ R x
  simp only [← truncate_witt_vector_truncate]

@[simp]
theorem truncate_comp {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
    (@truncate p _ _ R _ _ h1).comp (truncate h2) = truncate (h1.trans h2) := by
  ext1 x
  simp only [← truncate_truncate, ← Function.comp_app, ← RingHom.coe_comp]

theorem truncate_surjective {m : ℕ} (hm : n ≤ m) : Surjective (@truncate p _ _ R _ _ hm) := by
  intro x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p _ R x
  exact ⟨WittVector.truncate _ x, truncate_witt_vector_truncate _ _⟩

@[simp]
theorem coeff_truncate {m : ℕ} (hm : n ≤ m) (i : Finₓ n) (x : TruncatedWittVector p m R) :
    (truncate hm x).coeff i = x.coeff (Finₓ.castLe hm i) := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p _ _ x
  simp only [← truncate_witt_vector_truncate, ← WittVector.coeff_truncate, ← Finₓ.coe_cast_le]

section Fintype

omit hp

instance {R : Type _} [Fintype R] : Fintype (TruncatedWittVector p n R) :=
  Pi.fintype

variable (p n R)

theorem card {R : Type _} [Fintype R] : Fintype.card (TruncatedWittVector p n R) = Fintype.card R ^ n := by
  simp only [← TruncatedWittVector, ← Fintype.card_fin, ← Fintype.card_fun]

end Fintype

theorem infi_ker_truncate : (⨅ i : ℕ, (@WittVector.truncate p _ i R _).ker) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext
  simp only [← WittVector.mem_ker_truncate, ← Ideal.mem_infi, ← WittVector.zero_coeff] at hx⊢
  exact hx _ _ (Nat.lt_succ_selfₓ _)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector hiding truncate coeff

section lift

variable [CommRingₓ R]

variable {S : Type _} [Semiringₓ S]

variable (f : ∀ k : ℕ, S →+* TruncatedWittVector p k R)

variable (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁)

variable {p R}

variable (n)

/-- Given a family `fₖ : S → truncated_witt_vector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
def liftFun (s : S) : 𝕎 R :=
  (WittVector.mk p) fun k => TruncatedWittVector.coeff (Finₓ.last k) (f (k + 1) s)

variable {f}

include f_compat

@[simp]
theorem truncate_lift_fun (s : S) : WittVector.truncate n (liftFun f s) = f n s := by
  ext i
  simp only [← lift_fun, ← TruncatedWittVector.coeff_mk, ← WittVector.truncate_mk]
  rw [← f_compat (i + 1) n i.is_lt, RingHom.comp_apply, TruncatedWittVector.coeff_truncate]
  -- this is a bit unfortunate
  congr with _
  simp only [← Finₓ.coe_last, ← Finₓ.coe_cast_le]

variable (f)

/-- Given compatible ring homs from `S` into `truncated_witt_vector n` for each `n`, we can lift these
to a ring hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `truncated_witt_vector n`.
-/
def lift : S →+* 𝕎 R := by
  refine_struct { toFun := lift_fun f } <;>
    · intros
      rw [← sub_eq_zero, ← Ideal.mem_bot, ← infi_ker_truncate, Ideal.mem_infi]
      simp [← RingHom.mem_ker, ← f_compat]
      

variable {f}

@[simp]
theorem truncate_lift (s : S) : WittVector.truncate n (lift _ f_compat s) = f n s :=
  truncate_lift_fun _ f_compat s

@[simp]
theorem truncate_comp_lift : (WittVector.truncate n).comp (lift _ f_compat) = f n := by
  ext1
  rw [RingHom.comp_apply, truncate_lift]

/-- The uniqueness part of the universal property of `𝕎 R`. -/
theorem lift_unique (g : S →+* 𝕎 R) (g_compat : ∀ k, (WittVector.truncate k).comp g = f k) : lift _ f_compat = g := by
  ext1 x
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← infi_ker_truncate, Ideal.mem_infi]
  intro i
  simp only [← RingHom.mem_ker, ← g_compat, RingHom.comp_apply, ← truncate_comp_lift, ← RingHom.map_sub, ← sub_self]

omit f_compat

include hp

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps]
def liftEquiv :
    { f : ∀ k, S →+* TruncatedWittVector p k R //
        ∀ (k₁ k₂) (hk : k₁ ≤ k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁ } ≃
      (S →+* 𝕎 R) where
  toFun := fun f => lift f.1 f.2
  invFun := fun g =>
    ⟨fun k => (truncate k).comp g, by
      intro _ _ h
      simp only [RingHom.comp_assoc, ← truncate_comp_witt_vector_truncate]⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [← truncate_comp_lift]
  right_inv := fun g => (lift_unique _ _) fun _ => rfl

theorem hom_ext (g₁ g₂ : S →+* 𝕎 R) (h : ∀ k, (truncate k).comp g₁ = (truncate k).comp g₂) : g₁ = g₂ :=
  liftEquiv.symm.Injective <| Subtype.ext <| funext h

end lift

end WittVector

