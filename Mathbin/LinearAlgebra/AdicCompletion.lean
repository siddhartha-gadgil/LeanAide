/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.GeomSum
import Mathbin.LinearAlgebra.Smodeq
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.JacobsonIdeal

/-!
# Completion of a module with respect to an ideal.

In this file we define the notions of Hausdorff, precomplete, and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `is_Hausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `is_precomplete I M`: this says that every Cauchy sequence converges.
- `is_adic_complete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorffification I M`: this is the universal Hausdorff module with a map from `M`.
- `completion I M`: if `I` is finitely generated, then this is the universal complete module (TODO)
  with a map from `M`. This map is injective iff `M` is Hausdorff and surjective iff `M` is
  precomplete.

-/


open Submodule

variable {R : Type _} [CommRingₓ R] (I : Ideal R)

variable (M : Type _) [AddCommGroupₓ M] [Module R M]

variable {N : Type _} [AddCommGroupₓ N] [Module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
class IsHausdorff : Prop where
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
class IsPrecomplete : Prop where
  prec' :
    ∀ f : ℕ → M,
      (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
        ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
class IsAdicComplete extends IsHausdorff I M, IsPrecomplete I M : Prop

variable {I M}

theorem IsHausdorff.haus (h : IsHausdorff I M) : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  IsHausdorff.haus'

theorem is_Hausdorff_iff : IsHausdorff I M ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩

theorem IsPrecomplete.prec (h : IsPrecomplete I M) {f : ℕ → M} :
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _

theorem is_precomplete_iff :
    IsPrecomplete I M ↔
      ∀ f : ℕ → M,
        (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
          ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

variable (I M)

/-- The Hausdorffification of a module with respect to an ideal. -/
@[reducible]
def Hausdorffification : Type _ :=
  M ⧸ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M)

/-- The completion of a module with respect to an ideal. This is not necessarily Hausdorff.
In fact, this is only complete if the ideal is finitely generated. -/
def adicCompletion : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  Carrier :=
    { f |
      ∀ {m n} (h : m ≤ n),
        liftq _ (mkq _)
            (by
              rw [ker_mkq]
              exact smul_mono (Ideal.pow_le_pow h) le_rfl)
            (f n) =
          f m }
  zero_mem' := fun m n hmn => by
    rw [Pi.zero_apply, Pi.zero_apply, LinearMap.map_zero]
  add_mem' := fun f g hf hg m n hmn => by
    rw [Pi.add_apply, Pi.add_apply, LinearMap.map_add, hf hmn, hg hmn]
  smul_mem' := fun c f hf m n hmn => by
    rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hf hmn]

namespace IsHausdorff

instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by
    simpa only [← pow_oneₓ ⊥, ← bot_smul, ← Smodeq.bot] using hx 1⟩

variable {M}

protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y =>
    eq_of_sub_eq_zero <|
      (h.haus (x - y)) fun n => by
        rw [Ideal.top_pow, top_smul]
        exact Smodeq.top⟩

variable (M)

instance (priority := 100) of_subsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun x _ => Subsingleton.elimₓ _ _⟩

variable {I M}

theorem infi_pow_smul (h : IsHausdorff I M) : (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2 fun x hx =>
    (mem_bot _).2 <| (h.haus x) fun n => Smodeq.zero.2 <| (mem_infi fun n : ℕ => I ^ n • ⊤).1 hx n

end IsHausdorff

namespace Hausdorffification

/-- The canonical linear map to the Hausdorffification. -/
def of : M →ₗ[R] Hausdorffification I M :=
  mkq _

variable {I M}

@[elab_as_eliminator]
theorem induction_on {C : Hausdorffification I M → Prop} (x : Hausdorffification I M) (ih : ∀ x, C (of I M x)) : C x :=
  Quotientₓ.induction_on' x ih

variable (I M)

instance : IsHausdorff I (Hausdorffification I M) :=
  ⟨fun x =>
    (Quotientₓ.induction_on' x) fun x hx =>
      (Quotient.mk_eq_zero _).2 <|
        (mem_infi _).2 fun n => by
          have := comap_map_mkq (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
          simp only [← sup_of_le_right (infi_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
          rw [← this, map_smul'', mem_comap, map_top, range_mkq, ← Smodeq.zero]
          exact hx n⟩

variable {M} [h : IsHausdorff I N]

include h

/-- universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftq _ f <|
    map_le_iff_le_comap.1 <|
      h.infi_pow_smul ▸
        le_infi fun n =>
          le_transₓ (map_mono <| infi_le _ n) <| by
            rw [map_smul'']
            exact smul_mono le_rfl le_top

theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl

theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext fun _ => rfl

/-- Uniqueness of lift. -/
theorem lift_eq (f : M →ₗ[R] N) (g : Hausdorffification I M →ₗ[R] N) (hg : g.comp (of I M) = f) : g = lift I f :=
  LinearMap.ext fun x =>
    (induction_on x) fun x => by
      rw [lift_of, ← hg, LinearMap.comp_apply]

end Hausdorffification

namespace IsPrecomplete

instance bot : IsPrecomplete (⊥ : Ideal R) M := by
  refine' ⟨fun f hf => ⟨f 1, fun n => _⟩⟩
  cases n
  · rw [pow_zeroₓ, Ideal.one_eq_top, top_smul]
    exact Smodeq.top
    
  specialize hf (Nat.le_add_leftₓ 1 n)
  rw [pow_oneₓ, bot_smul, Smodeq.bot] at hf
  rw [hf]

instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f hf =>
    ⟨0, fun n => by
      rw [Ideal.top_pow, top_smul]
      exact Smodeq.top⟩⟩

instance (priority := 100) of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f hf =>
    ⟨0, fun n => by
      rw [Subsingleton.elimₓ (f n) 0]⟩⟩

end IsPrecomplete

namespace adicCompletion

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] adicCompletion I M where
  toFun := fun x => ⟨fun n => mkq _ x, fun m n hmn => rfl⟩
  map_add' := fun x y => rfl
  map_smul' := fun c x => rfl

@[simp]
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkq _ x :=
  rfl

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : adicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun := fun f => f.1 n
  map_add' := fun f g => rfl
  map_smul' := fun c f => rfl

@[simp]
theorem coe_eval (n : ℕ) : (eval I M n : adicCompletion I M → M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl

theorem eval_apply (n : ℕ) (f : adicCompletion I M) : eval I M n f = f.1 n :=
  rfl

theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkq _ x :=
  rfl

@[simp]
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkq _ :=
  rfl

@[simp]
theorem range_eval (n : ℕ) : (eval I M n).range = ⊤ :=
  LinearMap.range_eq_top.2 fun x => (Quotientₓ.induction_on' x) fun x => ⟨of I M x, rfl⟩

variable {I M}

@[ext]
theorem ext {x y : adicCompletion I M} (h : ∀ n, eval I M n x = eval I M n y) : x = y :=
  Subtype.eq <| funext h

variable (I M)

instance : IsHausdorff I (adicCompletion I M) :=
  ⟨fun x hx =>
    ext fun n =>
      smul_induction_on (Smodeq.zero.1 <| hx n)
        (fun r hr x _ =>
          ((eval I M n).map_smul r x).symm ▸
            Quotientₓ.induction_on' (eval I M n x) fun x => Smodeq.zero.2 <| smul_mem_smul hr mem_top)
        fun _ _ ih1 ih2 => by
        rw [LinearMap.map_add, ih1, ih2, LinearMap.map_zero, add_zeroₓ]⟩

end adicCompletion

namespace IsAdicComplete

instance bot : IsAdicComplete (⊥ : Ideal R) M where

protected theorem subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.Subsingleton

instance (priority := 100) of_subsingleton [Subsingleton M] : IsAdicComplete I M where

open BigOperators

open Finset

theorem le_jacobson_bot [IsAdicComplete I R] : I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [← Ideal.neg_mem_iff, Ideal.mem_jacobson_bot]
  intro y
  rw [add_commₓ]
  let f : ℕ → R := fun n => ∑ i in range n, (x * y) ^ i
  have hf : ∀ m n, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [← f, ← Algebra.id.smul_eq_mul, ← Ideal.mul_top, ← Smodeq.sub_mem]
    rw [← add_tsub_cancel_of_le h, Finset.sum_range_add, ← sub_sub, sub_self, zero_sub, neg_mem_iff]
    apply Submodule.sum_mem
    intro n hn
    rw [mul_powₓ, pow_addₓ, mul_assoc]
    exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hx m)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec to_is_precomplete hf
  · rw [is_unit_iff_exists_inv]
    use L
    rw [← sub_eq_zero, neg_mul]
    apply IsHausdorff.haus (to_is_Hausdorff : IsHausdorff I R)
    intro n
    specialize hL n
    rw [Smodeq.sub_mem, Algebra.id.smul_eq_mul, Ideal.mul_top] at hL⊢
    rw [sub_zero]
    suffices (1 - x * y) * f n - 1 ∈ I ^ n by
      convert Ideal.sub_mem _ this (Ideal.mul_mem_left _ (1 + -(x * y)) hL) using 1
      ring
    cases n
    · simp only [← Ideal.one_eq_top, ← pow_zeroₓ]
      
    · dsimp' [← f]
      rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_commₓ, ← sub_sub, sub_self, zero_sub,
        neg_mem_iff, mul_powₓ]
      exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)
      
    

end IsAdicComplete

