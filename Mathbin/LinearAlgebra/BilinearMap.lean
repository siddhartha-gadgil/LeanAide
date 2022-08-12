/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import Mathbin.LinearAlgebra.Basic
import Mathbin.LinearAlgebra.Basis

/-!
# Basics on bilinear maps

This file provides basics on bilinear maps. The most general form considered are maps that are
semilinear in both arguments. They are of type `M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P`, where `M` and `N`
are modules over `R` and `S` respectively, `P` is a module over both `R₂` and `S₂` with
commuting actions, and `ρ₁₂ : R →+* R₂` and `σ₁₂ : S →+* S₂`.

## Main declarations

* `linear_map.mk₂`: a constructor for bilinear maps,
  taking an unbundled function together with proof witnesses of bilinearity
* `linear_map.flip`: turns a bilinear map `M × N → P` into `N × M → P`
* `linear_map.lcomp` and `linear_map.llcomp`: composition of linear maps as a bilinear map
* `linear_map.compl₂`: composition of a bilinear map `M × N → P` with a linear map `Q → M`
* `linear_map.compr₂`: composition of a bilinear map `M × N → P` with a linear map `Q → N`
* `linear_map.lsmul`: scalar multiplication as a bilinear map `R × M → M`

## Tags

bilinear
-/


variable {ι₁ ι₂ : Type _}

namespace LinearMap

section Semiringₓ

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {R : Type _} [Semiringₓ R] {S : Type _} [Semiringₓ S]

variable {R₂ : Type _} [Semiringₓ R₂] {S₂ : Type _} [Semiringₓ S₂]

variable {M : Type _} {N : Type _} {P : Type _}

variable {M₂ : Type _} {N₂ : Type _} {P₂ : Type _}

variable {Nₗ : Type _} {Pₗ : Type _}

variable {M' : Type _} {N' : Type _} {P' : Type _}

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P]

variable [AddCommMonoidₓ M₂] [AddCommMonoidₓ N₂] [AddCommMonoidₓ P₂]

variable [AddCommMonoidₓ Nₗ] [AddCommMonoidₓ Pₗ]

variable [AddCommGroupₓ M'] [AddCommGroupₓ N'] [AddCommGroupₓ P']

variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]

variable [Module R M₂] [Module S N₂] [Module R P₂] [Module S₂ P₂]

variable [Module R Pₗ] [Module S Pₗ]

variable [Module R M'] [Module S N'] [Module R₂ P'] [Module S₂ P']

variable [SmulCommClass S₂ R₂ P] [SmulCommClass S R Pₗ] [SmulCommClass S₂ R₂ P']

variable [SmulCommClass S₂ R P₂]

variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}

variable (ρ₁₂ σ₁₂)

/-- Create a bilinear map from a function that is semilinear in each component.
See `mk₂'` and `mk₂` for the linear case. -/
def mk₂'ₛₗ (f : M → N → P) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = ρ₁₂ c • f m n) (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : S) (m n), f m (c • n) = σ₁₂ c • f m n) : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P where
  toFun := fun m => { toFun := f m, map_add' := H3 m, map_smul' := fun c => H4 c m }
  map_add' := fun m₁ m₂ => LinearMap.ext <| H1 m₁ m₂
  map_smul' := fun c m => LinearMap.ext <| H2 c m

variable {ρ₁₂ σ₁₂}

@[simp]
theorem mk₂'ₛₗ_apply (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
    (mk₂'ₛₗ ρ₁₂ σ₁₂ f H1 H2 H3 H4 : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) m n = f m n :=
  rfl

variable (R S)

/-- Create a bilinear map from a function that is linear in each component.
See `mk₂` for the special case where both arguments come from modules over the same ring. -/
def mk₂' (f : M → N → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n) (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : S) (m n), f m (c • n) = c • f m n) : M →ₗ[R] N →ₗ[S] Pₗ :=
  mk₂'ₛₗ (RingHom.id R) (RingHom.id S) f H1 H2 H3 H4

variable {R S}

@[simp]
theorem mk₂'_apply (f : M → N → Pₗ) {H1 H2 H3 H4} (m : M) (n : N) :
    (mk₂' R S f H1 H2 H3 H4 : M →ₗ[R] N →ₗ[S] Pₗ) m n = f m n :=
  rfl

theorem ext₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (H : ∀ m n, f m n = g m n) : f = g :=
  LinearMap.ext fun m => LinearMap.ext fun n => H m n

theorem congr_fun₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : f = g) (x y) : f x y = g x y :=
  LinearMap.congr_fun (LinearMap.congr_fun h x) y

section

attribute [local instance] SmulCommClass.symm

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to
`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def flip (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P :=
  mk₂'ₛₗ σ₁₂ ρ₁₂ (fun n m => f m n) (fun n₁ n₂ m => (f m).map_add _ _) (fun c n m => (f m).map_smulₛₗ _ _)
    (fun n m₁ m₂ => by
      rw [f.map_add] <;> rfl)
    fun c n m => by
    rw [f.map_smulₛₗ] <;> rfl

end

@[simp]
theorem flip_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (m : M) (n : N) : flip f n m = f m n :=
  rfl

@[simp]
theorem flip_flip [SmulCommClass R₂ S₂ P] (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : f.flip.flip = f :=
  LinearMap.ext₂ fun x y => (f.flip.flip_apply _ _).trans (f.flip_apply _ _)

open BigOperators

variable {R}

theorem flip_inj {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (H : flip f = flip g) : f = g :=
  ext₂ fun m n =>
    show flip f n m = flip g n m by
      rw [H]

theorem map_zero₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (y) : f 0 y = 0 :=
  (flip f y).map_zero

theorem map_neg₂ (f : M' →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P') (x y) : f (-x) y = -f x y :=
  (flip f y).map_neg _

theorem map_sub₂ (f : M' →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P') (x y z) : f (x - y) z = f x z - f y z :=
  (flip f z).map_sub _ _

theorem map_add₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y :=
  (flip f y).map_add _ _

theorem map_smul₂ (f : M₂ →ₗ[R] N₂ →ₛₗ[σ₁₂] P₂) (r : R) (x y) : f (r • x) y = r • f x y :=
  (flip f y).map_smul _ _

theorem map_smulₛₗ₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (r : R) (x y) : f (r • x) y = ρ₁₂ r • f x y :=
  (flip f y).map_smulₛₗ _ _

theorem map_sum₂ {ι : Type _} (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (t : Finset ι) (x : ι → M) (y) :
    f (∑ i in t, x i) y = ∑ i in t, f (x i) y :=
  (flip f y).map_sum

/-- Restricting a bilinear map in the second entry -/
def domRestrict₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (q : Submodule S N) : M →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P where
  toFun := fun m => (f m).domRestrict q
  map_add' := fun m₁ m₂ =>
    LinearMap.ext fun _ => by
      simp only [← map_add, ← dom_restrict_apply, ← add_apply]
  map_smul' := fun c m =>
    LinearMap.ext fun _ => by
      simp only [← f.map_smulₛₗ, ← dom_restrict_apply, ← smul_apply]

theorem dom_restrict₂_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (q : Submodule S N) (x : M) (y : q) :
    f.domRestrict₂ q x y = f x y :=
  rfl

/-- Restricting a bilinear map in both components -/
def domRestrict₁₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N) : p →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P :=
  (f.domRestrict p).domRestrict₂ q

theorem dom_restrict₁₂_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N) (x : p) (y : q) :
    f.domRestrict₁₂ p q x y = f x y :=
  rfl

end Semiringₓ

section CommSemiringₓ

variable {R : Type _} [CommSemiringₓ R] {R₂ : Type _} [CommSemiringₓ R₂]

variable {R₃ : Type _} [CommSemiringₓ R₃] {R₄ : Type _} [CommSemiringₓ R₄]

variable {M : Type _} {N : Type _} {P : Type _} {Q : Type _}

variable {Mₗ : Type _} {Nₗ : Type _} {Pₗ : Type _} {Qₗ Qₗ' : Type _}

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P] [AddCommMonoidₓ Q]

variable [AddCommMonoidₓ Mₗ] [AddCommMonoidₓ Nₗ] [AddCommMonoidₓ Pₗ]

variable [AddCommMonoidₓ Qₗ] [AddCommMonoidₓ Qₗ']

variable [Module R M] [Module R₂ N] [Module R₃ P] [Module R₄ Q]

variable [Module R Mₗ] [Module R Nₗ] [Module R Pₗ] [Module R Qₗ] [Module R Qₗ']

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable {σ₄₂ : R₄ →+* R₂} {σ₄₃ : R₄ →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₄₂ σ₂₃ σ₄₃]

variable (R)

/-- Create a bilinear map from a function that is linear in each component.

This is a shorthand for `mk₂'` for the common case when `R = S`. -/
def mk₂ (f : M → Nₗ → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n) (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : R) (m n), f m (c • n) = c • f m n) : M →ₗ[R] Nₗ →ₗ[R] Pₗ :=
  mk₂' R R f H1 H2 H3 H4

@[simp]
theorem mk₂_apply (f : M → Nₗ → Pₗ) {H1 H2 H3 H4} (m : M) (n : Nₗ) :
    (mk₂ R f H1 H2 H3 H4 : M →ₗ[R] Nₗ →ₗ[R] Pₗ) m n = f m n :=
  rfl

variable (R M N P)

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map `M → N → P`,
change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def lflip : (M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) →ₗ[R₃] N →ₛₗ[σ₂₃] M →ₛₗ[σ₁₃] P where
  toFun := flip
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

variable {R M N P}

variable (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P)

@[simp]
theorem lflip_apply (m : M) (n : N) : lflip R M N P f n m = f m n :=
  rfl

variable (R Pₗ)

/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def lcomp (f : M →ₗ[R] Nₗ) : (Nₗ →ₗ[R] Pₗ) →ₗ[R] M →ₗ[R] Pₗ :=
  flip <| LinearMap.comp (flip id) f

variable {R Pₗ}

@[simp]
theorem lcomp_apply (f : M →ₗ[R] Nₗ) (g : Nₗ →ₗ[R] Pₗ) (x : M) : lcomp R Pₗ f g x = g (f x) :=
  rfl

theorem lcomp_apply' (f : M →ₗ[R] Nₗ) (g : Nₗ →ₗ[R] Pₗ) : lcomp R Pₗ f g = g ∘ₗ f :=
  rfl

variable (P σ₂₃)

/-- Composing a semilinear map `M → N` and a semilinear map `N → P` to form a semilinear map
`M → P` is itself a linear map. -/
def lcompₛₗ (f : M →ₛₗ[σ₁₂] N) : (N →ₛₗ[σ₂₃] P) →ₗ[R₃] M →ₛₗ[σ₁₃] P :=
  flip <| LinearMap.comp (flip id) f

variable {P σ₂₃}

include σ₁₃

@[simp]
theorem lcompₛₗ_apply (f : M →ₛₗ[σ₁₂] N) (g : N →ₛₗ[σ₂₃] P) (x : M) : lcompₛₗ P σ₂₃ f g x = g (f x) :=
  rfl

omit σ₁₃

variable (R M Nₗ Pₗ)

/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def llcomp : (Nₗ →ₗ[R] Pₗ) →ₗ[R] (M →ₗ[R] Nₗ) →ₗ[R] M →ₗ[R] Pₗ :=
  flip
    { toFun := lcomp R Pₗ, map_add' := fun f f' => ext₂ fun g x => g.map_add _ _,
      map_smul' := fun (c : R) f => ext₂ fun g x => g.map_smul _ _ }

variable {R M Nₗ Pₗ}

section

@[simp]
theorem llcomp_apply (f : Nₗ →ₗ[R] Pₗ) (g : M →ₗ[R] Nₗ) (x : M) : llcomp R M Nₗ Pₗ f g x = f (g x) :=
  rfl

theorem llcomp_apply' (f : Nₗ →ₗ[R] Pₗ) (g : M →ₗ[R] Nₗ) : llcomp R M Nₗ Pₗ f g = f ∘ₗ g :=
  rfl

end

/-- Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`. -/
def compl₂ (g : Q →ₛₗ[σ₄₂] N) : M →ₛₗ[σ₁₃] Q →ₛₗ[σ₄₃] P :=
  (lcompₛₗ _ _ g).comp f

include σ₄₃

@[simp]
theorem compl₂_apply (g : Q →ₛₗ[σ₄₂] N) (m : M) (q : Q) : f.compl₂ g m q = f m (g q) :=
  rfl

omit σ₄₃

/-- Composing linear maps `Q → M` and `Q' → N` with a bilinear map `M → N → P` to
form a bilinear map `Q → Q' → P`. -/
def compl₁₂ (f : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Qₗ →ₗ[R] Mₗ) (g' : Qₗ' →ₗ[R] Nₗ) : Qₗ →ₗ[R] Qₗ' →ₗ[R] Pₗ :=
  (f.comp g).compl₂ g'

@[simp]
theorem compl₁₂_apply (f : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Qₗ →ₗ[R] Mₗ) (g' : Qₗ' →ₗ[R] Nₗ) (x : Qₗ) (y : Qₗ') :
    f.compl₁₂ g g' x y = f (g x) (g' y) :=
  rfl

theorem compl₁₂_inj {f₁ f₂ : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ} {g : Qₗ →ₗ[R] Mₗ} {g' : Qₗ' →ₗ[R] Nₗ} (hₗ : Function.Surjective g)
    (hᵣ : Function.Surjective g') : f₁.compl₁₂ g g' = f₂.compl₁₂ g g' ↔ f₁ = f₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    cases' hₗ x with x' hx
    subst hx
    cases' hᵣ y with y' hy
    subst hy
    convert LinearMap.congr_fun₂ h x' y'
    
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h
    

/-- Composing a linear map `P → Q` and a bilinear map `M → N → P` to
form a bilinear map `M → N → Q`. -/
def compr₂ (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ) : M →ₗ[R] Nₗ →ₗ[R] Qₗ :=
  llcomp R Nₗ Pₗ Qₗ g ∘ₗ f

@[simp]
theorem compr₂_apply (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ) (m : M) (n : Nₗ) : f.compr₂ g m n = g (f m n) :=
  rfl

variable (R M)

/-- Scalar multiplication as a bilinear map `R → M → M`. -/
def lsmul : R →ₗ[R] M →ₗ[R] M :=
  mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by
    simp only [← smul_smul, ← smul_eq_mul, ← mul_comm]

variable {R M}

@[simp]
theorem lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m :=
  rfl

end CommSemiringₓ

section CommRingₓ

variable {R R₂ S S₂ M N P : Type _}

variable [CommRingₓ R] [CommRingₓ S] [CommRingₓ R₂] [CommRingₓ S₂]

variable [AddCommGroupₓ M] [AddCommGroupₓ N] [AddCommGroupₓ P]

variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]

variable [SmulCommClass S₂ R₂ P]

variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}

variable (b₁ : Basis ι₁ R M) (b₂ : Basis ι₂ S N)

theorem lsmul_injective [NoZeroSmulDivisors R M] {x : R} (hx : x ≠ 0) : Function.Injective (lsmul R M x) :=
  smul_right_injective _ hx

theorem ker_lsmul [NoZeroSmulDivisors R M] {a : R} (ha : a ≠ 0) : (LinearMap.lsmul R M a).ker = ⊥ :=
  LinearMap.ker_eq_bot_of_injective (LinearMap.lsmul_injective ha)

/-- Two bilinear maps are equal when they are equal on all basis vectors. -/
theorem ext_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : ∀ i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) : B = B' :=
  b₁.ext fun i => b₂.ext fun j => h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
theorem sum_repr_mul_repr_mul {B : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (x y) :
    ((b₁.repr x).Sum fun i xi => (b₂.repr y).Sum fun j yj => ρ₁₂ xi • σ₁₂ yj • B (b₁ i) (b₂ j)) = B x y := by
  conv_rhs => rw [← b₁.total_repr x, ← b₂.total_repr y]
  simp_rw [Finsupp.total_apply, Finsupp.sum, map_sum₂, map_sum, LinearMap.map_smulₛₗ₂, LinearMap.map_smulₛₗ]

end CommRingₓ

end LinearMap

