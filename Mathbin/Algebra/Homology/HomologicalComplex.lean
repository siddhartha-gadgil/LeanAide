/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Mathbin.Algebra.Homology.ComplexShape
import Mathbin.CategoryTheory.Subobject.Limits
import Mathbin.CategoryTheory.GradedObject

/-!
# Homological complexes.

A `homological_complex V c` with a "shape" controlled by `c : complex_shape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape'` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.

We provide `chain_complex V α` for
`α`-indexed chain complexes in which `d i j ≠ 0` only if `j + 1 = i`,
and similarly `cochain_complex V α`, with `i = j + 1`.

There is a category structure, where morphisms are chain maps.

For `C : homological_complex V c`, we define `C.X_next i`, which is either `C.X j` for some
arbitrarily chosen `j` such that `c.r i j`, or the zero object if there is no such `j`.
Similarly we have `C.X_prev j`.
Defined in terms of these we have `C.d_from i : C.X i ⟶ C.X_next i` and
`C.d_to j : C.X_prev j ⟶ C.X j`, which are either defined as `C.d i j`, or zero, as needed.
-/


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι : Type _}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

/-- A `homological_complex V c` with a "shape" controlled by `c : complex_shape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape'` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.
-/
structure HomologicalComplex (c : ComplexShape ι) where
  x : ι → V
  d : ∀ i j, X i ⟶ X j
  shape' : ∀ i j, ¬c.Rel i j → d i j = 0 := by
    run_tac
      obviously
  d_comp_d' : ∀ i j k, c.Rel i j → c.Rel j k → d i j ≫ d j k = 0 := by
    run_tac
      obviously

namespace HomologicalComplex

restate_axiom shape'

attribute [simp] shape

variable {V} {c : ComplexShape ι}

@[simp, reassoc]
theorem d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0 := by
  by_cases' hij : c.rel i j
  · by_cases' hjk : c.rel j k
    · exact C.d_comp_d' i j k hij hjk
      
    · rw [C.shape j k hjk, comp_zero]
      
    
  · rw [C.shape i j hij, zero_comp]
    

theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.x = C₂.x)
    (h_d : ∀ i j : ι, c.Rel i j → C₁.d i j ≫ eqToHom (congr_fun h_X j) = eqToHom (congr_fun h_X i) ≫ C₂.d i j) :
    C₁ = C₂ := by
  cases C₁
  cases C₂
  dsimp'  at h_X
  subst h_X
  simp only [← true_andₓ, ← eq_self_iff_true, ← heq_iff_eq]
  ext i j
  by_cases' hij : c.rel i j
  · simpa only [← id_comp, ← eq_to_hom_refl, ← comp_id] using h_d i j hij
    
  · rw [C₁_shape' i j hij, C₂_shape' i j hij]
    

end HomologicalComplex

/-- An `α`-indexed chain complex is a `homological_complex`
in which `d i j ≠ 0` only if `j + 1 = i`.
-/
abbrev ChainComplex (α : Type _) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.down α)

/-- An `α`-indexed cochain complex is a `homological_complex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
abbrev CochainComplex (α : Type _) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.up α)

namespace ChainComplex

@[simp]
theorem prev (α : Type _) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.down α).prev i = some ⟨i + 1, rfl⟩ :=
  Option.choice_eq _

@[simp]
theorem next (α : Type _) [AddGroupₓ α] [One α] (i : α) :
    (ComplexShape.down α).next i = some ⟨i - 1, sub_add_cancel i 1⟩ :=
  Option.choice_eq _

@[simp]
theorem next_nat_zero : (ComplexShape.down ℕ).next 0 = none :=
  @Option.choice_eq_none _
    ⟨by
      rintro ⟨j, ⟨⟩⟩⟩

@[simp]
theorem next_nat_succ (i : ℕ) : (ComplexShape.down ℕ).next (i + 1) = some ⟨i, rfl⟩ :=
  Option.choice_eq _

end ChainComplex

namespace CochainComplex

@[simp]
theorem prev (α : Type _) [AddGroupₓ α] [One α] (i : α) :
    (ComplexShape.up α).prev i = some ⟨i - 1, sub_add_cancel i 1⟩ :=
  Option.choice_eq _

@[simp]
theorem next (α : Type _) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.up α).next i = some ⟨i + 1, rfl⟩ :=
  Option.choice_eq _

@[simp]
theorem prev_nat_zero : (ComplexShape.up ℕ).prev 0 = none :=
  @Option.choice_eq_none _
    ⟨by
      rintro ⟨j, ⟨⟩⟩⟩

@[simp]
theorem prev_nat_succ (i : ℕ) : (ComplexShape.up ℕ).prev (i + 1) = some ⟨i, rfl⟩ :=
  Option.choice_eq _

end CochainComplex

namespace HomologicalComplex

variable {V} {c : ComplexShape ι} (C : HomologicalComplex V c)

/-- A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
@[ext]
structure Hom (A B : HomologicalComplex V c) where
  f : ∀ i, A.x i ⟶ B.x i
  comm' : ∀ i j, c.Rel i j → f i ≫ B.d i j = A.d i j ≫ f j := by
    run_tac
      obviously

@[simp, reassoc]
theorem Hom.comm {A B : HomologicalComplex V c} (f : A.Hom B) (i j : ι) : f.f i ≫ B.d i j = A.d i j ≫ f.f j := by
  by_cases' hij : c.rel i j
  · exact f.comm' i j hij
    
  rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]

instance (A B : HomologicalComplex V c) : Inhabited (Hom A B) :=
  ⟨{ f := fun i => 0 }⟩

/-- Identity chain map. -/
def id (A : HomologicalComplex V c) : Hom A A where f := fun _ => 𝟙 _

/-- Composition of chain maps. -/
def comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A C where f := fun i => φ.f i ≫ ψ.f i

section

attribute [local simp] id comp

instance : Category (HomologicalComplex V c) where
  Hom := Hom
  id := id
  comp := comp

end

@[simp]
theorem id_f (C : HomologicalComplex V c) (i : ι) : Hom.f (𝟙 C) i = 𝟙 (C.x i) :=
  rfl

@[simp]
theorem comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i :=
  rfl

@[simp]
theorem eq_to_hom_f {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι) :
    HomologicalComplex.Hom.f (eqToHom h) n = eqToHom (congr_fun (congr_arg HomologicalComplex.x h) n) := by
  subst h
  rfl

-- We'll use this later to show that `homological_complex V c` is preadditive when `V` is.
theorem hom_f_injective {C₁ C₂ : HomologicalComplex V c} : Function.Injective fun f : Hom C₁ C₂ => f.f := by
  tidy

instance : HasZeroMorphisms (HomologicalComplex V c) where HasZero := fun C D => ⟨{ f := fun i => 0 }⟩

@[simp]
theorem zero_apply (C D : HomologicalComplex V c) (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

open ZeroObject

/-- The zero complex -/
noncomputable def zero [HasZeroObject V] : HomologicalComplex V c where
  x := fun i => 0
  d := fun i j => 0

theorem is_zero_zero [HasZeroObject V] : IsZero (zero : HomologicalComplex V c) := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩ <;> ext

instance [HasZeroObject V] : HasZeroObject (HomologicalComplex V c) :=
  ⟨⟨zero, is_zero_zero⟩⟩

noncomputable instance [HasZeroObject V] : Inhabited (HomologicalComplex V c) :=
  ⟨zero⟩

theorem congr_hom {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i :=
  congr_fun (congr_arg Hom.f w) i

section

variable (V c)

/-- The functor picking out the `i`-th object of a complex. -/
@[simps]
def eval (i : ι) : HomologicalComplex V c ⥤ V where
  obj := fun C => C.x i
  map := fun C D f => f.f i

/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps]
def forget : HomologicalComplex V c ⥤ GradedObject ι V where
  obj := fun C => C.x
  map := fun _ _ f => f.f

/-- Forgetting the differentials than picking out the `i`-th object is the same as
just picking out the `i`-th object. -/
@[simps]
def forgetEval (i : ι) : forget V c ⋙ GradedObject.eval i ≅ eval V c i :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

end

open Classical

noncomputable section

/-- If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eq_to_hom`.
-/
@[simp]
theorem d_comp_eq_to_hom {i j j' : ι} (rij : c.Rel i j) (rij' : c.Rel i j') :
    C.d i j' ≫ eqToHom (congr_arg C.x (c.next_eq rij' rij)) = C.d i j := by
  have P : ∀ h : j' = j, C.d i j' ≫ eq_to_hom (congr_arg C.X h) = C.d i j := by
    rintro rfl
    simp
  apply P

/-- If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eq_to_hom`.
-/
@[simp]
theorem eq_to_hom_comp_d {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j) :
    eqToHom (congr_arg C.x (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j := by
  have P : ∀ h : i = i', eq_to_hom (congr_arg C.X h) ≫ C.d i' j = C.d i j := by
    rintro rfl
    simp
  apply P

theorem kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j') :
    kernelSubobject (C.d i j) = kernelSubobject (C.d i j') := by
  rw [← d_comp_eq_to_hom C r r']
  apply kernel_subobject_comp_mono

theorem image_eq_image [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j) (r' : c.Rel i' j) :
    imageSubobject (C.d i j) = imageSubobject (C.d i' j) := by
  rw [← eq_to_hom_comp_d C r r']
  apply image_subobject_iso_comp

section

variable [HasZeroObject V]

open ZeroObject

/-- Either `C.X i`, if there is some `i` with `c.rel i j`, or the zero object. -/
def xPrev (j : ι) : V :=
  match c.prev j with
  | none => 0
  | some ⟨i, _⟩ => C.x i

/-- If `c.rel i j`, then `C.X_prev j` is isomorphic to `C.X i`. -/
def xPrevIso {i j : ι} (r : c.Rel i j) : C.xPrev j ≅ C.x i :=
  eqToIso
    (by
      dsimp' [← X_prev]
      rw [c.prev_eq_some r]
      rfl)

/-- If there is no `i` so `c.rel i j`, then `C.X_prev j` is isomorphic to `0`. -/
def xPrevIsoZero {j : ι} (h : c.prev j = none) : C.xPrev j ≅ 0 :=
  eqToIso
    (by
      dsimp' [← X_prev]
      rw [h]
      rfl)

/-- Either `C.X j`, if there is some `j` with `c.rel i j`, or the zero object. -/
def xNext (i : ι) : V :=
  match c.next i with
  | none => 0
  | some ⟨j, _⟩ => C.x j

/-- If `c.rel i j`, then `C.X_next i` is isomorphic to `C.X j`. -/
def xNextIso {i j : ι} (r : c.Rel i j) : C.xNext i ≅ C.x j :=
  eqToIso
    (by
      dsimp' [← X_next]
      rw [c.next_eq_some r]
      rfl)

/-- If there is no `j` so `c.rel i j`, then `C.X_next i` is isomorphic to `0`. -/
def xNextIsoZero {i : ι} (h : c.next i = none) : C.xNext i ≅ 0 :=
  eqToIso
    (by
      dsimp' [← X_next]
      rw [h]
      rfl)

/-- The differential mapping into `C.X j`, or zero if there isn't one.
-/
def dTo (j : ι) : C.xPrev j ⟶ C.x j :=
  match c.prev j with
  | none => (0 : C.xPrev j ⟶ C.x j)
  | some ⟨i, w⟩ => (C.xPrevIso w).Hom ≫ C.d i j

/-- The differential mapping out of `C.X i`, or zero if there isn't one.
-/
def dFrom (i : ι) : C.x i ⟶ C.xNext i :=
  match c.next i with
  | none => (0 : C.x i ⟶ C.xNext i)
  | some ⟨j, w⟩ => C.d i j ≫ (C.xNextIso w).inv

theorem d_to_eq {i j : ι} (r : c.Rel i j) : C.dTo j = (C.xPrevIso r).Hom ≫ C.d i j := by
  dsimp' [← d_to, ← X_prev_iso]
  rw [c.prev_eq_some r]
  rfl

@[simp]
theorem d_to_eq_zero {j : ι} (h : c.prev j = none) : C.dTo j = 0 := by
  dsimp' [← d_to]
  rw [h]
  rfl

theorem d_from_eq {i j : ι} (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).inv := by
  dsimp' [← d_from, ← X_next_iso]
  rw [c.next_eq_some r]
  rfl

@[simp]
theorem d_from_eq_zero {i : ι} (h : c.next i = none) : C.dFrom i = 0 := by
  dsimp' [← d_from]
  rw [h]
  rfl

@[simp, reassoc]
theorem X_prev_iso_comp_d_to {i j : ι} (r : c.Rel i j) : (C.xPrevIso r).inv ≫ C.dTo j = C.d i j := by
  simp [← C.d_to_eq r]

@[simp, reassoc]
theorem X_prev_iso_zero_comp_d_to {j : ι} (h : c.prev j = none) : (C.xPrevIsoZero h).inv ≫ C.dTo j = 0 := by
  simp [← h]

@[simp, reassoc]
theorem d_from_comp_X_next_iso {i j : ι} (r : c.Rel i j) : C.dFrom i ≫ (C.xNextIso r).Hom = C.d i j := by
  simp [← C.d_from_eq r]

@[simp, reassoc]
theorem d_from_comp_X_next_iso_zero {i : ι} (h : c.next i = none) : C.dFrom i ≫ (C.xNextIsoZero h).Hom = 0 := by
  simp [← h]

@[simp]
theorem d_to_comp_d_from (j : ι) : C.dTo j ≫ C.dFrom j = 0 := by
  rcases h₁ : c.next j with (_ | ⟨k, w₁⟩)
  · rw [d_from_eq_zero _ h₁]
    simp
    
  · rw [d_from_eq _ w₁]
    rcases h₂ : c.prev j with (_ | ⟨i, w₂⟩)
    · rw [d_to_eq_zero _ h₂]
      simp
      
    · rw [d_to_eq _ w₂]
      simp
      
    

theorem kernel_from_eq_kernel [HasKernels V] {i j : ι} (r : c.Rel i j) :
    kernelSubobject (C.dFrom i) = kernelSubobject (C.d i j) := by
  rw [C.d_from_eq r]
  apply kernel_subobject_comp_mono

theorem image_to_eq_image [HasImages V] [HasEqualizers V] {i j : ι} (r : c.Rel i j) :
    imageSubobject (C.dTo j) = imageSubobject (C.d i j) := by
  rw [C.d_to_eq r]
  apply image_subobject_iso_comp

end

namespace Hom

variable {C₁ C₂ C₃ : HomologicalComplex V c}

/-- The `i`-th component of an isomorphism of chain complexes. -/
@[simps]
def isoApp (f : C₁ ≅ C₂) (i : ι) : C₁.x i ≅ C₂.x i :=
  (eval V c i).mapIso f

/-- Construct an isomorphism of chain complexes from isomorphism of the objects
which commute with the differentials. -/
@[simps]
def isoOfComponents (f : ∀ i, C₁.x i ≅ C₂.x i) (hf : ∀ i j, c.Rel i j → (f i).Hom ≫ C₂.d i j = C₁.d i j ≫ (f j).Hom) :
    C₁ ≅ C₂ where
  Hom := { f := fun i => (f i).Hom, comm' := hf }
  inv :=
    { f := fun i => (f i).inv,
      comm' := fun i j hij =>
        calc
          (f i).inv ≫ C₁.d i j = (f i).inv ≫ (C₁.d i j ≫ (f j).Hom) ≫ (f j).inv := by
            simp
          _ = (f i).inv ≫ ((f i).Hom ≫ C₂.d i j) ≫ (f j).inv := by
            rw [hf i j hij]
          _ = C₂.d i j ≫ (f j).inv := by
            simp
           }
  hom_inv_id' := by
    ext i
    exact (f i).hom_inv_id
  inv_hom_id' := by
    ext i
    exact (f i).inv_hom_id

@[simp]
theorem iso_of_components_app (f : ∀ i, C₁.x i ≅ C₂.x i)
    (hf : ∀ i j, c.Rel i j → (f i).Hom ≫ C₂.d i j = C₁.d i j ≫ (f j).Hom) (i : ι) :
    isoApp (isoOfComponents f hf) i = f i := by
  ext
  simp

variable [HasZeroObject V]

open ZeroObject

/-! Lemmas relating chain maps and `d_to`/`d_from`. -/


/-- `f.prev j` is `f.f i` if there is some `r i j`, and zero otherwise. -/
def prev (f : Hom C₁ C₂) (j : ι) : C₁.xPrev j ⟶ C₂.xPrev j :=
  match c.prev j with
  | none => 0
  | some ⟨i, w⟩ => (C₁.xPrevIso w).Hom ≫ f.f i ≫ (C₂.xPrevIso w).inv

theorem prev_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.prev j = (C₁.xPrevIso w).Hom ≫ f.f i ≫ (C₂.xPrevIso w).inv := by
  dsimp' [← prev]
  rw [c.prev_eq_some w]
  rfl

/-- `f.next i` is `f.f j` if there is some `r i j`, and zero otherwise. -/
def next (f : Hom C₁ C₂) (i : ι) : C₁.xNext i ⟶ C₂.xNext i :=
  match c.next i with
  | none => 0
  | some ⟨j, w⟩ => (C₁.xNextIso w).Hom ≫ f.f j ≫ (C₂.xNextIso w).inv

theorem next_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.next i = (C₁.xNextIso w).Hom ≫ f.f j ≫ (C₂.xNextIso w).inv := by
  dsimp' [← next]
  rw [c.next_eq_some w]
  rfl

@[simp, reassoc, elementwise]
theorem comm_from (f : Hom C₁ C₂) (i : ι) : f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i := by
  rcases h : c.next i with (_ | ⟨j, w⟩)
  · simp [← h]
    
  · simp [← d_from_eq _ w, ← next_eq _ w]
    

@[simp, reassoc, elementwise]
theorem comm_to (f : Hom C₁ C₂) (j : ι) : f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j := by
  rcases h : c.prev j with (_ | ⟨j, w⟩)
  · simp [← h]
    
  · simp [← d_to_eq _ w, ← prev_eq _ w]
    

/-- A morphism of chain complexes
induces a morphism of arrows of the differentials out of each object.
-/
def sqFrom (f : Hom C₁ C₂) (i : ι) : Arrow.mk (C₁.dFrom i) ⟶ Arrow.mk (C₂.dFrom i) :=
  Arrow.homMk (f.comm_from i)

@[simp]
theorem sq_from_left (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).left = f.f i :=
  rfl

@[simp]
theorem sq_from_right (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).right = f.next i :=
  rfl

@[simp]
theorem sq_from_id (C₁ : HomologicalComplex V c) (i : ι) : sqFrom (𝟙 C₁) i = 𝟙 _ := by
  rcases h : c.next i with (_ | ⟨j, w⟩)
  · ext
    · rfl
      
    · dsimp'
      simp only [← next, ← h]
      symm
      apply zero_of_target_iso_zero
      exact X_next_iso_zero _ h
      
    
  · ext
    rfl
    dsimp'
    simp [← next, ← h]
    

@[simp]
theorem sq_from_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : sqFrom (f ≫ g) i = sqFrom f i ≫ sqFrom g i := by
  rcases h : c.next i with (_ | ⟨j, w⟩)
  · ext
    · rfl
      
    · dsimp'
      simp only [← next, ← h]
      symm
      apply zero_of_target_iso_zero
      exact X_next_iso_zero _ h
      
    
  · ext
    rfl
    dsimp'
    simp [← next, ← h]
    

/-- A morphism of chain complexes
induces a morphism of arrows of the differentials into each object.
-/
def sqTo (f : Hom C₁ C₂) (j : ι) : Arrow.mk (C₁.dTo j) ⟶ Arrow.mk (C₂.dTo j) :=
  Arrow.homMk (f.comm_to j)

@[simp]
theorem sq_to_left (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).left = f.prev j :=
  rfl

@[simp]
theorem sq_to_right (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).right = f.f j :=
  rfl

end Hom

end HomologicalComplex

namespace ChainComplex

section Of

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/-- Construct an `α`-indexed chain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) : ChainComplex V α :=
  { x,
    d := fun i j =>
      if h : i = j + 1 then
        eqToHom
            (by
              subst h) ≫
          d j
      else 0,
    shape' := fun i j w => by
      rw [dif_neg (Ne.symm w)],
    d_comp_d' := fun i j k hij hjk => by
      dsimp'  at hij hjk
      substs hij hjk
      simp only [← category.id_comp, ← dif_pos rfl, ← eq_to_hom_refl]
      exact sq k }

variable (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0)

@[simp]
theorem of_X (n : α) : (of X d sq).x n = X n :=
  rfl

@[simp]
theorem of_d (j : α) : (of X d sq).d (j + 1) j = d j := by
  dsimp' [← of]
  rw [if_pos rfl, category.id_comp]

theorem of_d_ne {i j : α} (h : i ≠ j + 1) : (of X d sq).d i j = 0 := by
  dsimp' [← of]
  rw [dif_neg h]

end Of

section OfHom

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

variable (X : α → V) (d_X : ∀ n, X (n + 1) ⟶ X n) (sq_X : ∀ n, d_X (n + 1) ≫ d_X n = 0) (Y : α → V)
  (d_Y : ∀ n, Y (n + 1) ⟶ Y n) (sq_Y : ∀ n, d_Y (n + 1) ≫ d_Y n = 0)

/-- A constructor for chain maps between `α`-indexed chain complexes built using `chain_complex.of`,
from a dependently typed collection of morphisms.
-/
@[simps]
def ofHom (f : ∀ i : α, X i ⟶ Y i) (comm : ∀ i : α, f (i + 1) ≫ d_Y i = d_X i ≫ f i) : of X d_X sq_X ⟶ of Y d_Y sq_Y :=
  { f,
    comm' := fun n m => by
      by_cases' h : n = m + 1
      · subst h
        simpa using comm m
        
      · rw [of_d_ne X _ _ h, of_d_ne Y _ _ h]
        simp
         }

end OfHom

section Mk

/-- Auxiliary structure for setting up the recursion in `mk`.
This is purely an implementation detail: for some reason just using the dependent 6-tuple directly
results in `mk_aux` taking much longer (well over the `-T100000` limit) to elaborate.
-/
@[nolint has_inhabited_instance]
structure MkStruct where
  (x₀ x₁ x₂ : V)
  d₀ : X₁ ⟶ X₀
  d₁ : X₂ ⟶ X₁
  s : d₁ ≫ d₀ = 0

variable {V}

/-- Flatten to a tuple. -/
def MkStruct.flat (t : MkStruct V) : Σ'(X₀ X₁ X₂ : V)(d₀ : X₁ ⟶ X₀)(d₁ : X₂ ⟶ X₁), d₁ ≫ d₀ = 0 :=
  ⟨t.x₀, t.x₁, t.x₂, t.d₀, t.d₁, t.s⟩

variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ :
    ∀ t : Σ'(X₀ X₁ X₂ : V)(d₀ : X₁ ⟶ X₀)(d₁ : X₂ ⟶ X₁), d₁ ≫ d₀ = 0,
      Σ'(X₃ : V)(d₂ : X₃ ⟶ t.2.2.1), d₂ ≫ t.2.2.2.2.1 = 0)

/-- Auxiliary definition for `mk`. -/
def mkAuxₓ : ∀ n : ℕ, MkStruct V
  | 0 => ⟨X₀, X₁, X₂, d₀, d₁, s⟩
  | n + 1 =>
    let p := mk_aux n
    ⟨p.x₁, p.x₂, (succ p.flat).1, p.d₁, (succ p.flat).2.1, (succ p.flat).2.2⟩

/-- A inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropiately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : ChainComplex V ℕ :=
  of (fun n => (mkAuxₓ X₀ X₁ X₂ d₀ d₁ s succ n).x₀) (fun n => (mkAuxₓ X₀ X₁ X₂ d₀ d₁ s succ n).d₀) fun n =>
    (mkAuxₓ X₀ X₁ X₂ d₀ d₁ s succ n).s

@[simp]
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).x 0 = X₀ :=
  rfl

@[simp]
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).x 1 = X₁ :=
  rfl

@[simp]
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).x 2 = X₂ :=
  rfl

@[simp]
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl, category.id_comp]

@[simp]
theorem mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁ := by
  change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁
  rw [if_pos rfl, category.id_comp]

/-- A simpler inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
def mk' (X₀ X₁ : V) (d : X₁ ⟶ X₀) (succ' : ∀ t : ΣX₀ X₁ : V, X₁ ⟶ X₀, Σ'(X₂ : V)(d : X₂ ⟶ t.2.1), d ≫ t.2.2 = 0) :
    ChainComplex V ℕ :=
  mk X₀ X₁ (succ' ⟨X₀, X₁, d⟩).1 d (succ' ⟨X₀, X₁, d⟩).2.1 (succ' ⟨X₀, X₁, d⟩).2.2 fun t =>
    succ' ⟨t.2.1, t.2.2.1, t.2.2.2.2.1⟩

variable (succ' : ∀ t : ΣX₀ X₁ : V, X₁ ⟶ X₀, Σ'(X₂ : V)(d : X₂ ⟶ t.2.1), d ≫ t.2.2 = 0)

@[simp]
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').x 0 = X₀ :=
  rfl

@[simp]
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').x 1 = X₁ :=
  rfl

@[simp]
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl, category.id_comp]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
end Mk

section MkHom

variable {V} (P Q : ChainComplex V ℕ) (zero : P.x 0 ⟶ Q.x 0) (one : P.x 1 ⟶ Q.x 1)
  (one_zero_comm : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
  (succ :
    ∀ (n : ℕ) (p : Σ'(f : P.x n ⟶ Q.x n)(f' : P.x (n + 1) ⟶ Q.x (n + 1)), f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f),
      Σ'f'' : P.x (n + 2) ⟶ Q.x (n + 2), f'' ≫ Q.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1)

/-- An auxiliary construction for `mk_hom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mk_hom`.
-/
def mkHomAuxₓ : ∀ n, Σ'(f : P.x n ⟶ Q.x n)(f' : P.x (n + 1) ⟶ Q.x (n + 1)), f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mk_hom_aux n).2.1, (succ n (mk_hom_aux n)).1, (succ n (mk_hom_aux n)).2⟩

/-- A constructor for chain maps between `ℕ`-indexed chain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mkHom : P ⟶ Q where
  f := fun n => (mkHomAuxₓ P Q zero one one_zero_comm succ n).1
  comm' := fun n m => by
    rintro (rfl : m + 1 = n)
    exact (mk_hom_aux P Q zero one one_zero_comm succ m).2.2

@[simp]
theorem mk_hom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
theorem mk_hom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
theorem mk_hom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n, (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm (n + 1) n⟩).1 :=
  by
  dsimp' [← mk_hom, ← mk_hom_aux]
  induction n <;> congr

end MkHom

end ChainComplex

namespace CochainComplex

section Of

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/-- Construct an `α`-indexed cochain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0) : CochainComplex V α :=
  { x,
    d := fun i j =>
      if h : i + 1 = j then
        d _ ≫
          eqToHom
            (by
              subst h)
      else 0,
    shape' := fun i j w => by
      rw [dif_neg]
      exact w,
    d_comp_d' := fun i j k => by
      split_ifs with h h' h'
      · substs h h'
        simp [← sq]
        
      all_goals
        simp }

variable (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0)

@[simp]
theorem of_X (n : α) : (of X d sq).x n = X n :=
  rfl

@[simp]
theorem of_d (j : α) : (of X d sq).d j (j + 1) = d j := by
  dsimp' [← of]
  rw [if_pos rfl, category.comp_id]

theorem of_d_ne {i j : α} (h : i + 1 ≠ j) : (of X d sq).d i j = 0 := by
  dsimp' [← of]
  rw [dif_neg h]

end Of

section OfHom

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

variable (X : α → V) (d_X : ∀ n, X n ⟶ X (n + 1)) (sq_X : ∀ n, d_X n ≫ d_X (n + 1) = 0) (Y : α → V)
  (d_Y : ∀ n, Y n ⟶ Y (n + 1)) (sq_Y : ∀ n, d_Y n ≫ d_Y (n + 1) = 0)

/-- A constructor for chain maps between `α`-indexed cochain complexes built using `cochain_complex.of`,
from a dependently typed collection of morphisms.
-/
@[simps]
def ofHom (f : ∀ i : α, X i ⟶ Y i) (comm : ∀ i : α, f i ≫ d_Y i = d_X i ≫ f (i + 1)) : of X d_X sq_X ⟶ of Y d_Y sq_Y :=
  { f,
    comm' := fun n m => by
      by_cases' h : n + 1 = m
      · subst h
        simpa using comm n
        
      · rw [of_d_ne X _ _ h, of_d_ne Y _ _ h]
        simp
         }

end OfHom

section Mk

/-- Auxiliary structure for setting up the recursion in `mk`.
This is purely an implementation detail: for some reason just using the dependent 6-tuple directly
results in `mk_aux` taking much longer (well over the `-T100000` limit) to elaborate.
-/
@[nolint has_inhabited_instance]
structure MkStruct where
  (x₀ x₁ x₂ : V)
  d₀ : X₀ ⟶ X₁
  d₁ : X₁ ⟶ X₂
  s : d₀ ≫ d₁ = 0

variable {V}

/-- Flatten to a tuple. -/
def MkStruct.flat (t : MkStruct V) : Σ'(X₀ X₁ X₂ : V)(d₀ : X₀ ⟶ X₁)(d₁ : X₁ ⟶ X₂), d₀ ≫ d₁ = 0 :=
  ⟨t.x₀, t.x₁, t.x₂, t.d₀, t.d₁, t.s⟩

variable (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ :
    ∀ t : Σ'(X₀ X₁ X₂ : V)(d₀ : X₀ ⟶ X₁)(d₁ : X₁ ⟶ X₂), d₀ ≫ d₁ = 0,
      Σ'(X₃ : V)(d₂ : t.2.2.1 ⟶ X₃), t.2.2.2.2.1 ≫ d₂ = 0)

/-- Auxiliary definition for `mk`. -/
def mkAuxₓ : ∀ n : ℕ, MkStruct V
  | 0 => ⟨X₀, X₁, X₂, d₀, d₁, s⟩
  | n + 1 =>
    let p := mk_aux n
    ⟨p.x₁, p.x₂, (succ p.flat).1, p.d₁, (succ p.flat).2.1, (succ p.flat).2.2⟩

/-- A inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropiately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : CochainComplex V ℕ :=
  of (fun n => (mkAuxₓ X₀ X₁ X₂ d₀ d₁ s succ n).x₀) (fun n => (mkAuxₓ X₀ X₁ X₂ d₀ d₁ s succ n).d₀) fun n =>
    (mkAuxₓ X₀ X₁ X₂ d₀ d₁ s succ n).s

@[simp]
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).x 0 = X₀ :=
  rfl

@[simp]
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).x 1 = X₁ :=
  rfl

@[simp]
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).x 2 = X₂ :=
  rfl

@[simp]
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl, category.comp_id]

@[simp]
theorem mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁ := by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁
  rw [if_pos rfl, category.comp_id]

/-- A simpler inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
def mk' (X₀ X₁ : V) (d : X₀ ⟶ X₁) (succ' : ∀ t : ΣX₀ X₁ : V, X₀ ⟶ X₁, Σ'(X₂ : V)(d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0) :
    CochainComplex V ℕ :=
  mk X₀ X₁ (succ' ⟨X₀, X₁, d⟩).1 d (succ' ⟨X₀, X₁, d⟩).2.1 (succ' ⟨X₀, X₁, d⟩).2.2 fun t =>
    succ' ⟨t.2.1, t.2.2.1, t.2.2.2.2.1⟩

variable (succ' : ∀ t : ΣX₀ X₁ : V, X₀ ⟶ X₁, Σ'(X₂ : V)(d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0)

@[simp]
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').x 0 = X₀ :=
  rfl

@[simp]
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').x 1 = X₁ :=
  rfl

@[simp]
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl, category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
end Mk

section MkHom

variable {V} (P Q : CochainComplex V ℕ) (zero : P.x 0 ⟶ Q.x 0) (one : P.x 1 ⟶ Q.x 1)
  (one_zero_comm : zero ≫ Q.d 0 1 = P.d 0 1 ≫ one)
  (succ :
    ∀ (n : ℕ) (p : Σ'(f : P.x n ⟶ Q.x n)(f' : P.x (n + 1) ⟶ Q.x (n + 1)), f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'),
      Σ'f'' : P.x (n + 2) ⟶ Q.x (n + 2), p.2.1 ≫ Q.d (n + 1) (n + 2) = P.d (n + 1) (n + 2) ≫ f'')

/-- An auxiliary construction for `mk_hom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mk_hom`.
-/
def mkHomAuxₓ : ∀ n, Σ'(f : P.x n ⟶ Q.x n)(f' : P.x (n + 1) ⟶ Q.x (n + 1)), f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mk_hom_aux n).2.1, (succ n (mk_hom_aux n)).1, (succ n (mk_hom_aux n)).2⟩

/-- A constructor for chain maps between `ℕ`-indexed cochain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mkHom : P ⟶ Q where
  f := fun n => (mkHomAuxₓ P Q zero one one_zero_comm succ n).1
  comm' := fun n m => by
    rintro (rfl : n + 1 = m)
    exact (mk_hom_aux P Q zero one one_zero_comm succ n).2.2

@[simp]
theorem mk_hom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
theorem mk_hom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
theorem mk_hom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n, (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm n (n + 1)⟩).1 :=
  by
  dsimp' [← mk_hom, ← mk_hom_aux]
  induction n <;> congr

end MkHom

end CochainComplex

