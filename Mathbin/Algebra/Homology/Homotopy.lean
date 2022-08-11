/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Homology.Additive
import Mathbin.Tactic.Abel

/-!
# Chain homotopies

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/


universe v u

open Classical

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

section

/-- The composition of `C.d i i' ≫ f i' i` if there is some `i'` coming after `i`,
and `0` otherwise. -/
def dNext (i : ι) : (∀ i j, C.x i ⟶ D.x j) →+ (C.x i ⟶ D.x i) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.next i with
      | none => 0
      | some ⟨i', w⟩ => C.d i i' ≫ f i' i)
    (by
      intro f g
      rcases c.next i with (_ | ⟨i', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.comp_add _ _ _ _ _ _)

/-- `f i' i` if `i'` comes after `i`, and 0 if there's no such `i'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def fromNext [HasZeroObject V] (i : ι) : (∀ i j, C.x i ⟶ D.x j) →+ (C.xNext i ⟶ D.x i) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.next i with
      | none => 0
      | some ⟨i', w⟩ => (C.xNextIso w).Hom ≫ f i' i)
    (by
      intro f g
      rcases c.next i with (_ | ⟨i', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.comp_add _ _ _ _ _ _)

@[simp]
theorem d_next_eq_d_from_from_next [HasZeroObject V] (f : ∀ i j, C.x i ⟶ D.x j) (i : ι) :
    dNext i f = C.dFrom i ≫ fromNext i f := by
  dsimp' [← dNext, ← fromNext]
  rcases c.next i with (⟨⟩ | ⟨⟨i', w⟩⟩) <;>
    · dsimp' [← dNext, ← fromNext]
      simp
      

theorem d_next_eq (f : ∀ i j, C.x i ⟶ D.x j) {i i' : ι} (w : c.Rel i i') : dNext i f = C.d i i' ≫ f i' i := by
  dsimp' [← dNext]
  rw [c.next_eq_some w]
  rfl

@[simp]
theorem d_next_comp_left (f : C ⟶ D) (g : ∀ i j, D.x i ⟶ E.x j) (i : ι) :
    (dNext i fun i j => f.f i ≫ g i j) = f.f i ≫ dNext i g := by
  dsimp' [← dNext]
  rcases c.next i with (_ | ⟨i', w⟩)
  · exact comp_zero.symm
    
  · dsimp' [← dNext]
    simp
    

@[simp]
theorem d_next_comp_right (f : ∀ i j, C.x i ⟶ D.x j) (g : D ⟶ E) (i : ι) :
    (dNext i fun i j => f i j ≫ g.f j) = dNext i f ≫ g.f i := by
  dsimp' [← dNext]
  rcases c.next i with (_ | ⟨i', w⟩)
  · exact zero_comp.symm
    
  · dsimp' [← dNext]
    simp
    

/-- The composition of `f j j' ≫ D.d j' j` if there is some `j'` coming before `j`,
and `0` otherwise. -/
def prevD (j : ι) : (∀ i j, C.x i ⟶ D.x j) →+ (C.x j ⟶ D.x j) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.prev j with
      | none => 0
      | some ⟨j', w⟩ => f j j' ≫ D.d j' j)
    (by
      intro f g
      rcases c.prev j with (_ | ⟨j', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.add_comp _ _ _ _ _ _)

/-- `f j j'` if `j'` comes after `j`, and 0 if there's no such `j'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def toPrev [HasZeroObject V] (j : ι) : (∀ i j, C.x i ⟶ D.x j) →+ (C.x j ⟶ D.xPrev j) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.prev j with
      | none => 0
      | some ⟨j', w⟩ => f j j' ≫ (D.xPrevIso w).inv)
    (by
      intro f g
      rcases c.prev j with (_ | ⟨j', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.add_comp _ _ _ _ _ _)

@[simp]
theorem prev_d_eq_to_prev_d_to [HasZeroObject V] (f : ∀ i j, C.x i ⟶ D.x j) (j : ι) :
    prevD j f = toPrev j f ≫ D.dTo j := by
  dsimp' [← prevD, ← toPrev]
  rcases c.prev j with (⟨⟩ | ⟨⟨j', w⟩⟩) <;>
    · dsimp' [← prevD, ← toPrev]
      simp
      

theorem prev_d_eq (f : ∀ i j, C.x i ⟶ D.x j) {j j' : ι} (w : c.Rel j' j) : prevD j f = f j j' ≫ D.d j' j := by
  dsimp' [← prevD]
  rw [c.prev_eq_some w]
  rfl

@[simp]
theorem prev_d_comp_left (f : C ⟶ D) (g : ∀ i j, D.x i ⟶ E.x j) (j : ι) :
    (prevD j fun i j => f.f i ≫ g i j) = f.f j ≫ prevD j g := by
  dsimp' [← prevD]
  rcases c.prev j with (_ | ⟨j', w⟩)
  · exact comp_zero.symm
    
  · dsimp' [← prevD, ← hom.prev]
    simp
    

@[simp]
theorem prev_d_comp_right (f : ∀ i j, C.x i ⟶ D.x j) (g : D ⟶ E) (j : ι) :
    (prevD j fun i j => f i j ≫ g.f j) = prevD j f ≫ g.f j := by
  dsimp' [← prevD]
  rcases c.prev j with (_ | ⟨j', w⟩)
  · exact zero_comp.symm
    
  · dsimp' [← prevD]
    simp
    

theorem d_next_nat (C D : ChainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.x i ⟶ D.x j) :
    dNext i f = C.d i (i - 1) ≫ f (i - 1) i := by
  cases i
  · dsimp' [← dNext]
    rcases(ComplexShape.down ℕ).next 0 with (_ | ⟨j, hj⟩) <;> dsimp' [← dNext]
    · rw [C.shape, zero_comp]
      dsimp'
      decide
      
    · dsimp'  at hj
      exact (Nat.succ_ne_zero _ hj).elim
      
    
  rw [d_next_eq]
  dsimp'
  rfl

theorem prev_d_nat (C D : CochainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.x i ⟶ D.x j) :
    prevD i f = f i (i - 1) ≫ D.d (i - 1) i := by
  cases i
  · dsimp' [← prevD]
    rcases(ComplexShape.up ℕ).prev 0 with (_ | ⟨j, hj⟩) <;> dsimp' [← prevD]
    · rw [D.shape, comp_zero]
      dsimp'
      decide
      
    · dsimp'  at hj
      exact (Nat.succ_ne_zero _ hj).elim
      
    
  rw [prev_d_eq]
  dsimp'
  rfl

/-- A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X j`
which are zero unless `c.rel j i`, satisfying the homotopy condition.
-/
@[ext, nolint has_inhabited_instance]
structure Homotopy (f g : C ⟶ D) where
  Hom : ∀ i j, C.x i ⟶ D.x j
  zero' : ∀ i j, ¬c.Rel j i → hom i j = 0 := by
    run_tac
      obviously
  comm : ∀ i, f.f i = dNext i hom + prevD i hom + g.f i := by
    run_tac
      obviously'

variable {f g}

namespace Homotopy

restate_axiom Homotopy.zero'

/-- `f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equivSubZero : Homotopy f g ≃ Homotopy (f - g) 0 where
  toFun := fun h =>
    { Hom := fun i j => h.Hom i j, zero' := fun i j w => h.zero _ _ w,
      comm := fun i => by
        simp [← h.comm] }
  invFun := fun h =>
    { Hom := fun i j => h.Hom i j, zero' := fun i j w => h.zero _ _ w,
      comm := fun i => by
        simpa [← sub_eq_iff_eq_add] using h.comm i }
  left_inv := by
    tidy
  right_inv := by
    tidy

/-- Equal chain maps are homotopic. -/
@[simps]
def ofEq (h : f = g) : Homotopy f g where
  Hom := 0
  zero' := fun _ _ _ => rfl
  comm := fun _ => by
    simp only [← AddMonoidHom.map_zero, ← zero_addₓ, ← h]

/-- Every chain map is homotopic to itself. -/
@[simps, refl]
def refl (f : C ⟶ D) : Homotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps, symm]
def symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f where
  Hom := -h.Hom
  zero' := fun i j w => by
    rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero]
  comm := fun i => by
    rw [AddMonoidHom.map_neg, AddMonoidHom.map_neg, h.comm, ← neg_add, ← add_assocₓ, neg_add_selfₓ, zero_addₓ]

/-- homotopy is a transitive relation. -/
@[simps, trans]
def trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g where
  Hom := h.Hom + k.Hom
  zero' := fun i j w => by
    rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_addₓ]
  comm := fun i => by
    rw [AddMonoidHom.map_add, AddMonoidHom.map_add, h.comm, k.comm]
    abel

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps]
def add {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ + f₂) (g₁ + g₂) where
  Hom := h₁.Hom + h₂.Hom
  zero' := fun i j hij => by
    rw [Pi.add_apply, Pi.add_apply, h₁.zero' i j hij, h₂.zero' i j hij, add_zeroₓ]
  comm := fun i => by
    simp only [← HomologicalComplex.add_f_apply, ← h₁.comm, ← h₂.comm, ← AddMonoidHom.map_add]
    abel

/-- homotopy is closed under composition (on the right) -/
@[simps]
def compRight {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E) : Homotopy (e ≫ g) (f ≫ g) where
  Hom := fun i j => h.Hom i j ≫ g.f j
  zero' := fun i j w => by
    rw [h.zero i j w, zero_comp]
  comm := fun i => by
    simp only [← h.comm i, ← d_next_comp_right, ← preadditive.add_comp, ← prev_d_comp_right, ← comp_f]

/-- homotopy is closed under composition (on the left) -/
@[simps]
def compLeft {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D) : Homotopy (e ≫ f) (e ≫ g) where
  Hom := fun i j => e.f i ≫ h.Hom i j
  zero' := fun i j w => by
    rw [h.zero i j w, comp_zero]
  comm := fun i => by
    simp only [← h.comm i, ← d_next_comp_left, ← preadditive.comp_add, ← prev_d_comp_left, ← comp_f]

/-- homotopy is closed under composition -/
@[simps]
def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃} (h₁ : Homotopy f₁ g₁)
    (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- a variant of `homotopy.comp_right` useful for dealing with homotopy equivalences. -/
@[simps]
def compRightId {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D) : Homotopy (f ≫ g) g :=
  (h.compRight g).trans (of_eq <| Category.id_comp _)

/-- a variant of `homotopy.comp_left` useful for dealing with homotopy equivalences. -/
@[simps]
def compLeftId {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D) : Homotopy (g ≫ f) g :=
  (h.compLeft g).trans (of_eq <| Category.comp_id _)

/-!
Null homotopic maps can be constructed using the formula `hd+dh`. We show that
these morphisms are homotopic to `0` and provide some convenient simplification
lemmas that give a degreewise description of `hd+dh`, depending on whether we have
two differentials going to and from a certain degree, only one, or none.
-/


/-- The null homotopic map associated to a family `hom` of morphisms `C_i ⟶ D_j`.
This is the same datum as for the field `hom` in the structure `homotopy`. For
this definition, we do not need the field `zero` of that structure
as this definition uses only the maps `C_i ⟶ C_j` when `c.rel j i`. -/
def nullHomotopicMap (hom : ∀ i j, C.x i ⟶ D.x j) : C ⟶ D where
  f := fun i => dNext i hom + prevD i hom
  comm' := fun i j hij => by
    have eq1 : prevD i hom ≫ D.d i j = 0 := by
      rcases h : c.prev i with (_ | ⟨i', w⟩)
      · dsimp' [← prevD]
        rw [h]
        erw [zero_comp]
        
      · rw [prev_d_eq hom w, category.assoc, D.d_comp_d' i' i j w hij, comp_zero]
        
    have eq2 : C.d i j ≫ dNext j hom = 0 := by
      rcases h : c.next j with (_ | ⟨j', w⟩)
      · dsimp' [← dNext]
        rw [h]
        erw [comp_zero]
        
      · rw [d_next_eq hom w, ← category.assoc, C.d_comp_d' i j j' hij w, zero_comp]
        
    rw [d_next_eq hom hij, prev_d_eq hom hij, preadditive.comp_add, preadditive.add_comp, eq1, eq2, add_zeroₓ,
      zero_addₓ, category.assoc]

/-- Variant of `null_homotopic_map` where the input consists only of the
relevant maps `C_i ⟶ D_j` such that `c.rel j i`. -/
def nullHomotopicMap' (h : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) : C ⟶ D :=
  nullHomotopicMap fun i j => dite (c.Rel j i) (h i j) fun _ => 0

/-- Compatibility of `null_homotopic_map` with the postcomposition by a morphism
of complexes. -/
theorem null_homotopic_map_comp (hom : ∀ i j, C.x i ⟶ D.x j) (g : D ⟶ E) :
    nullHomotopicMap hom ≫ g = nullHomotopicMap fun i j => hom i j ≫ g.f j := by
  ext n
  dsimp' [← null_homotopic_map]
  simp only [← preadditive.add_comp, ← d_next_comp_right, ← prev_d_comp_right]

/-- Compatibility of `null_homotopic_map'` with the postcomposition by a morphism
of complexes. -/
theorem null_homotopic_map'_comp (hom : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) (g : D ⟶ E) :
    nullHomotopicMap' hom ≫ g = nullHomotopicMap' fun i j hij => hom i j hij ≫ g.f j := by
  ext n
  erw [null_homotopic_map_comp]
  congr
  ext i j
  split_ifs
  · rfl
    
  · rw [zero_comp]
    

/-- Compatibility of `null_homotopic_map` with the precomposition by a morphism
of complexes. -/
theorem comp_null_homotopic_map (f : C ⟶ D) (hom : ∀ i j, D.x i ⟶ E.x j) :
    f ≫ nullHomotopicMap hom = nullHomotopicMap fun i j => f.f i ≫ hom i j := by
  ext n
  dsimp' [← null_homotopic_map]
  simp only [← preadditive.comp_add, ← d_next_comp_left, ← prev_d_comp_left]

/-- Compatibility of `null_homotopic_map'` with the precomposition by a morphism
of complexes. -/
theorem comp_null_homotopic_map' (f : C ⟶ D) (hom : ∀ i j, c.Rel j i → (D.x i ⟶ E.x j)) :
    f ≫ nullHomotopicMap' hom = nullHomotopicMap' fun i j hij => f.f i ≫ hom i j hij := by
  ext n
  erw [comp_null_homotopic_map]
  congr
  ext i j
  split_ifs
  · rfl
    
  · rw [comp_zero]
    

/-- Compatibility of `null_homotopic_map` with the application of additive functors -/
theorem map_null_homotopic_map {W : Type _} [Category W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : ∀ i j, C.x i ⟶ D.x j) :
    (G.mapHomologicalComplex c).map (nullHomotopicMap hom) = nullHomotopicMap fun i j => G.map (hom i j) := by
  ext i
  dsimp' [← null_homotopic_map, ← dNext, ← prevD]
  rcases c.next i with (_ | ⟨inext, wn⟩) <;>
    rcases c.prev i with (_ | ⟨iprev, wp⟩) <;>
      dsimp' [← dNext, ← prevD] <;> simp only [← G.map_comp, ← functor.map_zero, ← functor.map_add]

/-- Compatibility of `null_homotopic_map'` with the application of additive functors -/
theorem map_null_homotopic_map' {W : Type _} [Category W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) :
    (G.mapHomologicalComplex c).map (nullHomotopicMap' hom) = nullHomotopicMap' fun i j hij => G.map (hom i j hij) := by
  ext n
  erw [map_null_homotopic_map]
  congr
  ext i j
  split_ifs
  · rfl
    
  · rw [G.map_zero]
    

/-- Tautological construction of the `homotopy` to zero for maps constructed by
`null_homotopic_map`, at least when we have the `zero'` condition. -/
@[simps]
def nullHomotopy (hom : ∀ i j, C.x i ⟶ D.x j) (zero' : ∀ i j, ¬c.Rel j i → hom i j = 0) :
    Homotopy (nullHomotopicMap hom) 0 :=
  { Hom, zero',
    comm := by
      intro i
      rw [HomologicalComplex.zero_f_apply, add_zeroₓ]
      rfl }

/-- Homotopy to zero for maps constructed with `null_homotopic_map'` -/
@[simps]
def nullHomotopy' (h : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) : Homotopy (nullHomotopicMap' h) 0 := by
  apply null_homotopy fun i j => dite (c.rel j i) (h i j) fun _ => 0
  intro i j hij
  dsimp'
  rw [dite_eq_right_iff]
  intro hij'
  exfalso
  exact hij hij'

/-! This lemma and the following ones can be used in order to compute
the degreewise morphisms induced by the null homotopic maps constructed
with `null_homotopic_map` or `null_homotopic_map'` -/


@[simp]
theorem null_homotopic_map_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀) (hom : ∀ i j, C.x i ⟶ D.x j) :
    (nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ + hom k₁ k₂ ≫ D.d k₂ k₁ := by
  dsimp' [← null_homotopic_map]
  rw [d_next_eq hom r₁₀, prev_d_eq hom r₂₁]

@[simp]
theorem null_homotopic_map'_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
    (h : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) :
    (nullHomotopicMap' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ + h k₁ k₂ r₂₁ ≫ D.d k₂ k₁ := by
  simp only [null_homotopic_map']
  rw [null_homotopic_map_f r₂₁ r₁₀ fun i j => dite (c.rel j i) (h i j) fun _ => 0]
  dsimp'
  split_ifs
  rfl

@[simp]
theorem null_homotopic_map_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₀ : ∀ l : ι, ¬c.Rel k₀ l)
    (hom : ∀ i j, C.x i ⟶ D.x j) : (nullHomotopicMap hom).f k₀ = hom k₀ k₁ ≫ D.d k₁ k₀ := by
  dsimp' [← null_homotopic_map]
  rw [prev_d_eq hom r₁₀]
  rcases h : c.next k₀ with (_ | ⟨l, w⟩)
  swap
  exfalso
  exact hk₀ l w
  dsimp' [← dNext]
  rw [h]
  erw [zero_addₓ]

@[simp]
theorem null_homotopic_map'_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₀ : ∀ l : ι, ¬c.Rel k₀ l)
    (h : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) : (nullHomotopicMap' h).f k₀ = h k₀ k₁ r₁₀ ≫ D.d k₁ k₀ := by
  simp only [null_homotopic_map']
  rw [null_homotopic_map_f_of_not_rel_left r₁₀ hk₀ fun i j => dite (c.rel j i) (h i j) fun _ => 0]
  dsimp'
  split_ifs
  rfl

@[simp]
theorem null_homotopic_map_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₁ : ∀ l : ι, ¬c.Rel l k₁)
    (hom : ∀ i j, C.x i ⟶ D.x j) : (nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ := by
  dsimp' [← null_homotopic_map]
  rw [d_next_eq hom r₁₀]
  rcases h : c.prev k₁ with (_ | ⟨l, w⟩)
  swap
  exfalso
  exact hk₁ l w
  dsimp' [← prevD]
  rw [h]
  erw [add_zeroₓ]

@[simp]
theorem null_homotopic_map'_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₁ : ∀ l : ι, ¬c.Rel l k₁)
    (h : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) : (nullHomotopicMap' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ := by
  simp only [null_homotopic_map']
  rw [null_homotopic_map_f_of_not_rel_right r₁₀ hk₁ fun i j => dite (c.rel j i) (h i j) fun _ => 0]
  dsimp'
  split_ifs
  rfl

@[simp]
theorem null_homotopic_map_f_eq_zero {k₀ : ι} (hk₀ : ∀ l : ι, ¬c.Rel k₀ l) (hk₀' : ∀ l : ι, ¬c.Rel l k₀)
    (hom : ∀ i j, C.x i ⟶ D.x j) : (nullHomotopicMap hom).f k₀ = 0 := by
  dsimp' [← null_homotopic_map]
  rcases h1 : c.next k₀ with (_ | ⟨l, w⟩)
  swap
  exfalso
  exact hk₀ l w
  rcases h2 : c.prev k₀ with (_ | ⟨l, w⟩)
  swap
  exfalso
  exact hk₀' l w
  dsimp' [← dNext, ← prevD]
  rw [h1, h2]
  erw [zero_addₓ]
  rfl

@[simp]
theorem null_homotopic_map'_f_eq_zero {k₀ : ι} (hk₀ : ∀ l : ι, ¬c.Rel k₀ l) (hk₀' : ∀ l : ι, ¬c.Rel l k₀)
    (h : ∀ i j, c.Rel j i → (C.x i ⟶ D.x j)) : (nullHomotopicMap' h).f k₀ = 0 := by
  simp only [null_homotopic_map']
  exact null_homotopic_map_f_eq_zero hk₀ hk₀' fun i j => dite (c.rel j i) (h i j) fun _ => 0

/-!
`homotopy.mk_inductive` allows us to build a homotopy of chain complexes inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.

To simplify the situation, we only construct homotopies of the form `homotopy e 0`.
`homotopy.equiv_sub_zero` can provide the general case.

Notice however, that this construction does not have particularly good definitional properties:
we have to insert `eq_to_hom` in several places.
Hopefully this is okay in most applications, where we only need to have the existence of some
homotopy.
-/


section MkInductive

variable {P Q : ChainComplex V ℕ}

@[simp]
theorem prev_d_chain_complex (f : ∀ i j, P.x i ⟶ Q.x j) (j : ℕ) : prevD j f = f j (j + 1) ≫ Q.d _ _ := by
  dsimp' [← prevD]
  simp only [← ChainComplex.prev]
  rfl

@[simp]
theorem d_next_succ_chain_complex (f : ∀ i j, P.x i ⟶ Q.x j) (i : ℕ) : dNext (i + 1) f = P.d _ _ ≫ f i (i + 1) := by
  dsimp' [← dNext]
  simp only [← ChainComplex.next_nat_succ]
  rfl

@[simp]
theorem d_next_zero_chain_complex (f : ∀ i j, P.x i ⟶ Q.x j) : dNext 0 f = 0 := by
  dsimp' [← dNext]
  simp only [← ChainComplex.next_nat_zero]
  rfl

variable (e : P ⟶ Q) (zero : P.x 0 ⟶ Q.x 1) (comm_zero : e.f 0 = zero ≫ Q.d 1 0) (one : P.x 1 ⟶ Q.x 2)
  (comm_one : e.f 1 = P.d 1 0 ≫ zero + one ≫ Q.d 2 1)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ'(f : P.x n ⟶ Q.x (n + 1))(f' : P.x (n + 1) ⟶ Q.x (n + 2)),
          e.f (n + 1) = P.d (n + 1) n ≫ f + f' ≫ Q.d (n + 2) (n + 1)),
      Σ'f'' : P.x (n + 2) ⟶ Q.x (n + 3), e.f (n + 2) = P.d (n + 2) (n + 1) ≫ p.2.1 + f'' ≫ Q.d (n + 3) (n + 2))

include comm_one comm_zero

/-- An auxiliary construction for `mk_inductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mk_inductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `X_next` and `X_prev`,
which we do in `mk_inductive_aux₂`.
-/
@[simp, nolint unused_arguments]
def mkInductiveAux₁ₓ :
    ∀ n,
      Σ'(f : P.x n ⟶ Q.x (n + 1))(f' : P.x (n + 1) ⟶ Q.x (n + 2)),
        e.f (n + 1) = P.d (n + 1) n ≫ f + f' ≫ Q.d (n + 2) (n + 1)
  | 0 => ⟨zero, one, comm_one⟩
  | 1 => ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
  | n + 2 =>
    ⟨(mk_inductive_aux₁ (n + 1)).2.1, (succ (n + 1) (mk_inductive_aux₁ (n + 1))).1,
      (succ (n + 1) (mk_inductive_aux₁ (n + 1))).2⟩

section

variable [HasZeroObject V]

/-- An auxiliary construction for `mk_inductive`.
-/
@[simp]
def mkInductiveAux₂ₓ : ∀ n, Σ'(f : P.xNext n ⟶ Q.x n)(f' : P.x n ⟶ Q.xPrev n), e.f n = P.dFrom n ≫ f + f' ≫ Q.dTo n
  | 0 =>
    ⟨0, zero ≫ (Q.xPrevIso rfl).inv, by
      simpa using comm_zero⟩
  | n + 1 =>
    let I := mkInductiveAux₁ₓ e zero comm_zero one comm_one succ n
    ⟨(P.xNextIso rfl).Hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by
      simpa using I.2.2⟩

theorem mk_inductive_aux₃ (i : ℕ) :
    (mkInductiveAux₂ₓ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso rfl).Hom =
      (P.xNextIso rfl).inv ≫ (mkInductiveAux₂ₓ e zero comm_zero one comm_one succ (i + 1)).1 :=
  by
  rcases i with (_ | _ | i) <;>
    · dsimp'
      simp
      

/-- A constructor for a `homotopy e 0`, for `e` a chain map between `ℕ`-indexed chain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
def mkInductive : Homotopy e 0 where
  Hom := fun i j =>
    if h : i + 1 = j then (mkInductiveAux₂ₓ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso h).Hom else 0
  zero' := fun i j w => by
    rwa [dif_neg]
  comm := fun i => by
    dsimp'
    simp only [← add_zeroₓ]
    convert (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.2
    · rcases i with (_ | _ | _ | i)
      · dsimp'
        simp only [← d_next_zero_chain_complex, ← d_from_eq_zero, ← limits.comp_zero]
        
      all_goals
        simp only [← d_next_succ_chain_complex]
        dsimp'
        simp only [← category.comp_id, ← category.assoc, ← iso.inv_hom_id, ← d_from_comp_X_next_iso_assoc, ←
          dite_eq_ite, ← if_true, ← eq_self_iff_true]
      
    · cases i
      all_goals
        simp only [← prev_d_chain_complex]
        dsimp'
        simp only [← category.comp_id, ← category.assoc, ← iso.inv_hom_id, ← X_prev_iso_comp_d_to, ← dite_eq_ite, ←
          if_true, ← eq_self_iff_true]
      

end

end MkInductive

/-!
`homotopy.mk_coinductive` allows us to build a homotopy of cochain complexes inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.
-/


section MkCoinductive

variable {P Q : CochainComplex V ℕ}

@[simp]
theorem d_next_cochain_complex (f : ∀ i j, P.x i ⟶ Q.x j) (j : ℕ) : dNext j f = P.d _ _ ≫ f (j + 1) j := by
  dsimp' [← dNext]
  simp only [← CochainComplex.next]
  rfl

@[simp]
theorem prev_d_succ_cochain_complex (f : ∀ i j, P.x i ⟶ Q.x j) (i : ℕ) :
    prevD (i + 1) f = f (i + 1) _ ≫ Q.d i (i + 1) := by
  dsimp' [← prevD]
  simp [← CochainComplex.prev_nat_succ]
  rfl

@[simp]
theorem prev_d_zero_cochain_complex (f : ∀ i j, P.x i ⟶ Q.x j) : prevD 0 f = 0 := by
  dsimp' [← prevD]
  simp only [← CochainComplex.prev_nat_zero]
  rfl

variable (e : P ⟶ Q) (zero : P.x 1 ⟶ Q.x 0) (comm_zero : e.f 0 = P.d 0 1 ≫ zero) (one : P.x 2 ⟶ Q.x 1)
  (comm_one : e.f 1 = zero ≫ Q.d 0 1 + P.d 1 2 ≫ one)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ'(f : P.x (n + 1) ⟶ Q.x n)(f' : P.x (n + 2) ⟶ Q.x (n + 1)),
          e.f (n + 1) = f ≫ Q.d n (n + 1) + P.d (n + 1) (n + 2) ≫ f'),
      Σ'f'' : P.x (n + 3) ⟶ Q.x (n + 2), e.f (n + 2) = p.2.1 ≫ Q.d (n + 1) (n + 2) + P.d (n + 2) (n + 3) ≫ f'')

include comm_one comm_zero succ

/-- An auxiliary construction for `mk_coinductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mk_coinductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `X_next` and `X_prev`,
which we do in `mk_inductive_aux₂`.
-/
@[simp, nolint unused_arguments]
def mkCoinductiveAux₁ₓ :
    ∀ n,
      Σ'(f : P.x (n + 1) ⟶ Q.x n)(f' : P.x (n + 2) ⟶ Q.x (n + 1)),
        e.f (n + 1) = f ≫ Q.d n (n + 1) + P.d (n + 1) (n + 2) ≫ f'
  | 0 => ⟨zero, one, comm_one⟩
  | 1 => ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
  | n + 2 =>
    ⟨(mk_coinductive_aux₁ (n + 1)).2.1, (succ (n + 1) (mk_coinductive_aux₁ (n + 1))).1,
      (succ (n + 1) (mk_coinductive_aux₁ (n + 1))).2⟩

section

variable [HasZeroObject V]

/-- An auxiliary construction for `mk_inductive`.
-/
@[simp]
def mkCoinductiveAux₂ₓ : ∀ n, Σ'(f : P.x n ⟶ Q.xPrev n)(f' : P.xNext n ⟶ Q.x n), e.f n = f ≫ Q.dTo n + P.dFrom n ≫ f'
  | 0 =>
    ⟨0, (P.xNextIso rfl).Hom ≫ zero, by
      simpa using comm_zero⟩
  | n + 1 =>
    let I := mkCoinductiveAux₁ₓ e zero comm_zero one comm_one succ n
    ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).Hom ≫ I.2.1, by
      simpa using I.2.2⟩

theorem mk_coinductive_aux₃ (i : ℕ) :
    (mkCoinductiveAux₂ₓ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso rfl).inv =
      (P.xNextIso rfl).Hom ≫ (mkCoinductiveAux₂ₓ e zero comm_zero one comm_one succ (i + 1)).1 :=
  by
  rcases i with (_ | _ | i) <;>
    · dsimp'
      simp
      

/-- A constructor for a `homotopy e 0`, for `e` a chain map between `ℕ`-indexed cochain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
def mkCoinductive : Homotopy e 0 where
  Hom := fun i j =>
    if h : j + 1 = i then (P.xNextIso h).inv ≫ (mkCoinductiveAux₂ₓ e zero comm_zero one comm_one succ j).2.1 else 0
  zero' := fun i j w => by
    rwa [dif_neg]
  comm := fun i => by
    dsimp'
    rw [add_zeroₓ, add_commₓ]
    convert (mk_coinductive_aux₂ e zero comm_zero one comm_one succ i).2.2 using 2
    · rcases i with (_ | _ | _ | i)
      · simp only [← mk_coinductive_aux₂, ← prev_d_zero_cochain_complex, ← zero_comp]
        
      all_goals
        simp only [← prev_d_succ_cochain_complex]
        dsimp'
        simp only [← eq_self_iff_true, ← iso.inv_hom_id_assoc, ← dite_eq_ite, ← if_true, ← category.assoc, ←
          X_prev_iso_comp_d_to]
      
    · cases i
      · dsimp'
        simp only [← eq_self_iff_true, ← d_next_cochain_complex, ← dif_pos, ← d_from_comp_X_next_iso_assoc, comm_zero]
        rw [mk_coinductive_aux₂]
        dsimp'
        convert comm_zero.symm
        simp only [← iso.inv_hom_id_assoc]
        
      · dsimp'
        simp only [← eq_self_iff_true, ← d_next_cochain_complex, ← dif_pos, ← d_from_comp_X_next_iso_assoc]
        rw [mk_coinductive_aux₂]
        dsimp' only
        simp only [← iso.inv_hom_id_assoc]
        
      

end

end MkCoinductive

end Homotopy

/-- A homotopy equivalence between two chain complexes consists of a chain map each way,
and homotopies from the compositions to the identity chain maps.

Note that this contains data;
arguably it might be more useful for many applications if we truncated it to a Prop.
-/
structure HomotopyEquiv (C D : HomologicalComplex V c) where
  Hom : C ⟶ D
  inv : D ⟶ C
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 C)
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 D)

namespace HomotopyEquiv

/-- Any complex is homotopy equivalent to itself. -/
@[refl]
def refl (C : HomologicalComplex V c) : HomotopyEquiv C C where
  Hom := 𝟙 C
  inv := 𝟙 C
  homotopyHomInvId := by
    simp
  homotopyInvHomId := by
    simp

instance : Inhabited (HomotopyEquiv C C) :=
  ⟨refl C⟩

/-- Being homotopy equivalent is a symmetric relation. -/
@[symm]
def symm {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) : HomotopyEquiv D C where
  Hom := f.inv
  inv := f.Hom
  homotopyHomInvId := f.homotopyInvHomId
  homotopyInvHomId := f.homotopyHomInvId

/-- Homotopy equivalence is a transitive relation. -/
@[trans]
def trans {C D E : HomologicalComplex V c} (f : HomotopyEquiv C D) (g : HomotopyEquiv D E) : HomotopyEquiv C E where
  Hom := f.Hom ≫ g.Hom
  inv := g.inv ≫ f.inv
  homotopyHomInvId := by
    simpa using ((g.homotopy_hom_inv_id.comp_right_id f.inv).compLeft f.hom).trans f.homotopy_hom_inv_id
  homotopyInvHomId := by
    simpa using ((f.homotopy_inv_hom_id.comp_right_id g.hom).compLeft g.inv).trans g.homotopy_inv_hom_id

end HomotopyEquiv

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V] [HasZeroObject V]

/-- Homotopic maps induce the same map on homology.
-/
theorem homology_map_eq_of_homotopy (h : Homotopy f g) (i : ι) :
    (homologyFunctor V c i).map f = (homologyFunctor V c i).map g := by
  dsimp' [← homologyFunctor]
  apply eq_of_sub_eq_zero
  ext
  simp only [← homology.π_map, ← comp_zero, ← preadditive.comp_sub]
  dsimp' [← kernel_subobject_map]
  simp_rw [h.comm i]
  simp only [← zero_addₓ, ← zero_comp, ← d_next_eq_d_from_from_next, ← kernel_subobject_arrow_comp_assoc, ←
    preadditive.comp_add]
  rw [← preadditive.sub_comp]
  simp only [← CategoryTheory.Subobject.factor_thru_add_sub_factor_thru_right]
  erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)]
  · simp
    
  · rw [prev_d_eq_to_prev_d_to, ← category.assoc]
    apply image_subobject_factors_comp_self
    

/-- Homotopy equivalent complexes have isomorphic homologies. -/
def homologyObjIsoOfHomotopyEquiv (f : HomotopyEquiv C D) (i : ι) :
    (homologyFunctor V c i).obj C ≅ (homologyFunctor V c i).obj D where
  Hom := (homologyFunctor V c i).map f.Hom
  inv := (homologyFunctor V c i).map f.inv
  hom_inv_id' := by
    rw [← functor.map_comp, homology_map_eq_of_homotopy f.homotopy_hom_inv_id, CategoryTheory.Functor.map_id]
  inv_hom_id' := by
    rw [← functor.map_comp, homology_map_eq_of_homotopy f.homotopy_inv_hom_id, CategoryTheory.Functor.map_id]

end

namespace CategoryTheory

variable {W : Type _} [Category W] [Preadditive W]

/-- An additive functor takes homotopies to homotopies. -/
@[simps]
def Functor.mapHomotopy (F : V ⥤ W) [F.Additive] {f g : C ⟶ D} (h : Homotopy f g) :
    Homotopy ((F.mapHomologicalComplex c).map f) ((F.mapHomologicalComplex c).map g) where
  Hom := fun i j => F.map (h.Hom i j)
  zero' := fun i j w => by
    rw [h.zero i j w, F.map_zero]
  comm := fun i => by
    have := h.comm i
    dsimp' [← dNext, ← prevD]  at *
    rcases c.next i with (_ | ⟨inext, wn⟩) <;>
      rcases c.prev i with (_ | ⟨iprev, wp⟩) <;>
        dsimp' [← dNext, ← prevD]  at * <;>
          · intro h
            simp [← h]
            

/-- An additive functor preserves homotopy equivalences. -/
@[simps]
def Functor.mapHomotopyEquiv (F : V ⥤ W) [F.Additive] (h : HomotopyEquiv C D) :
    HomotopyEquiv ((F.mapHomologicalComplex c).obj C) ((F.mapHomologicalComplex c).obj D) where
  Hom := (F.mapHomologicalComplex c).map h.Hom
  inv := (F.mapHomologicalComplex c).map h.inv
  homotopyHomInvId := by
    rw [← (F.map_homological_complex c).map_comp, ← (F.map_homological_complex c).map_id]
    exact F.map_homotopy h.homotopy_hom_inv_id
  homotopyInvHomId := by
    rw [← (F.map_homological_complex c).map_comp, ← (F.map_homological_complex c).map_id]
    exact F.map_homotopy h.homotopy_inv_hom_id

end CategoryTheory

