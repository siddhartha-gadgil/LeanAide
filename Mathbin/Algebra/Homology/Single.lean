/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Homology.Homology

/-!
# Chain complexes supported in a single degree

We define `single V j c : V ⥤ homological_complex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

Similarly `single₀ V : V ⥤ chain_complex V ℕ` is the special case for
`ℕ`-indexed chain complexes, with the object supported in degree `0`,
but with better definitional properties.

In `to_single₀_equiv` we characterize chain maps to a `ℕ`-indexed complex concentrated in degree 0;
they are equivalent to `{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type _} [DecidableEq ι] (c : ComplexShape ι)

attribute [local instance] has_zero_object.has_zero

/-- The functor `V ⥤ homological_complex V c` creating a chain complex supported in a single degree.

See also `chain_complex.single₀ : V ⥤ chain_complex V ℕ`,
which has better definitional properties,
if you are working with `ℕ`-indexed complexes.
-/
@[simps]
def single (j : ι) : V ⥤ HomologicalComplex V c where
  obj := fun A => { x := fun i => if i = j then A else 0, d := fun i j => 0 }
  map := fun A B f =>
    { f := fun i =>
        if h : i = j then
          eqToHom
              (by
                dsimp'
                rw [if_pos h]) ≫
            f ≫
              eqToHom
                (by
                  dsimp'
                  rw [if_pos h])
        else 0 }
  map_id' := fun A => by
    ext
    dsimp'
    split_ifs with h
    · subst h
      simp
      
    · rw [if_neg h]
      simp
      
  map_comp' := fun A B C f g => by
    ext
    dsimp'
    split_ifs with h
    · subst h
      simp
      
    · simp
      

/-- The object in degree `j` of `(single V c h).obj A` is just `A`.
-/
@[simps]
def singleObjXSelf (j : ι) (A : V) : ((single V c j).obj A).x j ≅ A :=
  eqToIso
    (by
      simp )

@[simp]
theorem single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
    ((single V c j).map f).f j = (singleObjXSelf V c j A).Hom ≫ f ≫ (singleObjXSelf V c j B).inv := by
  simp
  rfl

instance (j : ι) :
    Faithful (single V c j) where map_injective' := fun X Y f g w => by
    have := congr_hom w j
    dsimp'  at this
    simp only [← dif_pos] at this
    rw [← is_iso.inv_comp_eq, inv_eq_to_hom, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp, ←
      is_iso.comp_inv_eq, category.assoc, inv_eq_to_hom, eq_to_hom_trans, eq_to_hom_refl, category.comp_id] at this
    exact this

instance (j : ι) : Full (single V c j) where
  preimage := fun X Y f =>
    eqToHom
        (by
          simp ) ≫
      f.f j ≫
        eqToHom
          (by
            simp )
  witness' := fun X Y f => by
    ext i
    dsimp'
    split_ifs
    · subst h
      simp
      
    · symm
      apply zero_of_target_iso_zero
      dsimp'
      rw [if_neg h]
      

end HomologicalComplex

open HomologicalComplex

namespace ChainComplex

attribute [local instance] has_zero_object.has_zero

/-- `chain_complex.single₀ V` is the embedding of `V` into `chain_complex V ℕ`
as chain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ ChainComplex V ℕ where
  obj := fun X =>
    { x := fun n =>
        match n with
        | 0 => X
        | n + 1 => 0,
      d := fun i j => 0 }
  map := fun X Y f =>
    { f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id' := fun X => by
    ext n
    cases n
    rfl
    dsimp'
    unfold_aux
    simp
  map_comp' := fun X Y Z f g => by
    ext n
    cases n
    rfl
    dsimp'
    unfold_aux
    simp

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).x 0 = X :=
  rfl

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).x (n + 1) = 0 :=
  rfl

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl

@[simp]
theorem single₀_obj_X_d_to (X : V) (j : ℕ) : ((single₀ V).obj X).dTo j = 0 := by
  rw [d_to_eq ((single₀ V).obj X) rfl]
  simp

@[simp]
theorem single₀_obj_X_d_from (X : V) (i : ℕ) : ((single₀ V).obj X).dFrom i = 0 := by
  cases i
  · rw [d_from_eq_zero]
    simp
    
  · rw [d_from_eq ((single₀ V).obj X) rfl]
    simp
    

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl

section

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/-- Sending objects to chain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ V ⋙ homologyFunctor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _
          (by
            simp )
          (by
            simp ) ≪≫
        homologyZeroZero)
    fun X Y f => by
    ext
    dsimp' [← homologyFunctor]
    simp

/-- Sending objects to chain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homologyFunctorSuccSingle₀ (n : ℕ) : single₀ V ⋙ homologyFunctor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _
          (by
            simp )
          (by
            simp ) ≪≫
        homologyZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun X Y f => (functor.zero_obj _).eq_of_tgt _ _

end

variable {V}

/-- Morphisms from a `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
def toSingle₀Equiv (C : ChainComplex V ℕ) (X : V) : (C ⟶ (single₀ V).obj X) ≃ { f : C.x 0 ⟶ X // C.d 1 0 ≫ f = 0 } where
  toFun := fun f =>
    ⟨f.f 0, by
      rw [← f.comm 1 0]
      simp ⟩
  invFun := fun f =>
    { f := fun i =>
        match i with
        | 0 => f.1
        | n + 1 => 0,
      comm' := fun i j h => by
        rcases i with (_ | _ | i) <;> cases j <;> unfold_aux <;> simp only [← comp_zero, ← zero_comp, ← single₀_obj_X_d]
        · rw [C.shape, zero_comp]
          simp
          
        · exact f.2.symm
          
        · rw [C.shape, zero_comp]
          simp [← i.succ_succ_ne_one.symm]
           }
  left_inv := fun f => by
    ext i
    rcases i with ⟨⟩
    · rfl
      
    · ext
      
  right_inv := by
    tidy

variable (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀IsoSingle : single₀ V ≅ single V _ 0 :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          { f := fun i => by
              cases i <;> simpa using 𝟙 _ },
        inv :=
          { f := fun i => by
              cases i <;> simpa using 𝟙 _ },
        hom_inv_id' := by
          ext (_ | i) <;>
            · dsimp'
              simp
              ,
        inv_hom_id' := by
          ext (_ | i)
          · apply category.id_comp
            
          · apply has_zero_object.to_zero_ext
             })
    fun X Y f => by
    ext (_ | i) <;>
      · dsimp'
        simp
        

instance : Faithful (single₀ V) :=
  Faithful.of_iso (single₀IsoSingle V).symm

instance : Full (single₀ V) :=
  Full.ofIso (single₀IsoSingle V).symm

end ChainComplex

namespace CochainComplex

attribute [local instance] has_zero_object.has_zero

/-- `cochain_complex.single₀ V` is the embedding of `V` into `cochain_complex V ℕ`
as cochain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ CochainComplex V ℕ where
  obj := fun X =>
    { x := fun n =>
        match n with
        | 0 => X
        | n + 1 => 0,
      d := fun i j => 0 }
  map := fun X Y f =>
    { f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id' := fun X => by
    ext n
    cases n
    rfl
    dsimp'
    unfold_aux
    simp
  map_comp' := fun X Y Z f g => by
    ext n
    cases n
    rfl
    dsimp'
    unfold_aux
    simp

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).x 0 = X :=
  rfl

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).x (n + 1) = 0 :=
  rfl

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl

@[simp]
theorem single₀_obj_X_d_from (X : V) (j : ℕ) : ((single₀ V).obj X).dFrom j = 0 := by
  rw [d_from_eq ((single₀ V).obj X) rfl]
  simp

@[simp]
theorem single₀_obj_X_d_to (X : V) (i : ℕ) : ((single₀ V).obj X).dTo i = 0 := by
  cases i
  · rw [d_to_eq_zero]
    simp
    
  · rw [d_to_eq ((single₀ V).obj X) rfl]
    simp
    

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl

section

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/-- Sending objects to cochain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ V ⋙ homologyFunctor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _
          (by
            simp )
          (by
            simp ) ≪≫
        homologyZeroZero)
    fun X Y f => by
    ext
    dsimp' [← homologyFunctor]
    simp

/-- Sending objects to cochain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homologyFunctorSuccSingle₀ (n : ℕ) : single₀ V ⋙ homologyFunctor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _
          (by
            simp )
          (by
            simp ) ≪≫
        homologyZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun X Y f => (functor.zero_obj _).eq_of_tgt _ _

end

variable {V}

/-- Morphisms from a single object cochain complex with `X` concentrated in degree 0
to a `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`.
-/
def fromSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.x 0 // f ≫ C.d 0 1 = 0 } where
  toFun := fun f =>
    ⟨f.f 0, by
      rw [f.comm 0 1]
      simp ⟩
  invFun := fun f =>
    { f := fun i =>
        match i with
        | 0 => f.1
        | n + 1 => 0,
      comm' := fun i j h => by
        rcases j with (_ | _ | j) <;> cases i <;> unfold_aux <;> simp only [← comp_zero, ← zero_comp, ← single₀_obj_X_d]
        · convert comp_zero
          rw [C.shape]
          simp
          
        · exact f.2
          
        · convert comp_zero
          rw [C.shape]
          simp only [← ComplexShape.up_rel, ← zero_addₓ]
          exact (Nat.one_lt_succ_succ j).Ne
           }
  left_inv := fun f => by
    ext i
    rcases i with ⟨⟩
    · rfl
      
    · ext
      
  right_inv := by
    tidy

variable (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀IsoSingle : single₀ V ≅ single V _ 0 :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          { f := fun i => by
              cases i <;> simpa using 𝟙 _ },
        inv :=
          { f := fun i => by
              cases i <;> simpa using 𝟙 _ },
        hom_inv_id' := by
          ext (_ | i) <;>
            · dsimp'
              simp
              ,
        inv_hom_id' := by
          ext (_ | i)
          · apply category.id_comp
            
          · apply has_zero_object.to_zero_ext
             })
    fun X Y f => by
    ext (_ | i) <;>
      · dsimp'
        simp
        

instance : Faithful (single₀ V) :=
  Faithful.of_iso (single₀IsoSingle V).symm

instance : Full (single₀ V) :=
  Full.ofIso (single₀IsoSingle V).symm

end CochainComplex

