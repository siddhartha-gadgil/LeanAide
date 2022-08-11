/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Fintype.Basic

/-!
# Matrices
-/


universe u u' v w z

/-- `dmatrix m n` is the type of dependently typed matrices
whose rows are indexed by the fintype `m` and
whose columns are indexed by the fintype `n`. -/
@[nolint unused_arguments]
def Dmatrix (m : Type u) (n : Type u') [Fintype m] [Fintype n] (α : m → n → Type v) : Type max u u' v :=
  ∀ i j, α i j

variable {l m n o : Type _} [Fintype l] [Fintype m] [Fintype n] [Fintype o]

variable {α : m → n → Type v}

namespace Dmatrix

section Ext

variable {M N : Dmatrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by
    simp [← h]⟩

@[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp

end Ext

/-- `M.map f` is the dmatrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : Dmatrix m n α) {β : m → n → Type w} (f : ∀ ⦃i j⦄, α i j → β i j) : Dmatrix m n β := fun i j => f (M i j)

@[simp]
theorem map_apply {M : Dmatrix m n α} {β : m → n → Type w} {f : ∀ ⦃i j⦄, α i j → β i j} {i : m} {j : n} :
    M.map f i j = f (M i j) :=
  rfl

@[simp]
theorem map_map {M : Dmatrix m n α} {β : m → n → Type w} {γ : m → n → Type z} {f : ∀ ⦃i j⦄, α i j → β i j}
    {g : ∀ ⦃i j⦄, β i j → γ i j} : (M.map f).map g = M.map fun i j x => g (f x) := by
  ext
  simp

/-- The transpose of a dmatrix. -/
def transposeₓ (M : Dmatrix m n α) : Dmatrix n m fun j i => α i j
  | x, y => M y x

-- mathport name: «expr ᵀ»
localized [Dmatrix] postfix:1024 "ᵀ" => Dmatrix.transposeₓ

/-- `dmatrix.col u` is the column matrix whose entries are given by `u`. -/
def colₓ {α : m → Type v} (w : ∀ i, α i) : Dmatrix m Unit fun i j => α i
  | x, y => w x

/-- `dmatrix.row u` is the row matrix whose entries are given by `u`. -/
def rowₓ {α : n → Type v} (v : ∀ j, α j) : Dmatrix Unit n fun i j => α j
  | x, y => v y

instance [∀ i j, Inhabited (α i j)] : Inhabited (Dmatrix m n α) :=
  Pi.inhabited _

instance [∀ i j, Add (α i j)] : Add (Dmatrix m n α) :=
  Pi.hasAdd

instance [∀ i j, AddSemigroupₓ (α i j)] : AddSemigroupₓ (Dmatrix m n α) :=
  Pi.addSemigroup

instance [∀ i j, AddCommSemigroupₓ (α i j)] : AddCommSemigroupₓ (Dmatrix m n α) :=
  Pi.addCommSemigroup

instance [∀ i j, Zero (α i j)] : Zero (Dmatrix m n α) :=
  Pi.hasZero

instance [∀ i j, AddMonoidₓ (α i j)] : AddMonoidₓ (Dmatrix m n α) :=
  Pi.addMonoid

instance [∀ i j, AddCommMonoidₓ (α i j)] : AddCommMonoidₓ (Dmatrix m n α) :=
  Pi.addCommMonoid

instance [∀ i j, Neg (α i j)] : Neg (Dmatrix m n α) :=
  Pi.hasNeg

instance [∀ i j, Sub (α i j)] : Sub (Dmatrix m n α) :=
  Pi.hasSub

instance [∀ i j, AddGroupₓ (α i j)] : AddGroupₓ (Dmatrix m n α) :=
  Pi.addGroup

instance [∀ i j, AddCommGroupₓ (α i j)] : AddCommGroupₓ (Dmatrix m n α) :=
  Pi.addCommGroup

instance [∀ i j, Unique (α i j)] : Unique (Dmatrix m n α) :=
  Pi.unique

instance [∀ i j, Subsingleton (α i j)] : Subsingleton (Dmatrix m n α) :=
  Pi.subsingleton

@[simp]
theorem zero_apply [∀ i j, Zero (α i j)] (i j) : (0 : Dmatrix m n α) i j = 0 :=
  rfl

@[simp]
theorem neg_apply [∀ i j, Neg (α i j)] (M : Dmatrix m n α) (i j) : (-M) i j = -M i j :=
  rfl

@[simp]
theorem add_apply [∀ i j, Add (α i j)] (M N : Dmatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
  rfl

@[simp]
theorem sub_apply [∀ i j, Sub (α i j)] (M N : Dmatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
  rfl

@[simp]
theorem map_zero [∀ i j, Zero (α i j)] {β : m → n → Type w} [∀ i j, Zero (β i j)] {f : ∀ ⦃i j⦄, α i j → β i j}
    (h : ∀ i j, f (0 : α i j) = 0) : (0 : Dmatrix m n α).map f = 0 := by
  ext
  simp [← h]

theorem map_add [∀ i j, AddMonoidₓ (α i j)] {β : m → n → Type w} [∀ i j, AddMonoidₓ (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : Dmatrix m n α) :
    ((M + N).map fun i j => @f i j) = (M.map fun i j => @f i j) + N.map fun i j => @f i j := by
  ext
  simp

theorem map_sub [∀ i j, AddGroupₓ (α i j)] {β : m → n → Type w} [∀ i j, AddGroupₓ (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j)
    (M N : Dmatrix m n α) : ((M - N).map fun i j => @f i j) = (M.map fun i j => @f i j) - N.map fun i j => @f i j := by
  ext
  simp

-- TODO[gh-6025]: make this an instance once safe to do so
theorem subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Dmatrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim i⟩

-- TODO[gh-6025]: make this an instance once safe to do so
theorem subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Dmatrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim j⟩

end Dmatrix

/-- The `add_monoid_hom` between spaces of dependently typed matrices
induced by an `add_monoid_hom` between their coefficients. -/
def AddMonoidHom.mapDmatrix [∀ i j, AddMonoidₓ (α i j)] {β : m → n → Type w} [∀ i j, AddMonoidₓ (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) : Dmatrix m n α →+ Dmatrix m n β where
  toFun := fun M => M.map fun i j => @f i j
  map_zero' := by
    simp
  map_add' := Dmatrix.map_add f

@[simp]
theorem AddMonoidHom.map_dmatrix_apply [∀ i j, AddMonoidₓ (α i j)] {β : m → n → Type w} [∀ i j, AddMonoidₓ (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M : Dmatrix m n α) : AddMonoidHom.mapDmatrix f M = M.map fun i j => @f i j :=
  rfl

