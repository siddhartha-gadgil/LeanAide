/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.GroupTheory.FreeGroup
import Mathbin.GroupTheory.Abelianization
import Mathbin.Algebra.Module.Basic

/-!
# Free abelian groups

The free abelian group on a type `α`, defined as the abelianisation of
the free group on `α`.

The free abelian group on `α` can be abstractly defined as the left adjoint of the
forgetful functor from abelian groups to types. Alternatively, one could define
it as the functions `α → ℤ` which send all but finitely many `(a : α)` to `0`,
under pointwise addition. In this file, it is defined as the abelianisation
of the free group on `α`. All the constructions and theorems required to show
the adjointness of the construction and the forgetful functor are proved in this
file, but the category-theoretic adjunction statement is in
`algebra.category.Group.adjunctions` .

## Main definitions

Here we use the following variables: `(α β : Type*) (A : Type*) [add_comm_group A]`

* `free_abelian_group α` : the free abelian group on a type `α`. As an abelian
group it is `α →₀ ℤ`, the functions from `α` to `ℤ` such that all but finitely
many elements get mapped to zero, however this is not how it is implemented.

* `lift f : free_abelian_group α →+ A` : the group homomorphism induced
  by the map `f : α → A`.

* `map (f : α → β) : free_abelian_group α →+ free_abelian_group β` : functoriality
    of `free_abelian_group`

* `instance [monoid α] : semigroup (free_abelian_group α)`

* `instance [comm_monoid α] : comm_ring (free_abelian_group α)`

It has been suggested that we would be better off refactoring this file
and using `finsupp` instead.

## Implementation issues

The definition is `def free_abelian_group : Type u :=
additive $ abelianization $ free_group α`

Chris Hughes has suggested that this all be rewritten in terms of `finsupp`.
Johan Commelin has written all the API relating the definition to `finsupp`
in the lean-liquid repo.

The lemmas `map_pure`, `map_of`, `map_zero`, `map_add`, `map_neg` and `map_sub`
are proved about the `functor.map` `<$>` construction, and need `α` and `β` to
be in the same universe. But
`free_abelian_group.map (f : α → β)` is defined to be the `add_group`
homomorphism `free_abelian_group α →+ free_abelian_group β` (with `α` and `β` now
allowed to be in different universes), so `(map f).map_add`
etc can be used to prove that `free_abelian_group.map` preserves addition. The
functions `map_id`, `map_id_apply`, `map_comp`, `map_comp_apply` and `map_of_apply`
are about `free_abelian_group.map`.

-/


-- we use the ℤ-module structure on an add_comm_group in punit_equiv
-- we use the ℤ-module structure on an add_comm_group in punit_equiv
universe u v

variable (α : Type u)

/-- The free abelian group on a type. -/
def FreeAbelianGroup : Type u :=
  Additive <| Abelianization <| FreeGroup α

instance : AddCommGroupₓ (FreeAbelianGroup α) :=
  @Additive.addCommGroup _ <| Abelianization.commGroup _

instance : Inhabited (FreeAbelianGroup α) :=
  ⟨0⟩

variable {α}

namespace FreeAbelianGroup

/-- The canonical map from α to `free_abelian_group α` -/
def of (x : α) : FreeAbelianGroup α :=
  Abelianization.of <| FreeGroup.of x

/-- The map `free_abelian_group α →+ A` induced by a map of types `α → A`. -/
def lift {β : Type v} [AddCommGroupₓ β] : (α → β) ≃ (FreeAbelianGroup α →+ β) :=
  (@FreeGroup.lift _ (Multiplicative β) _).trans <|
    (@Abelianization.lift _ _ (Multiplicative β) _).trans MonoidHom.toAdditive

namespace lift

variable {β : Type v} [AddCommGroupₓ β] (f : α → β)

open FreeAbelianGroup

@[simp]
protected theorem of (x : α) : lift f (of x) = f x := by
  convert @Abelianization.lift.of (FreeGroup α) _ (Multiplicative β) _ _ _
  convert free_group.lift.of.symm

protected theorem unique (g : FreeAbelianGroup α →+ β) (hg : ∀ x, g (of x) = f x) {x} : g x = lift f x :=
  AddMonoidHom.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ of = f)) _

/-- See note [partially-applied ext lemmas]. -/
@[ext]
protected theorem ext (g h : FreeAbelianGroup α →+ β) (H : ∀ x, g (of x) = h (of x)) : g = h :=
  lift.symm.Injective <| funext H

theorem map_hom {α β γ} [AddCommGroupₓ β] [AddCommGroupₓ γ] (a : FreeAbelianGroup α) (f : α → β) (g : β →+ γ) :
    g (lift f a) = lift (g ∘ f) a := by
  suffices : (g.comp (lift f)) a = lift (g ∘ f) a
  exact this
  apply @lift.unique
  intro a
  show g ((lift f) (of a)) = g (f a)
  simp only [← (· ∘ ·), ← lift.of]

end lift

section

open Classical

theorem of_injective : Function.Injective (of : α → FreeAbelianGroup α) := fun x y hoxy =>
  Classical.by_contradiction fun hxy : x ≠ y =>
    let f : FreeAbelianGroup α →+ ℤ := lift fun z => if x = z then (1 : ℤ) else 0
    have hfx1 : f (of x) = 1 := (lift.of _ _).trans <| if_pos rfl
    have hfy1 : f (of y) = 1 := hoxy ▸ hfx1
    have hfy0 : f (of y) = 0 := (lift.of _ _).trans <| if_neg hxy
    one_ne_zero <| hfy1.symm.trans hfy0

end

attribute [local instance] QuotientGroup.leftRel

@[elab_as_eliminator]
protected theorem induction_on {C : FreeAbelianGroup α → Prop} (z : FreeAbelianGroup α) (C0 : C 0) (C1 : ∀ x, C <| of x)
    (Cn : ∀ x, C (of x) → C (-of x)) (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
  (Quotientₓ.induction_on' z) fun x =>
    (Quot.induction_on x) fun L =>
      (List.recOn L C0) fun ⟨x, b⟩ tl ih => Bool.recOn b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

theorem lift.add' {α β} [AddCommGroupₓ β] (a : FreeAbelianGroup α) (f g : α → β) :
    lift (f + g) a = lift f a + lift g a := by
  refine' FreeAbelianGroup.induction_on a _ _ _ _
  · simp only [← (lift _).map_zero, ← zero_addₓ]
    
  · intro x
    simp only [← lift.of, ← Pi.add_apply]
    
  · intro x h
    simp only [← map_neg, ← lift.of, ← Pi.add_apply, ← neg_add]
    
  · intro x y hx hy
    simp only [← (lift _).map_add, ← hx, ← hy, ← add_add_add_commₓ]
    

/-- If `g : free_abelian_group X` and `A` is an abelian group then `lift_add_group_hom g`
is the additive group homomorphism sending a function `X → A` to the term of type `A`
corresponding to the evaluation of the induced map `free_abelian_group X → A` at `g`. -/
@[simps]
def liftAddGroupHom {α} (β) [AddCommGroupₓ β] (a : FreeAbelianGroup α) : (α → β) →+ β :=
  AddMonoidHom.mk' (fun f => lift f a) (lift.add' a)

theorem lift_neg' {β} [AddCommGroupₓ β] (f : α → β) : lift (-f) = -lift f :=
  AddMonoidHom.ext fun _ => (liftAddGroupHom _ _ : (α → β) →+ β).map_neg _

section Monadₓ

variable {β : Type u}

instance : Monadₓ FreeAbelianGroup.{u} where
  pure := fun α => of
  bind := fun α β x f => lift f x

@[elab_as_eliminator]
protected theorem induction_on' {C : FreeAbelianGroup α → Prop} (z : FreeAbelianGroup α) (C0 : C 0)
    (C1 : ∀ x, C <| pure x) (Cn : ∀ x, C (pure x) → C (-pure x)) (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
  FreeAbelianGroup.induction_on z C0 C1 Cn Cp

@[simp]
theorem map_pure (f : α → β) (x : α) : f <$> (pure x : FreeAbelianGroup α) = pure (f x) :=
  rfl

@[simp]
protected theorem map_zero (f : α → β) : f <$> (0 : FreeAbelianGroup α) = 0 :=
  (lift (of ∘ f)).map_zero

@[simp]
protected theorem map_add (f : α → β) (x y : FreeAbelianGroup α) : f <$> (x + y) = f <$> x + f <$> y :=
  (lift _).map_add _ _

@[simp]
protected theorem map_neg (f : α → β) (x : FreeAbelianGroup α) : f <$> -x = -f <$> x :=
  map_neg (lift <| of ∘ f) _

@[simp]
protected theorem map_sub (f : α → β) (x y : FreeAbelianGroup α) : f <$> (x - y) = f <$> x - f <$> y :=
  map_sub (lift <| of ∘ f) _ _

@[simp]
theorem map_of (f : α → β) (y : α) : f <$> of y = of (f y) :=
  rfl

@[simp]
theorem pure_bind (f : α → FreeAbelianGroup β) (x) : pure x >>= f = f x :=
  lift.of _ _

@[simp]
theorem zero_bind (f : α → FreeAbelianGroup β) : 0 >>= f = 0 :=
  (lift f).map_zero

@[simp]
theorem add_bind (f : α → FreeAbelianGroup β) (x y : FreeAbelianGroup α) : x + y >>= f = (x >>= f) + (y >>= f) :=
  (lift _).map_add _ _

@[simp]
theorem neg_bind (f : α → FreeAbelianGroup β) (x : FreeAbelianGroup α) : -x >>= f = -(x >>= f) :=
  map_neg (lift f) _

@[simp]
theorem sub_bind (f : α → FreeAbelianGroup β) (x y : FreeAbelianGroup α) : x - y >>= f = (x >>= f) - (y >>= f) :=
  map_sub (lift f) _ _

@[simp]
theorem pure_seq (f : α → β) (x : FreeAbelianGroup α) : pure f <*> x = f <$> x :=
  pure_bind _ _

@[simp]
theorem zero_seq (x : FreeAbelianGroup α) : (0 : FreeAbelianGroup (α → β)) <*> x = 0 :=
  zero_bind _

@[simp]
theorem add_seq (f g : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : f + g <*> x = (f <*> x) + (g <*> x) :=
  add_bind _ _ _

@[simp]
theorem neg_seq (f : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : -f <*> x = -(f <*> x) :=
  neg_bind _ _

@[simp]
theorem sub_seq (f g : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : f - g <*> x = (f <*> x) - (g <*> x) :=
  sub_bind _ _ _

/-- If `f : free_abelian_group (α → β)`, then `f <*>` is an additive morphism
`free_abelian_group α →+ free_abelian_group β`. -/
def seqAddGroupHom (f : FreeAbelianGroup (α → β)) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  AddMonoidHom.mk' ((· <*> ·) f) fun x y =>
    show lift (· <$> (x + y)) _ = _ by
      simp only [← FreeAbelianGroup.map_add]
      exact lift.add' f _ _

@[simp]
theorem seq_zero (f : FreeAbelianGroup (α → β)) : f <*> 0 = 0 :=
  (seqAddGroupHom f).map_zero

@[simp]
theorem seq_add (f : FreeAbelianGroup (α → β)) (x y : FreeAbelianGroup α) : f <*> x + y = (f <*> x) + (f <*> y) :=
  (seqAddGroupHom f).map_add x y

@[simp]
theorem seq_neg (f : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : f <*> -x = -(f <*> x) :=
  (seqAddGroupHom f).map_neg x

@[simp]
theorem seq_sub (f : FreeAbelianGroup (α → β)) (x y : FreeAbelianGroup α) : f <*> x - y = (f <*> x) - (f <*> y) :=
  (seqAddGroupHom f).map_sub x y

instance : IsLawfulMonad FreeAbelianGroup.{u} where
  id_map := fun α x =>
    FreeAbelianGroup.induction_on' x (FreeAbelianGroup.map_zero id) (map_pure id)
      (fun x ih => by
        rw [FreeAbelianGroup.map_neg, ih])
      fun x y ihx ihy => by
      rw [FreeAbelianGroup.map_add, ihx, ihy]
  pure_bind := fun α β x f => pure_bind f x
  bind_assoc := fun α β γ x f g =>
    FreeAbelianGroup.induction_on' x
      (by
        iterate 3 
          rw [zero_bind])
      (fun x => by
        iterate 2 
          rw [pure_bind])
      (fun x ih => by
        iterate 3 
            rw [neg_bind] <;>
          rw [ih])
      fun x y ihx ihy => by
      iterate 3 
          rw [add_bind] <;>
        rw [ihx, ihy]

instance :
    IsCommApplicative FreeAbelianGroup.{u} where commutative_prod := fun α β x y =>
    FreeAbelianGroup.induction_on' x
      (by
        rw [FreeAbelianGroup.map_zero, zero_seq, seq_zero])
      (fun p => by
        rw [map_pure, pure_seq] <;>
          exact
            FreeAbelianGroup.induction_on' y
              (by
                rw [FreeAbelianGroup.map_zero, FreeAbelianGroup.map_zero, zero_seq])
              (fun q => by
                rw [map_pure, map_pure, pure_seq, map_pure])
              (fun q ih => by
                rw [FreeAbelianGroup.map_neg, FreeAbelianGroup.map_neg, neg_seq, ih])
              fun y₁ y₂ ih1 ih2 => by
              rw [FreeAbelianGroup.map_add, FreeAbelianGroup.map_add, add_seq, ih1, ih2])
      (fun p ih => by
        rw [FreeAbelianGroup.map_neg, neg_seq, seq_neg, ih])
      fun x₁ x₂ ih1 ih2 => by
      rw [FreeAbelianGroup.map_add, add_seq, seq_add, ih1, ih2]

end Monadₓ

universe w

variable {β : Type v} {γ : Type w}

/-- The additive group homomorphism `free_abelian_group α →+ free_abelian_group β` induced from a
  map `α → β` -/
def map (f : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  lift (of ∘ f)

theorem lift_comp {α} {β} {γ} [AddCommGroupₓ γ] (f : α → β) (g : β → γ) (x : FreeAbelianGroup α) :
    lift (g ∘ f) x = lift g (map f x) := by
  apply FreeAbelianGroup.induction_on x
  · exact AddMonoidHom.map_zero _
    
  · intro y
    rfl
    
  · intro x h
    simp only [← h, ← AddMonoidHom.map_neg]
    
  · intro x y h₁ h₂
    simp only [← h₁, ← h₂, ← AddMonoidHom.map_add]
    

theorem map_id : map id = AddMonoidHom.id (FreeAbelianGroup α) :=
  Eq.symm <| (lift.ext _ _) fun x => (lift.unique of (AddMonoidHom.id _)) fun y => AddMonoidHom.id_apply _ _

theorem map_id_apply (x : FreeAbelianGroup α) : map id x = x := by
  rw [map_id]
  rfl

theorem map_comp {f : α → β} {g : β → γ} : map (g ∘ f) = (map g).comp (map f) :=
  Eq.symm <| (lift.ext _ _) fun x => Eq.symm <| lift_comp _ _ _

theorem map_comp_apply {f : α → β} {g : β → γ} (x : FreeAbelianGroup α) : map (g ∘ f) x = (map g) ((map f) x) := by
  rw [map_comp]
  rfl

-- version of map_of which uses `map`
@[simp]
theorem map_of_apply {f : α → β} (a : α) : map f (of a) = of (f a) :=
  rfl

variable (α)

section Mul

variable [Mul α]

instance : Mul (FreeAbelianGroup α) :=
  ⟨fun x => lift fun x₂ => lift (fun x₁ => of <| x₁ * x₂) x⟩

variable {α}

theorem mul_def (x y : FreeAbelianGroup α) : x * y = lift (fun x₂ => lift (fun x₁ => of (x₁ * x₂)) x) y :=
  rfl

@[simp]
theorem of_mul_of (x y : α) : of x * of y = of (x * y) :=
  rfl

theorem of_mul (x y : α) : of (x * y) = of x * of y :=
  rfl

instance : Distribₓ (FreeAbelianGroup α) :=
  { FreeAbelianGroup.hasMul _ with add := (· + ·), left_distrib := fun x y z => (lift _).map_add _ _,
    right_distrib := fun x y z => by
      simp only [← (· * ·), ← map_add, Pi.add_def, ← lift.add'] }

instance : NonUnitalNonAssocRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.distrib, FreeAbelianGroup.addCommGroup _ with
    zero_mul := fun a => by
      have h : 0 * a + 0 * a = 0 * a := by
        simp [add_mulₓ]
      simpa using h,
    mul_zero := fun a => rfl }

end Mul

instance [One α] : One (FreeAbelianGroup α) :=
  ⟨of 1⟩

instance [Semigroupₓ α] : NonUnitalRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.nonUnitalNonAssocRing with mul := (· * ·),
    mul_assoc := fun x y z => by
      refine'
        FreeAbelianGroup.induction_on z
          (by
            simp )
          (fun L3 => _) (fun L3 ih => _) fun z₁ z₂ ih₁ ih₂ => _
      · refine'
          FreeAbelianGroup.induction_on y
            (by
              simp )
            (fun L2 => _) (fun L2 ih => _) fun y₁ y₂ ih₁ ih₂ => _
        · refine'
            FreeAbelianGroup.induction_on x
              (by
                simp )
              (fun L1 => _) (fun L1 ih => _) fun x₁ x₂ ih₁ ih₂ => _
          · rw [of_mul_of, of_mul_of, of_mul_of, of_mul_of, mul_assoc]
            
          · rw [neg_mul, neg_mul, neg_mul, ih]
            
          · rw [add_mulₓ, add_mulₓ, add_mulₓ, ih₁, ih₂]
            
          
        · rw [neg_mul, mul_neg, mul_neg, neg_mul, ih]
          
        · rw [add_mulₓ, mul_addₓ, mul_addₓ, add_mulₓ, ih₁, ih₂]
          
        
      · rw [mul_neg, mul_neg, mul_neg, ih]
        
      · rw [mul_addₓ, mul_addₓ, mul_addₓ, ih₁, ih₂]
         }

section Monoidₓ

variable {R : Type _} [Monoidₓ α] [Ringₓ R]

instance : Ringₓ (FreeAbelianGroup α) :=
  { FreeAbelianGroup.nonUnitalRing _, FreeAbelianGroup.hasOne _ with mul := (· * ·),
    mul_one := fun x => by
      unfold Mul.mul Semigroupₓ.mul One.one
      rw [lift.of]
      refine' FreeAbelianGroup.induction_on x rfl (fun L => _) (fun L ih => _) fun x1 x2 ih1 ih2 => _
      · erw [lift.of]
        congr 1
        exact mul_oneₓ L
        
      · rw [map_neg, ih]
        
      · rw [map_add, ih1, ih2]
        ,
    one_mul := fun x => by
      unfold Mul.mul Semigroupₓ.mul One.one
      refine' FreeAbelianGroup.induction_on x rfl _ _ _
      · intro L
        rw [lift.of, lift.of]
        congr 1
        exact one_mulₓ L
        
      · intro L ih
        rw [map_neg, ih]
        
      · intro x1 x2 ih1 ih2
        rw [map_add, ih1, ih2]
         }

variable {α}

/-- `free_abelian_group.of` is a `monoid_hom` when `α` is a `monoid`. -/
def ofMulHom : α →* FreeAbelianGroup α where
  toFun := of
  map_one' := rfl
  map_mul' := of_mul

@[simp]
theorem of_mul_hom_coe : (ofMulHom : α → FreeAbelianGroup α) = of :=
  rfl

/-- If `f` preserves multiplication, then so does `lift f`. -/
def liftMonoid : (α →* R) ≃ (FreeAbelianGroup α →+* R) where
  toFun := fun f =>
    { lift f with toFun := lift f, map_one' := (lift.of f _).trans f.map_one,
      map_mul' := fun x y => by
        refine' FreeAbelianGroup.induction_on y (mul_zero _).symm (fun L2 => _) (fun L2 ih => _) _
        · refine' FreeAbelianGroup.induction_on x (zero_mul _).symm (fun L1 => _) (fun L1 ih => _) _
          · simp_rw [of_mul_of, lift.of]
            exact f.map_mul _ _
            
          · simp_rw [neg_mul, map_neg, neg_mul]
            exact congr_arg Neg.neg ih
            
          · intro x1 x2 ih1 ih2
            simp only [← add_mulₓ, ← map_add, ← ih1, ← ih2]
            
          
        · rw [mul_neg, map_neg, map_neg, mul_neg, ih]
          
        · intro y1 y2 ih1 ih2
          rw [mul_addₓ, map_add, map_add, mul_addₓ, ih1, ih2]
           }
  invFun := fun F => MonoidHom.comp (↑F) ofMulHom
  left_inv := fun f => MonoidHom.ext <| lift.of _
  right_inv := fun F => RingHom.coe_add_monoid_hom_injective <| lift.apply_symm_apply (↑F : FreeAbelianGroup α →+ R)

@[simp]
theorem lift_monoid_coe_add_monoid_hom (f : α →* R) : ↑(liftMonoid f) = lift f :=
  rfl

@[simp]
theorem lift_monoid_coe (f : α →* R) : ⇑(liftMonoid f) = lift f :=
  rfl

@[simp]
theorem lift_monoid_symm_coe (f : FreeAbelianGroup α →+* R) : ⇑(liftMonoid.symm f) = lift.symm ↑f :=
  rfl

theorem one_def : (1 : FreeAbelianGroup α) = of 1 :=
  rfl

theorem of_one : (of 1 : FreeAbelianGroup α) = 1 :=
  rfl

end Monoidₓ

instance [CommMonoidₓ α] : CommRingₓ (FreeAbelianGroup α) :=
  { FreeAbelianGroup.ring α with
    mul_comm := fun x y => by
      refine' FreeAbelianGroup.induction_on x (zero_mul y) _ _ _
      · intro s
        refine' FreeAbelianGroup.induction_on y (zero_mul _).symm _ _ _
        · intro t
          unfold Mul.mul Semigroupₓ.mul Ringₓ.mul
          iterate 4 
            rw [lift.of]
          congr 1
          exact mul_comm _ _
          
        · intro t ih
          rw [mul_neg, ih, neg_mul_eq_neg_mulₓ]
          
        · intro y1 y2 ih1 ih2
          rw [mul_addₓ, add_mulₓ, ih1, ih2]
          
        
      · intro s ih
        rw [neg_mul, ih, neg_mul_eq_mul_neg]
        
      · intro x1 x2 ih1 ih2
        rw [add_mulₓ, mul_addₓ, ih1, ih2]
         }

instance pemptyUnique : Unique (FreeAbelianGroup Pempty) where
  default := 0
  uniq := fun x =>
    FreeAbelianGroup.induction_on x rfl (fun x => Pempty.elimₓ x) (fun x => Pempty.elimₓ x)
      (by
        rintro - - rfl rfl
        simp )

/-- The free abelian group on a type with one term is isomorphic to `ℤ`. -/
def punitEquiv (T : Type _) [Unique T] : FreeAbelianGroup T ≃+ ℤ where
  toFun := FreeAbelianGroup.lift fun _ => (1 : ℤ)
  invFun := fun n => n • of Inhabited.default
  left_inv := fun z =>
    FreeAbelianGroup.induction_on z
      (by
        simp only [← zero_smul, ← AddMonoidHom.map_zero])
      (Unique.forall_iff.2 <| by
        simp only [← one_smul, ← lift.of])
      (Unique.forall_iff.2 <| by
        simp )
      fun x y hx hy => by
      simp only [← AddMonoidHom.map_add, ← add_smul] at *
      rw [hx, hy]
  right_inv := fun n => by
    rw [AddMonoidHom.map_zsmul, lift.of]
    exact zsmul_int_one n
  map_add' := AddMonoidHom.map_add _

/-- Isomorphic types have isomorphic free abelian groups. -/
def equivOfEquiv {α β : Type _} (f : α ≃ β) : FreeAbelianGroup α ≃+ FreeAbelianGroup β where
  toFun := map f
  invFun := map f.symm
  left_inv := by
    intro x
    rw [← map_comp_apply, Equivₓ.symm_comp_self, map_id]
    rfl
  right_inv := by
    intro x
    rw [← map_comp_apply, Equivₓ.self_comp_symm, map_id]
    rfl
  map_add' := AddMonoidHom.map_add _

end FreeAbelianGroup

