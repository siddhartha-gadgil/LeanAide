/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathbin.Algebra.Category.Ring.Colimits
import Mathbin.Algebra.Category.Ring.Limits
import Mathbin.Topology.Sheaves.LocalPredicate
import Mathbin.RingTheory.Localization.AtPrime
import Mathbin.RingTheory.Subring.Basic

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a ratio of
elements of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `topology.sheaves.sheaf_of_functions`,
where we show that dependent functions into any type family form a sheaf,
and also `topology.sheaves.local_predicate`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

We also set up the ring structure, obtaining
`structure_sheaf R : sheaf CommRing (Top.of (prime_spectrum R))`.

We then construct two basic isomorphisms, relating the structure sheaf to the underlying ring `R`.
First, `structure_sheaf.stalk_iso` gives an isomorphism between the stalk of the structure sheaf
at a point `p` and the localization of `R` at the prime ideal `p`. Second,
`structure_sheaf.basic_open_iso` gives an isomorphism between the structure sheaf on `basic_open f`
and the localization of `R` at the submonoid of powers of `f`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


universe u

noncomputable section

variable (R : Type u) [CommRingₓ R]

open Top

open TopologicalSpace

open CategoryTheory

open Opposite

namespace AlgebraicGeometry

/-- The prime spectrum, just as a topological space.
-/
def PrimeSpectrum.top : Top :=
  Top.of (PrimeSpectrum R)

namespace StructureSheaf

/-- The type family over `prime_spectrum R` consisting of the localization over each point.
-/
def Localizations (P : PrimeSpectrum.top R) : Type u :=
  Localization.AtPrime P.asIdeal deriving CommRingₓ, LocalRing

instance (P : PrimeSpectrum.top R) : Inhabited (Localizations R P) :=
  ⟨1⟩

instance (U : Opens (PrimeSpectrum.top R)) (x : U) : Algebra R (Localizations R x) :=
  Localization.algebra

instance (U : Opens (PrimeSpectrum.top R)) (x : U) :
    IsLocalization.AtPrime (Localizations R x) (x : PrimeSpectrum.top R).asIdeal :=
  Localization.is_localization

variable {R}

/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def IsFraction {U : Opens (PrimeSpectrum.top R)} (f : ∀ x : U, Localizations R x) : Prop :=
  ∃ r s : R, ∀ x : U, ¬s ∈ x.1.asIdeal ∧ f x * algebraMap _ _ s = algebraMap _ _ r

theorem IsFraction.eq_mk' {U : Opens (PrimeSpectrum.top R)} {f : ∀ x : U, Localizations R x} (hf : IsFraction f) :
    ∃ r s : R,
      ∀ x : U,
        ∃ hs : s ∉ x.1.asIdeal,
          f x =
            IsLocalization.mk' (Localization.AtPrime _) r (⟨s, hs⟩ : (x : PrimeSpectrum.top R).asIdeal.primeCompl) :=
  by
  rcases hf with ⟨r, s, h⟩
  refine' ⟨r, s, fun x => ⟨(h x).1, (is_localization.mk'_eq_iff_eq_mul.mpr _).symm⟩⟩
  exact (h x).2.symm

variable (R)

/-- The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def isFractionPrelocal : PrelocalPredicate (Localizations R) where
  pred := fun U f => IsFraction f
  res := by
    rintro V U i f ⟨r, s, w⟩
    exact ⟨r, s, fun x => w (i x)⟩

/-- We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of $𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, localizations x`.
-/
def isLocallyFraction : LocalPredicate (Localizations R) :=
  (isFractionPrelocal R).sheafify

@[simp]
theorem is_locally_fraction_pred {U : Opens (PrimeSpectrum.top R)} (f : ∀ x : U, Localizations R x) :
    (isLocallyFraction R).pred f =
      ∀ x : U,
        ∃ (V : _)(m : x.1 ∈ V)(i : V ⟶ U),
          ∃ r s : R, ∀ y : V, ¬s ∈ y.1.asIdeal ∧ f (i y : U) * algebraMap _ _ s = algebraMap _ _ r :=
  rfl

/-- The functions satisfying `is_locally_fraction` form a subring.
-/
def sectionsSubring (U : (Opens (PrimeSpectrum.top R))ᵒᵖ) : Subring (∀ x : unop U, Localizations R x) where
  Carrier := { f | (isLocallyFraction R).pred f }
  zero_mem' := by
    refine' fun x => ⟨unop U, x.2, 𝟙 _, 0, 1, fun y => ⟨_, _⟩⟩
    · rw [← Ideal.ne_top_iff_one]
      exact y.1.IsPrime.1
      
    · simp
      
  one_mem' := by
    refine' fun x => ⟨unop U, x.2, 𝟙 _, 1, 1, fun y => ⟨_, _⟩⟩
    · rw [← Ideal.ne_top_iff_one]
      exact y.1.IsPrime.1
      
    · simp
      
  add_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine' ⟨Va⊓Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * sb + rb * sa, sa * sb, _⟩
    intro y
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H
      cases y.1.IsPrime.mem_or_mem H <;> contradiction
      
    · simp only [← add_mulₓ, ← RingHom.map_add, ← Pi.add_apply, ← RingHom.map_mul]
      erw [← wa, ← wb]
      simp only [← mul_assoc]
      congr 2
      rw [mul_comm]
      rfl
      
  neg_mem' := by
    intro a ha x
    rcases ha x with ⟨V, m, i, r, s, w⟩
    refine' ⟨V, m, i, -r, s, _⟩
    intro y
    rcases w y with ⟨nm, w⟩
    fconstructor
    · exact nm
      
    · simp only [← RingHom.map_neg, ← Pi.neg_apply]
      erw [← w]
      simp only [← neg_mul]
      
  mul_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine' ⟨Va⊓Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * rb, sa * sb, _⟩
    intro y
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H
      cases y.1.IsPrime.mem_or_mem H <;> contradiction
      
    · simp only [← Pi.mul_apply, ← RingHom.map_mul]
      erw [← wa, ← wb]
      simp only [← mul_left_commₓ, ← mul_assoc, ← mul_comm]
      rfl
      

end StructureSheaf

open StructureSheaf

/-- The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def structureSheafInType : Sheaf (Type u) (PrimeSpectrum.top R) :=
  subsheafToTypes (isLocallyFraction R)

instance commRingStructureSheafInTypeObj (U : (Opens (PrimeSpectrum.top R))ᵒᵖ) :
    CommRingₓ ((structureSheafInType R).1.obj U) :=
  (sectionsSubring R U).toCommRing

open _Root_.PrimeSpectrum

/-- The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structurePresheafInCommRing : Presheaf CommRingₓₓ (PrimeSpectrum.top R) where
  obj := fun U => CommRingₓₓ.of ((structureSheafInType R).1.obj U)
  map := fun U V i =>
    { toFun := (structureSheafInType R).1.map i, map_zero' := rfl, map_add' := fun x y => rfl, map_one' := rfl,
      map_mul' := fun x y => rfl }

/-- Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structurePresheafCompForget : structurePresheafInCommRing R ⋙ forget CommRingₓₓ ≅ (structureSheafInType R).1 :=
  NatIso.ofComponents (fun U => Iso.refl _)
    (by
      tidy)

open Top.Presheaf

/-- The structure sheaf on $Spec R$, valued in `CommRing`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def Spec.structureSheaf : Sheaf CommRingₓₓ (PrimeSpectrum.top R) :=
  ⟨structurePresheafInCommRing R,
    (-- We check the sheaf condition under `forget CommRing`.
          is_sheaf_iff_is_sheaf_comp
          _ _).mpr
      (is_sheaf_of_iso (structurePresheafCompForget R).symm (structureSheafInType R).property)⟩

open Spec (structureSheaf)

namespace StructureSheaf

@[simp]
theorem res_apply (U V : Opens (PrimeSpectrum.top R)) (i : V ⟶ U) (s : (structureSheaf R).1.obj (op U)) (x : V) :
    ((structureSheaf R).1.map i.op s).1 x = (s.1 (i x) : _) :=
  rfl

/-- The section of `structure_sheaf R` on an open `U` sending each `x ∈ U` to the element
`f/g` in the localization of `R` at `x`. -/
/-

Notation in this comment

X = Spec R
OX = structure sheaf

In the following we construct an isomorphism between OX_p and R_p given any point p corresponding
to a prime ideal in R.

We do this via 8 steps:

1. def const (f g : R) (V) (hv : V ≤ D_g) : OX(V) [for api]
2. def to_open (U) : R ⟶ OX(U)
3. [2] def to_stalk (p : Spec R) : R ⟶ OX_p
4. [2] def to_basic_open (f : R) : R_f ⟶ OX(D_f)
5. [3] def localization_to_stalk (p : Spec R) : R_p ⟶ OX_p
6. def open_to_localization (U) (p) (hp : p ∈ U) : OX(U) ⟶ R_p
7. [6] def stalk_to_fiber_ring_hom (p : Spec R) : OX_p ⟶ R_p
8. [5,7] def stalk_iso (p : Spec R) : OX_p ≅ R_p

In the square brackets we list the dependencies of a construction on the previous steps.

-/
def const (f g : R) (U : Opens (PrimeSpectrum.top R))
    (hu : ∀, ∀ x ∈ U, ∀, g ∈ (x : PrimeSpectrum.top R).asIdeal.primeCompl) : (structureSheaf R).1.obj (op U) :=
  ⟨fun x => IsLocalization.mk' _ f ⟨g, hu x x.2⟩, fun x =>
    ⟨U, x.2, 𝟙 _, f, g, fun y => ⟨hu y y.2, IsLocalization.mk'_spec _ _ _⟩⟩⟩

@[simp]
theorem const_apply (f g : R) (U : Opens (PrimeSpectrum.top R))
    (hu : ∀, ∀ x ∈ U, ∀, g ∈ (x : PrimeSpectrum.top R).asIdeal.primeCompl) (x : U) :
    (const R f g U hu).1 x = IsLocalization.mk' _ f ⟨g, hu x x.2⟩ :=
  rfl

theorem const_apply' (f g : R) (U : Opens (PrimeSpectrum.top R))
    (hu : ∀, ∀ x ∈ U, ∀, g ∈ (x : PrimeSpectrum.top R).asIdeal.primeCompl) (x : U)
    (hx : g ∈ (asIdeal (x : PrimeSpectrum.top R)).primeCompl) :
    (const R f g U hu).1 x = IsLocalization.mk' _ f ⟨g, hx⟩ :=
  rfl

theorem exists_const (U) (s : (structureSheaf R).1.obj (op U)) (x : PrimeSpectrum.top R) (hx : x ∈ U) :
    ∃ (V : Opens (PrimeSpectrum.top R))(hxV : x ∈ V)(i : V ⟶ U)(f g : R)(hg : _),
      const R f g V hg = (structureSheaf R).1.map i.op s :=
  let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  ⟨V, hxV, iVU, f, g, fun y hyV => (hfg ⟨y, hyV⟩).1,
    Subtype.eq <| funext fun y => IsLocalization.mk'_eq_iff_eq_mul.2 <| Eq.symm <| (hfg y).2⟩

@[simp]
theorem res_const (f g : R) (U hu V hv i) : (structureSheaf R).1.map i (const R f g U hu) = const R f g V hv :=
  rfl

theorem res_const' (f g : R) (V hv) :
    (structureSheaf R).1.map (homOfLe hv).op (const R f g (basicOpen g) fun _ => id) = const R f g V hv :=
  rfl

theorem const_zero (f : R) (U hu) : const R 0 f U hu = 0 :=
  Subtype.eq <|
    funext fun x =>
      IsLocalization.mk'_eq_iff_eq_mul.2 <| by
        erw [RingHom.map_zero, Subtype.val_eq_coe, Subring.coe_zero, Pi.zero_apply, zero_mul]

theorem const_self (f : R) (U hu) : const R f f U hu = 1 :=
  Subtype.eq <| funext fun x => IsLocalization.mk'_self _ _

theorem const_one (U) : (const R 1 1 U fun p _ => Submonoid.one_mem _) = 1 :=
  const_self R 1 U _

theorem const_add (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
    const R f₁ g₁ U hu₁ + const R f₂ g₂ U hu₂ =
      const R (f₁ * g₂ + f₂ * g₁) (g₁ * g₂) U fun x hx => Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq <|
    funext fun x =>
      Eq.symm <| by
        convert IsLocalization.mk'_add f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

theorem const_mul (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
    const R f₁ g₁ U hu₁ * const R f₂ g₂ U hu₂ =
      const R (f₁ * f₂) (g₁ * g₂) U fun x hx => Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq <|
    funext fun x =>
      Eq.symm <| by
        convert IsLocalization.mk'_mul _ f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

theorem const_ext {f₁ f₂ g₁ g₂ : R} {U hu₁ hu₂} (h : f₁ * g₂ = f₂ * g₁) : const R f₁ g₁ U hu₁ = const R f₂ g₂ U hu₂ :=
  Subtype.eq <| funext fun x => IsLocalization.mk'_eq_of_eq h.symm

theorem const_congr {f₁ f₂ g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    const R f₁ g₁ U hu = const R f₂ g₂ U (hg ▸ hu) := by
  substs hf hg

theorem const_mul_rev (f g : R) (U hu₁ hu₂) : const R f g U hu₁ * const R g f U hu₂ = 1 := by
  rw [const_mul, const_congr R rfl (mul_comm g f), const_self]

theorem const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) : const R f g₁ U hu₁ * const R g₁ g₂ U hu₂ = const R f g₂ U hu₂ := by
  rw [const_mul, const_ext]
  rw [mul_assoc]

theorem const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) : const R g₁ g₂ U hu₂ * const R f g₁ U hu₁ = const R f g₂ U hu₂ :=
  by
  rw [mul_comm, const_mul_cancel]

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
def toOpen (U : Opens (PrimeSpectrum.top R)) : CommRingₓₓ.of R ⟶ (structureSheaf R).1.obj (op U) where
  toFun := fun f =>
    ⟨fun x => algebraMap R _ f, fun x =>
      ⟨U, x.2, 𝟙 _, f, 1, fun y =>
        ⟨(Ideal.ne_top_iff_one _).1 y.1.2.1, by
          rw [RingHom.map_one, mul_oneₓ]
          rfl⟩⟩⟩
  map_one' := Subtype.eq <| funext fun x => RingHom.map_one _
  map_mul' := fun f g => Subtype.eq <| funext fun x => RingHom.map_mul _ _ _
  map_zero' := Subtype.eq <| funext fun x => RingHom.map_zero _
  map_add' := fun f g => Subtype.eq <| funext fun x => RingHom.map_add _ _ _

@[simp]
theorem to_open_res (U V : Opens (PrimeSpectrum.top R)) (i : V ⟶ U) :
    toOpen R U ≫ (structureSheaf R).1.map i.op = toOpen R V :=
  rfl

@[simp]
theorem to_open_apply (U : Opens (PrimeSpectrum.top R)) (f : R) (x : U) : (toOpen R U f).1 x = algebraMap _ _ f :=
  rfl

theorem to_open_eq_const (U : Opens (PrimeSpectrum.top R)) (f : R) :
    toOpen R U f = const R f 1 U fun x _ => (Ideal.ne_top_iff_one _).1 x.2.1 :=
  Subtype.eq <| funext fun x => Eq.symm <| IsLocalization.mk'_one _ f

/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structure_sheaf R` at `x`. -/
def toStalk (x : PrimeSpectrum.top R) : CommRingₓₓ.of R ⟶ (structureSheaf R).1.stalk x :=
  (toOpen R ⊤ ≫ (structureSheaf R).1.germ ⟨x, ⟨⟩⟩ : _)

@[simp]
theorem to_open_germ (U : Opens (PrimeSpectrum.top R)) (x : U) :
    toOpen R U ≫ (structureSheaf R).1.germ x = toStalk R x := by
  rw [← to_open_res R ⊤ U (hom_of_le le_top : U ⟶ ⊤), category.assoc, presheaf.germ_res]
  rfl

@[simp]
theorem germ_to_open (U : Opens (PrimeSpectrum.top R)) (x : U) (f : R) :
    (structureSheaf R).1.germ x (toOpen R U f) = toStalk R x f := by
  rw [← to_open_germ]
  rfl

theorem germ_to_top (x : PrimeSpectrum.top R) (f : R) :
    (structureSheaf R).1.germ (⟨x, trivialₓ⟩ : (⊤ : Opens (PrimeSpectrum.top R))) (toOpen R ⊤ f) = toStalk R x f :=
  rfl

theorem is_unit_to_basic_open_self (f : R) : IsUnit (toOpen R (basicOpen f) f) :=
  is_unit_of_mul_eq_one _ (const R 1 f (basicOpen f) fun _ => id) <| by
    rw [to_open_eq_const, const_mul_rev]

theorem is_unit_to_stalk (x : PrimeSpectrum.top R) (f : x.asIdeal.primeCompl) : IsUnit (toStalk R x (f : R)) := by
  erw [← germ_to_open R (basic_open (f : R)) ⟨x, f.2⟩ (f : R)]
  exact RingHom.is_unit_map _ (is_unit_to_basic_open_self R f)

/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
def localizationToStalk (x : PrimeSpectrum.top R) :
    CommRingₓₓ.of (Localization.AtPrime x.asIdeal) ⟶ (structureSheaf R).1.stalk x :=
  show Localization.AtPrime x.asIdeal →+* _ from IsLocalization.lift (is_unit_to_stalk R x)

@[simp]
theorem localization_to_stalk_of (x : PrimeSpectrum.top R) (f : R) :
    localizationToStalk R x (algebraMap _ (Localization _) f) = toStalk R x f :=
  IsLocalization.lift_eq _ f

@[simp]
theorem localization_to_stalk_mk' (x : PrimeSpectrum.top R) (f : R) (s : (asIdeal x).primeCompl) :
    localizationToStalk R x (IsLocalization.mk' _ f s : Localization _) =
      (structureSheaf R).1.germ (⟨x, s.2⟩ : basicOpen (s : R)) (const R f s (basicOpen s) fun _ => id) :=
  (IsLocalization.lift_mk'_spec _ _ _ _).2 <| by
    erw [← germ_to_open R (basic_open s) ⟨x, s.2⟩, ← germ_to_open R (basic_open s) ⟨x, s.2⟩, ← RingHom.map_mul,
      to_open_eq_const, to_open_eq_const, const_mul_cancel']

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def openToLocalization (U : Opens (PrimeSpectrum.top R)) (x : PrimeSpectrum.top R) (hx : x ∈ U) :
    (structureSheaf R).1.obj (op U) ⟶ CommRingₓₓ.of (Localization.AtPrime x.asIdeal) where
  toFun := fun s => (s.1 ⟨x, hx⟩ : _)
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp]
theorem coe_open_to_localization (U : Opens (PrimeSpectrum.top R)) (x : PrimeSpectrum.top R) (hx : x ∈ U) :
    (openToLocalization R U x hx : (structureSheaf R).1.obj (op U) → Localization.AtPrime x.asIdeal) = fun s =>
      (s.1 ⟨x, hx⟩ : _) :=
  rfl

theorem open_to_localization_apply (U : Opens (PrimeSpectrum.top R)) (x : PrimeSpectrum.top R) (hx : x ∈ U)
    (s : (structureSheaf R).1.obj (op U)) : openToLocalization R U x hx s = (s.1 ⟨x, hx⟩ : _) :=
  rfl

/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `open_to_localization` maps. -/
def stalkToFiberRingHom (x : PrimeSpectrum.top R) :
    (structureSheaf R).1.stalk x ⟶ CommRingₓₓ.of (Localization.AtPrime x.asIdeal) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (structureSheaf R).1)
    { x := _, ι := { app := fun U => openToLocalization R ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 } }

@[simp]
theorem germ_comp_stalk_to_fiber_ring_hom (U : Opens (PrimeSpectrum.top R)) (x : U) :
    (structureSheaf R).1.germ x ≫ stalkToFiberRingHom R x = openToLocalization R U x x.2 :=
  Limits.colimit.ι_desc _ _

@[simp]
theorem stalk_to_fiber_ring_hom_germ' (U : Opens (PrimeSpectrum.top R)) (x : PrimeSpectrum.top R) (hx : x ∈ U)
    (s : (structureSheaf R).1.obj (op U)) :
    stalkToFiberRingHom R x ((structureSheaf R).1.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  RingHom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom R U ⟨x, hx⟩ : _) s

@[simp]
theorem stalk_to_fiber_ring_hom_germ (U : Opens (PrimeSpectrum.top R)) (x : U) (s : (structureSheaf R).1.obj (op U)) :
    stalkToFiberRingHom R x ((structureSheaf R).1.germ x s) = s.1 x := by
  cases x
  exact stalk_to_fiber_ring_hom_germ' R U _ _ _

@[simp]
theorem to_stalk_comp_stalk_to_fiber_ring_hom (x : PrimeSpectrum.top R) :
    toStalk R x ≫ stalkToFiberRingHom R x = (algebraMap _ _ : R →+* Localization _) := by
  erw [to_stalk, category.assoc, germ_comp_stalk_to_fiber_ring_hom]
  rfl

@[simp]
theorem stalk_to_fiber_ring_hom_to_stalk (x : PrimeSpectrum.top R) (f : R) :
    stalkToFiberRingHom R x (toStalk R x f) = algebraMap _ (Localization _) f :=
  RingHom.ext_iff.1 (to_stalk_comp_stalk_to_fiber_ring_hom R x) _

/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
@[simps]
def stalkIso (x : PrimeSpectrum.top R) :
    (structureSheaf R).1.stalk x ≅ CommRingₓₓ.of (Localization.AtPrime x.asIdeal) where
  hom := stalkToFiberRingHom R x
  inv := localizationToStalk R x
  hom_inv_id' :=
    (structureSheaf R).1.stalk_hom_ext fun U hxU => by
      ext s
      simp only [← comp_apply]
      rw [id_apply, stalk_to_fiber_ring_hom_germ']
      obtain ⟨V, hxV, iVU, f, g, hg, hs⟩ := exists_const _ _ s x hxU
      erw [← res_apply R U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localization_to_stalk_mk']
      refine' (structure_sheaf R).1.germ_ext V hxV (hom_of_le hg) iVU _
      erw [← hs, res_const']
  inv_hom_id' :=
    @IsLocalization.ring_hom_ext R _ x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal) _ _
        (Localization.AtPrime x.asIdeal) _ _ (RingHom.comp (stalkToFiberRingHom R x) (localizationToStalk R x))
        (RingHom.id (Localization.AtPrime _)) <|
      by
      ext f
      simp only [← RingHom.comp_apply, ← RingHom.id_apply, ← localization_to_stalk_of, ←
        stalk_to_fiber_ring_hom_to_stalk]

instance (x : PrimeSpectrum R) : IsIso (stalkToFiberRingHom R x) :=
  IsIso.of_iso (stalkIso R x)

instance (x : PrimeSpectrum R) : IsIso (localizationToStalk R x) :=
  IsIso.of_iso (stalkIso R x).symm

@[simp, reassoc]
theorem stalk_to_fiber_ring_hom_localization_to_stalk (x : PrimeSpectrum.top R) :
    stalkToFiberRingHom R x ≫ localizationToStalk R x = 𝟙 _ :=
  (stalkIso R x).hom_inv_id

@[simp, reassoc]
theorem localization_to_stalk_stalk_to_fiber_ring_hom (x : PrimeSpectrum.top R) :
    localizationToStalk R x ≫ stalkToFiberRingHom R x = 𝟙 _ :=
  (stalkIso R x).inv_hom_id

/-- The canonical ring homomorphism interpreting `s ∈ R_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
def toBasicOpen (f : R) : Localization.Away f →+* (structureSheaf R).1.obj (op <| basicOpen f) :=
  IsLocalization.Away.lift f (is_unit_to_basic_open_self R f)

@[simp]
theorem to_basic_open_mk' (s f : R) (g : Submonoid.powers s) :
    toBasicOpen R s (IsLocalization.mk' (Localization.Away s) f g) =
      const R f g (basicOpen s) fun x hx => Submonoid.powers_subset hx g.2 :=
  (IsLocalization.lift_mk'_spec _ _ _ _).2 <| by
    rw [to_open_eq_const, to_open_eq_const, const_mul_cancel']

@[simp]
theorem localization_to_basic_open (f : R) :
    RingHom.comp (toBasicOpen R f) (algebraMap R (Localization.Away f)) = toOpen R (basicOpen f) :=
  RingHom.ext fun g => by
    rw [to_basic_open, IsLocalization.Away.lift, RingHom.comp_apply, IsLocalization.lift_eq]

@[simp]
theorem to_basic_open_to_map (s f : R) :
    toBasicOpen R s (algebraMap R (Localization.Away s) f) = const R f 1 (basicOpen s) fun _ _ => Submonoid.one_mem _ :=
  (IsLocalization.lift_eq _ _).trans <| to_open_eq_const _ _ _

-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
theorem to_basic_open_injective (f : R) : Function.Injective (toBasicOpen R f) := by
  intro s t h_eq
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) s
  obtain ⟨c, ⟨d, hd⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) t
  simp only [← to_basic_open_mk'] at h_eq
  rw [IsLocalization.eq]
  -- We know that the fractions `a/b` and `c/d` are equal as sections of the structure sheaf on
  -- `basic_open f`. We need to show that they agree as elements in the localization of `R` at `f`.
  -- This amounts showing that `a * d * r = c * b * r`, for some power `r = f ^ n` of `f`.
  -- We define `I` as the ideal of *all* elements `r` satisfying the above equation.
  let I : Ideal R :=
    { Carrier := { r : R | a * d * r = c * b * r },
      zero_mem' := by
        simp only [← Set.mem_set_of_eq, ← mul_zero],
      add_mem' := fun r₁ r₂ hr₁ hr₂ => by
        dsimp'  at hr₁ hr₂⊢
        simp only [← mul_addₓ, ← hr₁, ← hr₂],
      smul_mem' := fun r₁ r₂ hr₂ => by
        dsimp'  at hr₂⊢
        simp only [← mul_comm r₁ r₂, mul_assoc, ← hr₂] }
  -- Our claim now reduces to showing that `f` is contained in the radical of `I`
  suffices f ∈ I.radical by
    cases' this with n hn
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩
  rw [← vanishing_ideal_zero_locus_eq_radical, mem_vanishing_ideal]
  intro p hfp
  contrapose hfp
  rw [mem_zero_locus, Set.not_subset]
  have := congr_fun (congr_arg Subtype.val h_eq) ⟨p, hfp⟩
  rw [const_apply, const_apply, IsLocalization.eq] at this
  cases' this with r hr
  exact ⟨r.1, hr, r.2⟩

/-
Auxiliary lemma for surjectivity of `to_basic_open`.
Every section can locally be represented on basic opens `basic_opens g` as a fraction `f/g`
-/
theorem locally_const_basic_open (U : Opens (PrimeSpectrum.top R)) (s : (structureSheaf R).1.obj (op U)) (x : U) :
    ∃ (f g : R)(i : basicOpen g ⟶ U),
      x.1 ∈ basicOpen g ∧ (const R f g (basicOpen g) fun y hy => hy) = (structureSheaf R).1.map i.op s :=
  by
  -- First, any section `s` can be represented as a fraction `f/g` on some open neighborhood of `x`
  -- and we may pass to a `basic_open h`, since these form a basis
  obtain ⟨V, hxV : x.1 ∈ V.1, iVU, f, g, hVDg : V ⊆ basic_open g, s_eq⟩ := exists_const R U s x.1 x.2
  obtain ⟨_, ⟨h, rfl⟩, hxDh, hDhV : basic_open h ⊆ V⟩ :=
    is_topological_basis_basic_opens.exists_subset_of_mem_open hxV V.2
  -- The problem is of course, that `g` and `h` don't need to coincide.
  -- But, since `basic_open h ≤ basic_open g`, some power of `h` must be a multiple of `g`
  cases' (basic_open_le_basic_open_iff h g).mp (Set.Subset.trans hDhV hVDg) with n hn
  -- Actually, we will need a *nonzero* power of `h`.
  -- This is because we will need the equality `basic_open (h ^ n) = basic_open h`, which only
  -- holds for a nonzero power `n`. We therefore artificially increase `n` by one.
  replace hn := Ideal.mul_mem_left (Ideal.span {g}) h hn
  rw [← pow_succₓ, Ideal.mem_span_singleton'] at hn
  cases' hn with c hc
  have basic_opens_eq :=
    basic_open_pow h (n + 1)
      (by
        linarith)
  have i_basic_open := eq_to_hom basic_opens_eq ≫ hom_of_le hDhV
  -- We claim that `(f * c) / h ^ (n+1)` is our desired representation
  use f * c, h ^ (n + 1), i_basic_open ≫ iVU, (basic_opens_eq.symm.le : _) hxDh
  rw [op_comp, functor.map_comp, comp_apply, ← s_eq, res_const]
  -- Note that the last rewrite here generated an additional goal, which was a parameter
  -- of `res_const`. We prove this goal first
  swap
  · intro y hy
    rw [basic_opens_eq] at hy
    exact (Set.Subset.trans hDhV hVDg : _) hy
    
  -- All that is left is a simple calculation
  apply const_ext
  rw [mul_assoc f c g, hc]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i j «expr ∈ » t)
/-
Auxiliary lemma for surjectivity of `to_basic_open`.
A local representation of a section `s` as fractions `a i / h i` on finitely many basic opens
`basic_open (h i)` can be "normalized" in such a way that `a i * h j = h i * a j` for all `i, j`
-/
theorem normalize_finite_fraction_representation (U : Opens (PrimeSpectrum.top R)) (s : (structureSheaf R).1.obj (op U))
    {ι : Type _} (t : Finset ι) (a h : ι → R) (iDh : ∀ i : ι, basicOpen (h i) ⟶ U)
    (h_cover : U.1 ⊆ ⋃ i ∈ t, (basicOpen (h i)).1)
    (hs : ∀ i : ι, (const R (a i) (h i) (basicOpen (h i)) fun y hy => hy) = (structureSheaf R).1.map (iDh i).op s) :
    ∃ (a' h' : ι → R)(iDh' : ∀ i : ι, basicOpen (h' i) ⟶ U),
      (U.1 ⊆ ⋃ i ∈ t, (basicOpen (h' i)).1) ∧
        (∀ (i j) (_ : i ∈ t) (_ : j ∈ t), a' i * h' j = h' i * a' j) ∧
          ∀,
            ∀ i ∈ t,
              ∀, (structureSheaf R).1.map (iDh' i).op s = const R (a' i) (h' i) (basicOpen (h' i)) fun y hy => hy :=
  by
  -- First we show that the fractions `(a i * h j) / (h i * h j)` and `(h i * a j) / (h i * h j)`
  -- coincide in the localization of `R` at `h i * h j`
  have fractions_eq :
    ∀ i j : ι,
      IsLocalization.mk' (Localization.Away _) (a i * h j) ⟨h i * h j, Submonoid.mem_powers _⟩ =
        IsLocalization.mk' _ (h i * a j) ⟨h i * h j, Submonoid.mem_powers _⟩ :=
    by
    intro i j
    let D := basic_open (h i * h j)
    let iDi : D ⟶ basic_open (h i) := hom_of_le (basic_open_mul_le_left _ _)
    let iDj : D ⟶ basic_open (h j) := hom_of_le (basic_open_mul_le_right _ _)
    -- Crucially, we need injectivity of `to_basic_open`
    apply to_basic_open_injective R (h i * h j)
    rw [to_basic_open_mk', to_basic_open_mk']
    simp only [← SetLike.coe_mk]
    -- Here, both sides of the equation are equal to a restriction of `s`
    trans
    convert congr_arg ((structure_sheaf R).1.map iDj.op) (hs j).symm using 1
    convert congr_arg ((structure_sheaf R).1.map iDi.op) (hs i) using 1
    swap
    all_goals
      rw [res_const]
      apply const_ext
      ring
    -- The remaining two goals were generated during the rewrite of `res_const`
    -- These can be solved immediately
    exacts[basic_open_mul_le_right _ _, basic_open_mul_le_left _ _]
  -- From the equality in the localization, we obtain for each `(i,j)` some power `(h i * h j) ^ n`
  -- which equalizes `a i * h j` and `h i * a j`
  have exists_power : ∀ i j : ι, ∃ n : ℕ, a i * h j * (h i * h j) ^ n = h i * a j * (h i * h j) ^ n := by
    intro i j
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := is_localization.eq.mp (fractions_eq i j)
    use n + 1
    rw [pow_succₓ]
    dsimp'  at hc
    convert hc using 1 <;> ring
  let n := fun p : ι × ι => (exists_power p.1 p.2).some
  have n_spec := fun p : ι × ι => (exists_power p.fst p.snd).some_spec
  -- We need one power `(h i * h j) ^ N` that works for *all* pairs `(i,j)`
  -- Since there are only finitely many indices involved, we can pick the supremum.
  let N := (t.product t).sup n
  have basic_opens_eq : ∀ i : ι, basic_open (h i ^ (N + 1)) = basic_open (h i) := fun i =>
    basic_open_pow _ _
      (by
        linarith)
  -- Expanding the fraction `a i / h i` by the power `(h i) ^ N` gives the desired normalization
  refine' ⟨fun i => a i * h i ^ N, fun i => h i ^ (N + 1), fun i => eq_to_hom (basic_opens_eq i) ≫ iDh i, _, _, _⟩
  · simpa only [← basic_opens_eq] using h_cover
    
  · intro i hi j hj
    -- Here we need to show that our new fractions `a i / h i` satisfy the normalization condition
    -- Of course, the power `N` we used to expand the fractions might be bigger than the power
    -- `n (i, j)` which was originally chosen. We denote their difference by `k`
    have n_le_N : n (i, j) ≤ N := Finset.le_sup (finset.mem_product.mpr ⟨hi, hj⟩)
    cases' Nat.Le.dest n_le_N with k hk
    simp only [hk, ← pow_addₓ, ← pow_oneₓ]
    -- To accommodate for the difference `k`, we multiply both sides of the equation `n_spec (i, j)`
      -- by `(h i * h j) ^ k`
      convert congr_arg (fun z => z * (h i * h j) ^ k) (n_spec (i, j)) using 1 <;>
      · simp only [← n, ← mul_powₓ]
        ring
        
    
  -- Lastly, we need to show that the new fractions still represent our original `s`
  intro i hi
  rw [op_comp, functor.map_comp, comp_apply, ← hs, res_const]
  -- additional goal spit out by `res_const`
  swap
  exact (basic_opens_eq i).le
  apply const_ext
  rw [pow_succₓ]
  ring

open Classical

open BigOperators

-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
theorem to_basic_open_surjective (f : R) : Function.Surjective (toBasicOpen R f) := by
  intro s
  -- In this proof, `basic_open f` will play two distinct roles: Firstly, it is an open set in the
  -- prime spectrum. Secondly, it is used as an indexing type for various families of objects
  -- (open sets, ring elements, ...). In order to make the distinction clear, we introduce a type
  -- alias `ι` that is used whenever we want think of it as an indexing type.
  let ι : Type u := basic_open f
  -- First, we pick some cover of basic opens, on which we can represent `s` as a fraction
  choose a' h' iDh' hxDh' s_eq' using locally_const_basic_open R (basic_open f) s
  -- Since basic opens are compact, we can pass to a finite subcover
  obtain ⟨t, ht_cover'⟩ :=
    (is_compact_basic_open f).elim_finite_subcover (fun i : ι => (basic_open (h' i)).1) (fun i => is_open_basic_open)
      fun x hx => _
  swap
  · -- Here, we need to show that our basic opens actually form a cover of `basic_open f`
    rw [Set.mem_Union]
    exact ⟨⟨x, hx⟩, hxDh' ⟨x, hx⟩⟩
    
  -- We use the normalization lemma from above to obtain the relation `a i * h j = h i * a j`
  obtain ⟨a, h, iDh, ht_cover, ah_ha, s_eq⟩ :=
    normalize_finite_fraction_representation R (basic_open f) s t a' h' iDh' ht_cover' s_eq'
  clear s_eq' iDh' hxDh' ht_cover' a' h'
  -- Next we show that some power of `f` is a linear combination of the `h i`
  obtain ⟨n, hn⟩ : f ∈ (Ideal.span (h '' ↑t)).radical := by
    rw [← vanishing_ideal_zero_locus_eq_radical, zero_locus_span]
    simp_rw [Subtype.val_eq_coe, basic_open_eq_zero_locus_compl] at ht_cover
    rw [Set.compl_subset_comm] at ht_cover
    -- Why doesn't `simp_rw` do this?
    simp_rw [Set.compl_Union, compl_compl, ← zero_locus_Union, ← Finset.set_bUnion_coe, ← Set.image_eq_Union] at
      ht_cover
    apply vanishing_ideal_anti_mono ht_cover
    exact subset_vanishing_ideal_zero_locus {f} (Set.mem_singleton f)
  replace hn := Ideal.mul_mem_left _ f hn
  erw [← pow_succₓ, Finsupp.mem_span_image_iff_total] at hn
  rcases hn with ⟨b, b_supp, hb⟩
  rw [Finsupp.total_apply_of_mem_supported R b_supp] at hb
  dsimp'  at hb
  -- Finally, we have all the ingredients.
  -- We claim that our preimage is given by `(∑ (i : ι) in t, b i * a i) / f ^ (n+1)`
  use
    IsLocalization.mk' (Localization.Away f) (∑ i : ι in t, b i * a i) (⟨f ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers _)
  rw [to_basic_open_mk']
  -- Since the structure sheaf is a sheaf, we can show the desired equality locally.
  -- Annoyingly, `sheaf.eq_of_locally_eq` requires an open cover indexed by a *type*, so we need to
  -- coerce our finset `t` to a type first.
  let tt := ((t : Set (basic_open f)) : Type u)
  apply (structure_sheaf R).eq_of_locally_eq' (fun i : tt => basic_open (h i)) (basic_open f) fun i : tt => iDh i
  · -- This feels a little redundant, since already have `ht_cover` as a hypothesis
    -- Unfortunately, `ht_cover` uses a bounded union over the set `t`, while here we have the
    -- Union indexed by the type `tt`, so we need some boilerplate to translate one to the other
    intro x hx
    erw [TopologicalSpace.Opens.mem_supr]
    have := ht_cover hx
    rw [← Finset.set_bUnion_coe, Set.mem_Union₂] at this
    rcases this with ⟨i, i_mem, x_mem⟩
    use i, i_mem
    
  rintro ⟨i, hi⟩
  dsimp'
  change (structure_sheaf R).1.map _ _ = (structure_sheaf R).1.map _ _
  rw [s_eq i hi, res_const]
  -- Again, `res_const` spits out an additional goal
  swap
  · intro y hy
    change y ∈ basic_open (f ^ (n + 1))
    rw
      [basic_open_pow f (n + 1)
        (by
          linarith)]
    exact (le_of_hom (iDh i) : _) hy
    
  -- The rest of the proof is just computation
  apply const_ext
  rw [← hb, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, ah_ha j hj i hi]
  ring

instance is_iso_to_basic_open (f : R) : IsIso (show CommRingₓₓ.of _ ⟶ _ from toBasicOpen R f) := by
  have : is_iso ((forget CommRingₓₓ).map (show CommRingₓₓ.of _ ⟶ _ from to_basic_open R f)) :=
    (is_iso_iff_bijective _).mpr ⟨to_basic_open_injective R f, to_basic_open_surjective R f⟩
  exact is_iso_of_reflects_iso _ (forget CommRingₓₓ)

/-- The ring isomorphism between the structure sheaf on `basic_open f` and the localization of `R`
at the submonoid of powers of `f`. -/
def basicOpenIso (f : R) : (structureSheaf R).1.obj (op (basicOpen f)) ≅ CommRingₓₓ.of (Localization.Away f) :=
  (asIso (show CommRingₓₓ.of _ ⟶ _ from toBasicOpen R f)).symm

instance stalkAlgebra (p : PrimeSpectrum R) : Algebra R ((structureSheaf R).val.stalk p) :=
  (toStalk R p).toAlgebra

@[simp]
theorem stalk_algebra_map (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((structureSheaf R).val.stalk p) r = toStalk R p r :=
  rfl

/-- Stalk of the structure sheaf at a prime p as localization of R -/
instance IsLocalization.to_stalk (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((structureSheaf R).val.stalk p) p.asIdeal := by
  convert
    (IsLocalization.is_localization_iff_of_ring_equiv _ (stalk_iso R p).symm.commRingIsoToRingEquiv).mp
      Localization.is_localization
  apply Algebra.algebra_ext
  intro
  rw [stalk_algebra_map]
  congr 1
  erw [iso.eq_comp_inv]
  exact to_stalk_comp_stalk_to_fiber_ring_hom R p

instance openAlgebra (U : (Opens (PrimeSpectrum R))ᵒᵖ) : Algebra R ((structureSheaf R).val.obj U) :=
  (toOpen R (unop U)).toAlgebra

@[simp]
theorem open_algebra_map (U : (Opens (PrimeSpectrum R))ᵒᵖ) (r : R) :
    algebraMap R ((structureSheaf R).val.obj U) r = toOpen R (unop U) r :=
  rfl

/-- Sections of the structure sheaf of Spec R on a basic open as localization of R -/
instance IsLocalization.to_basic_open (r : R) :
    IsLocalization.Away r ((structureSheaf R).val.obj (op <| basicOpen r)) := by
  convert
    (IsLocalization.is_localization_iff_of_ring_equiv _ (basic_open_iso R r).symm.commRingIsoToRingEquiv).mp
      Localization.is_localization
  apply Algebra.algebra_ext
  intro x
  congr 1
  exact (localization_to_basic_open R r).symm

instance to_basic_open_epi (r : R) : Epi (toOpen R (basicOpen r)) :=
  ⟨fun S f g h => by
    refine' IsLocalization.ring_hom_ext _ _
    pick_goal 5
    exact is_localization.to_basic_open R r
    exact h⟩

@[elementwise]
theorem to_global_factors :
    toOpen R ⊤ =
      CommRingₓₓ.ofHom (algebraMap R (Localization.Away (1 : R))) ≫
        toBasicOpen R (1 : R) ≫ (structureSheaf R).1.map (eqToHom basic_open_one.symm).op :=
  by
  rw [← category.assoc]
  change to_open R ⊤ = (to_basic_open R 1).comp _ ≫ _
  unfold CommRingₓₓ.ofHom
  rw [localization_to_basic_open R, to_open_res]

instance is_iso_to_global : IsIso (toOpen R ⊤) := by
  let hom := CommRingₓₓ.ofHom (algebraMap R (Localization.Away (1 : R)))
  have : is_iso hom := is_iso.of_iso (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingIso
  rw [to_global_factors R]
  infer_instance

/-- The ring isomorphism between the ring `R` and the global sections `Γ(X, 𝒪ₓ)`. -/
@[simps]
def globalSectionsIso : CommRingₓₓ.of R ≅ (structureSheaf R).1.obj (op ⊤) :=
  asIso (toOpen R ⊤)

@[simp]
theorem global_sections_iso_hom (R : CommRingₓₓ) : (globalSectionsIso R).hom = toOpen R ⊤ :=
  rfl

@[simp, reassoc, elementwise]
theorem to_stalk_stalk_specializes {R : Type _} [CommRingₓ R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    toStalk R y ≫ (structureSheaf R).val.stalkSpecializes h = toStalk R x := by
  dsimp' [← to_stalk]
  simpa

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
@[simp, reassoc, elementwise]
theorem localization_to_stalk_stalk_specializes {R : Type _} [CommRingₓ R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    StructureSheaf.localizationToStalk R y ≫ (structureSheaf R).val.stalkSpecializes h =
      CommRingₓₓ.ofHom (PrimeSpectrum.localizationMapOfSpecializes h) ≫ StructureSheaf.localizationToStalk R x :=
  by
  apply IsLocalization.ring_hom_ext y.as_ideal.prime_compl
  any_goals {
  }
  erw [RingHom.comp_assoc]
  conv_rhs => erw [RingHom.comp_assoc]
  dsimp' [← CommRingₓₓ.ofHom, ← localization_to_stalk, ← PrimeSpectrum.localizationMapOfSpecializes]
  rw [IsLocalization.lift_comp, IsLocalization.lift_comp, IsLocalization.lift_comp]
  exact to_stalk_stalk_specializes h

@[simp, reassoc, elementwise]
theorem stalk_specializes_stalk_to_fiber {R : Type _} [CommRingₓ R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    (structureSheaf R).val.stalkSpecializes h ≫ StructureSheaf.stalkToFiberRingHom R x =
      StructureSheaf.stalkToFiberRingHom R y ≫ PrimeSpectrum.localizationMapOfSpecializes h :=
  by
  change _ ≫ (structure_sheaf.stalk_iso R x).hom = (structure_sheaf.stalk_iso R y).hom ≫ _
  rw [← iso.eq_comp_inv, category.assoc, ← iso.inv_comp_eq]
  exact localization_to_stalk_stalk_specializes h

section Comap

variable {R} {S : Type u} [CommRingₓ S] {P : Type u} [CommRingₓ P]

/-- Given a ring homomorphism `f : R →+* S`, an open set `U` of the prime spectrum of `R` and an open
set `V` of the prime spectrum of `S`, such that `V ⊆ (comap f) ⁻¹' U`, we can push a section `s`
on `U` to a section on `V`, by composing with `localization.local_ring_hom _ _ f` from the left and
`comap f` from the right. Explicitly, if `s` evaluates on `comap f p` to `a / b`, its image on `V`
evaluates on `p` to `f(a) / f(b)`.

At the moment, we work with arbitrary dependent functions `s : Π x : U, localizations R x`. Below,
we prove the predicate `is_locally_fraction` is preserved by this map, hence it can be extended to
a morphism between the structure sheaves of `R` and `S`.
-/
def comapFun (f : R →+* S) (U : Opens (PrimeSpectrum.top R)) (V : Opens (PrimeSpectrum.top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : ∀ x : U, Localizations R x) (y : V) : Localizations S y :=
  Localization.localRingHom (PrimeSpectrum.comap f y.1).asIdeal _ f rfl (s ⟨PrimeSpectrum.comap f y.1, hUV y.2⟩ : _)

theorem comap_fun_is_locally_fraction (f : R →+* S) (U : Opens (PrimeSpectrum.top R)) (V : Opens (PrimeSpectrum.top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : ∀ x : U, Localizations R x)
    (hs : (isLocallyFraction R).toPrelocalPredicate.pred s) :
    (isLocallyFraction S).toPrelocalPredicate.pred (comapFun f U V hUV s) := by
  rintro ⟨p, hpV⟩
  -- Since `s` is locally fraction, we can find a neighborhood `W` of `prime_spectrum.comap f p`
  -- in `U`, such that `s = a / b` on `W`, for some ring elements `a, b : R`.
  rcases hs ⟨PrimeSpectrum.comap f p, hUV hpV⟩ with ⟨W, m, iWU, a, b, h_frac⟩
  -- We claim that we can write our new section as the fraction `f a / f b` on the neighborhood
  -- `(comap f) ⁻¹ W ⊓ V` of `p`.
  refine' ⟨opens.comap (comap f) W⊓V, ⟨m, hpV⟩, opens.inf_le_right _ _, f a, f b, _⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  specialize h_frac ⟨PrimeSpectrum.comap f q, hqW⟩
  refine' ⟨h_frac.1, _⟩
  dsimp' only [← comap_fun]
  erw [← Localization.local_ring_hom_to_map (PrimeSpectrum.comap f q).asIdeal, ← RingHom.map_mul, h_frac.2,
    Localization.local_ring_hom_to_map]
  rfl

/-- For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
def comap (f : R →+* S) (U : Opens (PrimeSpectrum.top R)) (V : Opens (PrimeSpectrum.top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) :
    (structureSheaf R).1.obj (op U) →+* (structureSheaf S).1.obj (op V) where
  toFun := fun s => ⟨comapFun f U V hUV s.1, comap_fun_is_locally_fraction f U V hUV s.1 s.2⟩
  map_one' :=
    Subtype.ext <|
      funext fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_one, Pi.one_apply,
          RingHom.map_one]
        rfl
  map_zero' :=
    Subtype.ext <|
      funext fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_zero, Pi.zero_apply,
          RingHom.map_zero]
        rfl
  map_add' := fun s t =>
    Subtype.ext <|
      funext fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_add, Pi.add_apply,
          RingHom.map_add]
        rfl
  map_mul' := fun s t =>
    Subtype.ext <|
      funext fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_mul, Pi.mul_apply,
          RingHom.map_mul]
        rfl

@[simp]
theorem comap_apply (f : R →+* S) (U : Opens (PrimeSpectrum.top R)) (V : Opens (PrimeSpectrum.top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comap f U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩ : _) :=
  rfl

theorem comap_const (f : R →+* S) (U : Opens (PrimeSpectrum.top R)) (V : Opens (PrimeSpectrum.top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (a b : R)
    (hb : ∀ x : PrimeSpectrum R, x ∈ U → b ∈ x.asIdeal.primeCompl) :
    comap f U V hUV (const R a b U hb) = const S (f a) (f b) V fun p hpV => hb (PrimeSpectrum.comap f p) (hUV hpV) :=
  Subtype.eq <|
    funext fun p => by
      rw [comap_apply, const_apply, const_apply]
      erw [Localization.local_ring_hom_mk']
      rfl

/-- For an inclusion `i : V ⟶ U` between open sets of the prime spectrum of `R`, the comap of the
identity from OO_X(U) to OO_X(V) equals as the restriction map of the structure sheaf.

This is a generalization of the fact that, for fixed `U`, the comap of the identity from OO_X(U)
to OO_X(U) is the identity.
-/
theorem comap_id_eq_map (U V : Opens (PrimeSpectrum.top R)) (iVU : V ⟶ U) :
    (comap (RingHom.id R) U V fun p hpV =>
        le_of_hom iVU <| by
          rwa [PrimeSpectrum.comap_id]) =
      (structureSheaf R).1.map iVU.op :=
  RingHom.ext fun s =>
    Subtype.eq <|
      funext fun p => by
        rw [comap_apply]
        -- Unfortunately, we cannot use `localization.local_ring_hom_id` here, because
        -- `prime_spectrum.comap (ring_hom.id R) p` is not *definitionally* equal to `p`. Instead, we use
        -- that we can write `s` as a fraction `a/b` in a small neighborhood around `p`. Since
        -- `prime_spectrum.comap (ring_hom.id R) p` equals `p`, it is also contained in the same
        -- neighborhood, hence `s` equals `a/b` there too.
        obtain ⟨W, hpW, iWU, h⟩ := s.2 (iVU p)
        obtain ⟨a, b, h'⟩ := h.eq_mk'
        obtain ⟨hb₁, s_eq₁⟩ := h' ⟨p, hpW⟩
        obtain ⟨hb₂, s_eq₂⟩ :=
          h'
            ⟨PrimeSpectrum.comap (RingHom.id _) p.1, by
              rwa [PrimeSpectrum.comap_id]⟩
        dsimp' only  at s_eq₁ s_eq₂
        erw [s_eq₂, Localization.local_ring_hom_mk', ← s_eq₁, ← res_apply]

/-- The comap of the identity is the identity. In this variant of the lemma, two open subsets `U` and
`V` are given as arguments, together with a proof that `U = V`. This is be useful when `U` and `V`
are not definitionally equal.
-/
theorem comap_id (U V : Opens (PrimeSpectrum.top R)) (hUV : U = V) :
    (comap (RingHom.id R) U V fun p hpV => by
        rwa [hUV, PrimeSpectrum.comap_id]) =
      eqToHom
        (show (structureSheaf R).1.obj (op U) = _ by
          rw [hUV]) :=
  by
  erw [comap_id_eq_map U V (eq_to_hom hUV.symm), eq_to_hom_op, eq_to_hom_map]

@[simp]
theorem comap_id' (U : Opens (PrimeSpectrum.top R)) :
    (comap (RingHom.id R) U U fun p hpU => by
        rwa [PrimeSpectrum.comap_id]) =
      RingHom.id _ :=
  by
  rw [comap_id U U rfl]
  rfl

theorem comap_comp (f : R →+* S) (g : S →+* P) (U : Opens (PrimeSpectrum.top R)) (V : Opens (PrimeSpectrum.top S))
    (W : Opens (PrimeSpectrum.top P)) (hUV : ∀, ∀ p ∈ V, ∀, PrimeSpectrum.comap f p ∈ U)
    (hVW : ∀, ∀ p ∈ W, ∀, PrimeSpectrum.comap g p ∈ V) :
    (comap (g.comp f) U W fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) =
      (comap g V W hVW).comp (comap f U V hUV) :=
  RingHom.ext fun s =>
    Subtype.eq <|
      funext fun p => by
        rw [comap_apply]
        erw [Localization.local_ring_hom_comp _ (PrimeSpectrum.comap g p.1).asIdeal]
        -- refl works here, because `prime_spectrum.comap (g.comp f) p` is defeq to
        -- `prime_spectrum.comap f (prime_spectrum.comap g p)`
        rfl

@[elementwise, reassoc]
theorem to_open_comp_comap (f : R →+* S) (U : Opens (PrimeSpectrum.top R)) :
    (toOpen R U ≫ comap f U (Opens.comap (PrimeSpectrum.comap f) U) fun _ => id) = CommRingₓₓ.ofHom f ≫ toOpen S _ :=
  RingHom.ext fun s =>
    Subtype.eq <|
      funext fun p => by
        simp_rw [comp_apply, comap_apply, Subtype.val_eq_coe]
        erw [Localization.local_ring_hom_to_map]
        rfl

end Comap

end StructureSheaf

end AlgebraicGeometry

