/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathbin.Topology.Sheaves.SheafOfFunctions
import Mathbin.Topology.Sheaves.Stalks
import Mathbin.Topology.LocalHomeomorph
import Mathbin.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Functions satisfying a local predicate form a sheaf.

At this stage, in `topology/sheaves/sheaf_of_functions.lean`
we've proved that not-necessarily-continuous functions from a topological space
into some type (or type family) form a sheaf.

Why do the continuous functions form a sheaf?
The point is just that continuity is a local condition,
so one can use the lifting condition for functions to provide a candidate lift,
then verify that the lift is actually continuous by using the factorisation condition for the lift
(which guarantees that on each open set it agrees with the functions being lifted,
which were assumed to be continuous).

This file abstracts this argument to work for
any collection of dependent functions on a topological space
satisfying a "local predicate".

As an application, we check that continuity is a local predicate in this sense, and provide
* `Top.sheaf_to_Top`: continuous functions into a topological space form a sheaf

A sheaf constructed in this way has a natural map `stalk_to_fiber` from the stalks
to the types in the ambient type family.

We give conditions sufficient to show that this map is injective and/or surjective.
-/


universe v

noncomputable section

variable {X : Top.{v}}

variable (T : X → Type v)

open TopologicalSpace

open Opposite

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.Types

namespace Top

/-- Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : prelocal_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate.
-/
structure PrelocalPredicate where
  pred : ∀ {U : Opens X}, (∀ x : U, T x) → Prop
  res : ∀ {U V : Opens X} (i : U ⟶ V) (f : ∀ x : V, T x) (h : pred f), pred fun x : U => f (i x)

variable (X)

/-- Continuity is a "prelocal" predicate on functions to a fixed topological space `T`.
-/
@[simps]
def continuousPrelocal (T : Top.{v}) : PrelocalPredicate fun x : X => T where
  pred := fun U f => Continuous f
  res := fun U V i f h => Continuous.comp h (Opens.open_embedding_of_le i.le).Continuous

/-- Satisfying the inhabited linter. -/
instance inhabitedPrelocalPredicate (T : Top.{v}) : Inhabited (PrelocalPredicate fun x : X => T) :=
  ⟨continuousPrelocal X T⟩

variable {X}

/-- Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : local_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate, and
* a proof that given some `f : Π x : U, T x`,
  if for every `x : U` we can find an open set `x ∈ V ≤ U`
  so that the restriction of `f` to `V` satisfies the predicate,
  then `f` itself satisfies the predicate.
-/
structure LocalPredicate extends PrelocalPredicate T where
  locality :
    ∀ {U : Opens X} (f : ∀ x : U, T x)
      (w : ∀ x : U, ∃ (V : Opens X)(m : x.1 ∈ V)(i : V ⟶ U), pred fun x : V => f (i x : U)), pred f

variable (X)

/-- Continuity is a "local" predicate on functions to a fixed topological space `T`.
-/
def continuousLocal (T : Top.{v}) : LocalPredicate fun x : X => T :=
  { continuousPrelocal X T with
    locality := fun U f w => by
      apply continuous_iff_continuous_at.2
      intro x
      specialize w x
      rcases w with ⟨V, m, i, w⟩
      dsimp'  at w
      rw [continuous_iff_continuous_at] at w
      specialize w ⟨x, m⟩
      simpa using (opens.open_embedding_of_le i.le).continuous_at_iff.1 w }

/-- Satisfying the inhabited linter. -/
instance inhabitedLocalPredicate (T : Top.{v}) : Inhabited (LocalPredicate _) :=
  ⟨continuousLocal X T⟩

variable {X T}

/-- Given a `P : prelocal_predicate`, we can always construct a `local_predicate`
by asking that the condition from `P` holds locally near every point.
-/
def PrelocalPredicate.sheafify {T : X → Type v} (P : PrelocalPredicate T) : LocalPredicate T where
  pred := fun U f => ∀ x : U, ∃ (V : Opens X)(m : x.1 ∈ V)(i : V ⟶ U), P.pred fun x : V => f (i x : U)
  res := fun V U i f w x => by
    specialize w (i x)
    rcases w with ⟨V', m', i', p⟩
    refine' ⟨V⊓V', ⟨x.2, m'⟩, opens.inf_le_left _ _, _⟩
    convert P.res (opens.inf_le_right V V') _ p
  locality := fun U f w x => by
    specialize w x
    rcases w with ⟨V, m, i, p⟩
    specialize p ⟨x.1, m⟩
    rcases p with ⟨V', m', i', p'⟩
    exact ⟨V', m', i' ≫ i, p'⟩

theorem PrelocalPredicate.sheafify_of {T : X → Type v} {P : PrelocalPredicate T} {U : Opens X} {f : ∀ x : U, T x}
    (h : P.pred f) : P.sheafify.pred f := fun x =>
  ⟨U, x.2, 𝟙 _, by
    convert h
    ext ⟨y, w⟩
    rfl⟩

/-- The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
@[simps]
def subpresheafToTypes (P : PrelocalPredicate T) : Presheaf (Type v) X where
  obj := fun U => { f : ∀ x : unop U, T x // P.pred f }
  map := fun U V i f => ⟨fun x => f.1 (i.unop x), P.res i.unop f.1 f.2⟩

namespace SubpresheafToTypes

variable (P : PrelocalPredicate T)

/-- The natural transformation including the subpresheaf of functions satisfying a local predicate
into the presheaf of all functions.
-/
def subtype : subpresheafToTypes P ⟶ presheafToTypes X T where app := fun U f => f.1

open Top.Presheaf

/-- The functions satisfying a local predicate satisfy the sheaf condition.
-/
theorem is_sheaf (P : LocalPredicate T) : (subpresheafToTypes P.toPrelocalPredicate).IsSheaf :=
  (Presheaf.is_sheaf_of_is_sheaf_unique_gluing_types _) fun ι U sf sf_comp => by
    -- We show the sheaf condition in terms of unique gluing.
    -- First we obtain a family of sections for the underlying sheaf of functions,
    -- by forgetting that the prediacte holds
    let sf' : ∀ i : ι, (presheaf_to_Types X T).obj (op (U i)) := fun i => (sf i).val
    -- Since our original family is compatible, this one is as well
    have sf'_comp : (presheaf_to_Types X T).IsCompatible U sf' := fun i j => congr_arg Subtype.val (sf_comp i j)
    -- So, we can obtain a unique gluing
    obtain ⟨gl, gl_spec, gl_uniq⟩ := (sheaf_to_Types X T).exists_unique_gluing U sf' sf'_comp
    refine' ⟨⟨gl, _⟩, _, _⟩
    · -- Our first goal is to show that this chosen gluing satisfies the
      -- predicate. Of course, we use locality of the predicate.
      apply P.locality
      rintro ⟨x, mem⟩
      -- Once we're at a particular point `x`, we can select some open set `x ∈ U i`.
      choose i hi using opens.mem_supr.mp mem
      -- We claim that the predicate holds in `U i`
      use U i, hi, opens.le_supr U i
      -- This follows, since our original family `sf` satisfies the predicate
      convert (sf i).property
      exact gl_spec i
      
    -- It remains to show that the chosen lift is really a gluing for the subsheaf and
    -- that it is unique. Both of which follow immediately from the corresponding facts
    -- in the sheaf of functions without the local predicate.
    · intro i
      ext1
      exact gl_spec i
      
    · intro gl' hgl'
      ext1
      exact gl_uniq gl'.1 fun i => congr_arg Subtype.val (hgl' i)
      

end SubpresheafToTypes

/-- The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
def subsheafToTypes (P : LocalPredicate T) : Sheaf (Type v) X :=
  ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.is_sheaf P⟩

/-- There is a canonical map from the stalk to the original fiber, given by evaluating sections.
-/
def stalkToFiber (P : LocalPredicate T) (x : X) : (subsheafToTypes P).1.stalk x ⟶ T x := by
  refine' colimit.desc _ { x := T x, ι := { app := fun U f => _, naturality' := _ } }
  · exact f.1 ⟨x, (unop U).2⟩
    
  · tidy
    

@[simp]
theorem stalk_to_fiber_germ (P : LocalPredicate T) (U : Opens X) (x : U) (f) :
    stalkToFiber P x ((subsheafToTypes P).1.germ x f) = f.1 x := by
  dsimp' [← presheaf.germ, ← stalk_to_fiber]
  cases x
  simp
  rfl

/-- The `stalk_to_fiber` map is surjective at `x` if
every point in the fiber `T x` has an allowed section passing through it.
-/
theorem stalk_to_fiber_surjective (P : LocalPredicate T) (x : X)
    (w : ∀ t : T x, ∃ (U : OpenNhds x)(f : ∀ y : U.1, T y)(h : P.pred f), f ⟨x, U.2⟩ = t) :
    Function.Surjective (stalkToFiber P x) := fun t => by
  rcases w t with ⟨U, f, h, rfl⟩
  fconstructor
  · exact (subsheaf_to_Types P).1.germ ⟨x, U.2⟩ ⟨f, h⟩
    
  · exact stalk_to_fiber_germ _ U.1 ⟨x, U.2⟩ ⟨f, h⟩
    

/-- The `stalk_to_fiber` map is injective at `x` if any two allowed sections which agree at `x`
agree on some neighborhood of `x`.
-/
theorem stalk_to_fiber_injective (P : LocalPredicate T) (x : X)
    (w :
      ∀ (U V : OpenNhds x) (fU : ∀ y : U.1, T y) (hU : P.pred fU) (fV : ∀ y : V.1, T y) (hV : P.pred fV)
        (e : fU ⟨x, U.2⟩ = fV ⟨x, V.2⟩),
        ∃ (W : OpenNhds x)(iU : W ⟶ U)(iV : W ⟶ V), ∀ w : W.1, fU (iU w : U.1) = fV (iV w : V.1)) :
    Function.Injective (stalkToFiber P x) := fun tU tV h => by
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    ∃ (W : (open_nhds x)ᵒᵖ)(s : ∀ w : (unop W).1, T w)(hW : P.pred s),
      tU = (subsheaf_to_Types P).1.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ ∧
        tV = (subsheaf_to_Types P).1.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ :=
    _
  · choose W s hW e using Q
    exact e.1.trans e.2.symm
    
  -- Then use induction to pick particular representatives of `tU tV : stalk x`
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective'.{v, v} tU
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective'.{v, v} tV
  · -- Decompose everything into its constituent parts:
    dsimp'
    simp only [← stalk_to_fiber, ← types.colimit.ι_desc_apply'] at h
    specialize w (unop U) (unop V) fU hU fV hV h
    rcases w with ⟨W, iU, iV, w⟩
    -- and put it back together again in the correct order.
    refine' ⟨op W, fun w => fU (iU w : (unop U).1), P.res _ _ hU, _⟩
    rcases W with ⟨W, m⟩
    exact ⟨colimit_sound iU.op (Subtype.eq rfl), colimit_sound iV.op (Subtype.eq (funext w).symm)⟩
    

/-- Some repackaging:
the presheaf of functions satisfying `continuous_prelocal` is just the same thing as
the presheaf of continuous functions.
-/
def subpresheafContinuousPrelocalIsoPresheafToTop (T : Top.{v}) :
    subpresheafToTypes (continuousPrelocal X T) ≅ presheafToTop X T :=
  NatIso.ofComponents
    (fun X =>
      { Hom := by
          rintro ⟨f, c⟩
          exact ⟨f, c⟩,
        inv := by
          rintro ⟨f, c⟩
          exact ⟨f, c⟩,
        hom_inv_id' := by
          ext ⟨f, p⟩ x
          rfl,
        inv_hom_id' := by
          ext ⟨f, p⟩ x
          rfl })
    (by
      tidy)

/-- The sheaf of continuous functions on `X` with values in a space `T`.
-/
def sheafToTop (T : Top.{v}) : Sheaf (Type v) X :=
  ⟨presheafToTop X T,
    Presheaf.is_sheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.is_sheaf (continuousLocal X T))⟩

end Top

