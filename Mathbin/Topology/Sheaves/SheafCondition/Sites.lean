/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathbin.CategoryTheory.Sites.Spaces
import Mathbin.Topology.Sheaves.Sheaf
import Mathbin.CategoryTheory.Sites.DenseSubsite

/-!

# The sheaf condition in terms of sites.

The theory of sheaves on sites is developed independently from sheaves on spaces in
`category_theory/sites`. In this file, we connect the two theories: We show that for a topological
space `X`, a presheaf `F : (opens X)ᵒᵖ ⥤ C` is a sheaf on the site `opens X` if and only if it is
a sheaf on `X` in the usual sense.

Recall that a presheaf `F : (opens X)ᵒᵖ ⥤ C` is called a *sheaf* on the space `X`, if for every
family of opens `U : ι → opens X`, the object `F.obj (op (supr U))` is the limit of some fork
diagram. On the other hand, `F` is called a *sheaf* on the site `opens X`, if for every open set
`U : opens X` and every presieve `R : presieve U`, the object `F.obj (op U)` is the limit of a
very similar fork diagram. In this file, we will construct the two functions `covering_of_presieve`
and `presieve_of_covering`, which translate between the two concepts. We then prove a bunch of
naturality lemmas relating the two fork diagrams to each other.

## Main statements
* `is_sheaf_sites_iff_is_sheaf_spaces`. A presheaf `F : (opens X)ᵒᵖ ⥤ C` is a sheaf on the site
  `opens X` if and only if it is a sheaf on the space `X`.
* `Sheaf_sites_eq_sheaf_spaces`. The type of sheaves on the site `opens X` is *equal* to the type
  of sheaves on the space `X`.

-/


noncomputable section

universe u v w

namespace Top.Presheaf

open CategoryTheory TopologicalSpace Top CategoryTheory.Limits Opposite

open Top.Presheaf.SheafConditionEqualizerProducts

variable {C : Type u} [Category.{v} C] [HasProducts.{v} C]

variable {X : Top.{v}} (F : Presheaf C X)

/-- Given a presieve `R` on `U`, we obtain a covering family of open sets in `X`, by taking as index
type the type of dependent pairs `(V, f)`, where `f : V ⟶ U` is in `R`.
-/
def coveringOfPresieve (U : Opens X) (R : Presieve U) : (ΣV, { f : V ⟶ U // R f }) → Opens X := fun f => f.1

@[simp]
theorem covering_of_presieve_apply (U : Opens X) (R : Presieve U) (f : ΣV, { f : V ⟶ U // R f }) :
    coveringOfPresieve U R f = f.1 :=
  rfl

namespace CoveringOfPresieve

variable (U : Opens X) (R : Presieve U)

/-!
In this section, we will relate two different fork diagrams to each other.

The first one is the defining fork diagram for the sheaf condition in terms of sites, applied to
the presieve `R`. It will henceforth be called the _sites diagram_. Its objects are called
`presheaf.first_obj` and `presheaf.second_obj` and its morphisms are `presheaf.first_map` and
`presheaf.second_obj`. The fork map into this diagram is called `presheaf.fork_map`.

The second one is the defining fork diagram for the sheaf condition in terms of spaces, applied to
the family of opens `covering_of_presieve U R`. It will henceforth be called the _spaces diagram_.
Its objects are called `pi_opens` and `pi_inters` and its morphisms are `left_res` and `right_res`.
The fork map into this diagram is called `res`.

-/


/-- If `R` is a presieve in the grothendieck topology on `opens X`, the covering family associated to
`R` really is _covering_, i.e. the union of all open sets equals `U`.
-/
theorem supr_eq_of_mem_grothendieck (hR : Sieve.generate R ∈ Opens.grothendieckTopology X U) :
    supr (coveringOfPresieve U R) = U := by
  apply le_antisymmₓ
  · refine' supr_le _
    intro f
    exact f.2.1.le
    
  intro x hxU
  rw [opens.mem_coe, opens.mem_supr]
  obtain ⟨V, iVU, ⟨W, iVW, iWU, hiWU, -⟩, hxV⟩ := hR x hxU
  exact ⟨⟨W, ⟨iWU, hiWU⟩⟩, iVW.le hxV⟩

/-- The first object in the sites diagram is isomorphic to the first object in the spaces diagram.
Actually, they are even definitionally equal, but it is convenient to give this isomorphism a name.
-/
def firstObjIsoPiOpens : Presheaf.firstObj R F ≅ piOpens F (coveringOfPresieve U R) :=
  eqToIso rfl

/-- The isomorphism `first_obj_iso_pi_opens` is compatible with canonical projections out of the
product.
-/
theorem first_obj_iso_pi_opens_π (f : ΣV, { f : V ⟶ U // R f }) :
    (firstObjIsoPiOpens F U R).Hom ≫ Pi.π _ f = Pi.π _ f :=
  Category.id_comp _

/-- The second object in the sites diagram is isomorphic to the second object in the spaces diagram.
-/
def secondObjIsoPiInters : Presheaf.secondObj R F ≅ piInters F (coveringOfPresieve U R) :=
  has_limit.iso_of_nat_iso <| discrete.nat_iso fun i => F.mapIso (eqToIso (CompleteLattice.pullback_eq_inf _ _).symm).op

/-- The isomorphism `second_obj_iso_pi_inters` is compatible with canonical projections out of the
product. Here, we have to insert an `eq_to_hom` arrow to pass from
`F.obj (op (pullback f.2.1 g.2.1))` to `F.obj (op (f.1 ⊓ g.1))`.
-/
theorem second_obj_iso_pi_inters_π (f g : ΣV, { f : V ⟶ U // R f }) :
    (secondObjIsoPiInters F U R).Hom ≫ Pi.π _ (f, g) =
      Pi.π _ (f, g) ≫ F.map (eqToHom (CompleteLattice.pullback_eq_inf f.2.1 g.2.1).symm).op :=
  by
  dunfold second_obj_iso_pi_inters
  rw [has_limit.iso_of_nat_iso_hom_π]
  rfl

/-- Composing the fork map of the sites diagram with the isomorphism `first_obj_iso_pi_opens` is the
same as the fork map of the spaces diagram (modulo an `eq_to_hom` arrow).
-/
theorem fork_map_comp_first_obj_iso_pi_opens_eq (hR : Sieve.generate R ∈ Opens.grothendieckTopology X U) :
    Presheaf.forkMap R F ≫ (firstObjIsoPiOpens F U R).Hom =
      F.map (eqToHom (supr_eq_of_mem_grothendieck U R hR)).op ≫ res F (coveringOfPresieve U R) :=
  by
  ext ⟨f⟩
  rw [category.assoc, category.assoc, first_obj_iso_pi_opens_π]
  dunfold presheaf.fork_map res
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ← F.map_comp]
  congr

/-- First naturality condition. Under the isomorphisms `first_obj_iso_pi_opens` and
`second_obj_iso_pi_inters`, the map `presheaf.first_map` corresponds to `left_res`.
-/
theorem first_obj_iso_comp_left_res_eq :
    Presheaf.firstMap R F ≫ (secondObjIsoPiInters F U R).Hom =
      (firstObjIsoPiOpens F U R).Hom ≫ leftRes F (coveringOfPresieve U R) :=
  by
  ext ⟨f, g⟩
  rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π]
  dunfold left_res presheaf.first_map
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π_assoc, fan.mk_π_app, ← category.assoc]
  erw [first_obj_iso_pi_opens_π, category.assoc, ← F.map_comp]
  rfl

/-- Second naturality condition. Under the isomorphisms `first_obj_iso_pi_opens` and
`second_obj_iso_pi_inters`, the map `presheaf.second_map` corresponds to `right_res`.
-/
theorem first_obj_iso_comp_right_res_eq :
    Presheaf.secondMap R F ≫ (secondObjIsoPiInters F U R).Hom =
      (firstObjIsoPiOpens F U R).Hom ≫ rightRes F (coveringOfPresieve U R) :=
  by
  ext ⟨f, g⟩
  dunfold right_res presheaf.second_map
  rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π, limit.lift_π, fan.mk_π_app, limit.lift_π_assoc,
    fan.mk_π_app, ← category.assoc, first_obj_iso_pi_opens_π, category.assoc, ← F.map_comp]
  rfl

/-- The natural isomorphism between the sites diagram and the spaces diagram. -/
@[simps]
def diagramNatIso :
    parallelPair (Presheaf.firstMap R F) (Presheaf.secondMap R F) ≅ diagram F (coveringOfPresieve U R) :=
  (NatIso.ofComponents fun i =>
      WalkingParallelPair.casesOn i (firstObjIsoPiOpens F U R) (secondObjIsoPiInters F U R)) <|
    by
    intro i j f
    cases i
    · cases j
      · cases f
        simp
        
      · cases f
        · exact first_obj_iso_comp_left_res_eq F U R
          
        · exact first_obj_iso_comp_right_res_eq F U R
          
        
      
    · cases j
      · cases f
        
      · cases f
        simp
        
      

/-- Postcomposing the given fork of the _sites_ diagram with the natural isomorphism between the
diagrams gives us a fork of the _spaces_ diagram. We construct a morphism from this fork to the
given fork of the _spaces_ diagram. This is shown to be an isomorphism below.
-/
@[simps]
def postcomposeDiagramForkHom (hR : Sieve.generate R ∈ Opens.grothendieckTopology X U) :
    (Cones.postcompose (diagramNatIso F U R).Hom).obj (Fork.ofι _ (Presheaf.w R F)) ⟶ fork F (coveringOfPresieve U R) :=
  Fork.mkHom (F.map (eqToHom (supr_eq_of_mem_grothendieck U R hR)).op)
    (fork_map_comp_first_obj_iso_pi_opens_eq F U R hR).symm

instance is_iso_postcompose_diagram_fork_hom_hom (hR : Sieve.generate R ∈ Opens.grothendieckTopology X U) :
    IsIso (postcomposeDiagramForkHom F U R hR).Hom := by
  rw [postcompose_diagram_fork_hom_hom, eq_to_hom_map]
  apply eq_to_hom.is_iso

instance is_iso_postcompose_diagram_fork_hom (hR : Sieve.generate R ∈ Opens.grothendieckTopology X U) :
    IsIso (postcomposeDiagramForkHom F U R hR) :=
  Cones.cone_iso_of_hom_iso _

/-- See `postcompose_diagram_fork_hom`. -/
def postcomposeDiagramForkIso (hR : Sieve.generate R ∈ Opens.grothendieckTopology X U) :
    (Cones.postcompose (diagramNatIso F U R).Hom).obj (Fork.ofι _ (Presheaf.w R F)) ≅ fork F (coveringOfPresieve U R) :=
  asIso (postcomposeDiagramForkHom F U R hR)

end CoveringOfPresieve

theorem is_sheaf_sites_of_is_sheaf_spaces (Fsh : F.IsSheaf) : Presheaf.IsSheaf (Opens.grothendieckTopology X) F := by
  rw [presheaf.is_sheaf_iff_is_sheaf']
  intro U R hR
  refine' ⟨_⟩
  apply (is_limit.of_cone_equiv (cones.postcompose_equivalence (covering_of_presieve.diagram_nat_iso F U R : _))).toFun
  apply (is_limit.equiv_iso_limit (covering_of_presieve.postcompose_diagram_fork_iso F U R hR)).invFun
  exact (Fsh (covering_of_presieve U R)).some

/-- Given a family of opens `U : ι → opens X` and any open `Y : opens X`, we obtain a presieve
on `Y` by declaring that a morphism `f : V ⟶ Y` is a member of the presieve if and only if
there exists an index `i : ι` such that `V = U i`.
-/
def PresieveOfCoveringAux {ι : Type v} (U : ι → Opens X) (Y : Opens X) : Presieve Y := fun V f => ∃ i, V = U i

/-- Take `Y` to be `supr U` and obtain a presieve over `supr U`. -/
def PresieveOfCovering {ι : Type v} (U : ι → Opens X) : Presieve (supr U) :=
  PresieveOfCoveringAux U (supr U)

/-- Given a presieve `R` on `Y`, if we take its associated family of opens via
    `covering_of_presieve` (which may not cover `Y` if `R` is not covering), and take
    the presieve on `Y` associated to the family of opens via `presieve_of_covering_aux`,
    then we get back the original presieve `R`. -/
@[simp]
theorem covering_presieve_eq_self {Y : Opens X} (R : Presieve Y) :
    PresieveOfCoveringAux (coveringOfPresieve Y R) Y = R := by
  ext Z f
  exact
    ⟨fun ⟨⟨_, _, h⟩, rfl⟩ => by
      convert h, fun h => ⟨⟨Z, f, h⟩, rfl⟩⟩

namespace PresieveOfCovering

/-!
In this section, we will relate two different fork diagrams to each other.

The first one is the defining fork diagram for the sheaf condition in terms of spaces, applied to
the family of opens `U`. It will henceforth be called the _spaces diagram_. Its objects are called
`pi_opens` and `pi_inters` and its morphisms are `left_res` and `right_res`. The fork map into this
diagram is called `res`.

The second one is the defining fork diagram for the sheaf condition in terms of sites, applied to
the presieve `presieve_of_covering U`. It will henceforth be called the _sites diagram_. Its objects
are called `presheaf.first_obj` and `presheaf.second_obj` and its morphisms are `presheaf.first_map`
and `presheaf.second_obj`. The fork map into this diagram is called `presheaf.fork_map`.

-/


variable {ι : Type v} (U : ι → Opens X)

/-- The sieve generated by `presieve_of_covering U` is a member of the grothendieck topology.
-/
theorem mem_grothendieck_topology : Sieve.generate (PresieveOfCovering U) ∈ Opens.grothendieckTopology X (supr U) := by
  intro x hx
  obtain ⟨i, hxi⟩ := opens.mem_supr.mp hx
  exact ⟨U i, opens.le_supr U i, ⟨U i, 𝟙 _, opens.le_supr U i, ⟨i, rfl⟩, category.id_comp _⟩, hxi⟩

/-- An index `i : ι` can be turned into a dependent pair `(V, f)`, where `V` is an open set and
`f : V ⟶ supr U` is a member of `presieve_of_covering U f`.
-/
def homOfIndex (i : ι) : ΣV, { f : V ⟶ supr U // PresieveOfCovering U f } :=
  ⟨U i, Opens.leSupr U i, i, rfl⟩

/-- By using the axiom of choice, a dependent pair `(V, f)` where `f : V ⟶ supr U` is a member of
`presieve_of_covering U f` can be turned into an index `i : ι`, such that `V = U i`.
-/
def indexOfHom (f : ΣV, { f : V ⟶ supr U // PresieveOfCovering U f }) : ι :=
  f.2.2.some

theorem index_of_hom_spec (f : ΣV, { f : V ⟶ supr U // PresieveOfCovering U f }) : f.1 = U (indexOfHom U f) :=
  f.2.2.some_spec

/-- The canonical morphism from the first object in the sites diagram to the first object in the
spaces diagram. Note that this is *not* an isomorphism, as the product `pi_opens F U` may contain
duplicate factors, i.e. `U : ι → opens X` may not be injective.
-/
def firstObjToPiOpens : Presheaf.firstObj (PresieveOfCovering U) F ⟶ piOpens F U :=
  Pi.lift fun i => Pi.π _ (homOfIndex U i)

/-- The canonical morphism from the first object in the spaces diagram to the first object in the
sites diagram. Note that this is *not* an isomorphism, as the product `pi_opens F U` may contain
duplicate factors, i.e. `U : ι → opens X` may not be injective.
-/
def piOpensToFirstObj : piOpens F U ⟶ Presheaf.firstObj.{v, v, u} (PresieveOfCovering U) F :=
  Pi.lift fun f => Pi.π _ (indexOfHom U f) ≫ F.map (eqToHom (index_of_hom_spec U f)).op

/-- Even though `first_obj_to_pi_opens` and `pi_opens_to_first_obj` are not inverse to each other,
applying them both after a fork map `s.ι` does nothing. The intuition here is that a compatible
family `s : Π i : ι, F.obj (op (U i))` does not care about duplicate open sets:
If `U i = U j` the compatible family coincides on the intersection `U i ⊓ U j = U i = U j`,
hence `s i = s j` (module an `eq_to_hom` arrow).
-/
theorem fork_ι_comp_pi_opens_to_first_obj_to_pi_opens_eq (s : Limits.Fork (leftRes F U) (rightRes F U)) :
    s.ι ≫ piOpensToFirstObj F U ≫ firstObjToPiOpens F U = s.ι := by
  ext ⟨j⟩
  dunfold first_obj_to_pi_opens pi_opens_to_first_obj
  rw [category.assoc, category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app]
  -- The issue here is that `index_of_hom U (hom_of_index U j)` need not be equal to `j`.
  -- But `U j = U (index_of_hom U (hom_of_index U j))` and hence we obtain the following
  -- `eq_to_hom` arrow:
  have i_eq : U j ⟶ U j⊓U (index_of_hom U (hom_of_index U j)) := by
    apply eq_to_hom
    rw [← index_of_hom_spec U]
    exact inf_idem.symm
  -- Since `s` is a fork, we know that `s.ι ≫ left_res F U = s.ι ≫ right_res F U`.
  -- We compose both sides of this equality with the canonical projection at the index pair
  -- `(j, index_of_hom U (hom_of_index U j)` and the restriction along `i_eq`.
  have :=
    congr_arg
      (fun f =>
        f ≫ pi.π (fun p : ι × ι => F.obj (op (U p.1⊓U p.2))) (j, index_of_hom U (hom_of_index U j)) ≫ F.map i_eq.op)
      s.condition
  dsimp'  at this
  rw [category.assoc, category.assoc] at this
  symm
  -- We claim that this is equality is our goal
  convert this using 2
  · dunfold left_res
    rw [limit.lift_π_assoc, fan.mk_π_app, category.assoc, ← F.map_comp]
    erw [F.map_id]
    rw [category.comp_id]
    
  · dunfold right_res
    rw [limit.lift_π_assoc, fan.mk_π_app, category.assoc, ← F.map_comp]
    congr
    

/-- The canonical morphism from the second object of the spaces diagram to the second object of the
sites diagram.
-/
def piIntersToSecondObj : piInters F U ⟶ Presheaf.secondObj.{v, v, u} (PresieveOfCovering U) F :=
  Pi.lift fun f =>
    Pi.π _ (indexOfHom U f.fst, indexOfHom U f.snd) ≫
      F.map
        (eqToHom
            (by
              rw [complete_lattice.pullback_eq_inf, ← index_of_hom_spec U, ← index_of_hom_spec U])).op

theorem pi_opens_to_first_obj_comp_fist_map_eq :
    piOpensToFirstObj F U ≫ Presheaf.firstMap (PresieveOfCovering U) F = leftRes F U ≫ piIntersToSecondObj F U := by
  ext ⟨f, g⟩
  dunfold pi_opens_to_first_obj presheaf.first_map left_res pi_inters_to_second_obj
  rw [category.assoc, category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ← category.assoc, ←
    category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, category.assoc, category.assoc, ←
    F.map_comp, ← F.map_comp]
  rfl

theorem pi_opens_to_first_obj_comp_second_map_eq :
    piOpensToFirstObj F U ≫ Presheaf.secondMap (PresieveOfCovering U) F = rightRes F U ≫ piIntersToSecondObj F U := by
  ext ⟨f, g⟩
  dunfold pi_opens_to_first_obj presheaf.second_map right_res pi_inters_to_second_obj
  rw [category.assoc, category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ← category.assoc, ←
    category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, category.assoc, category.assoc, ←
    F.map_comp, ← F.map_comp]
  rfl

theorem fork_map_comp_first_map_to_pi_opens_eq :
    Presheaf.forkMap (PresieveOfCovering U) F ≫ firstObjToPiOpens F U = res F U := by
  ext i
  dsimp' [← presheaf.fork_map, ← first_obj_to_pi_opens, ← res]
  rw [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app]
  rfl

theorem res_comp_pi_opens_to_first_obj_eq :
    res F U ≫ piOpensToFirstObj F U = Presheaf.forkMap (PresieveOfCovering U) F := by
  ext f
  dunfold res pi_opens_to_first_obj presheaf.fork_map
  rw [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ← category.assoc, limit.lift_π,
    fan.mk_π_app, ← F.map_comp]
  congr

end PresieveOfCovering

open PresieveOfCovering

theorem is_sheaf_spaces_of_is_sheaf_sites (Fsh : Presheaf.IsSheaf (Opens.grothendieckTopology X) F) : F.IsSheaf := by
  intro ι U
  rw [presheaf.is_sheaf_iff_is_sheaf'] at Fsh
  -- We know that the sites diagram for `presieve_of_covering U` is a limit fork
  obtain ⟨h_limit⟩ := Fsh (supr U) (presieve_of_covering U) (presieve_of_covering.mem_grothendieck_topology U)
  refine' ⟨fork.is_limit.mk' _ _⟩
  -- Here, we are given an arbitrary fork of the spaces diagram and need to show that it factors
  -- uniquely through our limit fork.
  intro s
  -- Composing `s.ι` with `pi_opens_to_first_obj F U` gives a fork of the sites diagram, which
  -- must factor through `presheaf.fork_map`.
  obtain ⟨l, hl⟩ := fork.is_limit.lift' h_limit (s.ι ≫ pi_opens_to_first_obj F U) _
  swap
  · rw [category.assoc, category.assoc, pi_opens_to_first_obj_comp_fist_map_eq,
      pi_opens_to_first_obj_comp_second_map_eq, ← category.assoc, ← category.assoc, s.condition]
    
  -- We claim that `l` also gives a factorization of `s.ι`
  refine' ⟨l, _, _⟩
  · rw [← fork_ι_comp_pi_opens_to_first_obj_to_pi_opens_eq F U s, ← category.assoc, ← hl, category.assoc, fork.ι_of_ι,
      fork_map_comp_first_map_to_pi_opens_eq]
    rfl
    
  · intro m hm
    apply fork.is_limit.hom_ext h_limit
    rw [hl, fork.ι_of_ι]
    simp_rw [← res_comp_pi_opens_to_first_obj_eq]
    erw [← category.assoc, hm]
    

theorem is_sheaf_sites_iff_is_sheaf_spaces : Presheaf.IsSheaf (Opens.grothendieckTopology X) F ↔ F.IsSheaf :=
  Iff.intro (is_sheaf_spaces_of_is_sheaf_sites F) (is_sheaf_sites_of_is_sheaf_spaces F)

variable (C X)

/-- Turn a sheaf on the site `opens X` into a sheaf on the space `X`. -/
@[simps]
def sheafSitesToSheafSpaces : Sheaf (Opens.grothendieckTopology X) C ⥤ Sheaf C X where
  obj := fun F => ⟨F.1, is_sheaf_spaces_of_is_sheaf_sites F.1 F.2⟩
  map := fun F G f => f.val

/-- Turn a sheaf on the space `X` into a sheaf on the site `opens X`. -/
@[simps]
def sheafSpacesToSheafSites : Sheaf C X ⥤ Sheaf (Opens.grothendieckTopology X) C where
  obj := fun F => ⟨F.1, is_sheaf_sites_of_is_sheaf_spaces F.1 F.2⟩
  map := fun F G f => ⟨f⟩

/-- The equivalence of categories between sheaves on the site `opens X` and sheaves on the space `X`.
-/
@[simps]
def sheafSpacesEquivSheafSites : Sheaf (Opens.grothendieckTopology X) C ≌ Sheaf C X where
  Functor := sheafSitesToSheafSpaces C X
  inverse := sheafSpacesToSheafSites C X
  unitIso :=
    (NatIso.ofComponents fun t =>
        ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by
          ext1
          simp , by
          ext1
          simp ⟩) <|
      by
      intros
      ext1
      dsimp'
      simp
  counitIso :=
    (NatIso.ofComponents fun t =>
        ⟨𝟙 _, 𝟙 _, by
          ext
          simp , by
          ext
          simp ⟩) <|
      by
      intros
      ext
      dsimp'
      simp

/-- The two forgetful functors are isomorphic via `Sheaf_spaces_equiv_sheaf_sites`. -/
def sheafSpacesEquivSheafSitesFunctorForget :
    (sheafSpacesEquivSheafSites C X).Functor ⋙ Sheaf.forget C X ≅ sheafToPresheaf _ _ :=
  NatIso.ofComponents (fun F => Iso.refl F.1) fun F G f => by
    erw [category.comp_id, category.id_comp]
    rfl

/-- The two forgetful functors are isomorphic via `Sheaf_spaces_equiv_sheaf_sites`. -/
def sheafSpacesEquivSheafSitesInverseForget :
    (sheafSpacesEquivSheafSites C X).inverse ⋙ sheafToPresheaf _ _ ≅ Sheaf.forget C X :=
  NatIso.ofComponents (fun F => Iso.refl F.1) fun F G f => by
    erw [category.comp_id, category.id_comp]
    rfl

end Top.Presheaf

namespace Top.Opens

open CategoryTheory TopologicalSpace

variable {X : Top} {ι : Type _}

theorem cover_dense_iff_is_basis [Category ι] (B : ι ⥤ Opens X) :
    CoverDense (Opens.grothendieckTopology X) B ↔ Opens.IsBasis (Set.Range B.obj) := by
  rw [opens.is_basis_iff_nbhd]
  constructor
  intro hd U x hx
  rcases hd.1 U x hx with ⟨V, f, ⟨i, f₁, f₂, hc⟩, hV⟩
  exact ⟨B.obj i, ⟨i, rfl⟩, f₁.le hV, f₂.le⟩
  intro hb
  constructor
  intro U x hx
  rcases hb hx with ⟨_, ⟨i, rfl⟩, hx, hi⟩
  exact ⟨B.obj i, ⟨⟨hi⟩⟩, ⟨⟨i, 𝟙 _, ⟨⟨hi⟩⟩, rfl⟩⟩, hx⟩

theorem cover_dense_induced_functor {B : ι → Opens X} (h : Opens.IsBasis (Set.Range B)) :
    CoverDense (Opens.grothendieckTopology X) (inducedFunctor B) :=
  (cover_dense_iff_is_basis _).2 h

end Top.Opens

namespace Top.Sheaf

open CategoryTheory TopologicalSpace Top Opposite

variable {C : Type u} [Category.{v} C] [Limits.HasProducts.{v} C]

variable {X : Top.{v}} {ι : Type _} {B : ι → Opens X}

variable (F : Presheaf C X) (F' : Sheaf C X) (h : Opens.IsBasis (Set.Range B))

/-- The empty component of a sheaf is terminal -/
def isTerminalOfEmpty (F : Sheaf C X) : Limits.IsTerminal (F.val.obj (op ∅)) :=
  ((Presheaf.sheafSpacesToSheafSites C X).obj F).isTerminalOfBotCover ∅
    (by
      tidy)

/-- A variant of `is_terminal_of_empty` that is easier to `apply`. -/
def isTerminalOfEqEmpty (F : X.Sheaf C) {U : Opens X} (h : U = ∅) : Limits.IsTerminal (F.val.obj (op U)) := by
  convert F.is_terminal_of_empty

/-- If a family `B` of open sets forms a basis of the topology on `X`, and if `F'`
    is a sheaf on `X`, then a homomorphism between a presheaf `F` on `X` and `F'`
    is equivalent to a homomorphism between their restrictions to the indexing type
    `ι` of `B`, with the induced category structure on `ι`. -/
def restrictHomEquivHom : ((inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) ≃ (F ⟶ F'.1) :=
  @CoverDense.restrictHomEquivHom _ _ _ _ _ _ _ _ (Opens.cover_dense_induced_functor h) _ F
    ((Presheaf.sheafSpacesToSheafSites C X).obj F')

@[simp]
theorem extend_hom_app (α : (inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) (i : ι) :
    (restrictHomEquivHom F F' h α).app (op (B i)) = α.app (op i) := by
  nth_rw 1[← (restrict_hom_equiv_hom F F' h).left_inv α]
  rfl

include h

theorem hom_ext {α β : F ⟶ F'.1} (he : ∀ i, α.app (op (B i)) = β.app (op (B i))) : α = β := by
  apply (restrict_hom_equiv_hom F F' h).symm.Injective
  ext i
  exact he i.unop

end Top.Sheaf

