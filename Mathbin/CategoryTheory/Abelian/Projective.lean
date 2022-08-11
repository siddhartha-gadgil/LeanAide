/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathbin.CategoryTheory.Abelian.Exact
import Mathbin.CategoryTheory.Preadditive.ProjectiveResolution

/-!
# Abelian categories with enough projectives have projective resolutions

When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

open CategoryTheory.Projective

variable {C : Type u} [Category.{v} C]

section

variable [EnoughProjectives C] [Abelian C]

/-- When `C` is abelian, `projective.d f` and `f` are exact.
-/
theorem exact_d_f {X Y : C} (f : X ⟶ Y) : Exact (d f) f :=
  (Abelian.exact_iff _ _).2 <|
    ⟨by
      simp ,
      zero_of_epi_comp (π _) <| by
        rw [← category.assoc, cokernel.condition]⟩

end

namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `projective.syzygies`
applied to the previously constructed morphism,
and the map to the `n`-th object as `projective.d`.
-/


variable [Abelian C] [EnoughProjectives C]

/-- Auxiliary definition for `ProjectiveResolution.of`. -/
@[simps]
def ofComplex (Z : C) : ChainComplex C ℕ :=
  ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z)) (Projective.d (Projective.π Z))
    fun ⟨X, Y, f⟩ => ⟨Projective.syzygies f, Projective.d f, (exact_d_f f).w⟩

/-- In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projective resolution of the object `Z`.
-/
irreducible_def of (Z : C) : ProjectiveResolution Z :=
  { complex := ofComplex Z,
    π :=
      ChainComplex.mkHom _ _ (Projective.π Z) 0
        (by
          simp
          exact (exact_d_f (projective.π Z)).w.symm)
        fun n _ =>
        ⟨0, by
          ext⟩,
    Projective := by
      rintro (_ | _ | _ | n) <;> apply projective.projective_over,
    exact₀ := by
      simpa using exact_d_f (projective.π Z),
    exact := by
      rintro (_ | n) <;>
        · simp
          apply exact_d_f
          ,
    Epi := Projective.π_epi Z }

instance (priority := 100) (Z : C) : HasProjectiveResolution Z where out := ⟨of Z⟩

instance (priority := 100) :
    HasProjectiveResolutions C where out := fun Z => by
    infer_instance

end ProjectiveResolution

end CategoryTheory

