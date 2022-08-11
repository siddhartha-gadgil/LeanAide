/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Limits.Shapes.NormalMono.Basic
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Normal mono categories with finite products and kernels have all equalizers.

This, and the dual result, are used in the development of abelian categories.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type _} [Category C] [HasZeroMorphisms C]

namespace CategoryTheory.NormalMonoCategory

variable [HasFiniteProducts C] [HasKernels C] [NormalMonoCategory C]

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The pullback of two monomorphisms exists. -/
irreducible_def pullback_of_mono {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Mono a] [Mono b] : HasLimit (cospan a b) :=
  let ⟨P, f, haf, i⟩ := normalMonoOfMono a
  let ⟨Q, g, hbg, i'⟩ := normalMonoOfMono b
  let ⟨a', ha'⟩ :=
    KernelFork.IsLimit.lift' i (kernel.ι (prod.lift f g)) <|
      calc
        kernel.ι (prod.lift f g) ≫ f = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ limits.prod.fst := by
          rw [prod.lift_fst]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ limits.prod.fst := by
          rw [kernel.condition_assoc]
        _ = 0 := zero_comp
        
  let ⟨b', hb'⟩ :=
    KernelFork.IsLimit.lift' i' (kernel.ι (prod.lift f g)) <|
      calc
        kernel.ι (prod.lift f g) ≫ g = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ limits.prod.snd := by
          rw [prod.lift_snd]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ limits.prod.snd := by
          rw [kernel.condition_assoc]
        _ = 0 := zero_comp
        
  HasLimit.mk
    { Cone :=
        PullbackCone.mk a' b' <| by
          simp at ha' hb'
          rw [ha', hb'],
      IsLimit :=
        PullbackCone.IsLimit.mk _
          (fun s =>
            kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b) <|
              prod.hom_ext
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ limits.prod.fst = PullbackCone.snd s ≫ b ≫ f := by
                    simp only [← prod.lift_fst, ← category.assoc]
                  _ = PullbackCone.fst s ≫ a ≫ f := by
                    rw [pullback_cone.condition_assoc]
                  _ = PullbackCone.fst s ≫ 0 := by
                    rw [haf]
                  _ = 0 ≫ limits.prod.fst := by
                    rw [comp_zero, zero_comp]
                  )
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ limits.prod.snd = PullbackCone.snd s ≫ b ≫ g := by
                    simp only [← prod.lift_snd, ← category.assoc]
                  _ = PullbackCone.snd s ≫ 0 := by
                    rw [hbg]
                  _ = 0 ≫ limits.prod.snd := by
                    rw [comp_zero, zero_comp]
                  ))
          (fun s =>
            (cancel_mono a).1 <| by
              rw [kernel_fork.ι_of_ι] at ha'
              simp [← ha', ← pullback_cone.condition s])
          (fun s =>
            (cancel_mono b).1 <| by
              rw [kernel_fork.ι_of_ι] at hb'
              simp [← hb'])
          fun s m h₁ h₂ =>
          (cancel_mono (kernel.ι (prod.lift f g))).1 <|
            calc
              m ≫ kernel.ι (prod.lift f g) = m ≫ a' ≫ a := by
                congr
                exact ha'.symm
              _ = PullbackCone.fst s ≫ a := by
                rw [← category.assoc, h₁]
              _ = PullbackCone.snd s ≫ b := PullbackCone.condition s
              _ = kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b) _ ≫ kernel.ι (prod.lift f g) := by
                rw [kernel.lift_ι]
               }

section

attribute [local instance] pullback_of_mono

/-- The pullback of `(𝟙 X, f)` and `(𝟙 X, g)` -/
private abbrev P {X Y : C} (f g : X ⟶ Y) [Mono (prod.lift (𝟙 X) f)] [Mono (prod.lift (𝟙 X) g)] : C :=
  pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The equalizer of `f` and `g` exists. -/
irreducible_def has_limit_parallel_pair {X Y : C} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  have huv : (pullback.fst : p f g ⟶ X) = pullback.snd :=
    calc
      (pullback.fst : p f g ⟶ X) = pullback.fst ≫ 𝟙 _ := Eq.symm <| Category.comp_id _
      _ = pullback.fst ≫ prod.lift (𝟙 X) f ≫ limits.prod.fst := by
        rw [prod.lift_fst]
      _ = pullback.snd ≫ prod.lift (𝟙 X) g ≫ limits.prod.fst := by
        rw [pullback.condition_assoc]
      _ = pullback.snd := by
        rw [prod.lift_fst, category.comp_id]
      
  have hvu : (pullback.fst : p f g ⟶ X) ≫ f = pullback.snd ≫ g :=
    calc
      (pullback.fst : p f g ⟶ X) ≫ f = pullback.fst ≫ prod.lift (𝟙 X) f ≫ limits.prod.snd := by
        rw [prod.lift_snd]
      _ = pullback.snd ≫ prod.lift (𝟙 X) g ≫ limits.prod.snd := by
        rw [pullback.condition_assoc]
      _ = pullback.snd ≫ g := by
        rw [prod.lift_snd]
      
  have huu : (pullback.fst : p f g ⟶ X) ≫ f = pullback.fst ≫ g := by
    rw [hvu, ← huv]
  HasLimit.mk
    { Cone := Fork.ofι pullback.fst huu,
      IsLimit :=
        Fork.IsLimit.mk _
          (fun s =>
            pullback.lift (Fork.ι s) (Fork.ι s) <|
              prod.hom_ext
                (by
                  simp only [← prod.lift_fst, ← category.assoc])
                (by
                  simp only [← prod.comp_lift, ← fork.condition]))
          (fun s => by
            simp only [← fork.ι_of_ι, ← pullback.lift_fst])
          fun s m h =>
          pullback.hom_ext
            (by
              simpa only [← pullback.lift_fst] using h)
            (by
              simpa only [← huv.symm, ← pullback.lift_fst] using h) }

end

section

attribute [local instance] has_limit_parallel_pair

/-- A `normal_mono_category` category with finite products and kernels has all equalizers. -/
instance (priority := 100) has_equalizers : HasEqualizers C :=
  has_equalizers_of_has_limit_parallel_pair _

end

/-- If a zero morphism is a cokernel of `f`, then `f` is an epimorphism. -/
theorem epi_of_zero_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l :
      IsColimit
        (CokernelCofork.ofπ (0 : Y ⟶ Z)
          (show f ≫ 0 = 0 by
            simp ))) :
    Epi f :=
  ⟨fun P u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normal_mono_of_mono (equalizer.ι u v)
    obtain ⟨m, hm⟩ := equalizer.lift' f huv
    have hwf : f ≫ w = 0 := by
      rw [← hm, category.assoc, hw, comp_zero]
    obtain ⟨n, hn⟩ := cokernel_cofork.is_colimit.desc' l _ hwf
    rw [cofork.π_of_π, zero_comp] at hn
    have : is_iso (equalizer.ι u v) := by
      apply is_iso_limit_cone_parallel_pair_of_eq hn.symm hl
    apply (cancel_epi (equalizer.ι u v)).1
    exact equalizer.condition _ _⟩

section

variable [HasZeroObject C]

open ZeroObject

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `g` is a monomorphism. -/
theorem epi_of_zero_cancel {X Y : C} (f : X ⟶ Y) (hf : ∀ (Z : C) (g : Y ⟶ Z) (hgf : f ≫ g = 0), g = 0) : Epi f :=
  epi_of_zero_cokernel f 0 <| zeroCokernelOfZeroCancel f hf

end

end CategoryTheory.NormalMonoCategory

namespace CategoryTheory.NormalEpiCategory

variable [HasFiniteCoproducts C] [HasCokernels C] [NormalEpiCategory C]

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The pushout of two epimorphisms exists. -/
irreducible_def pushout_of_epi {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Epi a] [Epi b] : HasColimit (span a b) :=
  let ⟨P, f, hfa, i⟩ := normalEpiOfEpi a
  let ⟨Q, g, hgb, i'⟩ := normalEpiOfEpi b
  let ⟨a', ha'⟩ :=
    CokernelCofork.IsColimit.desc' i (cokernel.π (coprod.desc f g)) <|
      calc
        f ≫ cokernel.π (coprod.desc f g) = coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inl_desc_assoc]
        _ = coprod.inl ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by
          rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _
        
  let ⟨b', hb'⟩ :=
    CokernelCofork.IsColimit.desc' i' (cokernel.π (coprod.desc f g)) <|
      calc
        g ≫ cokernel.π (coprod.desc f g) = coprod.inr ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inr_desc_assoc]
        _ = coprod.inr ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by
          rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _
        
  HasColimit.mk
    { Cocone :=
        PushoutCocone.mk a' b' <| by
          simp only [← cofork.π_of_π] at ha' hb'
          rw [ha', hb'],
      IsColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s =>
            cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s) <|
              coprod.hom_ext
                (calc
                  coprod.inl ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s = f ≫ b ≫ PushoutCocone.inr s := by
                    rw [coprod.inl_desc_assoc]
                  _ = f ≫ a ≫ PushoutCocone.inl s := by
                    rw [pushout_cocone.condition]
                  _ = 0 ≫ PushoutCocone.inl s := by
                    rw [reassoc_of hfa]
                  _ = coprod.inl ≫ 0 := by
                    rw [comp_zero, zero_comp]
                  )
                (calc
                  coprod.inr ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s = g ≫ b ≫ PushoutCocone.inr s := by
                    rw [coprod.inr_desc_assoc]
                  _ = 0 ≫ PushoutCocone.inr s := by
                    rw [reassoc_of hgb]
                  _ = coprod.inr ≫ 0 := by
                    rw [comp_zero, zero_comp]
                  ))
          (fun s =>
            (cancel_epi a).1 <| by
              rw [cokernel_cofork.π_of_π] at ha'
              simp [← reassoc_of ha', ← pushout_cocone.condition s])
          (fun s =>
            (cancel_epi b).1 <| by
              rw [cokernel_cofork.π_of_π] at hb'
              simp [← reassoc_of hb'])
          fun s m h₁ h₂ =>
          (cancel_epi (cokernel.π (coprod.desc f g))).1 <|
            calc
              cokernel.π (coprod.desc f g) ≫ m = (a ≫ a') ≫ m := by
                congr
                exact ha'.symm
              _ = a ≫ PushoutCocone.inl s := by
                rw [category.assoc, h₁]
              _ = b ≫ PushoutCocone.inr s := PushoutCocone.condition s
              _ = cokernel.π (coprod.desc f g) ≫ cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s) _ := by
                rw [cokernel.π_desc]
               }

section

attribute [local instance] pushout_of_epi

/-- The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`. -/
private abbrev Q {X Y : C} (f g : X ⟶ Y) [Epi (coprod.desc (𝟙 Y) f)] [Epi (coprod.desc (𝟙 Y) g)] : C :=
  pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The coequalizer of `f` and `g` exists. -/
irreducible_def has_colimit_parallel_pair {X Y : C} (f g : X ⟶ Y) : HasColimit (parallelPair f g) :=
  have huv : (pushout.inl : Y ⟶ q f g) = pushout.inr :=
    calc
      (pushout.inl : Y ⟶ q f g) = 𝟙 _ ≫ pushout.inl := Eq.symm <| Category.id_comp _
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl := by
        rw [coprod.inl_desc]
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr := by
        simp only [← category.assoc, ← pushout.condition]
      _ = pushout.inr := by
        rw [coprod.inl_desc, category.id_comp]
      
  have hvu : f ≫ (pushout.inl : Y ⟶ q f g) = g ≫ pushout.inr :=
    calc
      f ≫ (pushout.inl : Y ⟶ q f g) = (coprod.inr ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl := by
        rw [coprod.inr_desc]
      _ = (coprod.inr ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr := by
        simp only [← category.assoc, ← pushout.condition]
      _ = g ≫ pushout.inr := by
        rw [coprod.inr_desc]
      
  have huu : f ≫ (pushout.inl : Y ⟶ q f g) = g ≫ pushout.inl := by
    rw [hvu, huv]
  HasColimit.mk
    { Cocone := Cofork.ofπ pushout.inl huu,
      IsColimit :=
        Cofork.IsColimit.mk _
          (fun s =>
            pushout.desc (Cofork.π s) (Cofork.π s) <|
              coprod.hom_ext
                (by
                  simp only [← coprod.inl_desc_assoc])
                (by
                  simp only [← coprod.desc_comp, ← cofork.condition]))
          (fun s => by
            simp only [← pushout.inl_desc, ← cofork.π_of_π])
          fun s m h =>
          pushout.hom_ext
            (by
              simpa only [← pushout.inl_desc] using h)
            (by
              simpa only [← huv.symm, ← pushout.inl_desc] using h) }

end

section

attribute [local instance] has_colimit_parallel_pair

/-- A `normal_epi_category` category with finite coproducts and cokernels has all coequalizers. -/
instance (priority := 100) has_coequalizers : HasCoequalizers C :=
  has_coequalizers_of_has_colimit_parallel_pair _

end

/-- If a zero morphism is a kernel of `f`, then `f` is a monomorphism. -/
theorem mono_of_zero_kernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l :
      IsLimit
        (KernelFork.ofι (0 : Z ⟶ X)
          (show 0 ≫ f = 0 by
            simp ))) :
    Mono f :=
  ⟨fun P u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normal_epi_of_epi (coequalizer.π u v)
    obtain ⟨m, hm⟩ := coequalizer.desc' f huv
    have hwf : w ≫ f = 0 := by
      rw [← hm, reassoc_of hw, zero_comp]
    obtain ⟨n, hn⟩ := kernel_fork.is_limit.lift' l _ hwf
    rw [fork.ι_of_ι, has_zero_morphisms.comp_zero] at hn
    have : is_iso (coequalizer.π u v) := by
      apply is_iso_colimit_cocone_parallel_pair_of_eq hn.symm hl
    apply (cancel_mono (coequalizer.π u v)).1
    exact coequalizer.condition _ _⟩

section

variable [HasZeroObject C]

open ZeroObject

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `f` is a monomorphism. -/
theorem mono_of_cancel_zero {X Y : C} (f : X ⟶ Y) (hf : ∀ (Z : C) (g : Z ⟶ X) (hgf : g ≫ f = 0), g = 0) : Mono f :=
  mono_of_zero_kernel f 0 <| zeroKernelOfCancelZero f hf

end

end CategoryTheory.NormalEpiCategory

