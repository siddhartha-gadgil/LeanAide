/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Order.OmegaCompletePartialOrder
import Mathbin.Order.Category.Preorder
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Category of types with a omega complete partial order

In this file, we bundle the class `omega_complete_partial_order` into a
concrete category and prove that continuous functions also form
a `omega_complete_partial_order`.

## Main definitions

 * `ωCPO`
   * an instance of `category` and `concrete_category`

 -/


open CategoryTheory

universe u v

/-- The category of types with a omega complete partial order. -/
def ωCPO : Type (u + 1) :=
  Bundled OmegaCompletePartialOrder

namespace ωCPO

open OmegaCompletePartialOrder

instance : BundledHom @ContinuousHom where
  toFun := @ContinuousHom.Simps.apply
  id := @ContinuousHom.id
  comp := @ContinuousHom.comp
  hom_ext := @ContinuousHom.coe_inj

deriving instance LargeCategory, ConcreteCategory for ωCPO

instance : CoeSort ωCPO (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type _) [OmegaCompletePartialOrder α] : ωCPO :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [OmegaCompletePartialOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited ωCPO :=
  ⟨of PUnit⟩

instance (α : ωCPO) : OmegaCompletePartialOrder α :=
  α.str

section

open CategoryTheory.Limits

namespace HasProducts

/-- The pi-type gives a cone for a product. -/
def product {J : Type v} (f : J → ωCPO.{v}) : Fan f :=
  Fan.mk (of (∀ j, f j)) fun j => ContinuousHom.ofMono (Pi.evalOrderHom j) fun c => rfl

/-- The pi-type is a limit cone for the product. -/
def isProduct (J : Type v) (f : J → ωCPO) : IsLimit (product f) where
  lift := fun s =>
    ⟨⟨fun t j => s.π.app ⟨j⟩ t, fun x y h j => (s.π.app ⟨j⟩).Monotone h⟩, fun x =>
      funext fun j => (s.π.app ⟨j⟩).Continuous x⟩
  uniq' := fun s m w => by
    ext t j
    change m t j = s.π.app ⟨j⟩ t
    rw [← w ⟨j⟩]
    rfl
  fac' := fun s j => by
    cases j
    tidy

instance (J : Type v) (f : J → ωCPO.{v}) : HasProduct f :=
  HasLimit.mk ⟨_, isProduct _ f⟩

end HasProducts

instance omegaCompletePartialOrderEqualizer {α β : Type _} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α →𝒄 β) : OmegaCompletePartialOrder { a : α // f a = g a } :=
  (OmegaCompletePartialOrder.subtype _) fun c hc => by
    rw [f.continuous, g.continuous]
    congr 1
    ext
    apply hc _ ⟨_, rfl⟩

namespace HasEqualizers

/-- The equalizer inclusion function as a `continuous_hom`. -/
def equalizerι {α β : Type _} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] (f g : α →𝒄 β) :
    { a : α // f a = g a } →𝒄 α :=
  ContinuousHom.ofMono (OrderHom.Subtype.val _) fun c => rfl

/-- A construction of the equalizer fork. -/
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : Fork f g :=
  @Fork.ofι _ _ _ _ _ _ (ωCPO.of { a // f a = g a }) (equalizerι f g) (ContinuousHom.ext _ _ fun x => x.2)

/-- The equalizer fork is a limit. -/
def isEqualizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : IsLimit (equalizer f g) :=
  (Fork.IsLimit.mk' _) fun s =>
    ⟨{ toFun := fun x =>
          ⟨s.ι x, by
            apply continuous_hom.congr_fun s.condition⟩,
        monotone' := fun x y h => s.ι.Monotone h, cont := fun x => Subtype.ext (s.ι.Continuous x) },
      by
      ext
      rfl, fun m hm => by
      ext
      apply continuous_hom.congr_fun hm⟩

end HasEqualizers

instance : HasProducts.{v} ωCPO.{v} := fun J => { HasLimit := fun F => has_limit_of_iso Discrete.natIsoFunctor.symm }

instance {X Y : ωCPO.{v}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨_, HasEqualizers.isEqualizer f g⟩

instance : HasEqualizers ωCPO.{v} :=
  has_equalizers_of_has_limit_parallel_pair _

instance : HasLimits ωCPO.{v} :=
  limits_from_equalizers_and_products

end

end ωCPO

