/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Data.Set.Intervals.OrdConnected
import Mathbin.Order.Filter.SmallSets
import Mathbin.Order.Filter.AtTopBot

/-!
# Convergence of intervals

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.small_sets`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`.  Here and
below `Ixx` is one of `Icc`, `Ico`, `Ioc`, and `Ioo`. We define `filter.tendsto_Ixx_class Ixx l₁ l₂`
to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic a) (𝓟 $ Iio a)`,
i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁ n) (u₂ n)` is
eventually included in `Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `topology/algebra/ordered`.

| Input filter |  `Ixx = Icc`  |  `Ixx = Ico`  |  `Ixx = Ioc`  |  `Ixx = Ioo`  |
| -----------: | :-----------: | :-----------: | :-----------: | :-----------: |
|     `at_top` |    `at_top`   |    `at_top`   |    `at_top`   |    `at_top`   |
|     `at_bot` |    `at_bot`   |    `at_bot`   |    `at_bot`   |    `at_bot`   |
|     `pure a` |    `pure a`   |      `⊥`      |      `⊥`      |      `⊥`      |
|  `𝓟 (Iic a)` |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |
|  `𝓟 (Ici a)` |  `𝓟 (Ici a)`  |  `𝓟 (Ici a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Ioi a)` |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Iio a)` |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |
|        `𝓝 a` |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |
| `𝓝[Iic a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |
| `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |

-/


variable {α β : Type _}

open Classical Filter Interval

open Set Function

namespace Filter

section Preorderₓ

variable [Preorderₓ α]

/-- A pair of filters `l₁`, `l₂` has `tendsto_Ixx_class Ixx` property if `Ixx a b` tends to
`l₂.small_sets` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `Icc`, `Ico`, `Ioc`,
or `Ioo`. The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but
sometimes we can drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic
a) (𝓟 $ Iio a)`, i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁
n) (u₂ n)` is eventually included in `Iio a`.

We mark `l₂` as an `out_param` so that Lean can automatically find an appropriate `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying explicitly `l₂`. -/
class TendstoIxxClass (Ixx : α → α → Set α) (l₁ : Filter α) (l₂ : outParam <| Filter α) : Prop where
  tendsto_Ixx : Tendsto (fun p : α × α => Ixx p.1 p.2) (l₁ ×ᶠ l₁) l₂.smallSets

theorem Tendsto.Icc {l₁ l₂ : Filter α} [TendstoIxxClass Icc l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) : Tendsto (fun x => Icc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂

theorem Tendsto.Ioc {l₁ l₂ : Filter α} [TendstoIxxClass Ioc l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) : Tendsto (fun x => Ioc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂

theorem Tendsto.Ico {l₁ l₂ : Filter α} [TendstoIxxClass Ico l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) : Tendsto (fun x => Ico (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂

theorem Tendsto.Ioo {l₁ l₂ : Filter α} [TendstoIxxClass Ioo l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) : Tendsto (fun x => Ioo (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » s)
theorem tendsto_Ixx_class_principal {s t : Set α} {Ixx : α → α → Set α} :
    TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ ∀ (x y) (_ : x ∈ s) (_ : y ∈ s), Ixx x y ⊆ t :=
  Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ <| by
    simp only [← small_sets_principal, ← prod_principal_principal, ← tendsto_principal_principal, ← forall_prod_set, ←
      mem_powerset_iff, ← mem_principal]

theorem tendsto_Ixx_class_inf {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : TendstoIxxClass Ixx l₁ l₂]
    [h' : TendstoIxxClass Ixx l₁' l₂'] : TendstoIxxClass Ixx (l₁⊓l₁') (l₂⊓l₂') :=
  ⟨by
    simpa only [← prod_inf_prod, ← small_sets_inf] using h.1.inf h'.1⟩

theorem tendsto_Ixx_class_of_subset {l₁ l₂ : Filter α} {Ixx Ixx' : α → α → Set α} (h : ∀ a b, Ixx a b ⊆ Ixx' a b)
    [h' : TendstoIxxClass Ixx' l₁ l₂] : TendstoIxxClass Ixx l₁ l₂ :=
  ⟨h'.1.small_sets_mono <| eventually_of_forall <| Prod.forall.2 h⟩

theorem HasBasis.tendsto_Ixx_class {ι : Type _} {p : ι → Prop} {s} {l : Filter α} (hl : l.HasBasis p s)
    {Ixx : α → α → Set α} (H : ∀ i, p i → ∀, ∀ x ∈ s i, ∀, ∀ y ∈ s i, ∀, Ixx x y ⊆ s i) : TendstoIxxClass Ixx l l :=
  ⟨(hl.prod_self.tendsto_iff hl.smallSets).2 fun i hi => ⟨i, hi, fun x hx => H i hi _ hx.1 _ hx.2⟩⟩

instance tendsto_Icc_at_top_at_top : TendstoIxxClass Icc (atTop : Filter α) atTop :=
  (has_basis_infi_principal_finite _).TendstoIxxClass fun s hs =>
    Set.OrdConnected.out <| ord_connected_bInter fun i hi => ord_connected_Ici

instance tendsto_Ico_at_top_at_top : TendstoIxxClass Ico (atTop : Filter α) atTop :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_at_top_at_top : TendstoIxxClass Ioc (atTop : Filter α) atTop :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_at_top_at_top : TendstoIxxClass Ioo (atTop : Filter α) atTop :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Icc_self

instance tendsto_Icc_at_bot_at_bot : TendstoIxxClass Icc (atBot : Filter α) atBot :=
  (has_basis_infi_principal_finite _).TendstoIxxClass fun s hs =>
    Set.OrdConnected.out <| ord_connected_bInter fun i hi => ord_connected_Iic

instance tendsto_Ico_at_bot_at_bot : TendstoIxxClass Ico (atBot : Filter α) atBot :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_at_bot_at_bot : TendstoIxxClass Ioc (atBot : Filter α) atBot :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_at_bot_at_bot : TendstoIxxClass Ioo (atBot : Filter α) atBot :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Icc_self

instance OrdConnected.tendsto_Icc {s : Set α} [hs : OrdConnected s] : TendstoIxxClass Icc (𝓟 s) (𝓟 s) :=
  tendsto_Ixx_class_principal.2 hs.out

instance tendsto_Ico_Ici_Ici {a : α} : TendstoIxxClass Ico (𝓟 (Ici a)) (𝓟 (Ici a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ico_Ioi_Ioi {a : α} : TendstoIxxClass Ico (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ico_Iic_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_principal.2 fun a ha b hb x hx => lt_of_lt_of_leₓ hx.2 hb

instance tendsto_Ico_Iio_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_Ici_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_principal.2 fun x hx y hy t ht => lt_of_le_of_ltₓ hx ht.1

instance tendsto_Ioc_Iic_Iic {a : α} : TendstoIxxClass Ioc (𝓟 (Iic a)) (𝓟 (Iic a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioc_Iio_Iio {a : α} : TendstoIxxClass Ioc (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioc_Ioi_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_Ici_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Ioo_Iic_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ico_self

instance tendsto_Ioo_Ioi_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Ioo_Iio_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Icc_Icc_Icc {a b : α} : TendstoIxxClass Icc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendsto_Ixx_class_principal.mpr fun x hx y hy => Icc_subset_Icc hx.1 hy.2

instance tendsto_Ioc_Icc_Icc {a b : α} : TendstoIxxClass Ioc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

instance tendsto_Icc_pure_pure {a : α} : TendstoIxxClass Icc (pure a) (pure a : Filter α) := by
  rw [← principal_singleton]
  exact tendsto_Ixx_class_principal.2 ord_connected_singleton.out

instance tendsto_Ico_pure_bot {a : α} : TendstoIxxClass Ico (pure a) ⊥ :=
  ⟨by
    simp ⟩

instance tendsto_Ioc_pure_bot {a : α} : TendstoIxxClass Ioc (pure a) ⊥ :=
  ⟨by
    simp ⟩

instance tendsto_Ioo_pure_bot {a : α} : TendstoIxxClass Ioo (pure a) ⊥ :=
  ⟨by
    simp ⟩

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
instance tendsto_Icc_interval_interval {a b : α} :
    TendstoIxxClass Icc (𝓟 "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
      (𝓟 "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :=
  Filter.tendsto_Icc_Icc_Icc

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
instance tendsto_Ioc_interval_interval {a b : α} :
    TendstoIxxClass Ioc (𝓟 "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
      (𝓟 "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :=
  Filter.tendsto_Ioc_Icc_Icc

instance tendsto_interval_of_Icc {l : Filter α} [TendstoIxxClass Icc l l] : TendstoIxxClass Interval l l := by
  refine' ⟨fun s hs => mem_map.2 <| mem_prod_self_iff.2 _⟩
  obtain ⟨t, htl, hts⟩ : ∃ t ∈ l, ∀, ∀ p ∈ (t : Set α) ×ˢ t, ∀, Icc (p : α × α).1 p.2 ∈ s
  exact mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs))
  refine' ⟨t, htl, fun p hp => _⟩
  cases le_totalₓ p.1 p.2
  · rw [mem_preimage, interval_of_le h]
    exact hts p hp
    
  · rw [mem_preimage, interval_of_ge h]
    exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩
    

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem Tendsto.interval {l : Filter α} [TendstoIxxClass Icc l l] {f g : β → α} {lb : Filter β} (hf : Tendsto f lb l)
    (hg : Tendsto g lb l) :
    Tendsto (fun x => "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") lb l.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| hf.prod_mk hg

end LinearOrderₓ

end Filter

