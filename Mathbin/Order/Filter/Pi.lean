/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex Kontorovich
-/
import Mathbin.Order.Filter.Bases

/-!
# (Co)product of a family of filters

In this file we define two filters on `Π i, α i` and prove some basic properties of these filters.

* `filter.pi (f : Π i, filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, filter.tendsto (function.eval i) (filter.pi f) (f i)`. It is defined as
  `Π i, filter.comap (function.eval i) (f i)`. This is a generalization of `filter.prod` to indexed
  products.

* `filter.Coprod (f : Π i, filter (α i))`: a generalization of `filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/


open Set Function

open Classical Filter

namespace Filter

variable {ι : Type _} {α : ι → Type _} {f f₁ f₂ : ∀ i, Filter (α i)} {s : ∀ i, Set (α i)}

section Pi

/-- The product of an indexed family of filters. -/
def pi (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨅ i, comap (eval i) (f i)

theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_infi' i tendsto_comap

theorem tendsto_pi {β : Type _} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [← pi, ← tendsto_infi, ← tendsto_comap_iff]

theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi

@[mono]
theorem pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ :=
  infi_mono fun i => comap_mono <| h i

theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s ∈ f i) : eval i ⁻¹' s ∈ pi f :=
  mem_infi_of_mem i <| preimage_mem_comap hs

theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : ∀, ∀ i ∈ I, ∀, s i ∈ f i) : I.pi s ∈ pi f := by
  rw [pi_def, bInter_eq_Inter]
  refine' mem_infi_of_Inter hI (fun i => _) subset.rfl
  exact preimage_mem_comap (h i i.2)

theorem mem_pi {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Set ι, I.Finite ∧ ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s := by
  constructor
  · simp only [← pi, ← mem_infi', ← mem_comap, ← pi_def]
    rintro ⟨I, If, V, hVf, hVI, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, Inter₂_mono fun i _ => htV i⟩
    
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset ((pi_mem_pi If) fun i _ => htf i) hts
    

theorem mem_pi' {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Finset ι, ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ Set.Pi (↑I) t ⊆ s :=
  mem_pi.trans exists_finite_iff_finset

theorem mem_of_pi_mem_pi [∀ i, NeBot (f i)] {I : Set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) : s i ∈ f i := by
  rcases mem_pi.1 h with ⟨I', I'f, t, htf, hts⟩
  refine' mem_of_superset (htf i) fun x hx => _
  have : ∀ i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg
  have : update g i x ∈ I'.pi t := by
    intro j hj
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi

@[simp]
theorem pi_mem_pi_iff [∀ i, NeBot (f i)] {I : Set ι} (hI : I.Finite) : I.pi s ∈ pi f ↔ ∀, ∀ i ∈ I, ∀, s i ∈ f i :=
  ⟨fun h i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩

theorem has_basis_pi {ι' : ι → Type} {s : ∀ i, ι' i → Set (α i)} {p : ∀ i, ι' i → Prop}
    (h : ∀ i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀, ∀ i ∈ If.1, ∀, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => If.1.pi fun i => s i <| If.2 i :=
  by
  have : (pi f).HasBasis _ _ := has_basis_infi fun i => (h i).comap (eval i : (∀ j, α j) → α i)
  convert this
  ext
  simp

@[simp]
theorem pi_inf_principal_univ_pi_eq_bot : pi f⊓𝓟 (Set.Pi Univ s) = ⊥ ↔ ∃ i, f i⊓𝓟 (s i) = ⊥ := by
  constructor
  · simp only [← inf_principal_eq_bot, ← mem_pi]
    contrapose!
    rintro (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I If t htf hts
    have : ∀ i, (s i ∩ t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt
    exact hts (fun i hi => hxt i) (mem_univ_pi.2 hxs)
    
  · simp only [← inf_principal_eq_bot]
    rintro ⟨i, hi⟩
    filter_upwards [mem_pi_of_mem i hi] with x using mt fun h => h i trivialₓ
    

@[simp]
theorem pi_inf_principal_pi_eq_bot [∀ i, NeBot (f i)] {I : Set ι} :
    pi f⊓𝓟 (Set.Pi I s) = ⊥ ↔ ∃ i ∈ I, f i⊓𝓟 (s i) = ⊥ := by
  rw [← univ_pi_piecewise I, pi_inf_principal_univ_pi_eq_bot]
  refine' exists_congr fun i => _
  by_cases' hi : i ∈ I <;> simp [← hi, ← (‹∀ i, ne_bot (f i)› i).Ne]

@[simp]
theorem pi_inf_principal_univ_pi_ne_bot : NeBot (pi f⊓𝓟 (Set.Pi Univ s)) ↔ ∀ i, NeBot (f i⊓𝓟 (s i)) := by
  simp [← ne_bot_iff]

@[simp]
theorem pi_inf_principal_pi_ne_bot [∀ i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f⊓𝓟 (I.pi s)) ↔ ∀, ∀ i ∈ I, ∀, NeBot (f i⊓𝓟 (s i)) := by
  simp [← ne_bot_iff]

instance PiInfPrincipalPi.ne_bot [h : ∀ i, NeBot (f i⊓𝓟 (s i))] {I : Set ι} : NeBot (pi f⊓𝓟 (I.pi s)) :=
  (pi_inf_principal_univ_pi_ne_bot.2 ‹_›).mono <| inf_le_inf_left _ <| principal_mono.2 fun x hx i hi => hx i trivialₓ

@[simp]
theorem pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ

@[simp]
theorem pi_ne_bot : NeBot (pi f) ↔ ∀ i, NeBot (f i) := by
  simp [← ne_bot_iff]

instance [∀ i, NeBot (f i)] : NeBot (pi f) :=
  pi_ne_bot.2 ‹_›

end Pi

/-! ### `n`-ary coproducts of filters -/


section Coprod

/-- Coproduct of filters. -/
protected def coprodₓ (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)

theorem mem_Coprod_iff {s : Set (∀ i, α i)} : s ∈ Filter.coprodₓ f ↔ ∀ i : ι, ∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s := by
  simp [← Filter.coprodₓ]

theorem compl_mem_Coprod {s : Set (∀ i, α i)} : sᶜ ∈ Filter.coprodₓ f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i := by
  simp only [← Filter.coprodₓ, ← mem_supr, ← compl_mem_comap]

theorem Coprod_ne_bot_iff' : NeBot (Filter.coprodₓ f) ↔ (∀ i, Nonempty (α i)) ∧ ∃ d, NeBot (f d) := by
  simp only [← Filter.coprodₓ, ← supr_ne_bot, exists_and_distrib_left, comap_eval_ne_bot_iff']

@[simp]
theorem Coprod_ne_bot_iff [∀ i, Nonempty (α i)] : NeBot (Filter.coprodₓ f) ↔ ∃ d, NeBot (f d) := by
  simp [← Coprod_ne_bot_iff', *]

theorem Coprod_eq_bot_iff' : Filter.coprodₓ f = ⊥ ↔ (∃ i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa [← not_and_distrib, ← funext_iff] using not_congr Coprod_ne_bot_iff'

@[simp]
theorem Coprod_eq_bot_iff [∀ i, Nonempty (α i)] : Filter.coprodₓ f = ⊥ ↔ f = ⊥ := by
  simpa [← funext_iff] using not_congr Coprod_ne_bot_iff

@[simp]
theorem Coprod_bot' : Filter.coprodₓ (⊥ : ∀ i, Filter (α i)) = ⊥ :=
  Coprod_eq_bot_iff'.2 (Or.inr rfl)

@[simp]
theorem Coprod_bot : Filter.coprodₓ (fun _ => ⊥ : ∀ i, Filter (α i)) = ⊥ :=
  Coprod_bot'

theorem NeBot.Coprod [∀ i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprodₓ f) :=
  Coprod_ne_bot_iff.2 ⟨i, h⟩

@[instance]
theorem Coprod_ne_bot [∀ i, Nonempty (α i)] [Nonempty ι] (f : ∀ i, Filter (α i)) [H : ∀ i, NeBot (f i)] :
    NeBot (Filter.coprodₓ f) :=
  (H (Classical.arbitrary ι)).coprod

@[mono]
theorem Coprod_mono (hf : ∀ i, f₁ i ≤ f₂ i) : Filter.coprodₓ f₁ ≤ Filter.coprodₓ f₂ :=
  supr_mono fun i => comap_mono (hf i)

variable {β : ι → Type _} {m : ∀ i, α i → β i}

theorem map_pi_map_Coprod_le :
    map (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodₓ f) ≤ Filter.coprodₓ fun i => map (m i) (f i) := by
  simp only [← le_def, ← mem_map, ← mem_Coprod_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x ∈ t }, H, fun x hx => hH hx⟩

theorem Tendsto.pi_map_Coprod {g : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodₓ f) (Filter.coprodₓ g) :=
  map_pi_map_Coprod_le.trans (Coprod_mono h)

end Coprod

end Filter

