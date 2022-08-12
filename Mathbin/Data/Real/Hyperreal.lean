/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
-/
import Mathbin.Order.Filter.FilterProduct
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/


open Filter Filter.Germ

open TopologicalSpace Classical

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving LinearOrderedField, Inhabited

namespace Hyperreal

-- mathport name: «exprℝ*»
notation "ℝ*" => Hyperreal

noncomputable instance : CoeTₓ ℝ ℝ* :=
  ⟨fun x => (↑x : Germ _ _)⟩

@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  germ.const_inj

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ) = (1 : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ) = (0 : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_inv (x : ℝ) : ↑x⁻¹ = (x⁻¹ : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_bit0 (x : ℝ) : ↑(bit0 x) = (bit0 x : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_bit1 (x : ℝ) : ↑(bit1 x) = (bit1 x : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  germ.const_lt

@[simp, norm_cast]
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe

@[simp, norm_cast]
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  germ.const_le_iff

@[simp, norm_cast]
theorem coe_abs (x : ℝ) : ((abs x : ℝ) : ℝ*) = abs x := by
  convert const_abs x
  apply linear_order.to_lattice_eq_filter_germ_lattice

@[simp, norm_cast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max x y :=
  Germ.const_max _ _

@[simp, norm_cast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min x y :=
  Germ.const_min _ _

/-- Construct a hyperreal number from a sequence of real numbers. -/
noncomputable def ofSeq (f : ℕ → ℝ) : ℝ* :=
  (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* :=
  of_seq fun n => n⁻¹

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* :=
  ofSeq coe

-- mathport name: «exprε»
localized [Hyperreal] notation "ε" => Hyperreal.epsilon

-- mathport name: «exprω»
localized [Hyperreal] notation "ω" => Hyperreal.omega

theorem epsilon_eq_inv_omega : ε = ω⁻¹ :=
  rfl

theorem inv_epsilon_eq_omega : ε⁻¹ = ω :=
  @inv_invₓ _ _ ω

theorem epsilon_pos : 0 < ε := by
  suffices ∀ᶠ i in hyperfilter ℕ, (0 : ℝ) < (i : ℕ)⁻¹ by
    rwa [lt_def]
  have h0' : { n : ℕ | ¬0 < n } = {0} := by
    simp only [← not_ltₓ, ← Set.set_of_eq_eq_singleton.symm] <;> ext <;> exact Nat.le_zero_iffₓ
  simp only [← inv_pos, ← Nat.cast_pos]
  exact
    mem_hyperfilter_of_finite_compl
      (by
        convert Set.finite_singleton _)

theorem epsilon_ne_zero : ε ≠ 0 :=
  ne_of_gtₓ epsilon_pos

theorem omega_pos : 0 < ω := by
  rw [← inv_epsilon_eq_omega] <;> exact inv_pos.2 epsilon_pos

theorem omega_ne_zero : ω ≠ 0 :=
  ne_of_gtₓ omega_pos

theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel _ _ ω omega_ne_zero

theorem lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) : ∀ {r : ℝ}, 0 < r → ofSeq f < (r : ℝ*) := by
  simp only [← Metric.tendsto_at_top, ← Real.dist_eq, ← sub_zero, ← lt_def] at hf⊢
  intro r hr
  cases' hf r hr with N hf'
  have hs : { i : ℕ | f i < r }ᶜ ⊆ { i : ℕ | i ≤ N } := fun i hi1 =>
    le_of_ltₓ
      (by
        simp only [← lt_iff_not_geₓ] <;> exact fun hi2 => hi1 (lt_of_le_of_ltₓ (le_abs_self _) (hf' i hi2)) : i < N)
  exact mem_hyperfilter_of_finite_compl ((Set.finite_le_nat N).Subset hs)

theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < ofSeq f := fun r hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt
    (by
      rw [neg_zero] at hg <;> exact lt_of_tendsto_zero_of_pos hg hr)

theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) : ∀ {r : ℝ}, r < 0 → (r : ℝ*) < ofSeq f :=
  fun r hr => by
  rw [← neg_negₓ r, coe_neg] <;> exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)

theorem epsilon_lt_pos (x : ℝ) : 0 < x → ε < x :=
  lt_of_tendsto_zero_of_pos tendsto_inverse_at_top_nhds_0_nat

/-- Standard part predicate -/
def IsSt (x : ℝ*) (r : ℝ) :=
  ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r + δ

/-- Standard part function: like a "round" to ℝ instead of ℤ -/
noncomputable def st : ℝ* → ℝ := fun x => if h : ∃ r, IsSt x r then Classical.some h else 0

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def Infinitesimal (x : ℝ*) :=
  IsSt x 0

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def InfinitePos (x : ℝ*) :=
  ∀ r : ℝ, ↑r < x

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def InfiniteNeg (x : ℝ*) :=
  ∀ r : ℝ, x < r

/-- A hyperreal number is infinite if it is infinite positive or infinite negative -/
def Infinite (x : ℝ*) :=
  InfinitePos x ∨ InfiniteNeg x

/-!
### Some facts about `st`
-/


private theorem is_st_unique' (x : ℝ*) (r s : ℝ) (hr : IsSt x r) (hs : IsSt x s) (hrs : r < s) : False := by
  have hrs' := half_pos <| sub_pos_of_lt hrs
  have hr' := (hr _ hrs').2
  have hs' := (hs _ hrs').1
  have h : s - (s - r) / 2 = r + (s - r) / 2 := by
    linarith
  norm_cast  at *
  rw [h] at hs'
  exact not_lt_of_lt hs' hr'

theorem is_st_unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
  rcases lt_trichotomyₓ r s with (h | h | h)
  · exact False.elim (is_st_unique' x r s hr hs h)
    
  · exact h
    
  · exact False.elim (is_st_unique' x s r hs hr h)
    

theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, IsSt x r) → ¬Infinite x := fun he hi =>
  (Exists.dcases_on he) fun r hr =>
    hi.elim (fun hip => not_lt_of_lt (hr 2 zero_lt_two).2 (hip <| r + 2)) fun hin =>
      not_lt_of_lt (hr 2 zero_lt_two).1 (hin <| r - 2)

theorem is_st_Sup {x : ℝ*} (hni : ¬Infinite x) : IsSt x (sup { y : ℝ | (y : ℝ*) < x }) :=
  let S : Set ℝ := { y : ℝ | (y : ℝ*) < x }
  let R : _ := sup S
  have hnile := not_forall.mp (not_or_distrib.mp hni).1
  have hnige := not_forall.mp (not_or_distrib.mp hni).2
  Exists.dcases_on hnile <|
    (Exists.dcases_on hnige) fun r₁ hr₁ r₂ hr₂ =>
      have HR₁ : S.Nonempty := ⟨r₁ - 1, lt_of_lt_of_leₓ (coe_lt_coe.2 <| sub_one_lt _) (not_ltₓ.mp hr₁)⟩
      have HR₂ : BddAbove S := ⟨r₂, fun y hy => le_of_ltₓ (coe_lt_coe.1 (lt_of_lt_of_leₓ hy (not_ltₓ.mp hr₂)))⟩
      fun δ hδ =>
      ⟨lt_of_not_le fun c =>
          have hc : ∀, ∀ y ∈ S, ∀, y ≤ R - δ := fun y hy => coe_le_coe.1 <| le_of_ltₓ <| lt_of_lt_of_leₓ hy c
          not_lt_of_le (cSup_le HR₁ hc) <| sub_lt_self R hδ,
        lt_of_not_le fun c =>
          have hc : ↑(R + δ / 2) < x := lt_of_lt_of_leₓ (add_lt_add_left (coe_lt_coe.2 (half_lt_self hδ)) R) c
          not_lt_of_le (le_cSup HR₂ hc) <| (lt_add_iff_pos_right _).mpr <| half_pos hδ⟩

theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, IsSt x r :=
  ⟨sup { y : ℝ | (y : ℝ*) < x }, is_st_Sup hni⟩

theorem st_eq_Sup {x : ℝ*} : st x = sup { y : ℝ | (y : ℝ*) < x } := by
  unfold st
  split_ifs
  · exact is_st_unique (Classical.some_spec h) (is_st_Sup (not_infinite_of_exists_st h))
    
  · cases' not_imp_comm.mp exists_st_of_not_infinite h with H H
    · rw [(Set.ext fun i => ⟨fun hi => Set.mem_univ i, fun hi => H i⟩ : { y : ℝ | (y : ℝ*) < x } = Set.Univ)]
      exact real.Sup_univ.symm
      
    · rw
        [(Set.ext fun i =>
          ⟨fun hi => False.elim (not_lt_of_lt (H i) hi), fun hi => False.elim (Set.not_mem_empty i hi)⟩ :
          { y : ℝ | (y : ℝ*) < x } = ∅)]
      exact real.Sup_empty.symm
      
    

theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite

theorem st_infinite {x : ℝ*} (hi : Infinite x) : st x = 0 := by
  unfold st
  split_ifs
  · exact False.elim ((infinite_iff_not_exists_st.mp hi) h)
    
  · rfl
    

theorem st_of_is_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : st x = r := by
  unfold st
  split_ifs
  · exact is_st_unique (Classical.some_spec h) hxr
    
  · exact False.elim (h ⟨r, hxr⟩)
    

theorem is_st_st_of_is_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [st_of_is_st hxr]

theorem is_st_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, IsSt x r) : IsSt x (st x) :=
  Exists.dcases_on hx fun r => is_st_st_of_is_st

theorem is_st_st {x : ℝ*} (hx : st x ≠ 0) : IsSt x (st x) := by
  unfold st
  split_ifs
  · exact Classical.some_spec h
    
  · exact
      False.elim
        (hx
          (by
            unfold st <;> split_ifs <;> rfl))
    

theorem is_st_st' {x : ℝ*} (hx : ¬Infinite x) : IsSt x (st x) :=
  is_st_st_of_exists_st <| exists_st_of_not_infinite hx

theorem is_st_refl_real (r : ℝ) : IsSt r r := fun δ hδ =>
  ⟨sub_lt_self _ (coe_lt_coe.2 hδ), lt_add_of_pos_right _ (coe_lt_coe.2 hδ)⟩

theorem st_id_real (r : ℝ) : st r = r :=
  st_of_is_st (is_st_refl_real r)

theorem eq_of_is_st_real {r s : ℝ} : IsSt r s → r = s :=
  is_st_unique (is_st_refl_real r)

theorem is_st_real_iff_eq {r s : ℝ} : IsSt r s ↔ r = s :=
  ⟨eq_of_is_st_real, fun hrs => by
    rw [hrs] <;> exact is_st_refl_real s⟩

theorem is_st_symm_real {r s : ℝ} : IsSt r s ↔ IsSt s r := by
  rw [is_st_real_iff_eq, is_st_real_iff_eq, eq_comm]

theorem is_st_trans_real {r s t : ℝ} : IsSt r s → IsSt s t → IsSt r t := by
  rw [is_st_real_iff_eq, is_st_real_iff_eq, is_st_real_iff_eq] <;> exact Eq.trans

theorem is_st_inj_real {r₁ r₂ s : ℝ} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_is_st_real h1) (eq_of_is_st_real h2).symm

theorem is_st_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : IsSt x r ↔ ∀ δ : ℝ, 0 < δ → abs (x - r) < δ := by
  simp only [← abs_sub_lt_iff, ← sub_lt_iff_lt_add, ← is_st, ← and_comm, ← add_commₓ]

theorem is_st_add {x y : ℝ*} {r s : ℝ} : IsSt x r → IsSt y s → IsSt (x + y) (r + s) := fun hxr hys d hd =>
  have hxr' := hxr (d / 2) (half_pos hd)
  have hys' := hys (d / 2) (half_pos hd)
  ⟨by
    convert add_lt_add hxr'.1 hys'.1 using 1 <;> norm_cast <;> linarith, by
    convert add_lt_add hxr'.2 hys'.2 using 1 <;> norm_cast <;> linarith⟩

theorem is_st_neg {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt (-x) (-r) := fun d hd =>
  show -(r : ℝ*) - d < -x ∧ -x < -r + d by
    cases hxr d hd <;> constructor <;> linarith

theorem is_st_sub {x y : ℝ*} {r s : ℝ} : IsSt x r → IsSt y s → IsSt (x - y) (r - s) := fun hxr hys => by
  rw [sub_eq_add_neg, sub_eq_add_neg] <;> exact is_st_add hxr (is_st_neg hys)

-- (st x < st y) → (x < y) → (x ≤ y) → (st x ≤ st y)
theorem lt_of_is_st_lt {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : r < s → x < y := fun hrs => by
  have hrs' : 0 < (s - r) / 2 := half_pos (sub_pos.mpr hrs)
  have hxr' := (hxr _ hrs').2
  have hys' := (hys _ hrs').1
  have H1 : r + (s - r) / 2 = (r + s) / 2 := by
    linarith
  have H2 : s - (s - r) / 2 = (r + s) / 2 := by
    linarith
  norm_cast  at *
  rw [H1] at hxr'
  rw [H2] at hys'
  exact lt_transₓ hxr' hys'

theorem is_st_le_of_le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) : x ≤ y → r ≤ s := by
  rw [← not_ltₓ, ← not_ltₓ, not_imp_not] <;> exact lt_of_is_st_lt hsy hrx

theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  have hx' := is_st_st' hix
  have hy' := is_st_st' hiy
  is_st_le_of_le hx' hy'

theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  have hx' := is_st_st' hix
  have hy' := is_st_st' hiy
  lt_of_is_st_lt hx' hy'

/-!
### Basic lemmas about infinite
-/


theorem infinite_pos_def {x : ℝ*} : InfinitePos x ↔ ∀ r : ℝ, ↑r < x := by
  rw [iff_eq_eq] <;> rfl

theorem infinite_neg_def {x : ℝ*} : InfiniteNeg x ↔ ∀ r : ℝ, x < r := by
  rw [iff_eq_eq] <;> rfl

theorem ne_zero_of_infinite {x : ℝ*} : Infinite x → x ≠ 0 := fun hI h0 =>
  Or.cases_on hI
    (fun hip =>
      lt_irreflₓ (0 : ℝ*)
        ((by
            rwa [← h0] : InfinitePos 0)
          0))
    fun hin =>
    lt_irreflₓ (0 : ℝ*)
      ((by
          rwa [← h0] : InfiniteNeg 0)
        0)

theorem not_infinite_zero : ¬Infinite 0 := fun hI => ne_zero_of_infinite hI rfl

theorem pos_of_infinite_pos {x : ℝ*} : InfinitePos x → 0 < x := fun hip => hip 0

theorem neg_of_infinite_neg {x : ℝ*} : InfiniteNeg x → x < 0 := fun hin => hin 0

theorem not_infinite_pos_of_infinite_neg {x : ℝ*} : InfiniteNeg x → ¬InfinitePos x := fun hn hp =>
  not_lt_of_lt (hn 1) (hp 1)

theorem not_infinite_neg_of_infinite_pos {x : ℝ*} : InfinitePos x → ¬InfiniteNeg x :=
  imp_not_comm.mp not_infinite_pos_of_infinite_neg

theorem infinite_neg_neg_of_infinite_pos {x : ℝ*} : InfinitePos x → InfiniteNeg (-x) := fun hp r => neg_lt.mp (hp (-r))

theorem infinite_pos_neg_of_infinite_neg {x : ℝ*} : InfiniteNeg x → InfinitePos (-x) := fun hp r => lt_neg.mp (hp (-r))

theorem infinite_pos_iff_infinite_neg_neg {x : ℝ*} : InfinitePos x ↔ InfiniteNeg (-x) :=
  ⟨infinite_neg_neg_of_infinite_pos, fun hin => neg_negₓ x ▸ infinite_pos_neg_of_infinite_neg hin⟩

theorem infinite_neg_iff_infinite_pos_neg {x : ℝ*} : InfiniteNeg x ↔ InfinitePos (-x) :=
  ⟨infinite_pos_neg_of_infinite_neg, fun hin => neg_negₓ x ▸ infinite_neg_neg_of_infinite_pos hin⟩

theorem infinite_iff_infinite_neg {x : ℝ*} : Infinite x ↔ Infinite (-x) :=
  ⟨fun hi =>
    Or.cases_on hi (fun hip => Or.inr (infinite_neg_neg_of_infinite_pos hip)) fun hin =>
      Or.inl (infinite_pos_neg_of_infinite_neg hin),
    fun hi =>
    Or.cases_on hi (fun hipn => Or.inr (infinite_neg_iff_infinite_pos_neg.mpr hipn)) fun hinp =>
      Or.inl (infinite_pos_iff_infinite_neg_neg.mpr hinp)⟩

theorem not_infinite_of_infinitesimal {x : ℝ*} : Infinitesimal x → ¬Infinite x := fun hi hI =>
  have hi' := hi 2 zero_lt_two
  Or.dcases_on hI
    (fun hip =>
      have hip' := hip 2
      not_lt_of_lt hip'
        (by
          convert hi'.2 <;> exact (zero_addₓ 2).symm))
    fun hin =>
    have hin' := hin (-2)
    not_lt_of_lt hin'
      (by
        convert hi'.1 <;> exact (zero_sub 2).symm)

theorem not_infinitesimal_of_infinite {x : ℝ*} : Infinite x → ¬Infinitesimal x :=
  imp_not_comm.mp not_infinite_of_infinitesimal

theorem not_infinitesimal_of_infinite_pos {x : ℝ*} : InfinitePos x → ¬Infinitesimal x := fun hp =>
  not_infinitesimal_of_infinite (Or.inl hp)

theorem not_infinitesimal_of_infinite_neg {x : ℝ*} : InfiniteNeg x → ¬Infinitesimal x := fun hn =>
  not_infinitesimal_of_infinite (Or.inr hn)

theorem infinite_pos_iff_infinite_and_pos {x : ℝ*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hip => hip) fun hin => False.elim (not_lt_of_lt hp (hin 0))⟩

theorem infinite_neg_iff_infinite_and_neg {x : ℝ*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_lt hp (hin 0))) fun hip => hip⟩

theorem infinite_pos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : InfinitePos x ↔ Infinite x := by
  rw [infinite_pos_iff_infinite_and_pos] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hp⟩⟩

theorem infinite_pos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : InfinitePos x ↔ Infinite x :=
  Or.cases_on (lt_or_eq_of_leₓ hp) infinite_pos_iff_infinite_of_pos fun h => by
    rw [h.symm] <;>
      exact ⟨fun hIP => False.elim (not_infinite_zero (Or.inl hIP)), fun hI => False.elim (not_infinite_zero hI)⟩

theorem infinite_neg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x := by
  rw [infinite_neg_iff_infinite_and_neg] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hn⟩⟩

theorem infinite_pos_abs_iff_infinite_abs {x : ℝ*} : InfinitePos (abs x) ↔ Infinite (abs x) :=
  infinite_pos_iff_infinite_of_nonneg (abs_nonneg _)

theorem infinite_iff_infinite_pos_abs {x : ℝ*} : Infinite x ↔ InfinitePos (abs x) :=
  ⟨fun hi d =>
    Or.cases_on hi
      (fun hip => by
        rw [abs_of_pos (hip 0)] <;> exact hip d)
      fun hin => by
      rw [abs_of_neg (hin 0)] <;> exact lt_neg.mp (hin (-d)),
    fun hipa => by
    rcases lt_trichotomyₓ x 0 with (h | h | h)
    · exact
        Or.inr
          (infinite_neg_iff_infinite_pos_neg.mpr
            (by
              rwa [abs_of_neg h] at hipa))
      
    · exact
        False.elim
          (ne_zero_of_infinite
            (Or.inl
              (by
                rw [h] <;> rwa [h, abs_zero] at hipa))
            h)
      
    · exact
        Or.inl
          (by
            rwa [abs_of_pos h] at hipa)
      ⟩

theorem infinite_iff_infinite_abs {x : ℝ*} : Infinite x ↔ Infinite (abs x) := by
  rw [← infinite_pos_iff_infinite_of_nonneg (abs_nonneg _), infinite_iff_infinite_pos_abs]

theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (abs r : ℝ*) < abs x :=
  ⟨fun hI r => coe_abs r ▸ infinite_iff_infinite_pos_abs.mp hI (abs r), fun hR =>
    Or.cases_on (max_choice x (-x)) (fun h => Or.inl fun r => lt_of_le_of_ltₓ (le_abs_self _) (h ▸ hR r)) fun h =>
      Or.inr fun r => neg_lt_neg_iff.mp <| lt_of_le_of_ltₓ (neg_le_abs_self _) (h ▸ hR r)⟩

theorem infinite_pos_add_not_infinite_neg {x y : ℝ*} : InfinitePos x → ¬InfiniteNeg y → InfinitePos (x + y) := by
  intro hip hnin r
  cases' not_forall.mp hnin with r₂ hr₂
  convert add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp

theorem not_infinite_neg_add_infinite_pos {x y : ℝ*} : ¬InfiniteNeg x → InfinitePos y → InfinitePos (x + y) :=
  fun hx hy => by
  rw [add_commₓ] <;> exact infinite_pos_add_not_infinite_neg hy hx

theorem infinite_neg_add_not_infinite_pos {x y : ℝ*} : InfiniteNeg x → ¬InfinitePos y → InfiniteNeg (x + y) := by
  rw [@infinite_neg_iff_infinite_pos_neg x, @infinite_pos_iff_infinite_neg_neg y,
      @infinite_neg_iff_infinite_pos_neg (x + y), neg_add] <;>
    exact infinite_pos_add_not_infinite_neg

theorem not_infinite_pos_add_infinite_neg {x y : ℝ*} : ¬InfinitePos x → InfiniteNeg y → InfiniteNeg (x + y) :=
  fun hx hy => by
  rw [add_commₓ] <;> exact infinite_neg_add_not_infinite_pos hy hx

theorem infinite_pos_add_infinite_pos {x y : ℝ*} : InfinitePos x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  infinite_pos_add_not_infinite_neg hx (not_infinite_neg_of_infinite_pos hy)

theorem infinite_neg_add_infinite_neg {x y : ℝ*} : InfiniteNeg x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  infinite_neg_add_not_infinite_pos hx (not_infinite_pos_of_infinite_neg hy)

theorem infinite_pos_add_not_infinite {x y : ℝ*} : InfinitePos x → ¬Infinite y → InfinitePos (x + y) := fun hx hy =>
  infinite_pos_add_not_infinite_neg hx (not_or_distrib.mp hy).2

theorem infinite_neg_add_not_infinite {x y : ℝ*} : InfiniteNeg x → ¬Infinite y → InfiniteNeg (x + y) := fun hx hy =>
  infinite_neg_add_not_infinite_pos hx (not_or_distrib.mp hy).1

theorem infinite_pos_of_tendsto_top {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) : InfinitePos (ofSeq f) := fun r =>
  have hf' := tendsto_at_top_at_top.mp hf
  (Exists.cases_on (hf' (r + 1))) fun i hi =>
    have hi' : ∀ a : ℕ, f a < r + 1 → a < i := fun a => by
      rw [← not_leₓ, ← not_leₓ] <;> exact not_imp_not.mpr (hi a)
    have hS : { a : ℕ | r < f a }ᶜ ⊆ { a : ℕ | a ≤ i } := by
      simp only [← Set.compl_set_of, ← not_ltₓ] <;>
        exact fun a har => le_of_ltₓ (hi' a (lt_of_le_of_ltₓ har (lt_add_one _)))
    Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).Subset hS

theorem infinite_neg_of_tendsto_bot {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) : InfiniteNeg (ofSeq f) := fun r =>
  have hf' := tendsto_at_top_at_bot.mp hf
  (Exists.cases_on (hf' (r - 1))) fun i hi =>
    have hi' : ∀ a : ℕ, r - 1 < f a → a < i := fun a => by
      rw [← not_leₓ, ← not_leₓ] <;> exact not_imp_not.mpr (hi a)
    have hS : { a : ℕ | f a < r }ᶜ ⊆ { a : ℕ | a ≤ i } := by
      simp only [← Set.compl_set_of, ← not_ltₓ] <;>
        exact fun a har => le_of_ltₓ (hi' a (lt_of_lt_of_leₓ (sub_one_lt _) har))
    Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).Subset hS

theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) :=
  not_imp_not.mpr infinite_iff_infinite_neg.mpr

theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have hx' := exists_st_of_not_infinite hx
  have hy' := exists_st_of_not_infinite hy
  Exists.cases_on hx' <| (Exists.cases_on hy') fun r hr s hs => not_infinite_of_exists_st <| ⟨s + r, is_st_add hs hr⟩

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni =>
    Exists.dcases_on (not_forall.mp (not_or_distrib.mp hni).1) <|
      (Exists.dcases_on (not_forall.mp (not_or_distrib.mp hni).2)) fun r hr s hs => by
        rw [not_ltₓ] at hr hs <;>
          exact
            ⟨r - 1, s + 1,
              ⟨lt_of_lt_of_leₓ
                  (by
                    rw [sub_eq_add_neg] <;> norm_num)
                  hr,
                lt_of_le_of_ltₓ hs
                  (by
                    norm_num)⟩⟩,
    fun hrs =>
    (Exists.dcases_on hrs) fun r hr =>
      (Exists.dcases_on hr) fun s hs =>
        not_or_distrib.mpr ⟨not_forall.mpr ⟨s, lt_asymmₓ hs.2⟩, not_forall.mpr ⟨r, lt_asymmₓ hs.1⟩⟩⟩

theorem not_infinite_real (r : ℝ) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt] <;> exact ⟨r - 1, r + 1, coe_lt_coe.2 <| sub_one_lt r, coe_lt_coe.2 <| lt_add_one r⟩

theorem not_real_of_infinite {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r := fun hi r hr =>
  not_infinite_real r <| @Eq.subst _ Infinite _ _ hr hi

/-!
### Facts about `st` that require some infinite machinery
-/


private theorem is_st_mul' {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) (hs : s ≠ 0) : IsSt (x * y) (r * s) :=
  have hxr' := is_st_iff_abs_sub_lt_delta.mp hxr
  have hys' := is_st_iff_abs_sub_lt_delta.mp hys
  have h :=
    not_infinite_iff_exist_lt_gt.mp <|
      not_imp_not.mpr infinite_iff_infinite_abs.mpr <| not_infinite_of_exists_st ⟨r, hxr⟩
  (Exists.cases_on h) fun u h' =>
    (Exists.cases_on h') fun t ⟨hu, ht⟩ =>
      is_st_iff_abs_sub_lt_delta.mpr fun d hd =>
        calc
          abs (x * y - r * s) = abs (x * (y - s) + (x - r) * s) := by
            rw [mul_sub, sub_mul, add_sub, sub_add_cancel]
          _ ≤ abs (x * (y - s)) + abs ((x - r) * s) := abs_add _ _
          _ ≤ abs x * abs (y - s) + abs (x - r) * abs s := by
            simp only [← abs_mul]
          _ ≤ abs x * (d / t / 2 : ℝ) + (d / abs s / 2 : ℝ) * abs s :=
            add_le_add
              (mul_le_mul_of_nonneg_left
                  (le_of_ltₓ <| hys' _ <| half_pos <| div_pos hd <| coe_pos.1 <| lt_of_le_of_ltₓ (abs_nonneg x) ht) <|
                abs_nonneg _)
              (mul_le_mul_of_nonneg_right (le_of_ltₓ <| hxr' _ <| half_pos <| div_pos hd <| abs_pos.2 hs) <|
                abs_nonneg _)
          _ = (d / 2 * (abs x / t) + d / 2 : ℝ*) := by
            push_cast [-Filter.Germ.const_div]
            -- TODO: Why wasn't `hyperreal.coe_div` used?
            have : (abs s : ℝ*) ≠ 0 := by
              simpa
            have : (2 : ℝ*) ≠ 0 := two_ne_zero
            field_simp [*, ← add_mulₓ, ← mul_addₓ, ← mul_assoc, ← mul_comm, ← mul_left_commₓ]
          _ < (d / 2 * 1 + d / 2 : ℝ*) :=
            add_lt_add_right
              (mul_lt_mul_of_pos_left ((div_lt_one <| lt_of_le_of_ltₓ (abs_nonneg x) ht).mpr ht) <|
                half_pos <| coe_pos.2 hd)
              _
          _ = (d : ℝ*) := by
            rw [mul_oneₓ, add_halves]
          

theorem is_st_mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
  have h :=
    not_infinite_iff_exist_lt_gt.mp <|
      not_imp_not.mpr infinite_iff_infinite_abs.mpr <| not_infinite_of_exists_st ⟨r, hxr⟩
  (Exists.cases_on h) fun u h' =>
    (Exists.cases_on h') fun t ⟨hu, ht⟩ => by
      by_cases' hs : s = 0
      · apply is_st_iff_abs_sub_lt_delta.mpr
        intro d hd
        have hys' : _ :=
          is_st_iff_abs_sub_lt_delta.mp hys (d / t) (div_pos hd (coe_pos.1 (lt_of_le_of_ltₓ (abs_nonneg x) ht)))
        rw [hs, coe_zero, sub_zero] at hys'
        rw [hs, mul_zero, coe_zero, sub_zero, abs_mul, mul_comm, ←
          div_mul_cancel (d : ℝ*) (ne_of_gtₓ (lt_of_le_of_ltₓ (abs_nonneg x) ht)), ← coe_div]
        exact mul_lt_mul'' hys' ht (abs_nonneg _) (abs_nonneg _)
        
      exact is_st_mul' hxr hys hs

--AN INFINITE LEMMA THAT REQUIRES SOME MORE ST MACHINERY
theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have hx' := exists_st_of_not_infinite hx
  have hy' := exists_st_of_not_infinite hy
  Exists.cases_on hx' <| (Exists.cases_on hy') fun r hr s hs => not_infinite_of_exists_st <| ⟨s * r, is_st_mul hs hr⟩

---
theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  have hx' := is_st_st' hx
  have hy' := is_st_st' hy
  have hxy := is_st_st' (not_infinite_add hx hy)
  have hxy' := is_st_add hx' hy'
  is_st_unique hxy hxy'

theorem st_neg (x : ℝ*) : st (-x) = -st x :=
  if h : Infinite x then by
    rw [st_infinite h, st_infinite (infinite_iff_infinite_neg.mp h), neg_zero]
  else is_st_unique (is_st_st' (not_infinite_neg h)) (is_st_neg (is_st_st' h))

theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := is_st_st' hx
  have hy' := is_st_st' hy
  have hxy := is_st_st' (not_infinite_mul hx hy)
  have hxy' := is_st_mul hx' hy'
  is_st_unique hxy hxy'

/-!
### Basic lemmas about infinitesimal
-/


theorem infinitesimal_def {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r :=
  ⟨fun hi r hr => by
    convert hi r hr <;> simp , fun hi d hd => by
    convert hi d hd <;> simp ⟩

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → x < r := fun hi r hr =>
  ((infinitesimal_def.mp hi) r hr).2

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x := fun hi r hr =>
  ((infinitesimal_def.mp hi) r hr).1

theorem gt_of_neg_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, r < 0 → ↑r < x := fun hi r hr => by
  convert ((infinitesimal_def.mp hi) (-r) (neg_pos.mpr hr)).1 <;> exact (neg_negₓ ↑r).symm

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → abs x < abs r :=
  ⟨fun hi r hr =>
    abs_lt.mpr
      (by
        rw [← coe_abs] <;> exact infinitesimal_def.mp hi (abs r) (abs_pos.2 hr)),
    fun hR => infinitesimal_def.mpr fun r hr => abs_lt.mp <| (abs_of_pos <| coe_pos.2 hr) ▸ hR r <| ne_of_gtₓ hr⟩

theorem infinitesimal_zero : Infinitesimal 0 :=
  is_st_refl_real 0

theorem zero_of_infinitesimal_real {r : ℝ} : Infinitesimal r → r = 0 :=
  eq_of_is_st_real

theorem zero_iff_infinitesimal_real {r : ℝ} : Infinitesimal r ↔ r = 0 :=
  ⟨zero_of_infinitesimal_real, fun hr => by
    rw [hr] <;> exact infinitesimal_zero⟩

theorem infinitesimal_add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) : Infinitesimal (x + y) := by
  simpa only [← add_zeroₓ] using is_st_add hx hy

theorem infinitesimal_neg {x : ℝ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [← neg_zero] using is_st_neg hx

theorem infinitesimal_neg_iff {x : ℝ*} : Infinitesimal x ↔ Infinitesimal (-x) :=
  ⟨infinitesimal_neg, fun h => neg_negₓ x ▸ @infinitesimal_neg (-x) h⟩

theorem infinitesimal_mul {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) : Infinitesimal (x * y) := by
  simpa only [← mul_zero] using is_st_mul hx hy

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} : Tendsto f atTop (𝓝 0) → Infinitesimal (ofSeq f) := fun hf d hd => by
  rw [sub_eq_add_neg, ← coe_neg, ← coe_add, ← coe_add, zero_addₓ, zero_addₓ] <;>
    exact ⟨neg_lt_of_tendsto_zero_of_pos hf hd, lt_of_tendsto_zero_of_pos hf hd⟩

theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inverse_at_top_nhds_0_nat

theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : Infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r := fun hi hx r hr =>
  hx <| hr.trans <| coe_eq_zero.2 <| is_st_unique (hr.symm ▸ is_st_refl_real r : IsSt x r) hi

theorem infinitesimal_sub_is_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : Infinitesimal (x - r) :=
  show IsSt (x - r) 0 by
    rw [sub_eq_add_neg, ← add_neg_selfₓ r]
    exact is_st_add hxr (is_st_refl_real (-r))

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : Infinitesimal (x - st x) :=
  infinitesimal_sub_is_st <| is_st_st' hx

theorem infinite_pos_iff_infinitesimal_inv_pos {x : ℝ*} : InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ :=
  ⟨fun hip =>
    ⟨infinitesimal_def.mpr fun r hr =>
        ⟨lt_transₓ (coe_lt_coe.2 (neg_neg_of_pos hr)) (inv_pos.2 (hip 0)),
          (inv_lt (coe_lt_coe.2 hr) (hip 0)).mp
            (by
              convert hip r⁻¹)⟩,
      inv_pos.2 <| hip 0⟩,
    fun ⟨hi, hp⟩ r =>
    (@Classical.by_cases (r = 0) (↑r < x) fun h => Eq.substr h (inv_pos.mp hp)) fun h =>
      lt_of_le_of_ltₓ (coe_le_coe.2 (le_abs_self r))
        ((inv_lt_inv (inv_pos.mp hp) (coe_lt_coe.2 (abs_pos.2 h))).mp
          ((infinitesimal_def.mp hi) (abs r)⁻¹ (inv_pos.2 (abs_pos.2 h))).2)⟩

theorem infinite_neg_iff_infinitesimal_inv_neg {x : ℝ*} : InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 :=
  ⟨fun hin => by
    have hin' := infinite_pos_iff_infinitesimal_inv_pos.mp (infinite_pos_neg_of_infinite_neg hin)
    rwa [infinitesimal_neg_iff, ← neg_pos, neg_inv], fun hin => by
    rwa [← neg_pos, infinitesimal_neg_iff, neg_inv, ← infinite_pos_iff_infinitesimal_inv_pos, ←
      infinite_neg_iff_infinite_pos_neg] at hin⟩

theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → Infinitesimal x⁻¹ := fun hi =>
  Or.cases_on hi (fun hip => (infinite_pos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infinite_neg_iff_infinitesimal_inv_neg.mp hin).1

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : Infinitesimal x⁻¹) : Infinite x := by
  cases' lt_or_gt_of_neₓ h0 with hn hp
  · exact Or.inr (infinite_neg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
    
  · exact Or.inl (infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)
    

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

theorem infinitesimal_pos_iff_infinite_pos_inv {x : ℝ*} : InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x := by
  convert infinite_pos_iff_infinitesimal_inv_pos <;> simp only [← inv_invₓ]

theorem infinitesimal_neg_iff_infinite_neg_inv {x : ℝ*} : InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 := by
  convert infinite_neg_iff_infinitesimal_inv_neg <;> simp only [← inv_invₓ]

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : Infinitesimal x ↔ Infinite x⁻¹ := by
  convert (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm <;> simp only [← inv_invₓ]

/-!
### `st` stuff that requires infinitesimal machinery
-/


theorem is_st_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r := by
  have hg : Tendsto (fun n => f n - r) atTop (𝓝 0) := sub_self r ▸ hf.sub tendsto_const_nhds
  rw [← zero_addₓ r, ← sub_add_cancel f fun n => r] <;>
    exact is_st_add (infinitesimal_of_tendsto_zero hg) (is_st_refl_real r)

theorem is_st_inv {x : ℝ*} {r : ℝ} (hi : ¬Infinitesimal x) : IsSt x r → IsSt x⁻¹ r⁻¹ := fun hxr =>
  have h : x ≠ 0 := fun h => hi (h.symm ▸ infinitesimal_zero)
  have H := exists_st_of_not_infinite <| not_imp_not.mpr (infinitesimal_iff_infinite_inv h).mpr hi
  (Exists.cases_on H) fun s hs =>
    have H' : IsSt 1 (r * s) := mul_inv_cancel h ▸ is_st_mul hxr hs
    have H'' : s = r⁻¹ := one_div r ▸ eq_one_div_of_mul_eq_one_right (eq_of_is_st_real H').symm
    H'' ▸ hs

theorem st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ := by
  by_cases' h0 : x = 0
  rw [h0, inv_zero, ← coe_zero, st_id_real, inv_zero]
  by_cases' h1 : infinitesimal x
  rw [st_infinite ((infinitesimal_iff_infinite_inv h0).mp h1), st_of_is_st h1, inv_zero]
  by_cases' h2 : Infinite x
  rw [st_of_is_st (infinitesimal_inv_of_infinite h2), st_infinite h2, inv_zero]
  exact st_of_is_st (is_st_inv h1 (is_st_st' h2))

/-!
### Infinite stuff that requires infinitesimal machinery
-/


theorem infinite_pos_omega : InfinitePos ω :=
  infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

theorem infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → 0 < y → InfinitePos (x * y) := fun hx hy₁ hy₂ r =>
  have hy₁' :=
    not_forall.mp
      (by
        rw [infinitesimal_def] at hy₁ <;> exact hy₁)
  (Exists.dcases_on hy₁') fun r₁ hy₁'' => by
    have hyr := by
      rw [not_imp, ← abs_lt, not_ltₓ, abs_of_pos hy₂] at hy₁'' <;> exact hy₁''
    rw [← div_mul_cancel r (ne_of_gtₓ hyr.1), coe_mul] <;>
      exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_ltₓ (hx 0))

theorem infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfinitePos y → InfinitePos (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hy hx hp

theorem infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → y < 0 → InfinitePos (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, ← neg_pos, ← neg_mul_neg, infinitesimal_neg_iff] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

theorem infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfiniteNeg y → InfinitePos (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hy hx hp

theorem infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → y < 0 → InfiniteNeg (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, ← neg_pos, neg_mul_eq_mul_neg, infinitesimal_neg_iff] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

theorem infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfinitePos y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hy hx hp

theorem infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → 0 < y → InfiniteNeg (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, infinite_neg_iff_infinite_pos_neg, neg_mul_eq_neg_mulₓ] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

theorem infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hy hx hp

theorem infinite_pos_mul_infinite_pos {x y : ℝ*} : InfinitePos x → InfinitePos y → InfinitePos (x * y) := fun hx hy =>
  infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

theorem infinite_neg_mul_infinite_neg {x y : ℝ*} : InfiniteNeg x → InfiniteNeg y → InfinitePos (x * y) := fun hx hy =>
  infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

theorem infinite_pos_mul_infinite_neg {x y : ℝ*} : InfinitePos x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hy =>
  infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

theorem infinite_neg_mul_infinite_pos {x y : ℝ*} : InfiniteNeg x → InfinitePos y → InfiniteNeg (x * y) := fun hx hy =>
  infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

theorem infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} : Infinite x → ¬Infinitesimal y → Infinite (x * y) :=
  fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_neₓ fun H0 => hy (Eq.substr H0 (is_st_refl_real 0))
  Or.dcases_on hx
    (Or.dcases_on h0 (fun H0 Hx => Or.inr (infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hx hy H0))
    (Or.dcases_on h0 (fun H0 Hx => Or.inl (infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inr (infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hx hy H0))

theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} : ¬Infinitesimal x → Infinite y → Infinite (x * y) :=
  fun hx hy => by
  rw [mul_comm] <;> exact infinite_mul_of_infinite_not_infinitesimal hy hx

theorem infinite_mul_infinite {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx (not_infinitesimal_of_infinite hy)

end Hyperreal

