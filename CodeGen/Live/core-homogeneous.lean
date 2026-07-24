import Mathlib
universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u₁ u₂ u₃
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
open scoped Nat
def PseudoLength {G R : Type _} [Group G] [Zero R] [Add R] [LE R] (l : G → R) : Prop :=
  (∀ g : G, 0 ≤ l g) ∧ l 1 = 0 ∧ (∀ g : G, l g⁻¹ = l g) ∧ ∀ g h : G, l (g * h) ≤ l g + l h
def IsLength {G R : Type _} [Group G] [Zero R] [Add R] [LE R] [LT R] (l : G → R) : Prop :=
  PseudoLength l ∧ ∀ g : G, g ≠ 1 → 0 < l g
def IsHomogeneousPseudoLength {G R : Type _} [Group G] [Zero R] [Add R] [LE R] [NatCast R] [Mul R] (l : G → R) : Prop :=
  PseudoLength l ∧ ∀ (g : G) (n : ℤ), l (g ^ n) = (Int.natAbs n : R) * l g
#check
  "commutatorElement has type {G : Type u_1} → [Group G] → Bracket G G with value `fun {G : Type u_1} [Group G] ↦ { bracket := fun (g₁ g₂ : G) ↦ g₁ * g₂ * g₁⁻¹ * g₂⁻¹ }`"
#check
  "commutator has type (G : Type u_1) → [inst : Group G] → Subgroup G with value `fun (G : Type u_1) [Group G] ↦ ⁅⊤, ⊤⁆`"
#check
  "Abelianization has type (G : Type u) → [Group G] → Type u with value `fun (G : Type u) [Group G] ↦ G ⧸ commutator G`"
#check
  "AddCommGroup.torsion has type (G : Type u_1) → [inst : AddCommGroup G] → AddSubgroup G with value `fun (G : Type u_1) [inst : AddCommGroup G] ↦\n  let __src : AddSubmonoid G := AddCommMonoid.addTorsion G;\n  { toAddSubmonoid := __src, neg_mem' := @AddCommGroup.torsion._proof_1 G inst }`"
def IsTorsionFree (A : Type _) [AddCommGroup A] : Prop :=
  AddCommGroup.torsion A = ⊥
theorem lemma_1 :
    ∀ (G : Type u_12) [inst : Group G] (l : G → ℝ), IsHomogeneousPseudoLength l → ∀ (x y : G), l (y * x * y⁻¹) = l x :=
  by
  intro G inst l a x y
  have assert_13069251041243470839 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l (y * x * y⁻¹) = l ((y * x * y⁻¹) ^ n) :=
    by
    intro inst_1 l_1 h_1 x_1 y_1 n_1 hn_1
    letI : Group G := inst_1
    let z : G := y_1 * x_1 * y_1⁻¹
    first
    | simpa [z, mul_comm] using (h_1.2 z n_1 hn_1).symm
    | simpa [z, mul_comm] using (h_1.2 z n_1 hn_1)
    | simpa [z, mul_comm] using (h_1.2 n_1 z hn_1).symm
    | simpa [z, mul_comm] using (h_1.2 n_1 z hn_1)
    | simpa [z, mul_comm] using (h_1.2 n_1 hn_1 z).symm
    | simpa [z, mul_comm] using (h_1.2 n_1 hn_1 z)
    | simpa [z, mul_comm] using (h_1.2 z n_1).symm
    | simpa [z, mul_comm] using (h_1.2 z n_1)
    | simpa [z, mul_comm] using (h_1.2 n_1 z).symm
    | simpa [z, mul_comm] using (h_1.2 n_1 z)
    | simpa [z, mul_comm] using (h_1.1 z n_1 hn_1).symm
    | simpa [z, mul_comm] using (h_1.1 z n_1 hn_1)
    | simpa [z, mul_comm] using (h_1.1 n_1 z hn_1).symm
    | simpa [z, mul_comm] using (h_1.1 n_1 z hn_1)
    | simpa [z, mul_comm] using (h_1.1 n_1 hn_1 z).symm
    | simpa [z, mul_comm] using (h_1.1 n_1 hn_1 z)
    | simpa [z, mul_comm] using (h_1.1 z n_1).symm
    | simpa [z, mul_comm] using (h_1.1 z n_1)
    | simpa [z, mul_comm] using (h_1.1 n_1 z).symm
    | simpa [z, mul_comm] using (h_1.1 n_1 z)
  have assert_2871322811644246378 : ∀ (n : ℕ), (0 : ℕ) < n → (y * x * y⁻¹) ^ n = y * x ^ n * y⁻¹ := by
    simp only [conj_pow, implies_true]
  have assert_2443844591074674155 : ∀ (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l (y * x * y⁻¹) = l (y * x ^ n * y⁻¹) := by
    grind only [#6418, #7a19]
  have assert_16587335859958109635 : ∀ (n : ℕ), (0 : ℕ) < n → l (y * x ^ n * y⁻¹) ≤ l y + l (x ^ n) + l y⁻¹ := by
    grind only [IsHomogeneousPseudoLength, PseudoLength, #67c8, #f957]
  have assert_770874412945853225 :
    ∀ [inst : Group G] (l : G → ℝ), IsHomogeneousPseudoLength l → ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → l y⁻¹ = l y := by
    grind only [IsHomogeneousPseudoLength, PseudoLength, #d1e8]
  have assert_12667148983041152940 : ∀ (n : ℕ), (0 : ℕ) < n → l (x ^ n) = (↑n : ℝ) * l x :=
    by
    intro n hn
    have h := assert_13069251041243470839 l a x 1 n hn
    simpa using h.symm
  have assert_551427383123442973 :
    ∀ (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l (y * x * y⁻¹) ≤ (2 : ℝ) * l y + (↑n : ℝ) * l x := by
    grind only [IsHomogeneousPseudoLength, PseudoLength, #13eb, #f663, #b46d, #f957]
  have assert_13007743013346282788 : ∀ (n : ℕ), (0 : ℕ) < n → l (y * x * y⁻¹) ≤ l x + (2 : ℝ) * l y / (↑n : ℝ) :=
    by
    intro n hn
    have h := assert_551427383123442973 n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply le_of_mul_le_mul_left (a := (n : ℝ))
    · have hr : (n : ℝ) * (l x + 2 * l y / (n : ℝ)) = 2 * l y + (n : ℝ) * l x :=
        by
        field_simp [ne_of_gt hnR]
        ring
      rw [hr]
      exact h
    · exact hnR
  have assert_13007743013346282788 : ∀ (n : ℕ), (0 : ℕ) < n → l (y * x * y⁻¹) ≤ l x + (2 : ℝ) * l y / (↑n : ℝ) := by
    grind only [#92c1]
  have assert_15969908638720860817 : l (y * x * y⁻¹) ≤ l x :=
    by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * l y / ε) 0)
    have hn0R : (0 : ℝ) < (n : ℝ) := by exact lt_of_le_of_lt (le_max_right (2 * l y / ε) 0) hn
    have hnpos : 0 < n := by exact Nat.cast_pos.mp hn0R
    have hcε : 2 * l y / ε < (n : ℝ) := by exact lt_of_le_of_lt (le_max_left (2 * l y / ε) 0) hn
    have hcn : 2 * l y < (n : ℝ) * ε := by exact (div_lt_iff₀ hε).1 hcε
    have hce : 2 * l y / (n : ℝ) < ε := by exact (div_lt_iff₀ hn0R).2 (by simpa [mul_comm] using hcn)
    have hmain := assert_13007743013346282788 n hnpos
    linarith
  let z : G := y * x * y⁻¹
  have assert_175800960906898629 : y * x * y⁻¹ = y * x * y⁻¹ := by simp only
  have assert_17768794013527502964 : x = y⁻¹ * (y * x * y⁻¹) * y := by simp [mul_assoc]
  repeat (sorry)
theorem lemma_2 :
    ∀ (G : Type u_12) [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (w y z s t : G),
          have C : ℕ → G := fun (n : ℕ) ↦ (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n;
          ∀ (n : ℕ), l (C n) ≤ l s⁻¹ + l t + (↑n : ℝ) * (l y + l z) :=
  by
  intro G inst l a w y z s t C n
  induction n with
  |
    zero =>
    have assert_14337186159885095727 : (fun (n : ℕ) ↦ (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) (0 : ℕ) = s⁻¹ * t := by
      simp only [pow_zero, one_mul, mul_one]
    have assert_14337186159885095727 : (fun (n : ℕ) ↦ (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) (0 : ℕ) = s⁻¹ * t := by
      simp only [pow_zero, one_mul, mul_one]
    have assert_12380498979322745870 :
      l ((fun (n : ℕ) ↦ (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) (0 : ℕ)) ≤ l s⁻¹ + l t := by
      grind only [IsHomogeneousPseudoLength, PseudoLength, #67c8]
    simp only [CharP.cast_eq_zero, zero_mul, add_zero]
    exact RCLike.ofReal_le_ofReal.mp assert_12380498979322745870
  | succ n ih => repeat (sorry)
  done
theorem lemma_3 :
    ∀ (G : Type u_12) [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G), a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → l a ≤ (l y + l z) / (2 : ℝ) :=
  by
  intro G inst l a a w y z s t a a
  repeat (sorry)
theorem lemma_4 :
    ∀ (G : Type u_12) [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ), f m k ≤ (f (m - (1 : ℤ)) k + f (m + (1 : ℤ)) (k - (1 : ℤ))) / (2 : ℝ) :=
  by
  intro G inst l a x y c f m k
  let a : G := x ^ m * c ^ k
  let w : G := x
  let u : G := x ^ (m - 1) * c ^ k
  let v : G := y⁻¹ * x ^ m * c ^ (k - 1) * x * y
  have assert_11691313655442793857 : x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k = x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k := by simp only
  have assert_14462059531505177398 : x = x := by simp only
  have assert_12117618858602479733 :
    x ^ (m - (1 : ℤ)) * (x * y * x⁻¹ * y⁻¹) ^ k = x ^ (m - (1 : ℤ)) * (x * y * x⁻¹ * y⁻¹) ^ k := by simp only
  have assert_6966404488016412834 :
    ∃ (s : G), x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k = s * (x * (x ^ (m - (1 : ℤ)) * (x * y * x⁻¹ * y⁻¹) ^ k)) * s⁻¹ := by
    exact
      ⟨1, by
        simp only [one_mul, inv_one, mul_one]
        rw [show x ^ m = x * x ^ (m - 1) by
            calc
              x ^ m = x ^ ((1 : ℤ) + (m - 1)) := by
                exact congrArg (fun n : ℤ => x ^ n) (show m = (1 : ℤ) + (m - 1) by omega)
              _ = x ^ (1 : ℤ) * x ^ (m - 1) := by exact zpow_add x (1 : ℤ) (m - 1)
              _ = x * x ^ (m - 1) := by simp]
        exact mul_assoc x (x ^ (m - 1)) ((x * y * x⁻¹ * y⁻¹) ^ k)⟩
  let ⟨s, assert_2575407295094486384⟩ := assert_6966404488016412834
  have assert_14462059531505177398 : x = x := by simp only
  have assert_10939558576725088047 :
    y⁻¹ * x ^ m * (x * y * x⁻¹ * y⁻¹) ^ (k - (1 : ℤ)) * x * y * x⁻¹ =
      y⁻¹ * x ^ m * (x * y * x⁻¹ * y⁻¹) ^ (k - (1 : ℤ)) * x * y * x⁻¹ :=
    by simp only
  have assert_2905112804828581331 : x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y := by simp only [inv_mul_cancel_right]
  have assert_11691313655442793857 : x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k = x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k := by simp only
  have assert_3120733429779813021 :
    x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k = y * (y⁻¹ * x ^ m * (x * y * x⁻¹ * y⁻¹) ^ (k - (1 : ℤ)) * x * y * x⁻¹) * y⁻¹ :=
    by
    change x ^ m * c ^ k = y * (y⁻¹ * x ^ m * c ^ (k - 1) * x * y * x⁻¹) * y⁻¹
    calc
      x ^ m * c ^ k = x ^ m * (c ^ (k - 1) * c) :=
        by
        conv_lhs =>
          rw [show k = (k - 1) + 1 by omega]
          rw [zpow_add]
        simp
      _ = y * (y⁻¹ * x ^ m * c ^ (k - 1) * x * y * x⁻¹) * y⁻¹ :=
        by
        change x ^ m * (c ^ (k - 1) * (x * y * x⁻¹ * y⁻¹)) = y * (y⁻¹ * x ^ m * c ^ (k - 1) * x * y * x⁻¹) * y⁻¹
        group
  have assert_3120733429779813021 :
    x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k = y * (y⁻¹ * x ^ m * (x * y * x⁻¹ * y⁻¹) ^ (k - (1 : ℤ)) * x * y * x⁻¹) * y⁻¹ := by
    grind only
  have assert_15418840957454385079 :
    ∃ (t : G),
      x ^ m * (x * y * x⁻¹ * y⁻¹) ^ k = t * (y⁻¹ * x ^ m * (x * y * x⁻¹ * y⁻¹) ^ (k - (1 : ℤ)) * x * y * x⁻¹) * t⁻¹ :=
    by grind only [#5f4c]
  let ⟨t, assert_9542014915168661426⟩ := assert_15418840957454385079
  repeat (sorry)
