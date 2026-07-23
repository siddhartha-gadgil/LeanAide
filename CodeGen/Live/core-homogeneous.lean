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
  intro G inst_14157295161945824867 l a_5288622521694023602 x y
  have assert_15969908638720860817 : l (y * x * y⁻¹) ≤ l x := by repeat (sorry)
  have assert_13069251041243470839 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l (y * x * y⁻¹) = l ((y * x * y⁻¹) ^ n) :=
    by
    intro inst l hl x y n hn
    letI := inst
    rcases hl with ⟨hpl, hhom⟩
    first
    | simpa using (hhom (y * x * y⁻¹) n hn).symm
    | simpa using (hhom (y * x * y⁻¹) n hn)
    | simpa using (hhom (y * x * y⁻¹) n).symm
    | simpa using (hhom (y * x * y⁻¹) n)
    | simpa using (hhom n (y * x * y⁻¹) hn).symm
    | simpa using (hhom n (y * x * y⁻¹) hn)
    | simpa using (hhom n (y * x * y⁻¹)).symm
    | simpa using (hhom n (y * x * y⁻¹))
  have assert_6975908855851819820 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l → ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → (y * x * y⁻¹) ^ n = y * x ^ n * y⁻¹ :=
    by simp only [conj_pow, implies_true]
  have assert_9020615521277418846 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l (y * x * y⁻¹) = l (y * x ^ n * y⁻¹) :=
    by
    intro inst l' hl x' y' n hn
    rw [assert_13069251041243470839 (inst := inst) l' hl x' y' n hn,
      assert_6975908855851819820 (inst := inst) l' hl x' y' n hn]
  have assert_13393355399038875995 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l → ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → l (y * x ^ n * y⁻¹) ≤ l y + l (x ^ n) + l y⁻¹ :=
    by grind only [IsHomogeneousPseudoLength, PseudoLength, #779d, #d1e8]
  have assert_770874412945853225 :
    ∀ [inst : Group G] (l : G → ℝ), IsHomogeneousPseudoLength l → ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → l y⁻¹ = l y := by
    grind only [IsHomogeneousPseudoLength, PseudoLength, #d1e8]
  have assert_1322500704111374650 :
    ∀ [inst : Group G] (l : G → ℝ), IsHomogeneousPseudoLength l → ∀ (x y : G), l (y * x * y⁻¹) = l x :=
    by
    intro inst l h x y
    letI : Group G := inst
    have hconj_le : ∀ (x y : G), l (y * x * y⁻¹) ≤ l x :=
      by
      intro x y
      by_contra hnot
      have hlt : l x < l (y * x * y⁻¹) := not_le.mp hnot
      have hdpos : 0 < l (y * x * y⁻¹) - l x := by linarith
      obtain ⟨n, hn_gt⟩ := exists_nat_gt (max (1 : ℝ) ((l y + l y) / (l (y * x * y⁻¹) - l x)))
      have h_n_real_pos : (0 : ℝ) < n :=
        by
        have h_one_lt : (1 : ℝ) < n :=
          lt_of_le_of_lt (le_max_left (1 : ℝ) ((l y + l y) / (l (y * x * y⁻¹) - l x))) hn_gt
        linarith
      have hnpos : 0 < n := by exact_mod_cast h_n_real_pos
      have hdiv_lt : (l y + l y) / (l (y * x * y⁻¹) - l x) < (n : ℝ) :=
        lt_of_le_of_lt (le_max_right (1 : ℝ) ((l y + l y) / (l (y * x * y⁻¹) - l x))) hn_gt
      have hC_lt : l y + l y < (n : ℝ) * (l (y * x * y⁻¹) - l x) :=
        by
        rw [div_lt_iff₀ hdpos] at hdiv_lt
        simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv_lt
      have h_pow : (n : ℝ) * l x = l (x ^ n) :=
        by
        have hp := assert_13069251041243470839 (inst := inst) l h x 1 n hnpos
        simpa using hp
      have h_inv : l y⁻¹ = l y := assert_770874412945853225 (inst := inst) l h x y n hnpos
      have h_eq : (n : ℝ) * l (y * x * y⁻¹) = l (y * x ^ n * y⁻¹) :=
        assert_9020615521277418846 (inst := inst) l h x y n hnpos
      have h_tri : l (y * x ^ n * y⁻¹) ≤ l y + l (x ^ n) + l y⁻¹ :=
        assert_13393355399038875995 (inst := inst) l h x y n hnpos
      have h_final_eq : l y + l (x ^ n) + l y⁻¹ = l y + (n : ℝ) * l x + l y := by rw [← h_pow, h_inv]
      have hleN : (n : ℝ) * l (y * x * y⁻¹) ≤ l y + (n : ℝ) * l x + l y :=
        by
        rw [h_eq]
        rw [← h_final_eq]
        exact h_tri
      nlinarith [hleN, hC_lt]
    exact
      le_antisymm (hconj_le x y)
        (by
          have hle := hconj_le (y * x * y⁻¹) y⁻¹
          simpa [mul_assoc] using hle)
  grind only [#a610]
theorem lemma_3 :
    ∀ (G : Type u_12) [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G), a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → l a ≤ (l y + l z) / (2 : ℝ) :=
  by
  intro G inst_14157295161945824867 l a_5288622521694023602 a w y z s t a_6383984861338069179 a_4866768517036219355
  have assert_18442646699720760567 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → ∀ (n : ℕ), (0 : ℕ) < n → a ^ n = s * (w * y) ^ n * s⁻¹ :=
    by repeat (sorry)
  have assert_4433385832573728897 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → ∀ (n : ℕ), (0 : ℕ) < n → a ^ n = t * (z * w⁻¹) ^ n * t⁻¹ :=
    by
    intro inst l_1 a_1 a_2 w_1 y_1 z_1 s_1 t_1 a_3 a_4 n a_5
    subst a_6383984861338069179 a_3
    simp_all only [conj_pow]
  have assert_3999321062533088758 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ →
            a = t * (z * w⁻¹) * t⁻¹ →
              ∀ (n : ℕ), (0 : ℕ) < n → a ^ ((2 : ℕ) * n) = s * (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n * t⁻¹ :=
    by
    intro inst l' hl a' w' y' z' s' t' hs ht n hn
    have h1 := assert_18442646699720760567 (inst := inst) l' hl a' w' y' z' s' t' hs ht n hn
    have h2 := assert_4433385832573728897 (inst := inst) l' hl a' w' y' z' s' t' hs ht n hn
    calc
      a' ^ (2 * n) = a' ^ n * a' ^ n := by rw [two_mul, pow_add]
      a' ^ n * a' ^ n = (s' * (w' * y') ^ n * s'⁻¹) * a' ^ n := by rw [h1]
      (s' * (w' * y') ^ n * s'⁻¹) * a' ^ n = (s' * (w' * y') ^ n * s'⁻¹) * (t' * (z' * w'⁻¹) ^ n * t'⁻¹) := by rw [h2]
      (s' * (w' * y') ^ n * s'⁻¹) * (t' * (z' * w'⁻¹) ^ n * t'⁻¹) =
          s' * (w' * y') ^ n * s'⁻¹ * t' * (z' * w'⁻¹) ^ n * t'⁻¹ :=
        by simp [mul_assoc]
  have assert_6448638436215229329 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ →
            a = t * (z * w⁻¹) * t⁻¹ → ∀ (n : ℕ), (0 : ℕ) < n → (↑((2 : ℕ) * n) : ℝ) * l a = l (a ^ ((2 : ℕ) * n)) :=
    by repeat (sorry)
  have assert_1682235720378939947 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ →
            a = t * (z * w⁻¹) * t⁻¹ →
              ∀ (n : ℕ),
                (0 : ℕ) < n → l (a ^ ((2 : ℕ) * n)) ≤ l s + l ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) + l t⁻¹ :=
    by
    intro inst' l' h' a' w' y' z' s' t' hs' ht' n hn
    letI : Group G := inst'
    let m : G := (w' * y') ^ n * s'⁻¹ * t' * (z' * w'⁻¹) ^ n
    have hpow : a' ^ (2 * n) = s' * (w' * y') ^ n * s'⁻¹ * t' * (z' * w'⁻¹) ^ n * t'⁻¹ :=
      @assert_3999321062533088758 inst' l' h' a' w' y' z' s' t' hs' ht' n hn
    rw [hpow]
    have htri : ∀ x y : G, l' (x * y) ≤ l' x + l' y := by
      first
      | exact h'.mul_le
      | exact h'.mul_le_add
      | exact h'.length_mul
      | exact h'.triangle
      | exact h'.1
      | exact h'.2
      | exact h'.3
      | exact h'.4
      | exact h'.1.1
      | exact h'.1.2
      | exact h'.2.1
      | exact h'.2.2
      | exact h'.1.2.2
      | exact h'.1.2.2.2
      | aesop  (add simp [IsHomogeneousPseudoLength, IsPseudoLength])
    have h1 : l' (s' * m * t'⁻¹) ≤ l' (s' * m) + l' t'⁻¹ := htri (s' * m) t'⁻¹
    have h2 : l' (s' * m) ≤ l' s' + l' m := htri s' m
    have h3 : l' (s' * m * t'⁻¹) ≤ l' s' + l' m + l' t'⁻¹ := by nlinarith
    simpa [m, mul_assoc] using h3
  have assert_1220477044916238898 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ →
            a = t * (z * w⁻¹) * t⁻¹ →
              ∀ (n : ℕ),
                (0 : ℕ) < n → l ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) ≤ l s⁻¹ + l t + (↑n : ℝ) * (l y + l z) :=
    by repeat (sorry)
  have assert_17991481076138951808 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G), a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → ∀ (n : ℕ), (0 : ℕ) < n → l s⁻¹ = l s :=
    by repeat (sorry)
  have assert_4469038508417128808 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G), a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → ∀ (n : ℕ), (0 : ℕ) < n → l t⁻¹ = l t :=
    by
    intro inst1 l1 hl a1 w1 y1 z1 s1 t1 h1 h2 n hn
    exact
      assert_17991481076138951808 (inst := inst1) (l := l1) hl a1 z1 w1⁻¹ (w1 * y1 * z1) t1 s1 h2
        (by simpa [mul_assoc] using h1) n hn
  have assert_2532486384229683008 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ →
            a = t * (z * w⁻¹) * t⁻¹ →
              ∀ (n : ℕ),
                (0 : ℕ) < n → (↑((2 : ℕ) * n) : ℝ) * l a ≤ (2 : ℝ) * l s + (2 : ℝ) * l t + (↑n : ℝ) * (l y + l z) :=
    by repeat (sorry)
  have assert_18164168398113666716 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G),
          a = s * (w * y) * s⁻¹ →
            a = t * (z * w⁻¹) * t⁻¹ → ∀ (n : ℕ), (0 : ℕ) < n → l a ≤ (l y + l z) / (2 : ℝ) + (l s + l t) / (↑n : ℝ) :=
    by repeat (sorry)
  have assert_1077745121518950193 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (a w y z s t : G), a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → l a ≤ (l y + l z) / (2 : ℝ) :=
    by repeat (sorry)
  exact assert_1077745121518950193 l a_5288622521694023602 a w y z s t a_6383984861338069179 a_4866768517036219355
theorem lemma_4 :
    ∀ (G : Type u_12) [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ), f m k ≤ (f (m - (1 : ℤ)) k + f (m + (1 : ℤ)) (k - (1 : ℤ))) / (2 : ℝ) :=
  by
  intro G inst_14157295161945824867 l a_5288622521694023602 x y c f m k
  let a : G := x ^ m * c ^ k
  let w : G := x
  let u : G := x ^ (m - 1) * c ^ k
  let v : G := y⁻¹ * x ^ m * c ^ (k - 1) * x * y
  have assert_15665916327694540794 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            a = x ^ m * c ^ k :=
    by simp only [implies_true]
  have assert_11674869339366833882 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            w = x :=
    by simp only [implies_true]
  have assert_9037165819738769132 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℕ → ℕ → ℝ := fun (m k : ℕ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            u = x ^ (m - (1 : ℤ)) * c ^ k :=
    by simp only [implies_true]
  have assert_5381524982797117950 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            w * u = a :=
    by repeat (sorry)
  have assert_5381524982797117950 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            w * u = a :=
    by grind only [#710b]
  have assert_10641974753323439939 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            ∃ (s : G), a = s * (w * u) * s⁻¹ :=
    by repeat (sorry)
  have assert_11674869339366833882 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            w = x :=
    by simp only [implies_true]
  have assert_15283677594251647278 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            v = y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y :=
    by simp only [implies_true]
  have assert_8048000074437989293 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ),
            have a : G := x ^ m * c ^ k;
            have w : G := x;
            have u : G := x ^ (m - (1 : ℤ)) * c ^ k;
            have v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
            v * w⁻¹ = y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y * x⁻¹ :=
    by simp only [implies_true]
  have assert_16329814440308656878 :
    ∀ [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹;
          have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
          ∀ (m k : ℤ), f m k ≤ (f (m - (1 : ℤ)) k + f (m + (1 : ℤ)) (k - (1 : ℤ))) / (2 : ℝ) :=
    by repeat (sorry)
  grind only [#9c95]
