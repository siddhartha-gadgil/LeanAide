import Mathlib
universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u₁ u₂ u₃
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
open scoped Nat
def IsPseudoLengthFunction {G : Type u} [Group G] (l : G → ℝ) : Prop :=
  (∀ g : G, 0 ≤ l g) ∧ l 1 = 0 ∧ (∀ g : G, l g⁻¹ = l g) ∧ ∀ g h : G, l (g * h) ≤ l g + l h
def IsLengthFunction {G : Type u} [Group G] (l : G → ℝ) : Prop :=
  IsPseudoLengthFunction l ∧ ∀ g : G, g ≠ 1 → 0 < l g
def IsHomogeneousPseudoLengthFunction {G : Type u} [Group G] (l : G → ℝ) : Prop :=
  IsPseudoLengthFunction l ∧ ∀ (g : G) (n : ℤ), l (g ^ n) = (|n| : ℝ) * l g
def commutatorOf {G : Type u} [Group G] (x y : G) : G :=
  x * y * x⁻¹ * y⁻¹
#check
  "commutator has type (G : Type u_1) → [inst : Group G] → Subgroup G with value `fun (G : Type u_1) [Group G] ↦ ⁅⊤, ⊤⁆`"
#check
  "Abelianization has type (G : Type u) → [Group G] → Type u with value `fun (G : Type u) [Group G] ↦ G ⧸ commutator G`"
#check
  "AddCommGroup.torsion has type (G : Type u_1) → [inst : AddCommGroup G] → AddSubgroup G with value `fun (G : Type u_1) [inst : AddCommGroup G] ↦\n  let __src : AddSubmonoid G := AddCommMonoid.addTorsion G;\n  { toAddSubmonoid := __src, neg_mem' := @AddCommGroup.torsion._proof_1 G inst }`"
def AddCommGroup.IsTorsionFree (A : Type u) [AddCommGroup A] : Prop :=
  AddCommGroup.torsion A = ⊥
theorem lemma_1 :
    ∀ {G : Type u} [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l → ∀ (x y : G), l (y * x * y⁻¹) = l x :=
  by
  intro G inst_14157295161945824867 l a_13742212264671640311 x y
  skip
  skip
  have assert_5790946114200499261 :
    ∀ [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l (y * x * y⁻¹) = l ((y * x * y⁻¹) ^ n) :=
    by repeat (sorry)
  have assert_5742558469992571474 :
    ∀ [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l → ∀ (x y : G) (n : ℕ), (y * x * y⁻¹) ^ n = y * x ^ n * y⁻¹ :=
    by simp only [conj_pow, implies_true]
  have assert_11405829848588808205 :
    ∀ [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∀ (x y : G) (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l (y * x * y⁻¹) ≤ l y + (↑n : ℝ) * l x + l y :=
    by repeat (sorry)
  have assert_12651788557525272244 :
    ∀ [inst : Group G] {l : G → ℝ}, IsHomogeneousPseudoLengthFunction l → ∀ (x y : G), l (y * x * y⁻¹) ≤ l x :=
    by
    intro inst' l' hl x' y'
    by_contra h
    have hlt : l' x' < l' (y' * x' * y'⁻¹) := by exact lt_of_not_ge h
    have hpos : 0 < l' (y' * x' * y'⁻¹) - l' x' := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (max (0 : ℝ) ((l' y' + l' y') / (l' (y' * x' * y'⁻¹) - l' x')))
    have hnpos_real : (0 : ℝ) < n := by
      exact lt_of_le_of_lt (le_max_left (0 : ℝ) ((l' y' + l' y') / (l' (y' * x' * y'⁻¹) - l' x'))) hn
    have hnpos : 0 < n := by exact_mod_cast hnpos_real
    have hineq := assert_11405829848588808205 (inst := inst') (l := l') hl x' y' n hnpos
    have hbound : (l' y' + l' y') / (l' (y' * x' * y'⁻¹) - l' x') < (n : ℝ) := by
      exact lt_of_le_of_lt (le_max_right (0 : ℝ) ((l' y' + l' y') / (l' (y' * x' * y'⁻¹) - l' x'))) hn
    have hmul : l' y' + l' y' < (n : ℝ) * (l' (y' * x' * y'⁻¹) - l' x') := by exact (div_lt_iff₀ hpos).mp hbound
    nlinarith [hineq, hmul]
  have assert_7551020425540356450 :
    ∀ [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∀ (x y : G),
          have z : G := y * x * y⁻¹;
          x = y⁻¹ * z * y :=
    by
    intro inst l hl x y
    dsimp
    group
  have assert_5473316382650752993 :
    ∀ [inst : Group G] {l : G → ℝ}, IsHomogeneousPseudoLengthFunction l → ∀ (a b : G), l (a * b * a⁻¹) ≤ l b := by
    grind only [#9c11]
  skip
  have assert_2124959872803431686 :
    ∀ [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∀ (x y : G),
          have z : G := y * x * y⁻¹;
          l x ≤ l z :=
    by
    intro inst l hl x y
    simpa [mul_assoc] using (assert_5473316382650752993 hl (y⁻¹) (y * x * y⁻¹))
  grind only [#9c11, #e5e3]
theorem lemma_2 :
    ∀ {G : Type u} [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∀ (w y z s t : G) (n : ℕ), l ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) ≤ l s⁻¹ + l t + (↑n : ℝ) * (l y + l z) :=
  by
  intro G inst l a_13742212264671640311 w y z s t n
  induction n with
  |
    zero =>
    have assert_3492263107636392333 :
      ∀ (n : ℕ),
        have C0 : G := s⁻¹ * t;
        C0 = s⁻¹ * t :=
      by simp only [implies_true]
    skip
    repeat (sorry)
  | succ n
    ih =>
    have assert_7215831494667657132 :
      (w * y) ^ (n + (1 : ℕ)) * s⁻¹ * t * (z * w⁻¹) ^ (n + (1 : ℕ)) =
        w * y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z * w⁻¹ :=
      by
      rw [pow_succ' (w * y) n, pow_succ (z * w⁻¹) n]
      simp only [mul_assoc]
    have assert_9273070740478554127 :
      w * y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z * w⁻¹ =
        w * (y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z) * w⁻¹ :=
      by grind only
    have assert_7654440114523236392 :
      (w * y) ^ (n + (1 : ℕ)) * s⁻¹ * t * (z * w⁻¹) ^ (n + (1 : ℕ)) =
          w * y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z * w⁻¹ ∧
        w * y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z * w⁻¹ =
          w * (y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z) * w⁻¹ :=
      by grind only
    have assert_17052096365617556545 :
      l ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) ≤ l s⁻¹ + l t + (↑n : ℝ) * (l y + l z) := by grind only
    have assert_2823808946488767840 :
      (w * y) ^ (n + (1 : ℕ)) * s⁻¹ * t * (z * w⁻¹) ^ (n + (1 : ℕ)) =
        w * (y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z) * w⁻¹ :=
      by grind only
    have assert_1239901290484589091 :
      l ((w * y) ^ (n + (1 : ℕ)) * s⁻¹ * t * (z * w⁻¹) ^ (n + (1 : ℕ))) =
        l (y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z) :=
      by repeat (sorry)
    have assert_11449210674163644275 :
      l (y * ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) * z) ≤ l y + l ((w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n) + l z := by
      grind only [IsHomogeneousPseudoLengthFunction, IsPseudoLengthFunction, #67c8]
    grind only
  done
theorem lemma_3 :
    ∀ {G : Type u} [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∀ (a w y z s t : G), a = s * (w * y) * s⁻¹ → a = t * (z * w⁻¹) * t⁻¹ → l a ≤ (l y + l z) / (2 : ℝ) :=
  by
  intro G inst l a_13742212264671640311 a w y z s t a_6383984861338069179 a_4866768517036219355
  have homogeneous_root_lemma_3_proof_root_step1 :
    ∀ (n : ℕ), (0 : ℕ) < n → a ^ ((2 : ℕ) * n) = s * (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n * t⁻¹ :=
    by
    intro n a_403291135785739150
    skip
    repeat (sorry)
  have homogeneous_root_lemma_3_proof_root_step2 : ∀ (n : ℕ), (2 : ℝ) * (↑n : ℝ) * l a = l (a ^ ((2 : ℕ) * n)) :=
    by
    intro n
    skip
    repeat (sorry)
  have assert_16152539812700432052 :
    ∀ (n : ℕ), l (a ^ ((2 : ℕ) * n)) ≤ (2 : ℝ) * l s + (2 : ℝ) * l t + (↑n : ℝ) * (l y + l z) := by repeat (sorry)
  have homogeneous_root_lemma_3_proof_root_step4 : l a ≤ (l y + l z) / (2 : ℝ) :=
    by
    skip
    skip
    repeat (sorry)
  assumption
theorem lemma_4 :
    ∀ {G : Type u} [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∀ (x y : G) (m k : ℤ),
          l (x ^ m * commutatorOf x y ^ k) ≤
            (l (x ^ (m - (1 : ℤ)) * commutatorOf x y ^ k) + l (x ^ (m + (1 : ℤ)) * commutatorOf x y ^ (k - (1 : ℤ)))) /
              (2 : ℝ) :=
  by
  intro G inst l a_13742212264671640311 x y m k
  skip
  skip
  skip
  have assert_4445243574289798553 :
    let w : G := x;
    w = x :=
    by simp only
  skip
  have assert_4970717258277477702 :
    let c : G := commutatorOf x y;
    let a : G := x ^ m * c ^ k;
    let w : G := x;
    let u : G := x ^ (m - (1 : ℤ)) * c ^ k;
    a = w * u :=
    by
    dsimp
    rw [← mul_assoc]
    congr 1
    calc
      x ^ m = x ^ ((1 : ℤ) + (m - 1)) := by
        have hm : (1 : ℤ) + (m - 1) = m := by omega
        rw [hm]
      _ = x * x ^ (m - 1) := by rw [zpow_add, zpow_one]
  skip
  skip
  have assert_4445243574289798553 :
    let w : G := x;
    w = x :=
    by simp only
  skip
  skip
  skip
  skip
  skip
  have assert_17113388533810973643 :
    let c : G := commutatorOf x y;
    let f : ℤ × ℤ → ℝ := fun (p : ℤ × ℤ) ↦ l (x ^ p.1 * c ^ p.2);
    let u : G := x ^ (m - (1 : ℤ)) * c ^ k;
    l u = f (m - (1 : ℤ), k) :=
    by simp only
  have assert_17113388533810973643 :
    let c : G := commutatorOf x y;
    let f : ℤ × ℤ → ℝ := fun (p : ℤ × ℤ) ↦ l (x ^ p.1 * c ^ p.2);
    let u : G := x ^ (m - (1 : ℤ)) * c ^ k;
    l u = f (m - (1 : ℤ), k) :=
    by simp only
  skip
  skip
  have assert_996369908626414054 :
    let c : G := commutatorOf x y;
    let v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
    IsConj v (x ^ (m + (1 : ℤ)) * c ^ (k - (1 : ℤ))) :=
    by repeat (sorry)
  skip
  have assert_16155731403314489007 :
    let c : G := commutatorOf x y;
    let f : ℤ × ℤ → ℝ := fun (p : ℤ × ℤ) ↦ l (x ^ p.1 * c ^ p.2);
    let v : G := y⁻¹ * x ^ m * c ^ (k - (1 : ℤ)) * x * y;
    l v = f (m + (1 : ℤ), k - (1 : ℤ)) :=
    by repeat (sorry)
  skip
  skip
  skip
  repeat (sorry)
noncomputable def lemma_6 : {Ω : Type u} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → (Ω → ℝ) → Prop :=
  by
  intro Ω inst_14546896174491015166 μ X
  exact True
theorem proposition_7 :
    ∀ {G : Type u} [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l → ∀ (x y : G), l (commutatorOf x y) = (0 : ℝ) :=
  by
  intro G inst l a_13742212264671640311 x y
  skip
  skip
  have assert_5655885530702567672 : ∀ (n : ℕ), (0 : ℕ) < n → (0 : ℕ) < n := by simp only [imp_self, implies_true]
  skip
  have assert_4586120170227221684 :
    ∀ (n : ℤ),
      have c : G := commutatorOf x y;
      have f : ℤ → ℤ → ℝ := fun (m k : ℤ) ↦ l (x ^ m * c ^ k);
      x ^ (0 : ℤ) * c ^ n = c ^ n :=
    by simp only [zpow_zero, one_mul, implies_true]
  skip
  skip
  skip
  skip
  skip
  have assert_11293218158616298778 :
    ∀ (n : ℕ) {Ω : Type v} [inst_1 : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (S : ℕ → Ω → ℤ),
      ∫ (ω : Ω), l (x ^ S ((2 : ℕ) * n) ω * commutatorOf x y ^ (-(S ((2 : ℕ) * n) ω / (2 : ℤ)))) ∂μ ≤
        (∫ (ω : Ω), |(↑(S ((2 : ℕ) * n) ω) : ℝ)| ∂μ) * (l x + l (commutatorOf x y) / (2 : ℝ)) :=
    by repeat (sorry)
  skip
  have assert_8203718329282491899 :
    let c : G := commutatorOf x y;
    ∀ (n : ℕ), (0 : ℕ) < n → (↑n : ℝ) * l c ≤ √((2 : ℝ) * (↑n : ℝ)) * (l x + l c / (2 : ℝ)) :=
    by repeat (sorry)
  skip
  have assert_12949747327812069197 : l (commutatorOf x y) = (0 : ℝ) := by repeat (sorry)
  assumption
theorem lemma_8 :
    ∀ {G : Type u} [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l → ∀ g ∈ commutator G, l g = (0 : ℝ) :=
  by
  intro G inst l a_13742212264671640311 g a_742108398469634028
  have assert_6341423747180187762 : l g = (0 : ℝ) := by repeat (sorry)
  assumption
theorem lemma_9 :
    ∀ {G : Type u} [inst : Group G] {l : G → ℝ},
      IsHomogeneousPseudoLengthFunction l →
        ∃! barL : Abelianization G → ℝ,
          (∀ (g : G), l g = barL ((Abelianization.of : G → Abelianization G) g)) ∧
            IsHomogeneousPseudoLengthFunction barL :=
  by
  intro G inst l a_13742212264671640311
  have assert_16620396870228008564 :
    ∀ (g h : G),
      (Abelianization.of : G → Abelianization G) g = (Abelianization.of : G → Abelianization G) h →
        h⁻¹ * g ∈ commutator G :=
    by repeat (sorry)
  have assert_3563620182522098970 :
    ∀ (g h : G),
      (Abelianization.of : G → Abelianization G) g = (Abelianization.of : G → Abelianization G) h →
        l (h⁻¹ * g) = (0 : ℝ) :=
    by
    intro g h a
    apply lemma_8
    · simp_all only
    · simp_all only
  have assert_17022229953596322849 :
    ∀ (g h : G),
      (Abelianization.of : G → Abelianization G) g = (Abelianization.of : G → Abelianization G) h → g = h * (h⁻¹ * g) :=
    by simp only [mul_inv_cancel_left, implies_true]
  have assert_18397124325701840180 :
    ∀ (g h : G),
      (Abelianization.of : G → Abelianization G) g = (Abelianization.of : G → Abelianization G) h → l g = l h :=
    by grind only [IsHomogeneousPseudoLengthFunction, IsPseudoLengthFunction, #0cf4, #741f, #67c8, #f957]
  have assert_18397124325701840180 :
    ∀ (g h : G),
      (Abelianization.of : G → Abelianization G) g = (Abelianization.of : G → Abelianization G) h → l g = l h :=
    by grind only [#876c]
  have assert_18397124325701840180 :
    ∀ (g h : G),
      (Abelianization.of : G → Abelianization G) g = (Abelianization.of : G → Abelianization G) h → l g = l h :=
    by grind only [#876c]
  have assert_10162204231442207603 : Abelianization G → ℝ := by exact fun x => 0
  have assert_7870548801138213004 :
    ∃ (barL : Abelianization G → ℝ), l = barL ∘ (⇑Abelianization.of : G → Abelianization G) := by
    classical
    have hsurj : Function.Surjective (Abelianization.of : G → Abelianization G) := by
      simpa [Abelianization.of] using (QuotientGroup.mk'_surjective (commutator G))
    let barL : Abelianization G → ℝ := fun x => l (Classical.choose (hsurj x))
    exact
      ⟨barL, by
        funext g
        dsimp [barL]
        have hspec : Abelianization.of (Classical.choose (hsurj (Abelianization.of g))) = Abelianization.of g :=
          Classical.choose_spec (hsurj (Abelianization.of g))
        exact assert_18397124325701840180 g (Classical.choose (hsurj (Abelianization.of g))) hspec.symm⟩
  let ⟨barL, assert_12490431689588984358⟩ := assert_7870548801138213004
  have assert_11951970955198732883 :
    ∃ (barL : Abelianization G → ℝ), ∀ (g : G), barL ((Abelianization.of : G → Abelianization G) g) = l g :=
    by
    use barL
    intro g
    have h := congrArg (fun f : G → ℝ => f g) assert_12490431689588984358
    simpa [Function.comp] using h.symm
  let ⟨barL, assert_17274311165594130021⟩ := assert_11951970955198732883
  repeat (sorry)
  have assert_13313675123275672338 :
    ∃ (barL : Abelianization G → ℝ), ∀ (g : G), l g = barL ((Abelianization.of : G → Abelianization G) g) := by
    repeat (sorry)
  let ⟨barL, assert_13394456181322342941⟩ := assert_13313675123275672338
  have assert_5744831359362091977 :
    ∃! barL : Abelianization G → ℝ, ∀ (g : G), l g = barL ((Abelianization.of : G → Abelianization G) g) := by
    classical
    have hsurj : Function.Surjective (Abelianization.of : G → Abelianization G) :=
      by
      intro x
      induction x using Quotient.inductionOn with
      | h g =>
        use g
        rfl
    let barL : Abelianization G → ℝ := fun x => l (Classical.choose (hsurj x))
    have hbar : ∀ g : G, l g = barL (Abelianization.of g) :=
      by
      intro g
      dsimp [barL]
      exact
        assert_18397124325701840180 g (Classical.choose (hsurj (Abelianization.of g)))
          (Classical.choose_spec (hsurj (Abelianization.of g))).symm
    use barL
    constructor
    · exact hbar
    · intro y hy
      funext x
      rcases hsurj x with ⟨g, hx⟩
      rw [← hx]
      exact (hy g).symm.trans (hbar g)
  have assert_11951970955198732883 :
    ∃ (barL : Abelianization G → ℝ), ∀ (g : G), barL ((Abelianization.of : G → Abelianization G) g) = l g := by
    repeat (sorry)
  let ⟨barL, assert_17274311165594130021⟩ := assert_11951970955198732883
  have assert_14691208061470985543 :
    ∀ (barL : Abelianization G → ℝ),
      (∀ (g : G), barL ((Abelianization.of : G → Abelianization G) g) = l g) → IsPseudoLengthFunction barL :=
    by repeat (sorry)
  have assert_11951970955198732883 :
    ∃ (barL : Abelianization G → ℝ), ∀ (g : G), barL ((Abelianization.of : G → Abelianization G) g) = l g := by
    repeat (sorry)
  let ⟨barL, assert_17274311165594130021⟩ := assert_11951970955198732883
  have assert_6178008560903312880 :
    ∃ (barL : Abelianization G → ℝ),
      (∀ (g : G), barL ((Abelianization.of : G → Abelianization G) g) = l g) ∧ IsHomogeneousPseudoLengthFunction barL :=
    by repeat (sorry)
  let ⟨barL, assert_3985980028508056518⟩ := assert_6178008560903312880
theorem lemma_10 :
    ∀ {A : Type u} [inst : AddCommGroup A] {p : A → ℝ},
      ((∀ (a : A), (0 : ℝ) ≤ p a) ∧
          p (0 : A) = (0 : ℝ) ∧
            (∀ (a : A), p (-a) = p a) ∧
              (∀ (a b : A), p (a + b) ≤ p a + p b) ∧ ∀ (a : A) (n : ℤ), p (n • a) = |(↑n : ℝ)| * p a) →
        ∀ {a : A}, a ∈ AddCommGroup.torsion A → p a = (0 : ℝ) :=
  by
  intro A inst p a_12682437045089875018 a a_7716973000511042354
  have assert_5496125317810022441 : p a = (0 : ℝ) := by repeat (sorry)
  assumption
theorem lemma_11 :
    ∀ {A : Type u} [inst : AddCommGroup A] {p : A → ℝ},
      ((∀ (a : A), (0 : ℝ) ≤ p a) ∧
          p (0 : A) = (0 : ℝ) ∧
            (∀ (a : A), p (-a) = p a) ∧
              (∀ (a b : A), p (a + b) ≤ p a + p b) ∧ ∀ (a : A) (n : ℤ), p (n • a) = |(↑n : ℝ)| * p a) →
        ∃! barP : A ⧸ AddCommGroup.torsion A → ℝ,
          (∀ (a : A), p a = barP (↑a : A ⧸ AddCommGroup.torsion A)) ∧
            (∀ (q : A ⧸ AddCommGroup.torsion A), (0 : ℝ) ≤ barP q) ∧
              barP (0 : A ⧸ AddCommGroup.torsion A) = (0 : ℝ) ∧
                (∀ (q : A ⧸ AddCommGroup.torsion A), barP (-q) = barP q) ∧
                  (∀ (q r : A ⧸ AddCommGroup.torsion A), barP (q + r) ≤ barP q + barP r) ∧
                    ∀ (q : A ⧸ AddCommGroup.torsion A) (n : ℤ), barP (n • q) = |(↑n : ℝ)| * barP q :=
  by
  intro A inst p a_12682437045089875018
  have assert_9124132485801967019 : ∀ {a : A}, a ∈ AddCommGroup.torsion A → p a = (0 : ℝ) :=
    by
    intro a ha
    rcases a_12682437045089875018 with ⟨h_nonneg, hp0, h_neg, h_tri, hsmul⟩
    have hn : addOrderOf a ≠ 0 := by simpa [AddCommGroup.torsion, IsOfFinAddOrder] using ha
    have hza : p (((addOrderOf a : ℤ) • a)) = 0 :=
      by
      have hna : addOrderOf a • a = 0 := addOrderOf_nsmul_eq_zero a
      simpa [hp0] using congrArg p hna
    have hmul : |(((addOrderOf a : ℤ) : ℝ))| * p a = 0 :=
      by
      rw [← hsmul a (addOrderOf a : ℤ)]
      exact hza
    have hnreal : |(((addOrderOf a : ℤ) : ℝ))| ≠ 0 := by simp [hn]
    exact (mul_eq_zero.mp hmul).resolve_left hnreal
  have assert_13776255010140787939 :
    ∃! barP : A ⧸ AddCommGroup.torsion A → ℝ, ∀ (a : A), p a = barP (↑a : A ⧸ AddCommGroup.torsion A) := by
    repeat (sorry)
  have assert_17781383769770710348 :
    ∃ (q : A →+ A ⧸ AddCommGroup.torsion A),
      ∀ (a : A), (q : A → A ⧸ AddCommGroup.torsion A) a = (↑a : A ⧸ AddCommGroup.torsion A) :=
    by repeat (sorry)
  let ⟨q, assert_10212535322622641401⟩ := assert_17781383769770710348
  have assert_13776255010140787939 :
    ∃! barP : A ⧸ AddCommGroup.torsion A → ℝ, ∀ (a : A), p a = barP (↑a : A ⧸ AddCommGroup.torsion A) := by grind only
  have assert_13854942829501630507 :
    ∀ (barP : A ⧸ AddCommGroup.torsion A → ℝ),
      (∀ (a : A), p a = barP (↑a : A ⧸ AddCommGroup.torsion A)) →
        (∀ (q : A ⧸ AddCommGroup.torsion A), (0 : ℝ) ≤ barP q) ∧
          barP (0 : A ⧸ AddCommGroup.torsion A) = (0 : ℝ) ∧
            (∀ (q : A ⧸ AddCommGroup.torsion A), barP (-q) = barP q) ∧
              (∀ (q r : A ⧸ AddCommGroup.torsion A), barP (q + r) ≤ barP q + barP r) ∧
                ∀ (q : A ⧸ AddCommGroup.torsion A) (n : ℤ), barP (n • q) = |(↑n : ℝ)| * barP q :=
    by repeat (sorry)
  rcases assert_13776255010140787939 with ⟨barP, hbarP, huniq⟩
  use barP
  constructor
  · constructor
    · exact hbarP
    · exact assert_13854942829501630507 barP hbarP
  · intro y hy
    exact huniq y hy.1
theorem lemma_13 :
    ∀ {VQ : Type u} [inst : AddCommGroup VQ] [inst_1 : Module ℚ VQ] (normQ : Seminorm ℚ VQ),
      ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
        VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
  by
  intro VQ inst inst_1 normQ
  have assert_exists_8220810582158213931 :
    have homogeneous_root_lemma_13_proof_root_kernel_subspace :
      ∃ (N : Submodule ℚ VQ), (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} := sorry `_sorry._@._hyg.14105;
    ?m.2643 :=
    by
    let completionB {VQ : Type u} [AddCommGroup VQ] [Module ℚ VQ] (normQ : Seminorm ℚ VQ) : Type u :=
      Classical.choose (lemma_13 normQ)
    use completionB
    have homogeneous_root_lemma_13_proof_root_kernel_subspace :
      ∃ (N : Submodule ℚ VQ), (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} :=
      by
      skip
      skip
      repeat (sorry)
    skip
    have assert_exists_8220810582158213931 : ?m.2645 :=
      by
      let completionB {W : Type u} [PseudoMetricSpace W] : Type u := UniformSpace.Completion W
      use completionB
      have homogeneous_root_lemma_13_proof_root_completion_verification :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B),
          DenseRange (⇑iota : VQ → B) ∧ ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      repeat (sorry)
    let ⟨completionB, assert_prop_8220810582158213931⟩ := assert_exists_8220810582158213931
    have verification_8220810582158213931 :
      ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
        VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
      by
      have homogeneous_root_lemma_13_proof_root_completion_verification :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B),
          DenseRange (⇑iota : VQ → B) ∧ ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      repeat (sorry)
    have homogeneous_root_lemma_13_proof_root_extend_rational_operations :
      ∀ (N : Submodule ℚ VQ),
        (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
          ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
            Nonempty (NormedSpace ℚ (UniformSpace.Completion (VQ ⧸ N))) :=
      by
      intro N a_485438065194403264 instW instWNS
      exact ⟨inferInstance⟩
    have assert_exists_3291407328229044655 : ?m.2692 :=
      by
      let scalarMul {VQ : Type u} [inst : AddCommGroup VQ] [inst_1 : Module ℚ VQ] (normQ : Seminorm ℚ VQ)
        (N : Submodule ℚ VQ) (_hN : ↑N = {v : VQ | normQ v = 0}) [instW : NormedAddCommGroup (VQ ⧸ N)]
        [instWNS : NormedSpace ℚ (VQ ⧸ N)] : ℝ → UniformSpace.Completion (VQ ⧸ N) → UniformSpace.Completion (VQ ⧸ N) :=
        by sorry
      use scalarMul
      have assert_exists_16342561502676299485 :
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          fun (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ) ↦ sorry `_sorry._@._hyg.18637;
        ?m.2889 :=
        by
        let realScalarMul {VQ : Type u} [inst : AddCommGroup VQ] [inst_1 : Module ℚ VQ] (normQ : Seminorm ℚ VQ)
          (N : Submodule ℚ VQ) (_ : ↑N = {v | normQ v = 0}) [instW : NormedAddCommGroup (VQ ⧸ N)]
          [instWNS : NormedSpace ℚ (VQ ⧸ N)] (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) :
          UniformSpace.Completion (VQ ⧸ N) := by sorry
        use realScalarMul
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        repeat (sorry)
      let ⟨realScalarMul, assert_prop_16342561502676299485⟩ := assert_exists_16342561502676299485
      have verification_16342561502676299485 :
        ∀ (N : Submodule ℚ VQ),
          (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
            ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
              ∃ (smul : ℝ → UniformSpace.Completion (VQ ⧸ N) → UniformSpace.Completion (VQ ⧸ N)),
                ∀ (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) (q : ℕ → ℚ) (w : ℕ → VQ ⧸ N),
                  Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop (nhds b) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n • w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop
                        (nhds (smul r b)) :=
        by
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        have h :=
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property
            (fun n : ℕ => (0 : ℚ)) (1 : ℝ) (fun n : ℕ => (0 : VQ)) (0 : VQ)
        have hbad : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (1 : ℝ)) := by simpa using h.1
        have hzero : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)) := tendsto_const_nhds
        have h01 : (0 : ℝ) = (1 : ℝ) := tendsto_nhds_unique hzero hbad
        norm_num at h01
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_cauchy_estimate :
        ∀ {B : Type u} [inst : NormedAddCommGroup B] [inst_2 : NormedSpace ℝ B] [CompleteSpace B] (q : ℕ → ℚ)
          (w : ℕ → B), ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
        by
        intro B inst_5765528929934430422 inst_9743531509386672818 inst_2394858571444162963 q w
        have assert_8729072714096066399 :
          ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) := by repeat (sorry)
        let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_well_definedness :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] [instComplete : CompleteSpace B]
          {r : ℝ} {b : B} (qn qn' : ℕ → ℚ) (wn wn' : ℕ → B) {L L' : B}, L = L' :=
        by
        intro B instB instNS instComplete r b qn qn' wn wn'
        have assert_2071645680532127799 : ∀ {L L' : B}, L = L' := by repeat (sorry)
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_extension :
        ∀ {W : Type u} [instW : AddCommGroup W] [instQ : Module ℚ W] [instR : Module ℝ W] (q : ℚ) (w : W),
          q • w = (↑q : ℝ) • w :=
        by
        intro W instW instQ instR q w
        skip
        have assert_8426525593406456410 : q • w = (↑q : ℝ) • w := by repeat (sorry)
        assumption
      repeat (sorry)
    let ⟨scalarMul, assert_prop_3291407328229044655⟩ := assert_exists_3291407328229044655
    have verification_3291407328229044655 :
      ∀ (N : Submodule ℚ VQ),
        (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
          ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
            ∃ (instBMod : Module ℝ (UniformSpace.Completion (VQ ⧸ N))) (instBNS :
              NormedSpace ℝ (UniformSpace.Completion (VQ ⧸ N))), IsScalarTower ℚ ℝ (UniformSpace.Completion (VQ ⧸ N)) :=
      by
      have assert_exists_16342561502676299485 :
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          fun (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ) ↦ sorry `_sorry._@._hyg.28582;
        ?m.3397 :=
        by
        let realScalarMul {VQ : Type u} [inst : AddCommGroup VQ] [inst_1 : Module ℚ VQ] (normQ : Seminorm ℚ VQ)
          (N : Submodule ℚ VQ) (_ : ↑N = {v | normQ v = 0}) [instW : NormedAddCommGroup (VQ ⧸ N)]
          [instWNS : NormedSpace ℚ (VQ ⧸ N)] (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) :
          UniformSpace.Completion (VQ ⧸ N) := by sorry
        use realScalarMul
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        repeat (sorry)
      let ⟨realScalarMul, assert_prop_16342561502676299485⟩ := assert_exists_16342561502676299485
      have verification_16342561502676299485 :
        ∀ (N : Submodule ℚ VQ),
          (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
            ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
              ∃ (smul : ℝ → UniformSpace.Completion (VQ ⧸ N) → UniformSpace.Completion (VQ ⧸ N)),
                ∀ (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) (q : ℕ → ℚ) (w : ℕ → VQ ⧸ N),
                  Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop (nhds b) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n • w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop
                        (nhds (smul r b)) :=
        by
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        have h :=
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property
            (fun n : ℕ => (0 : ℚ)) (1 : ℝ) (fun n : ℕ => (0 : VQ)) (0 : VQ)
        have hbad : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (1 : ℝ)) := by simpa using h.1
        have hzero : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)) := tendsto_const_nhds
        have h01 : (0 : ℝ) = (1 : ℝ) := tendsto_nhds_unique hzero hbad
        norm_num at h01
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_cauchy_estimate :
        ∀ {B : Type u} [inst : NormedAddCommGroup B] [inst_2 : NormedSpace ℝ B] [CompleteSpace B] (q : ℕ → ℚ)
          (w : ℕ → B), ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
        by
        intro B inst_5765528929934430422 inst_9743531509386672818 inst_2394858571444162963 q w
        have assert_8729072714096066399 :
          ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) := by repeat (sorry)
        let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_well_definedness :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] [instComplete : CompleteSpace B]
          {r : ℝ} {b : B} (qn qn' : ℕ → ℚ) (wn wn' : ℕ → B) {L L' : B}, L = L' :=
        by
        intro B instB instNS instComplete r b qn qn' wn wn'
        have assert_2071645680532127799 : ∀ {L L' : B}, L = L' := by repeat (sorry)
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_extension :
        ∀ {W : Type u} [instW : AddCommGroup W] [instQ : Module ℚ W] [instR : Module ℝ W] (q : ℚ) (w : W),
          q • w = (↑q : ℝ) • w :=
        by
        intro W instW instQ instR q w
        skip
        have assert_8426525593406456410 : q • w = (↑q : ℝ) • w := by repeat (sorry)
        assumption
      repeat (sorry)
    have homogeneous_root_lemma_13_proof_root_banach_space :
      ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B), CompleteSpace B := by
      exact ⟨PUnit, inferInstance, inferInstance, inferInstance⟩
    have assert_exists_17745801246652801861 : ?m.3709 :=
      by
      let lemma_13_iota {N : Submodule ℚ VQ} [NormedAddCommGroup (VQ ⧸ N)] [NormedSpace ℚ (VQ ⧸ N)] :
        VQ →ₗ[ℚ] UniformSpace.Completion (VQ ⧸ N) :=
        { toFun := fun v => ((Submodule.mkQ N v : VQ ⧸ N) : UniformSpace.Completion (VQ ⧸ N)), map_add' := by sorry,
          map_smul' := by sorry }
      use iota
      have homogeneous_root_lemma_13_proof_root_canonical_map_quotient_map :
        ∃ (W : Type u) (instW : NormedAddCommGroup W) (instWNS : NormedSpace ℚ W) (q : VQ →ₗ[ℚ] W),
          ∀ (v : VQ), ‖(q : VQ → W) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_completion_embedding :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℚ B) (_ : CompleteSpace B) (j : VQ →ₗ[ℚ] B),
          ∀ (w : VQ), ‖(j : VQ → B) w‖ = (normQ : VQ → ℝ) w :=
        by
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_compose :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_linearity :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
          (q : ℚ) (v : VQ), (iota : VQ → B) (q • v) = (algebraMap ℚ ℝ : ℚ → ℝ) q • (iota : VQ → B) v :=
        by
        intro B instB instNS iota q v
        simp only [LinearMap.map_smulₛₗ, Lake.FamilyOut.fam_eq, eq_ratCast]
      repeat (sorry)
    let ⟨iota, assert_prop_17745801246652801861⟩ := assert_exists_17745801246652801861
    have verification_17745801246652801861 :
      ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
        VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
      by
      have homogeneous_root_lemma_13_proof_root_canonical_map_quotient_map :
        ∃ (W : Type u) (instW : NormedAddCommGroup W) (instWNS : NormedSpace ℚ W) (q : VQ →ₗ[ℚ] W),
          ∀ (v : VQ), ‖(q : VQ → W) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_completion_embedding :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℚ B) (_ : CompleteSpace B) (j : VQ →ₗ[ℚ] B),
          ∀ (w : VQ), ‖(j : VQ → B) w‖ = (normQ : VQ → ℝ) w :=
        by
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_compose :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_linearity :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
          (q : ℚ) (v : VQ), (iota : VQ → B) (q • v) = (algebraMap ℚ ℝ : ℚ → ℝ) q • (iota : VQ → B) v :=
        by
        intro B instB instNS iota q v
        simp only [LinearMap.map_smulₛₗ, Lake.FamilyOut.fam_eq, eq_ratCast]
      repeat (sorry)
    repeat (sorry)
  let ⟨completionB, assert_prop_8220810582158213931⟩ := assert_exists_8220810582158213931
  have verification_8220810582158213931 :
    ∃ (completionB : Type u) (instB : NormedAddCommGroup completionB) (instNS : NormedSpace ℝ completionB) (_ :
      CompleteSpace completionB) (iota : VQ →ₛₗ[algebraMap ℚ ℝ] completionB),
      ∀ (v : VQ), ‖(iota : VQ → completionB) v‖ = (normQ : VQ → ℝ) v :=
    by
    have homogeneous_root_lemma_13_proof_root_kernel_subspace :
      ∃ (N : Submodule ℚ VQ), (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} :=
      by
      skip
      skip
      repeat (sorry)
    skip
    have assert_exists_8220810582158213931 : ?m.3758 :=
      by
      let completionB {W : Type u} [PseudoMetricSpace W] : Type u := UniformSpace.Completion W
      use completionB
      have homogeneous_root_lemma_13_proof_root_completion_verification :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B),
          DenseRange (⇑iota : VQ → B) ∧ ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      repeat (sorry)
    let ⟨completionB, assert_prop_8220810582158213931⟩ := assert_exists_8220810582158213931
    have verification_8220810582158213931 :
      ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
        VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
      by
      have homogeneous_root_lemma_13_proof_root_completion_verification :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B),
          DenseRange (⇑iota : VQ → B) ∧ ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      repeat (sorry)
    have homogeneous_root_lemma_13_proof_root_extend_rational_operations :
      ∀ (N : Submodule ℚ VQ),
        (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
          ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
            Nonempty (NormedSpace ℚ (UniformSpace.Completion (VQ ⧸ N))) :=
      by
      intro N a_485438065194403264 instW instWNS
      exact ⟨inferInstance⟩
    have assert_exists_3291407328229044655 : ?m.3805 :=
      by
      let scalarMul {VQ : Type u} [inst : AddCommGroup VQ] [inst_1 : Module ℚ VQ] (normQ : Seminorm ℚ VQ)
        (N : Submodule ℚ VQ) (_hN : ↑N = {v : VQ | normQ v = 0}) [instW : NormedAddCommGroup (VQ ⧸ N)]
        [instWNS : NormedSpace ℚ (VQ ⧸ N)] : ℝ → UniformSpace.Completion (VQ ⧸ N) → UniformSpace.Completion (VQ ⧸ N) :=
        by sorry
      use scalarMul
      have assert_exists_16342561502676299485 :
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          fun (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ) ↦ sorry `_sorry._@._hyg.56539;
        ?m.4002 :=
        by
        let realScalarMul {VQ : Type u} [inst : AddCommGroup VQ] [inst_1 : Module ℚ VQ] (normQ : Seminorm ℚ VQ)
          (N : Submodule ℚ VQ) (_ : ↑N = {v | normQ v = 0}) [instW : NormedAddCommGroup (VQ ⧸ N)]
          [instWNS : NormedSpace ℚ (VQ ⧸ N)] (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) :
          UniformSpace.Completion (VQ ⧸ N) := by sorry
        use realScalarMul
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        repeat (sorry)
      let ⟨realScalarMul, assert_prop_16342561502676299485⟩ := assert_exists_16342561502676299485
      have verification_16342561502676299485 :
        ∀ (N : Submodule ℚ VQ),
          (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
            ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
              ∃ (smul : ℝ → UniformSpace.Completion (VQ ⧸ N) → UniformSpace.Completion (VQ ⧸ N)),
                ∀ (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) (q : ℕ → ℚ) (w : ℕ → VQ ⧸ N),
                  Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop (nhds b) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n • w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop
                        (nhds (smul r b)) :=
        by
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        have h :=
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property
            (fun n : ℕ => (0 : ℚ)) (1 : ℝ) (fun n : ℕ => (0 : VQ)) (0 : VQ)
        have hbad : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (1 : ℝ)) := by simpa using h.1
        have hzero : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)) := tendsto_const_nhds
        have h01 : (0 : ℝ) = (1 : ℝ) := tendsto_nhds_unique hzero hbad
        norm_num at h01
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_cauchy_estimate :
        ∀ {B : Type u} [inst : NormedAddCommGroup B] [inst_2 : NormedSpace ℝ B] [CompleteSpace B] (q : ℕ → ℚ)
          (w : ℕ → B), ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
        by
        intro B inst_5765528929934430422 inst_9743531509386672818 inst_2394858571444162963 q w
        have assert_8729072714096066399 :
          ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) := by repeat (sorry)
        let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_well_definedness :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] [instComplete : CompleteSpace B]
          {r : ℝ} {b : B} (qn qn' : ℕ → ℚ) (wn wn' : ℕ → B) {L L' : B}, L = L' :=
        by
        intro B instB instNS instComplete r b qn qn' wn wn'
        have assert_2071645680532127799 : ∀ {L L' : B}, L = L' := by repeat (sorry)
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_extension :
        ∀ {W : Type u} [instW : AddCommGroup W] [instQ : Module ℚ W] [instR : Module ℝ W] (q : ℚ) (w : W),
          q • w = (↑q : ℝ) • w :=
        by
        intro W instW instQ instR q w
        skip
        have assert_8426525593406456410 : q • w = (↑q : ℝ) • w := by repeat (sorry)
        assumption
      repeat (sorry)
    let ⟨scalarMul, assert_prop_3291407328229044655⟩ := assert_exists_3291407328229044655
    have verification_3291407328229044655 :
      ∀ (N : Submodule ℚ VQ),
        (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
          ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
            ∃ (instBMod : Module ℝ (UniformSpace.Completion (VQ ⧸ N))) (instBNS :
              NormedSpace ℝ (UniformSpace.Completion (VQ ⧸ N))), IsScalarTower ℚ ℝ (UniformSpace.Completion (VQ ⧸ N)) :=
      by
      have assert_exists_16342561502676299485 :
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          fun (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ) ↦ sorry `_sorry._@._hyg.66462;
        ?m.4510 :=
        by
        let realScalarMul {VQ : Type u} [inst : AddCommGroup VQ] [inst_1 : Module ℚ VQ] (normQ : Seminorm ℚ VQ)
          (N : Submodule ℚ VQ) (_ : ↑N = {v | normQ v = 0}) [instW : NormedAddCommGroup (VQ ⧸ N)]
          [instWNS : NormedSpace ℚ (VQ ⧸ N)] (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) :
          UniformSpace.Completion (VQ ⧸ N) := by sorry
        use realScalarMul
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        repeat (sorry)
      let ⟨realScalarMul, assert_prop_16342561502676299485⟩ := assert_exists_16342561502676299485
      have verification_16342561502676299485 :
        ∀ (N : Submodule ℚ VQ),
          (↑N : Set VQ) = {v : VQ | (normQ : VQ → ℝ) v = (0 : ℝ)} →
            ∀ [instW : NormedAddCommGroup (VQ ⧸ N)] [instWNS : NormedSpace ℚ (VQ ⧸ N)],
              ∃ (smul : ℝ → UniformSpace.Completion (VQ ⧸ N) → UniformSpace.Completion (VQ ⧸ N)),
                ∀ (r : ℝ) (b : UniformSpace.Completion (VQ ⧸ N)) (q : ℕ → ℚ) (w : ℕ → VQ ⧸ N),
                  Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop (nhds b) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n • w n) : UniformSpace.Completion (VQ ⧸ N))) Filter.atTop
                        (nhds (smul r b)) :=
        by
        skip
        have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_limit_exists :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (q : ℕ → ℚ) (w : ℕ → B),
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
          by
          intro B instB instNS q w
          have assert_4862129672915261288 :
            ∀ (r : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) := by repeat (sorry)
          have assert_15074478095133780769 : ∃ (b : B), Filter.Tendsto w Filter.atTop (nhds b) :=
            by
            exfalso
            have h0 := assert_4862129672915261288 (0 : ℝ)
            have h1 := assert_4862129672915261288 (1 : ℝ)
            have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
            norm_num at h01
          let ⟨b, assert_5770763609839113725⟩ := assert_15074478095133780769
          have assert_8729072714096066399 :
            ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
            by
            refine ⟨0, ?_⟩
            have hq : Filter.Tendsto (fun n => ((q n : ℚ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
              assert_4862129672915261288 0
            simpa using hq.smul assert_5770763609839113725
          let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
          assumption
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_well_definedness :
          ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
            {q q' : ℕ → ℚ} {w w' : ℕ → VQ} {r : ℝ} {b L L' : B},
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ)) Filter.atTop (nhds r) →
              Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ)) Filter.atTop (nhds r) →
                Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w n)) Filter.atTop (nhds b) →
                  Filter.Tendsto (fun (n : ℕ) ↦ (iota : VQ → B) (w' n)) Filter.atTop (nhds b) →
                    Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • (iota : VQ → B) (w n)) Filter.atTop (nhds L) →
                      Filter.Tendsto (fun (n : ℕ) ↦ (↑(q' n) : ℝ) • (iota : VQ → B) (w' n)) Filter.atTop (nhds L') →
                        L = L' :=
          by
          intro B instB instNS iota q q' w w' r b
          intro L L' hq hq' hw hw' hL hL'
          exact (tendsto_nhds_unique hL (hq.smul hw)).trans (tendsto_nhds_unique hL' (hq'.smul hw')).symm
        have
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property :
          ∀ (qn : ℕ → ℚ) (r : ℝ) (wn : ℕ → VQ) (b : VQ),
            Filter.Tendsto (fun (n : ℕ) ↦ (↑(qn n) : ℝ)) Filter.atTop (nhds r) ∧
              Filter.Tendsto (fun (n : ℕ) ↦ (normQ : VQ → ℝ) (wn n - b)) Filter.atTop (nhds (0 : ℝ)) :=
          by
          intro qn r wn b
          skip
          skip
          repeat (sorry)
        have h :=
          homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_definition_by_approximation_extension_property
            (fun n : ℕ => (0 : ℚ)) (1 : ℝ) (fun n : ℕ => (0 : VQ)) (0 : VQ)
        have hbad : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (1 : ℝ)) := by simpa using h.1
        have hzero : Filter.Tendsto (fun n : ℕ => (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)) := tendsto_const_nhds
        have h01 : (0 : ℝ) = (1 : ℝ) := tendsto_nhds_unique hzero hbad
        norm_num at h01
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_cauchy_estimate :
        ∀ {B : Type u} [inst : NormedAddCommGroup B] [inst_2 : NormedSpace ℝ B] [CompleteSpace B] (q : ℕ → ℚ)
          (w : ℕ → B), ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) :=
        by
        intro B inst_5765528929934430422 inst_9743531509386672818 inst_2394858571444162963 q w
        have assert_8729072714096066399 :
          ∃ (b : B), Filter.Tendsto (fun (n : ℕ) ↦ (↑(q n) : ℝ) • w n) Filter.atTop (nhds b) := by repeat (sorry)
        let ⟨b, assert_7138884442092661262⟩ := assert_8729072714096066399
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_well_definedness :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] [instComplete : CompleteSpace B]
          {r : ℝ} {b : B} (qn qn' : ℕ → ℚ) (wn wn' : ℕ → B) {L L' : B}, L = L' :=
        by
        intro B instB instNS instComplete r b qn qn' wn wn'
        have assert_2071645680532127799 : ∀ {L L' : B}, L = L' := by repeat (sorry)
        assumption
      have homogeneous_root_lemma_13_proof_root_real_scalar_multiplication_extension :
        ∀ {W : Type u} [instW : AddCommGroup W] [instQ : Module ℚ W] [instR : Module ℝ W] (q : ℚ) (w : W),
          q • w = (↑q : ℝ) • w :=
        by
        intro W instW instQ instR q w
        skip
        have assert_8426525593406456410 : q • w = (↑q : ℝ) • w := by repeat (sorry)
        assumption
      repeat (sorry)
    have homogeneous_root_lemma_13_proof_root_banach_space :
      ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B), CompleteSpace B := by
      exact ⟨PUnit, inferInstance, inferInstance, inferInstance⟩
    have assert_exists_17745801246652801861 : ?m.4822 :=
      by
      let lemma_13_iota {N : Submodule ℚ VQ} [NormedAddCommGroup (VQ ⧸ N)] [NormedSpace ℚ (VQ ⧸ N)] :
        VQ →ₗ[ℚ] UniformSpace.Completion (VQ ⧸ N) :=
        { toFun := fun v => ((Submodule.mkQ N v : VQ ⧸ N) : UniformSpace.Completion (VQ ⧸ N)), map_add' := by sorry,
          map_smul' := by sorry }
      use iota
      have homogeneous_root_lemma_13_proof_root_canonical_map_quotient_map :
        ∃ (W : Type u) (instW : NormedAddCommGroup W) (instWNS : NormedSpace ℚ W) (q : VQ →ₗ[ℚ] W),
          ∀ (v : VQ), ‖(q : VQ → W) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_completion_embedding :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℚ B) (_ : CompleteSpace B) (j : VQ →ₗ[ℚ] B),
          ∀ (w : VQ), ‖(j : VQ → B) w‖ = (normQ : VQ → ℝ) w :=
        by
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_compose :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_linearity :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
          (q : ℚ) (v : VQ), (iota : VQ → B) (q • v) = (algebraMap ℚ ℝ : ℚ → ℝ) q • (iota : VQ → B) v :=
        by
        intro B instB instNS iota q v
        simp only [LinearMap.map_smulₛₗ, Lake.FamilyOut.fam_eq, eq_ratCast]
      repeat (sorry)
    let ⟨iota, assert_prop_17745801246652801861⟩ := assert_exists_17745801246652801861
    have verification_17745801246652801861 :
      ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
        VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
      by
      have homogeneous_root_lemma_13_proof_root_canonical_map_quotient_map :
        ∃ (W : Type u) (instW : NormedAddCommGroup W) (instWNS : NormedSpace ℚ W) (q : VQ →ₗ[ℚ] W),
          ∀ (v : VQ), ‖(q : VQ → W) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_completion_embedding :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℚ B) (_ : CompleteSpace B) (j : VQ →ₗ[ℚ] B),
          ∀ (w : VQ), ‖(j : VQ → B) w‖ = (normQ : VQ → ℝ) w :=
        by
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_compose :
        ∃ (B : Type u) (instB : NormedAddCommGroup B) (instNS : NormedSpace ℝ B) (_ : CompleteSpace B) (iota :
          VQ →ₛₗ[algebraMap ℚ ℝ] B), ∀ (v : VQ), ‖(iota : VQ → B) v‖ = (normQ : VQ → ℝ) v :=
        by
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        skip
        repeat (sorry)
      have homogeneous_root_lemma_13_proof_root_canonical_map_linearity :
        ∀ {B : Type u} [instB : NormedAddCommGroup B] [instNS : NormedSpace ℝ B] (iota : VQ →ₛₗ[algebraMap ℚ ℝ] B)
          (q : ℚ) (v : VQ), (iota : VQ → B) (q • v) = (algebraMap ℚ ℝ : ℚ → ℝ) q • (iota : VQ → B) v :=
        by
        intro B instB instNS iota q v
        simp only [LinearMap.map_smulₛₗ, Lake.FamilyOut.fam_eq, eq_ratCast]
      repeat (sorry)
    repeat (sorry)
