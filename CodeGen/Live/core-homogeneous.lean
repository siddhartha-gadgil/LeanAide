import Mathlib
universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u₁ u₂ u₃
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
