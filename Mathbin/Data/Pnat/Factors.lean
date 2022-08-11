/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathbin.Data.Pnat.Prime
import Mathbin.Data.Multiset.Sort

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `prime_multiset`: Type of multisets of prime numbers.
* `factor_multiset n`: Multiset of prime factors of `n`.
-/


/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/
def PrimeMultiset :=
  Multiset Nat.Primes deriving Inhabited, HasRepr, CanonicallyOrderedAddMonoid, DistribLattice, SemilatticeSup,
  OrderBot, Sub, HasOrderedSub

namespace PrimeMultiset

/-- The multiset consisting of a single prime -/
def ofPrime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)

theorem card_of_prime (p : Nat.Primes) : Multiset.card (ofPrime p) = 1 :=
  rfl

/-- We can forget the primality property and regard a multiset
 of primes as just a multiset of positive integers, or a multiset
 of natural numbers.  In the opposite direction, if we have a
 multiset of positive integers or natural numbers, together with
 a proof that all the elements are prime, then we can regard it
 as a multiset of primes.  The next block of results records
 obvious properties of these coercions.
-/
def toNatMultiset : PrimeMultiset → Multiset ℕ := fun v => v.map fun p => (p : ℕ)

instance coeNat : Coe PrimeMultiset (Multiset ℕ) :=
  ⟨toNatMultiset⟩

/-- `prime_multiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `add_monoid_hom`. -/
def coeNatMonoidHom : PrimeMultiset →+ Multiset ℕ :=
  { Multiset.mapAddMonoidHom coe with toFun := coe }

@[simp]
theorem coe_coe_nat_monoid_hom : (coeNatMonoidHom : PrimeMultiset → Multiset ℕ) = coe :=
  rfl

theorem coe_nat_injective : Function.Injective (coe : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_inj

theorem coe_nat_of_prime (p : Nat.Primes) : (ofPrime p : Multiset ℕ) = {p} :=
  rfl

theorem coe_nat_prime (v : PrimeMultiset) (p : ℕ) (h : p ∈ (v : Multiset ℕ)) : p.Prime := by
  rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
  exact h_eq ▸ hp'

/-- Converts a `prime_multiset` to a `multiset ℕ+`. -/
def toPnatMultiset : PrimeMultiset → Multiset ℕ+ := fun v => v.map fun p => (p : ℕ+)

instance coePnat : Coe PrimeMultiset (Multiset ℕ+) :=
  ⟨toPnatMultiset⟩

/-- `coe_pnat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `add_monoid_hom`. -/
def coePnatMonoidHom : PrimeMultiset →+ Multiset ℕ+ :=
  { Multiset.mapAddMonoidHom coe with toFun := coe }

@[simp]
theorem coe_coe_pnat_monoid_hom : (coePnatMonoidHom : PrimeMultiset → Multiset ℕ+) = coe :=
  rfl

theorem coe_pnat_injective : Function.Injective (coe : PrimeMultiset → Multiset ℕ+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_inj

theorem coe_pnat_of_prime (p : Nat.Primes) : (ofPrime p : Multiset ℕ+) = {(p : ℕ+)} :=
  rfl

theorem coe_pnat_prime (v : PrimeMultiset) (p : ℕ+) (h : p ∈ (v : Multiset ℕ+)) : p.Prime := by
  rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
  exact h_eq ▸ hp'

instance coeMultisetPnatNat : Coe (Multiset ℕ+) (Multiset ℕ) :=
  ⟨fun v => v.map fun n => (n : ℕ)⟩

theorem coe_pnat_nat (v : PrimeMultiset) : ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ) := by
  change (v.map (coe : Nat.Primes → ℕ+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  congr

/-- The product of a `prime_multiset`, as a `ℕ+`. -/
def prod (v : PrimeMultiset) : ℕ+ :=
  (v : Multiset Pnat).Prod

theorem coe_prod (v : PrimeMultiset) : (v.Prod : ℕ) = (v : Multiset ℕ).Prod := by
  let h : (v.prod : ℕ) = ((v.map coe).map coe).Prod := pnat.coe_monoid_hom.map_multiset_prod v.to_pnat_multiset
  rw [Multiset.map_map] at h
  have : (coe : ℕ+ → ℕ) ∘ (coe : Nat.Primes → ℕ+) = coe := funext fun p => rfl
  rw [this] at h
  exact h

theorem prod_of_prime (p : Nat.Primes) : (ofPrime p).Prod = (p : ℕ+) :=
  Multiset.prod_singleton _

/-- If a `multiset ℕ` consists only of primes, it can be recast as a `prime_multiset`. -/
def ofNatMultiset (v : Multiset ℕ) (h : ∀ p : ℕ, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h

theorem to_of_nat_multiset (v : Multiset ℕ) (h) : (ofNatMultiset v h : Multiset ℕ) = v := by
  unfold_coes
  dsimp' [← of_nat_multiset, ← to_nat_multiset]
  have : (fun (p : ℕ) (h : p.Prime) => ((⟨p, h⟩ : Nat.Primes) : ℕ)) = fun p h => id p := by
    funext p h
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]

theorem prod_of_nat_multiset (v : Multiset ℕ) (h) : ((ofNatMultiset v h).Prod : ℕ) = (v.Prod : ℕ) := by
  rw [coe_prod, to_of_nat_multiset]

/-- If a `multiset ℕ+` consists only of primes, it can be recast as a `prime_multiset`. -/
def ofPnatMultiset (v : Multiset ℕ+) (h : ∀ p : ℕ+, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ+ Nat.Primes Pnat.Prime (fun p hp => ⟨(p : ℕ), hp⟩) v h

theorem to_of_pnat_multiset (v : Multiset ℕ+) (h) : (ofPnatMultiset v h : Multiset ℕ+) = v := by
  unfold_coes
  dsimp' [← of_pnat_multiset, ← to_pnat_multiset]
  have : (fun (p : ℕ+) (h : p.Prime) => (coe : Nat.Primes → ℕ+) ⟨p, h⟩) = fun p h => id p := by
    funext p h
    apply Subtype.eq
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]

theorem prod_of_pnat_multiset (v : Multiset ℕ+) (h) : ((ofPnatMultiset v h).Prod : ℕ+) = v.Prod := by
  dsimp' [← Prod]
  rw [to_of_pnat_multiset]

/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
def ofNatList (l : List ℕ) (h : ∀ p : ℕ, p ∈ l → p.Prime) : PrimeMultiset :=
  ofNatMultiset (l : Multiset ℕ) h

theorem prod_of_nat_list (l : List ℕ) (h) : ((ofNatList l h).Prod : ℕ) = l.Prod := by
  have := prod_of_nat_multiset (l : Multiset ℕ) h
  rw [Multiset.coe_prod] at this
  exact this

/-- If a `list ℕ+` consists only of primes, it can be recast as a `prime_multiset` with
the coercion from lists to multisets. -/
def ofPnatList (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.Prime) : PrimeMultiset :=
  ofPnatMultiset (l : Multiset ℕ+) h

theorem prod_of_pnat_list (l : List ℕ+) (h) : (ofPnatList l h).Prod = l.Prod := by
  have := prod_of_pnat_multiset (l : Multiset ℕ+) h
  rw [Multiset.coe_prod] at this
  exact this

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
theorem prod_zero : (0 : PrimeMultiset).Prod = 1 := by
  dsimp' [← Prod]
  exact Multiset.prod_zero

theorem prod_add (u v : PrimeMultiset) : (u + v).Prod = u.Prod * v.Prod := by
  change (coe_pnat_monoid_hom (u + v)).Prod = _
  rw [coe_pnat_monoid_hom.map_add]
  exact Multiset.prod_add _ _

theorem prod_smul (d : ℕ) (u : PrimeMultiset) : (d • u).Prod = u.Prod ^ d := by
  induction' d with d ih
  rfl
  rw [succ_nsmul, prod_add, ih, Nat.succ_eq_add_one, pow_succₓ, mul_comm]

end PrimeMultiset

namespace Pnat

/-- The prime factors of n, regarded as a multiset -/
def factorMultiset (n : ℕ+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.factors n) (@Nat.prime_of_mem_factors n)

/-- The product of the factors is the original number -/
theorem prod_factor_multiset (n : ℕ+) : (factorMultiset n).Prod = n :=
  Eq <| by
    dsimp' [← factor_multiset]
    rw [PrimeMultiset.prod_of_nat_list]
    exact Nat.prod_factors n.ne_zero

theorem coe_nat_factor_multiset (n : ℕ+) : (factorMultiset n : Multiset ℕ) = (Nat.factors n : Multiset ℕ) :=
  PrimeMultiset.to_of_nat_multiset (Nat.factors n) (@Nat.prime_of_mem_factors n)

end Pnat

namespace PrimeMultiset

/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factor_multiset_prod (v : PrimeMultiset) : v.Prod.factorMultiset = v := by
  apply PrimeMultiset.coe_nat_injective
  rw [v.prod.coe_nat_factor_multiset, PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  unfold_coes
  dsimp' [← PrimeMultiset.toNatMultiset]
  rw [Multiset.coe_prod]
  let l' := l.map (coe : Nat.Primes → ℕ)
  have : ∀ p : ℕ, p ∈ l' → p.Prime := fun p hp => by
    rcases list.mem_map.mp hp with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
    exact h_eq ▸ hp'
  exact multiset.coe_eq_coe.mpr (@Nat.factors_unique _ l' rfl this).symm

end PrimeMultiset

namespace Pnat

/-- Positive integers biject with multisets of primes. -/
def factorMultisetEquiv : ℕ+ ≃ PrimeMultiset where
  toFun := factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factor_multiset
  right_inv := PrimeMultiset.factor_multiset_prod

/-- Factoring gives a homomorphism from the multiplicative
 monoid ℕ+ to the additive monoid of multisets. -/
theorem factor_multiset_one : factorMultiset 1 = 0 := by
  simp [← factor_multiset, ← PrimeMultiset.ofNatList, ← PrimeMultiset.ofNatMultiset]

theorem factor_multiset_mul (n m : ℕ+) : factorMultiset (n * m) = factorMultiset n + factorMultiset m := by
  let u := factor_multiset n
  let v := factor_multiset m
  have : n = u.prod := (prod_factor_multiset n).symm
  rw [this]
  have : m = v.prod := (prod_factor_multiset m).symm
  rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat'
    rw [PrimeMultiset.factor_multiset_prod]

theorem factor_multiset_pow (n : ℕ+) (m : ℕ) : factorMultiset (n ^ m) = m • factorMultiset n := by
  let u := factor_multiset n
  have : n = u.prod := (prod_factor_multiset n).symm
  rw [this, ← PrimeMultiset.prod_smul]
  repeat'
    rw [PrimeMultiset.factor_multiset_prod]

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factor_multiset_of_prime (p : Nat.Primes) : (p : ℕ+).factorMultiset = PrimeMultiset.ofPrime p := by
  apply factor_multiset_equiv.symm.injective
  change (p : ℕ+).factorMultiset.Prod = (PrimeMultiset.ofPrime p).Prod
  rw [(p : ℕ+).prod_factor_multiset, PrimeMultiset.prod_of_prime]

/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factor_multiset_le_iff {m n : ℕ+} : factorMultiset m ≤ factorMultiset n ↔ m ∣ n := by
  constructor
  · intro h
    rw [← prod_factor_multiset m, ← prod_factor_multiset m]
    apply Dvd.intro (n.factor_multiset - m.factor_multiset).Prod
    rw [← PrimeMultiset.prod_add, PrimeMultiset.factor_multiset_prod, add_tsub_cancel_of_le h, prod_factor_multiset]
    
  · intro h
    rw [← mul_div_exact h, factor_multiset_mul]
    exact le_self_add
    

theorem factor_multiset_le_iff' {m : ℕ+} {v : PrimeMultiset} : factorMultiset m ≤ v ↔ m ∣ v.Prod := by
  let h := @factor_multiset_le_iff m v.prod
  rw [v.factor_multiset_prod] at h
  exact h

end Pnat

namespace PrimeMultiset

theorem prod_dvd_iff {u v : PrimeMultiset} : u.Prod ∣ v.Prod ↔ u ≤ v := by
  let h := @Pnat.factor_multiset_le_iff' u.prod v
  rw [u.factor_multiset_prod] at h
  exact h.symm

theorem prod_dvd_iff' {u : PrimeMultiset} {n : ℕ+} : u.Prod ∣ n ↔ u ≤ n.factorMultiset := by
  let h := @prod_dvd_iff u n.factor_multiset
  rw [n.prod_factor_multiset] at h
  exact h

end PrimeMultiset

namespace Pnat

/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets. -/
theorem factor_multiset_gcd (m n : ℕ+) : factorMultiset (gcd m n) = factorMultiset m⊓factorMultiset n := by
  apply le_antisymmₓ
  · apply le_inf_iff.mpr <;> constructor <;> apply factor_multiset_le_iff.mpr
    exact gcd_dvd_left m n
    exact gcd_dvd_right m n
    
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    exact inf_le_left
    exact inf_le_right
    

theorem factor_multiset_lcm (m n : ℕ+) : factorMultiset (lcm m n) = factorMultiset m⊔factorMultiset n := by
  apply le_antisymmₓ
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
    apply lcm_dvd <;> rw [← factor_multiset_le_iff']
    exact le_sup_left
    exact le_sup_right
    
  · apply sup_le_iff.mpr <;> constructor <;> apply factor_multiset_le_iff.mpr
    exact dvd_lcm_left m n
    exact dvd_lcm_right m n
    

/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factor_multiset (m : ℕ+) (p : Nat.Primes) (k : ℕ) : (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factorMultiset.count p := by
  intros
  rw [Multiset.le_count_iff_repeat_le]
  rw [← factor_multiset_le_iff, factor_multiset_pow, factor_multiset_of_prime]
  congr 2
  apply multiset.eq_repeat.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_of_prime, mul_oneₓ]
    
  · intro q h
    rw [PrimeMultiset.ofPrime, Multiset.nsmul_singleton _ k] at h
    exact Multiset.eq_of_mem_repeat h
    

end Pnat

namespace PrimeMultiset

theorem prod_inf (u v : PrimeMultiset) : (u⊓v).Prod = Pnat.gcd u.Prod v.Prod := by
  let n := u.prod
  let m := v.prod
  change (u⊓v).Prod = Pnat.gcd n m
  have : u = n.factor_multiset := u.factor_multiset_prod.symm
  rw [this]
  have : v = m.factor_multiset := v.factor_multiset_prod.symm
  rw [this]
  rw [← Pnat.factor_multiset_gcd n m, Pnat.prod_factor_multiset]

theorem prod_sup (u v : PrimeMultiset) : (u⊔v).Prod = Pnat.lcm u.Prod v.Prod := by
  let n := u.prod
  let m := v.prod
  change (u⊔v).Prod = Pnat.lcm n m
  have : u = n.factor_multiset := u.factor_multiset_prod.symm
  rw [this]
  have : v = m.factor_multiset := v.factor_multiset_prod.symm
  rw [this]
  rw [← Pnat.factor_multiset_lcm n m, Pnat.prod_factor_multiset]

end PrimeMultiset

