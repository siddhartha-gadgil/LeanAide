/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathbin.Data.Zmod.Quotient
import Mathbin.Algebra.Module.Pid

/-!
# Structure of finite(ly generated) abelian groups

* `add_comm_group.equiv_free_prod_direct_sum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `add_comm_group.equiv_direct_sum_zmod_of_fintype` : Any finite abelian group is a direct sum of
  some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.

-/


open DirectSum

namespace AddCommGroupₓ

/-- **Structure theorem of finitely generated abelian groups** : Any finitely generated abelian
group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some
prime powers `p i ^ e i`.-/
theorem equiv_free_prod_direct_sum_zmod (G : Type _) [AddCommGroupₓ G] [hG : AddGroupₓ.Fg G] :
    ∃ (n : ℕ)(ι : Type)(_ : Fintype ι)(p : ι → ℕ)(_ : ∀ i, Nat.Prime <| p i)(e : ι → ℕ),
      Nonempty <| G ≃+ (Finₓ n →₀ ℤ) × ⨁ i : ι, Zmod (p i ^ e i) :=
  by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_direct_sum _ _ _ _ _ _ _ (module.finite.iff_add_group_fg.mpr hG)
  refine' ⟨n, ι, fι, fun i => (p i).natAbs, fun i => _, e, ⟨_⟩⟩
  · rw [← Int.prime_iff_nat_abs_prime, ← GcdMonoid.irreducible_iff_prime]
    exact hp i
    
  exact
    f.to_add_equiv.trans
      ((AddEquiv.refl _).prodCongr <|
        Dfinsupp.mapRange.addEquiv fun i =>
          ((Int.quotientSpanEquivZmod _).trans <| Zmod.ringEquivCongr <| (p i).nat_abs_pow _).toAddEquiv)

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.-/
theorem equiv_direct_sum_zmod_of_fintype (G : Type _) [AddCommGroupₓ G] [Fintype G] :
    ∃ (ι : Type)(_ : Fintype ι)(p : ι → ℕ)(_ : ∀ i, Nat.Prime <| p i)(e : ι → ℕ),
      Nonempty <| G ≃+ ⨁ i : ι, Zmod (p i ^ e i) :=
  by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_direct_sum_zmod G
  cases n
  · exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
    
  · have := @Fintype.prodLeft _ _ _ (Fintype.ofEquiv G f.to_equiv) _
    exact
      ((Fintype.ofSurjective fun f : Finₓ n.succ →₀ ℤ => f 0) fun a =>
            ⟨Finsupp.single 0 a, Finsupp.single_eq_same⟩).False.elim
    

end AddCommGroupₓ

