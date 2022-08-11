/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Computability.Encoding
import Mathbin.ModelTheory.Syntax
import Mathbin.SetTheory.Cardinal.Ordinal

/-! # Encodings and Cardinality of First-Order Syntax

## Main Definitions
* `first_order.language.term.encoding` encodes terms as lists.
* `first_order.language.bounded_formula.encoding` encodes bounded formulas as lists.

## Main Results
* `first_order.language.term.card_le` shows that the number of terms in `L.term α` is at most
`max ℵ₀ # (α ⊕ Σ i, L.functions i)`.
* `first_order.language.bounded_formula.card_le` shows that the number of bounded formulas in
`Σ n, L.bounded_formula α n` is at most
`max ℵ₀ (cardinal.lift.{max u v} (#α) + cardinal.lift.{u'} L.card)`.

## TODO
* `primcodable` instances for terms and formulas, based on the `encoding`s
* Computability facts about term and formula operations, to set up a computability approach to
incompleteness

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'}

open FirstOrder Cardinal

open Computability List Structure Cardinal Finₓ

namespace Term

/-- Encodes a term as a list of variables and function symbols. -/
def listEncodeₓ : L.Term α → List (Sum α (Σi, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts => Sum.inr (⟨_, f⟩ : Σi, L.Functions i) :: (List.finRange _).bind fun i => (ts i).listEncode

/-- Decodes a list of variables and function symbols as a list of terms. -/
def listDecodeₓ : List (Sum α (Σi, L.Functions i)) → List (Option (L.Term α))
  | [] => []
  | Sum.inl a :: l => some (var a) :: list_decode l
  | Sum.inr ⟨n, f⟩ :: l =>
    if h : ∀ i : Finₓ n, ((list_decode l).nth i).join.isSome then
      (func f fun i => Option.getₓ (h i)) :: (list_decode l).drop n
    else [none]

theorem list_decode_encode_list (l : List (L.Term α)) : listDecodeₓ (l.bind listEncodeₓ) = l.map Option.some := by
  suffices h :
    ∀ (t : L.term α) (l : List (Sum α (Σi, L.functions i))), list_decode (t.listEncode ++ l) = some t :: list_decode l
  · induction' l with t l lih
    · rfl
      
    · rw [cons_bind, h t (l.bind list_encode), lih, List.map]
      
    
  · intro t
    induction' t with a n f ts ih <;> intro l
    · rw [list_encode, singleton_append, list_decode]
      
    · rw [list_encode, cons_append, list_decode]
      have h :
        list_decode (((fin_range n).bind fun i : Finₓ n => (ts i).listEncode) ++ l) =
          (fin_range n).map (Option.some ∘ ts) ++ list_decode l :=
        by
        induction' fin_range n with i l' l'ih
        · rfl
          
        · rw [cons_bind, append_assoc, ih, map_cons, l'ih, cons_append]
          
      have h' :
        ∀ i,
          (list_decode (((fin_range n).bind fun i : Finₓ n => (ts i).listEncode) ++ l)).nth ↑i = some (some (ts i)) :=
        by
        intro i
        rw [h, nth_append, nth_map]
        · simp only [← Option.map_eq_some', ← Function.comp_app, ← nth_eq_some]
          refine' ⟨i, ⟨lt_of_lt_of_leₓ i.2 (ge_of_eq (length_fin_range _)), _⟩, rfl⟩
          rw [nth_le_fin_range, Finₓ.eta]
          
        · refine' lt_of_lt_of_leₓ i.2 _
          simp
          
      refine' (dif_pos fun i => Option.is_some_iff_exists.2 ⟨ts i, _⟩).trans _
      · rw [Option.join_eq_some, h']
        
      refine' congr (congr rfl (congr rfl (congr rfl (funext fun i => Option.get_of_memₓ _ _)))) _
      · simp [← h']
        
      · rw [h, drop_left']
        rw [length_map, length_fin_range]
        
      
    

/-- An encoding of terms as lists. -/
@[simps]
protected def encoding : Encoding (L.Term α) where
  Γ := Sum α (Σi, L.Functions i)
  encode := listEncodeₓ
  decode := fun l => (listDecodeₓ l).head'.join
  decode_encode := fun t => by
    have h := list_decode_encode_list [t]
    rw [bind_singleton] at h
    simp only [← h, ← Option.join, ← head', ← List.map, ← Option.some_bindₓ, ← id.def]

theorem list_encode_injective : Function.Injective (listEncodeₓ : L.Term α → List (Sum α (Σi, L.Functions i))) :=
  Term.encoding.encode_injective

theorem card_le : # (L.Term α) ≤ max ℵ₀ (# (Sum α (Σi, L.Functions i))) :=
  lift_le.1 (trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))

theorem card_sigma : # (Σn, L.Term (Sum α (Finₓ n))) = max ℵ₀ (# (Sum α (Σi, L.Functions i))) := by
  refine' le_antisymmₓ _ _
  · rw [mk_sigma]
    refine' (sum_le_supr_lift _).trans _
    rw [mk_nat, lift_aleph_0, mul_eq_max_of_aleph_0_le_left le_rfl, max_le_iff, csupr_le_iff' (bdd_above_range _)]
    · refine' ⟨le_max_leftₓ _ _, fun i => card_le.trans _⟩
      rw [max_le_iff]
      refine' ⟨le_max_leftₓ _ _, _⟩
      rw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_commₓ (Cardinal.lift (# α)), lift_add, add_assocₓ, lift_lift,
        lift_lift]
      refine' add_le_add_right _ _
      rw [lift_le_aleph_0, ← encodable_iff]
      exact ⟨inferInstance⟩
      
    · rw [← one_le_iff_ne_zero]
      refine' trans _ (le_csupr (bdd_above_range _) 1)
      rw [one_le_iff_ne_zero, mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
      
    
  · rw [max_le_iff, ← infinite_iff]
    refine' ⟨Infinite.of_injective (fun i => ⟨i + 1, var (Sum.inr i)⟩) fun i j ij => _, _⟩
    · cases ij
      rfl
      
    · rw [Cardinal.le_def]
      refine' ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩) fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩, _⟩⟩
      · rintro (a | a) (b | b) h
        · simp only [← Sum.elim_inl, ← eq_self_iff_true, ← heq_iff_eq, ← true_andₓ] at h
          rw [h]
          
        · simp only [← Sum.elim_inl, ← Sum.elim_inr, ← Nat.zero_ne_one, ← false_andₓ] at h
          exact h.elim
          
        · simp only [← Sum.elim_inr, ← Sum.elim_inl, ← Nat.one_ne_zero, ← false_andₓ] at h
          exact h.elim
          
        · simp only [← Sum.elim_inr, ← eq_self_iff_true, ← heq_iff_eq, ← true_andₓ] at h
          rw [Sigma.ext_iff.2 ⟨h.1, h.2.1⟩]
          
        
      
    

instance [Encodable α] [Encodable (Σi, L.Functions i)] : Encodable (L.Term α) :=
  Encodable.ofLeftInjection listEncodeₓ (fun l => (listDecodeₓ l).head'.join) fun t => by
    rw [← bind_singleton list_encode, list_decode_encode_list]
    simp only [← Option.join, ← head', ← List.map, ← Option.some_bindₓ, ← id.def]

theorem card_le_aleph_0 [h1 : Nonempty (Encodable α)] [h2 : L.CountableFunctions] : # (L.Term α) ≤ ℵ₀ := by
  refine' card_le.trans _
  rw [max_le_iff]
  simp only [← le_reflₓ, ← mk_sum, ← add_le_aleph_0, ← lift_le_aleph_0, ← true_andₓ]
  exact ⟨encodable_iff.1 h1, L.card_functions_le_aleph_0⟩

instance small [Small.{u} α] : Small.{u} (L.Term α) :=
  small_of_injective list_encode_injective

end Term

namespace BoundedFormula

/-- Encodes a bounded formula as a list of symbols. -/
def listEncodeₓ : ∀ {n : ℕ}, L.BoundedFormula α n → List (Sum (Σk, L.Term (Sum α (Finₓ k))) (Sum (Σn, L.Relations n) ℕ))
  | n, falsum => [Sum.inr (Sum.inr (n + 2))]
  | n, equal t₁ t₂ => [Sum.inl ⟨_, t₁⟩, Sum.inl ⟨_, t₂⟩]
  | n, rel R ts => [Sum.inr (Sum.inl ⟨_, R⟩), Sum.inr (Sum.inr n)] ++ (List.finRange _).map fun i => Sum.inl ⟨n, ts i⟩
  | n, imp φ₁ φ₂ => Sum.inr (Sum.inr 0) :: φ₁.listEncode ++ φ₂.listEncode
  | n, all φ => Sum.inr (Sum.inr 1) :: φ.listEncode

/-- Applies the `forall` quantifier to an element of `(Σ n, L.bounded_formula α n)`,
or returns `default` if not possible. -/
def sigmaAllₓ : (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨n + 1, φ⟩ => ⟨n, φ.all⟩
  | _ => default

/-- Applies `imp` to two elements of `(Σ n, L.bounded_formula α n)`,
or returns `default` if not possible. -/
def sigmaImpₓ : (Σn, L.BoundedFormula α n) → (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨m, φ⟩, ⟨n, ψ⟩ =>
    if h : m = n then
      ⟨m,
        φ.imp
          (Eq.mp
            (by
              rw [h])
            ψ)⟩
    else default

/-- Decodes a list of symbols as a list of formulas. -/
@[simp]
def listDecodeₓ :
    ∀ l : List (Sum (Σk, L.Term (Sum α (Finₓ k))) (Sum (Σn, L.Relations n) ℕ)),
      (Σn, L.BoundedFormula α n) ×
        { l' : List (Sum (Σk, L.Term (Sum α (Finₓ k))) (Sum (Σn, L.Relations n) ℕ)) // l'.sizeof ≤ max 1 l.sizeof }
  | Sum.inr (Sum.inr (n + 2)) :: l => ⟨⟨n, falsum⟩, l, le_max_of_le_right le_add_self⟩
  | Sum.inl ⟨n₁, t₁⟩ :: Sum.inl ⟨n₂, t₂⟩ :: l =>
    ⟨if h : n₁ = n₂ then
        ⟨n₁,
          equal t₁
            (Eq.mp
              (by
                rw [h])
              t₂)⟩
      else default,
      l, by
      simp only [← List.sizeof, add_assocₓ]
      exact le_max_of_le_right le_add_self⟩
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: l =>
    ⟨if h : ∀ i : Finₓ n, ((l.map Sum.getLeft).nth i).join.isSome then
        if h' : ∀ i, (Option.getₓ (h i)).1 = k then
          ⟨k,
            BoundedFormula.rel R fun i =>
              Eq.mp
                (by
                  rw [h' i])
                (Option.getₓ (h i)).2⟩
        else default
      else default,
      l.drop n, le_max_of_le_right (le_add_left (le_add_left (List.drop_sizeof_le _ _)))⟩
  | Sum.inr (Sum.inr 0) :: l =>
    have :
      (↑(list_decode l).2 : List (Sum (Σk, L.Term (Sum α (Finₓ k))) (Sum (Σn, L.Relations n) ℕ))).sizeof <
        1 + (1 + 1) + l.sizeof :=
      by
      refine'
        lt_of_le_of_ltₓ (list_decode l).2.2
          (max_ltₓ _
            (Nat.lt_add_of_pos_leftₓ
              (by
                decide)))
      rw [add_assocₓ, add_commₓ, Nat.lt_succ_iffₓ, add_assocₓ]
      exact le_self_add
    ⟨sigmaImpₓ (list_decode l).1 (list_decode (list_decode l).2).1, (list_decode (list_decode l).2).2,
      le_max_of_le_right
        (trans (list_decode _).2.2
          (max_leₓ (le_add_right le_self_add)
            (trans (list_decode _).2.2 (max_leₓ (le_add_right le_self_add) le_add_self))))⟩
  | Sum.inr (Sum.inr 1) :: l =>
    ⟨sigmaAllₓ (list_decode l).1, (list_decode l).2, (list_decode l).2.2.trans (max_le_max le_rfl le_add_self)⟩
  | _ => ⟨default, [], le_max_leftₓ _ _⟩

@[simp]
theorem list_decode_encode_list (l : List (Σn, L.BoundedFormula α n)) :
    (listDecodeₓ (l.bind fun φ => φ.2.listEncode)).1 = l.head := by
  suffices h :
    ∀ (φ : Σn, L.bounded_formula α n) (l),
      (list_decode (list_encode φ.2 ++ l)).1 = φ ∧ (list_decode (list_encode φ.2 ++ l)).2.1 = l
  · induction' l with φ l lih
    · rw [List.nil_bind]
      simp [← list_decode]
      
    · rw [cons_bind, (h φ _).1, head_cons]
      
    
  · rintro ⟨n, φ⟩
    induction' φ with _ _ _ _ _ _ _ ts _ _ _ ih1 ih2 _ _ ih <;> intro l
    · rw [list_encode, singleton_append, list_decode]
      simp only [← eq_self_iff_true, ← heq_iff_eq, ← and_selfₓ]
      
    · rw [list_encode, cons_append, cons_append, list_decode, dif_pos]
      · simp only [← eq_mp_eq_cast, ← cast_eq, ← eq_self_iff_true, ← heq_iff_eq, ← and_selfₓ, ← nil_append]
        
      · simp only [← eq_self_iff_true, ← heq_iff_eq, ← and_selfₓ]
        
      
    · rw [list_encode, cons_append, cons_append, singleton_append, cons_append, list_decode]
      · have h :
          ∀ i : Finₓ φ_l,
            ((List.map Sum.getLeft
                      (List.map
                          (fun i : Finₓ φ_l =>
                            Sum.inl
                              (⟨(⟨φ_n, rel φ_R ts⟩ : Σn, L.bounded_formula α n).fst, ts i⟩ :
                                Σn, L.term (Sum α (Finₓ n))))
                          (fin_range φ_l) ++
                        l)).nth
                  ↑i).join =
              some ⟨_, ts i⟩ :=
          by
          intro i
          simp only [← Option.join, ← map_append, ← map_map, ← Option.bind_eq_someₓ, ← id.def, ← exists_eq_right, ←
            nth_eq_some, ← length_append, ← length_map, ← length_fin_range]
          refine' ⟨lt_of_lt_of_leₓ i.2 le_self_add, _⟩
          rw [nth_le_append, nth_le_map]
          · simp only [← Sum.getLeft, ← nth_le_fin_range, ← Finₓ.eta, ← Function.comp_app, ← eq_self_iff_true, ←
              heq_iff_eq, ← and_selfₓ]
            
          · exact lt_of_lt_of_leₓ i.is_lt (ge_of_eq (length_fin_range _))
            
          · rw [length_map, length_fin_range]
            exact i.2
            
        rw [dif_pos]
        swap
        · exact fun i => Option.is_some_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
          
        rw [dif_pos]
        swap
        · intro i
          obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eqₓ.1 (h i)
          rw [h2]
          
        simp only [← eq_self_iff_true, ← heq_iff_eq, ← true_andₓ]
        refine' ⟨funext fun i => _, _⟩
        · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eqₓ.1 (h i)
          rw [eq_mp_eq_cast, cast_eq_iff_heq]
          exact (Sigma.ext_iff.1 ((Sigma.eta (Option.getₓ h1)).trans h2)).2
          
        rw [List.drop_append_eq_append_drop, length_map, length_fin_range, Nat.sub_self, drop, drop_eq_nil_of_le,
          nil_append]
        rw [length_map, length_fin_range]
        
      
    · rw [list_encode, append_assoc, cons_append, list_decode]
      simp only [← Subtype.val_eq_coe] at *
      rw [(ih1 _).1, (ih1 _).2, (ih2 _).1, (ih2 _).2, sigma_imp, dif_pos rfl]
      exact ⟨rfl, rfl⟩
      
    · rw [list_encode, cons_append, list_decode]
      simp only
      simp only [← Subtype.val_eq_coe] at *
      rw [(ih _).1, (ih _).2, sigma_all]
      exact ⟨rfl, rfl⟩
      
    

/-- An encoding of bounded formulas as lists. -/
@[simps]
protected def encoding : Encoding (Σn, L.BoundedFormula α n) where
  Γ := Sum (Σk, L.Term (Sum α (Finₓ k))) (Sum (Σn, L.Relations n) ℕ)
  encode := fun φ => φ.2.listEncode
  decode := fun l => (listDecodeₓ l).1
  decode_encode := fun φ => by
    have h := list_decode_encode_list [φ]
    rw [bind_singleton] at h
    rw [h]
    rfl

theorem list_encode_sigma_injective : Function.Injective fun φ : Σn, L.BoundedFormula α n => φ.2.listEncode :=
  BoundedFormula.encoding.encode_injective

theorem card_le : # (Σn, L.BoundedFormula α n) ≤ max ℵ₀ (Cardinal.lift.{max u v} (# α) + Cardinal.lift.{u'} L.card) :=
  by
  refine' lift_le.1 (bounded_formula.encoding.card_le_card_list.trans _)
  rw [encoding_Γ, mk_list_eq_max_mk_aleph_0, lift_max, lift_aleph_0, lift_max, lift_aleph_0, max_le_iff]
  refine' ⟨_, le_max_leftₓ _ _⟩
  rw [mk_sum, term.card_sigma, mk_sum, ← add_eq_max le_rfl, mk_sum, mk_nat]
  simp only [← lift_add, ← lift_lift, ← lift_aleph_0]
  rw [← add_assocₓ, add_commₓ, ← add_assocₓ, ← add_assocₓ, aleph_0_add_aleph_0, add_assocₓ, add_eq_max le_rfl,
    add_assocₓ, card, symbols, mk_sum, lift_add, lift_lift, lift_lift]

end BoundedFormula

end Language

end FirstOrder

