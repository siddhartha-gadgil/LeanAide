/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Data.LazyList.Basic
import Mathbin.Data.Tree
import Mathbin.Data.Int.Basic
import Mathbin.Control.Bifunctor
import Mathbin.Control.Ulift
import Mathbin.Tactic.Linarith.Default
import Mathbin.Testing.SlimCheck.Gen

/-!
# `sampleable` Class

This class permits the creation samples of a given type
controlling the size of those values using the `gen` monad`. It also
helps minimize examples by creating smaller versions of given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`slim_check` requires that `ℕ` have an instance of `sampleable` and for
`prime n` to be decidable.  `slim_check` will then use the instance of
`sampleable` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`slim_check` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `slim_check` moves on to trying more examples.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `sampleable` class
  * `sampleable_functor` and `sampleable_bifunctor` class
  * `sampleable_ext` class

### `sampleable`

`sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.

### `sampleable_ext`

`sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type.

### `sampleable_functor` and `sampleable_bifunctor`

`sampleable_functor F` and `sampleable_bifunctor F` makes it possible
to create samples of and shrink `F α` given a sampling function and a
shrinking function for arbitrary `α`.

This allows us to separate the logic for generating the shape of a
collection from the logic for generating its contents. Specifically,
the contents could be generated using either `sampleable` or
`sampleable_ext` instance and the `sampleable_(bi)functor` does not
need to use that information

## Shrinking

Shrinking happens when `slim_check` find a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `slim_check` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.

The `sampleable` class, beside having the `sample` function, has a
`shrink` function so that we can use specialized knowledge while
shrinking a value. It is not responsible for the whole shrinking process
however. It only has to take one step in the shrinking process.
`slim_check` will repeatedly call `shrink` until no more steps can
be taken. Because `shrink` guarantees that the size of the candidates
it produces is strictly smaller than the argument, we know that
`slim_check` is guaranteed to terminate.

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/


universe u v w

namespace SlimCheck

variable (α : Type u)

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => HasWellFounded.R

/-- `sizeof_lt x y` compares the sizes of `x` and `y`. -/
def SizeofLt {α} [SizeOf α] (x y : α) :=
  sizeof x < sizeof y

/-- `shrink_fn α` is the type of functions that shrink an
argument of type `α` -/
@[reducible]
def ShrinkFn (α : Type _) [SizeOf α] :=
  ∀ x : α, LazyList { y : α // SizeofLt y x }

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`sample] []
/-- `sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.  -/
class Sampleable where
  [wf : SizeOf α]
  sample : Genₓ α
  shrink : ∀ x : α, LazyList { y : α // @sizeof _ wf y < @sizeof _ wf x } := fun _ => LazyList.nil

attribute [instance] hasWellFoundedOfHasSizeof defaultHasSizeof

attribute [instance] sampleable.wf

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`sample] []
/-- `sampleable_functor F` makes it possible to create samples of and
shrink `F α` given a sampling function and a shrinking function for
arbitrary `α` -/
class SampleableFunctor (F : Type u → Type v) [Functor F] where
  [wf : ∀ (α) [SizeOf α], SizeOf (F α)]
  sample : ∀ {α}, Genₓ α → Genₓ (F α)
  shrink : ∀ (α) [SizeOf α], ShrinkFn α → ShrinkFn (F α)
  pRepr : ∀ α, HasRepr α → HasRepr (F α)

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`sample] []
/-- `sampleable_bifunctor F` makes it possible to create samples of
and shrink `F α β` given a sampling function and a shrinking function
for arbitrary `α` and `β` -/
class SampleableBifunctor (F : Type u → Type v → Type w) [Bifunctor F] where
  [wf : ∀ (α β) [SizeOf α] [SizeOf β], SizeOf (F α β)]
  sample : ∀ {α β}, Genₓ α → Genₓ β → Genₓ (F α β)
  shrink : ∀ (α β) [SizeOf α] [SizeOf β], ShrinkFn α → ShrinkFn β → ShrinkFn (F α β)
  pRepr : ∀ α β, HasRepr α → HasRepr β → HasRepr (F α β)

export Sampleable (sample shrink)

/-- This function helps infer the proxy representation and
interpretation in `sampleable_ext` instances. -/
unsafe def sampleable.mk_trivial_interp : tactic Unit :=
  tactic.refine (pquote.1 id)

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`interp] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`sample] []
/-- `sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class SampleableExtₓ (α : Sort u) where
  ProxyRepr : Type v
  [wf : SizeOf proxy_repr]
  interp : proxy_repr → α := by
    run_tac
      sampleable.mk_trivial_interp
  [pRepr : HasRepr proxy_repr]
  sample : Genₓ proxy_repr
  shrink : ShrinkFn proxy_repr

attribute [instance] sampleable_ext.p_repr sampleable_ext.wf

open Nat LazyList

section Prio

open SampleableExt

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option default_priority
set_option default_priority 50

instance SampleableExtₓ.ofSampleable {α} [Sampleable α] [HasRepr α] : SampleableExtₓ α where
  ProxyRepr := α
  sample := Sampleable.sample α
  shrink := shrink

instance Sampleable.functor {α} {F} [Functor F] [SampleableFunctor F] [Sampleable α] : Sampleable (F α) where
  wf := _
  sample := SampleableFunctor.sample F (Sampleable.sample α)
  shrink := SampleableFunctor.shrink α Sampleable.shrink

instance Sampleable.bifunctor {α β} {F} [Bifunctor F] [SampleableBifunctor F] [Sampleable α] [Sampleable β] :
    Sampleable (F α β) where
  wf := _
  sample := SampleableBifunctor.sample F (Sampleable.sample α) (Sampleable.sample β)
  shrink := SampleableBifunctor.shrink α β Sampleable.shrink Sampleable.shrink

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option default_priority
set_option default_priority 100

instance SampleableExtₓ.functor {α} {F} [Functor F] [SampleableFunctor F] [SampleableExtₓ α] :
    SampleableExtₓ (F α) where
  wf := _
  ProxyRepr := F (ProxyRepr α)
  interp := Functor.map (interp _)
  sample := SampleableFunctor.sample F (SampleableExtₓ.sample α)
  shrink := SampleableFunctor.shrink _ SampleableExtₓ.shrink
  pRepr := SampleableFunctor.pRepr _ SampleableExtₓ.pRepr

instance SampleableExtₓ.bifunctor {α β} {F} [Bifunctor F] [SampleableBifunctor F] [SampleableExtₓ α]
    [SampleableExtₓ β] : SampleableExtₓ (F α β) where
  wf := _
  ProxyRepr := F (ProxyRepr α) (ProxyRepr β)
  interp := Bifunctor.bimap (interp _) (interp _)
  sample := SampleableBifunctor.sample F (SampleableExtₓ.sample α) (SampleableExtₓ.sample β)
  shrink := SampleableBifunctor.shrink _ _ SampleableExtₓ.shrink SampleableExtₓ.shrink
  pRepr := SampleableBifunctor.pRepr _ _ SampleableExtₓ.pRepr SampleableExtₓ.pRepr

end Prio

/-- `nat.shrink' k n` creates a list of smaller natural numbers by
successively dividing `n` by 2 and subtracting the difference from
`k`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def Nat.shrink' (k : ℕ) :
    ∀ n : ℕ, n ≤ k → List { m : ℕ // HasWellFounded.R m k } → List { m : ℕ // HasWellFounded.R m k }
  | n, hn, ls =>
    if h : n ≤ 1 then ls.reverse
    else
      have h₂ : 0 < n := by
        linarith
      have : 1 * n / 2 < n :=
        Nat.div_lt_of_lt_mul
          (Nat.mul_lt_mul_of_pos_rightₓ
            (by
              norm_num)
            h₂)
      have : n / 2 < n := by
        simpa
      let m := n / 2
      have h₀ : m ≤ k := le_transₓ (le_of_ltₓ this) hn
      have h₃ : 0 < m := by
        simp only [← m, ← lt_iff_add_one_le, ← zero_addₓ] <;> rw [Nat.le_div_iff_mul_leₓ] <;> linarith
      have h₁ : k - m < k := Nat.sub_ltₓ (lt_of_lt_of_leₓ h₂ hn) h₃
      nat.shrink' m h₀ (⟨k - m, h₁⟩ :: ls)

/-- `nat.shrink n` creates a list of smaller natural numbers by
successively dividing by 2 and subtracting the difference from
`n`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def Nat.shrinkₓ (n : ℕ) : List { m : ℕ // HasWellFounded.R m n } :=
  if h : n > 0 then
    have : ∀ k, 1 < k → n / k < n := fun k hk =>
      Nat.div_lt_of_lt_mul
        (suffices 1 * n < k * n by
          simpa
        Nat.mul_lt_mul_of_pos_rightₓ hk h)
    ⟨n / 11,
        this _
          (by
            norm_num)⟩ ::
      ⟨n / 3,
          this _
            (by
              norm_num)⟩ ::
        Nat.shrink' n n le_rfl []
  else []

open Gen

/-- Transport a `sampleable` instance from a type `α` to a type `β` using
functions between the two, going in both directions.

Function `g` is used to define the well-founded order that
`shrink` is expected to follow.
-/
def Sampleable.lift (α : Type u) {β : Type u} [Sampleable α] (f : α → β) (g : β → α)
    (h : ∀ a : α, sizeof (g (f a)) ≤ sizeof a) : Sampleable β where
  wf := ⟨sizeof ∘ g⟩
  sample := f <$> sample α
  shrink := fun x =>
    have : ∀ a, sizeof a < sizeof (g x) → sizeof (g (f a)) < sizeof (g x) := by
      introv h' <;> solve_by_elim [← lt_of_le_of_ltₓ]
    Subtype.map f this <$> shrink (g x)

instance Nat.sampleable : Sampleable ℕ where
  sample :=
    sized fun sz =>
      freq [(1, coe <$> chooseAny (Finₓ <| succ (sz ^ 3))), (3, coe <$> chooseAny (Finₓ <| succ sz))]
        (by
          decide)
  shrink := fun x => LazyList.ofList <| Nat.shrinkₓ x

/-- `iterate_shrink p x` takes a decidable predicate `p` and a
value `x` of some sampleable type and recursively shrinks `x`.
It first calls `shrink x` to get a list of candidate sample,
finds the first that satisfies `p` and recursively tries
to shrink that one. -/
def iterateShrink {α} [HasToString α] [Sampleable α] (p : α → Prop) [DecidablePred p] : α → Option α :=
  (WellFounded.fix HasWellFounded.wf) fun x f_rec => do
    (trace s! "{x} : {(shrink x).toList}") <| pure ()
    let y ← (shrink x).find fun a => p a
    f_rec y y <|> some y

instance Fin.sampleable {n} [Fact <| 0 < n] : Sampleable (Finₓ n) :=
  (Sampleable.lift ℕ Finₓ.ofNat' Subtype.val) fun i => (mod_leₓ _ _ : i % n ≤ i)

instance (priority := 100) Fin.sampleable' {n} : Sampleable (Finₓ (succ n)) :=
  (Sampleable.lift ℕ Finₓ.ofNat Subtype.val) fun i => (mod_leₓ _ _ : i % succ n ≤ i)

instance Pnat.sampleable : Sampleable ℕ+ :=
  (Sampleable.lift ℕ Nat.succPnat Pnat.natPred) fun a => by
    unfold_wf <;> simp only [← Pnat.natPred, ← succ_pnat, ← Pnat.mk_coe, ← tsub_zero, ← succ_sub_succ_eq_sub]

/-- Redefine `sizeof` for `int` to make it easier to use with `nat` -/
def Int.hasSizeof : SizeOf ℤ :=
  ⟨Int.natAbs⟩

attribute [local instance] int.has_sizeof

instance Int.sampleable : Sampleable ℤ where
  wf := _
  sample :=
    sized fun sz =>
      freq
        [(1,
            Subtype.val <$>
              choose (-(sz ^ 3 + 1) : ℤ) (sz ^ 3 + 1)
                (neg_le_self
                  (by
                    decide))),
          (3,
            Subtype.val <$>
              choose (-(sz + 1)) (sz + 1)
                (neg_le_self
                  (by
                    decide)))]
        (by
          decide)
  shrink := fun x =>
    LazyList.ofList <|
      (nat.shrink <| Int.natAbs x).bind fun ⟨y, h⟩ =>
        [⟨y, h⟩,
          ⟨-y, by
            dsimp' [← sizeof, ← SizeOf.sizeof] <;> rw [Int.nat_abs_neg] <;> exact h⟩]

instance Bool.sampleable : Sampleable Bool where
  wf := ⟨fun b => if b then 1 else 0⟩
  sample := do
    let x ← chooseAny Bool
    return x
  shrink := fun b =>
    if h : b then
      LazyList.singleton
        ⟨false, by
          cases h <;> unfold_wf⟩
    else LazyList.nil

/-- Provided two shrinking functions `prod.shrink` shrinks a pair `(x, y)` by
first shrinking `x` and pairing the results with `y` and then shrinking
`y` and pairing the results with `x`.

All pairs either contain `x` untouched or `y` untouched. We rely on
shrinking being repeated for `x` to get maximally shrunken and then
for `y` to get shrunken too.
-/
def Prod.shrink {α β} [SizeOf α] [SizeOf β] (shr_a : ShrinkFn α) (shr_b : ShrinkFn β) : ShrinkFn (α × β)
  | ⟨x₀, x₁⟩ =>
    let xs₀ : LazyList { y : α × β // SizeofLt y (x₀, x₁) } :=
      (shr_a x₀).map <|
        Subtype.map (fun a => (a, x₁)) fun x h => by
          dsimp' [← sizeof_lt] <;> unfold_wf <;> apply h
    let xs₁ : LazyList { y : α × β // SizeofLt y (x₀, x₁) } :=
      (shr_b x₁).map <|
        Subtype.map (fun a => (x₀, a)) fun x h => by
          dsimp' [← sizeof_lt] <;> unfold_wf <;> apply h
    xs₀.append xs₁

instance Prod.sampleable : SampleableBifunctor.{u, v} Prod where
  wf := _
  sample := fun α β sama samb => do
    let ⟨x⟩ ← (Uliftable.up <| sama : Genₓ (ULift.{max u v} α))
    let ⟨y⟩ ← (Uliftable.up <| samb : Genₓ (ULift.{max u v} β))
    pure (x, y)
  shrink := @Prod.shrink
  pRepr := @Prod.hasRepr

instance Sigma.sampleable {α β} [Sampleable α] [Sampleable β] : Sampleable (Σ_ : α, β) :=
  (Sampleable.lift (α × β) (fun ⟨x, y⟩ => ⟨x, y⟩) fun ⟨x, y⟩ => ⟨x, y⟩) fun ⟨x, y⟩ => le_rfl

/-- shrinking function for sum types -/
def Sum.shrink {α β} [SizeOf α] [SizeOf β] (shrink_α : ShrinkFn α) (shrink_β : ShrinkFn β) : ShrinkFn (Sum α β)
  | Sum.inr x =>
    (shrink_β x).map <|
      (Subtype.map Sum.inr) fun a => by
        dsimp' [← sizeof_lt] <;> unfold_wf <;> solve_by_elim
  | Sum.inl x =>
    (shrink_α x).map <|
      (Subtype.map Sum.inl) fun a => by
        dsimp' [← sizeof_lt] <;> unfold_wf <;> solve_by_elim

instance Sum.sampleable : SampleableBifunctor.{u, v} Sum where
  wf := _
  sample := fun (α : Type u) (β : Type v) sam_α sam_β =>
    @Uliftable.upMap Genₓ.{u} Genₓ.{max u v} _ _ _ _ (@Sum.inl α β) sam_α <|>
      @Uliftable.upMap Genₓ.{v} Genₓ.{max v u} _ _ _ _ (@Sum.inr α β) sam_β
  shrink := fun α β Iα Iβ shr_α shr_β => @Sum.shrink _ _ Iα Iβ shr_α shr_β
  pRepr := @Sum.hasRepr

instance Rat.sampleable : Sampleable ℚ :=
  (Sampleable.lift (ℤ × ℕ+) (fun x => Prod.casesOn x Rat.mkPnat) fun r => (r.Num, ⟨r.denom, r.Pos⟩)) <| by
    intro i
    rcases i with ⟨x, ⟨y, hy⟩⟩ <;> unfold_wf <;> dsimp' [← Rat.mkPnat]
    mono*
    · rw [← Int.coe_nat_le, ← Int.abs_eq_nat_abs, ← Int.abs_eq_nat_abs]
      apply Int.abs_div_le_abs
      
    · change _ - 1 ≤ y - 1
      apply tsub_le_tsub_right
      apply Nat.div_le_of_le_mulₓ
      suffices 1 * y ≤ x.nat_abs.gcd y * y by
        simpa
      apply Nat.mul_le_mul_rightₓ
      apply gcd_pos_of_pos_right _ hy
      

/-- `sampleable_char` can be specialized into customized `sampleable char` instances.

The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `characters` with uniform probabilities.  -/
def sampleableChar (length : Nat) (characters : Stringₓ) : Sampleable Charₓ where
  sample := do
    let x ←
      chooseNat 0 length
          (by
            decide)
    if x = 0 then do
        let n ← sample ℕ
        pure <| Charₓ.ofNat n
      else do
        let i ←
          choose_nat 0 (characters - 1)
              (by
                decide)
        pure (characters i).curr
  shrink := fun _ => LazyList.nil

instance Char.sampleableₓ : Sampleable Charₓ :=
  sampleableChar 3 " 0123abcABC:,;`\\/"

variable {α}

section ListShrink

variable [SizeOf α] (shr : ∀ x : α, LazyList { y : α // SizeofLt y x })

theorem List.sizeof_drop_lt_sizeof_of_lt_length {xs : List α} {k} (hk : 0 < k) (hk' : k < xs.length) :
    sizeof (List.dropₓ k xs) < sizeof xs := by
  induction' xs with x xs generalizing k
  · cases hk'
    
  cases k
  · cases hk
    
  have : sizeof xs < sizeof (x :: xs) := by
    unfold_wf
  cases k
  · simp only [← this, ← List.dropₓ]
    
  · simp only [← List.dropₓ]
    trans
    · solve_by_elim [← xs_ih, ← lt_of_succ_lt_succ hk', ← zero_lt_succ]
      
    · assumption
      
    

theorem List.sizeof_cons_lt_right (a b : α) {xs : List α} (h : sizeof a < sizeof b) :
    sizeof (a :: xs) < sizeof (b :: xs) := by
  unfold_wf <;> assumption

theorem List.sizeof_cons_lt_left (x : α) {xs xs' : List α} (h : sizeof xs < sizeof xs') :
    sizeof (x :: xs) < sizeof (x :: xs') := by
  unfold_wf <;> assumption

theorem List.sizeof_append_lt_left {xs ys ys' : List α} (h : sizeof ys < sizeof ys') :
    sizeof (xs ++ ys) < sizeof (xs ++ ys') := by
  induction xs
  · apply h
    
  · unfold_wf
    simp only [← List.sizeof, ← add_lt_add_iff_left]
    exact xs_ih
    

theorem List.one_le_sizeof (xs : List α) : 1 ≤ sizeof xs := by
  cases xs <;> unfold_wf <;> linarith

/-- `list.shrink_removes` shrinks a list by removing chunks of size `k` in
the middle of the list.
-/
def List.shrinkRemoves (k : ℕ) (hk : 0 < k) :
    ∀ (xs : List α) (n), n = xs.length → LazyList { ys : List α // SizeofLt ys xs }
  | xs, n, hn =>
    if hkn : k > n then LazyList.nil
    else
      if hkn' : k = n then
        have : 1 < xs.sizeof := by
          subst_vars
          cases xs
          · contradiction
            
          unfold_wf
          apply lt_of_lt_of_leₓ
          show 1 < 1 + SizeOf.sizeof xs_hd + 1
          · linarith
            
          · mono
            apply list.one_le_sizeof
            
        LazyList.singleton ⟨[], this⟩
      else
        have h₂ : k < xs.length := hn ▸ lt_of_le_of_neₓ (le_of_not_gtₓ hkn) hkn'
        match List.splitAtₓ k xs, rfl with
        | ⟨xs₁, xs₂⟩, h =>
          have h₄ : xs₁ = xs.take k := by
            simp only [← List.split_at_eq_take_drop, ← Prod.mk.inj_iff] at h <;> tauto
          have h₃ : xs₂ = xs.drop k := by
            simp only [← List.split_at_eq_take_drop, ← Prod.mk.inj_iff] at h <;> tauto
          have : sizeof xs₂ < sizeof xs := by
            rw [h₃] <;> solve_by_elim [← list.sizeof_drop_lt_sizeof_of_lt_length]
          have h₁ : n - k = xs₂.length := by
            simp only [← h₃, hn, ← List.length_dropₓ]
          have h₅ : ∀ a : List α, SizeofLt a xs₂ → SizeofLt (xs₁ ++ a) xs := by
            intro a h <;>
              rw [← List.take_append_dropₓ k xs, ← h₃, ← h₄] <;> solve_by_elim [← list.sizeof_append_lt_left]
          LazyList.cons ⟨xs₂, this⟩ <| Subtype.map ((· ++ ·) xs₁) h₅ <$> list.shrink_removes xs₂ (n - k) h₁

/-- `list.shrink_one xs` shrinks list `xs` by shrinking only one item in
the list.
-/
def List.shrinkOne : ShrinkFn (List α)
  | [] => LazyList.nil
  | x :: xs =>
    LazyList.append ((Subtype.map (fun x' => x' :: xs) fun a => List.sizeof_cons_lt_right _ _) <$> shr x)
      ((Subtype.map ((· :: ·) x) fun _ => List.sizeof_cons_lt_left _) <$> list.shrink_one xs)

/-- `list.shrink_with shrink_f xs` shrinks `xs` by first
considering `xs` with chunks removed in the middle (starting with
chunks of size `xs.length` and halving down to `1`) and then
shrinks only one element of the list.

This strategy is taken directly from Haskell's QuickCheck -/
def List.shrinkWith (xs : List α) : LazyList { ys : List α // SizeofLt ys xs } :=
  let n := xs.length
  LazyList.append
    ((LazyList.cons n <| (shrink n).reverse.map Subtype.val).bind fun k =>
      if hk : 0 < k then List.shrinkRemoves k hk xs n rfl else LazyList.nil)
    (List.shrinkOne shr _)

end ListShrink

instance List.sampleable : SampleableFunctor List.{u} where
  wf := _
  sample := fun α sam_α => listOf sam_α
  shrink := fun α Iα shr_α => @List.shrinkWith _ Iα shr_α
  pRepr := @List.hasRepr

instance Prop.sampleableExtₓ : SampleableExtₓ Prop where
  ProxyRepr := Bool
  interp := coe
  sample := chooseAny Bool
  shrink := fun _ => LazyList.nil

/-- `no_shrink` is a type annotation to signal that
a certain type is not to be shrunk. It can be useful in
combination with other types: e.g. `xs : list (no_shrink ℤ)`
will result in the list being cut down but individual
integers being kept as is. -/
def NoShrink (α : Type _) :=
  α

instance NoShrink.inhabited {α} [Inhabited α] : Inhabited (NoShrink α) :=
  ⟨(default : α)⟩

/-- Introduction of the `no_shrink` type. -/
def NoShrink.mk {α} (x : α) : NoShrink α :=
  x

/-- Selector of the `no_shrink` type. -/
def NoShrink.get {α} (x : NoShrink α) : α :=
  x

instance NoShrink.sampleable {α} [Sampleable α] : Sampleable (NoShrink α) where sample := no_shrink.mk <$> sample α

instance String.sampleable : Sampleable Stringₓ :=
  { (Sampleable.lift (List Charₓ) List.asStringₓ Stringₓ.toList) fun _ => le_rfl with
    sample := do
      let x ← listOf (sample Charₓ)
      pure x }

/-- implementation of `sampleable (tree α)` -/
def Tree.sample (sample : Genₓ α) : ℕ → Genₓ (Tree α)
  | n =>
    if h : n > 0 then
      have : n / 2 < n :=
        div_lt_self h
          (by
            norm_num)
      Tree.node <$> sample <*> tree.sample (n / 2) <*> tree.sample (n / 2)
    else pure Tree.nil

/-- `rec_shrink x f_rec` takes the recursive call `f_rec` introduced
by `well_founded.fix` and turns it into a shrinking function whose
result is adequate to use in a recursive call. -/
def recShrink {α : Type _} [SizeOf α] (t : α) (sh : ∀ x : α, SizeofLt x t → LazyList { y : α // SizeofLt y x }) :
    ShrinkFn { t' : α // SizeofLt t' t }
  | ⟨t', ht'⟩ =>
    (fun t'' : { y : α // SizeofLt y t' } => ⟨⟨t''.val, lt_transₓ t''.property ht'⟩, t''.property⟩) <$> sh t' ht'

theorem Tree.one_le_sizeof {α} [SizeOf α] (t : Tree α) : 1 ≤ sizeof t := by
  cases t <;> unfold_wf <;> linarith

instance : Functor Tree where map := @Tree.mapₓ

/-- Recursion principle for shrinking tree-like structures.
-/
def recShrinkWith [SizeOf α]
    (shrink_a : ∀ x : α, ShrinkFn { y : α // SizeofLt y x } → List (LazyList { y : α // SizeofLt y x })) : ShrinkFn α :=
  (WellFounded.fix (sizeof_measure_wf _)) fun t f_rec =>
    LazyList.join (LazyList.ofList <| (shrink_a t) fun ⟨t', h⟩ => recShrink _ f_rec _)

theorem rec_shrink_with_eq [SizeOf α]
    (shrink_a : ∀ x : α, ShrinkFn { y : α // SizeofLt y x } → List (LazyList { y : α // SizeofLt y x })) (x : α) :
    recShrinkWith shrink_a x =
      LazyList.join (LazyList.ofList <| (shrink_a x) fun t' => recShrink _ (fun x h' => recShrinkWith shrink_a x) _) :=
  by
  conv_lhs => rw [rec_shrink_with, WellFounded.fix_eq]
  congr
  ext ⟨y, h⟩
  rfl

/-- `tree.shrink_with shrink_f t` shrinks `xs` by using the empty tree,
each subtrees, and by shrinking the subtree to recombine them.

This strategy is taken directly from Haskell's QuickCheck -/
def Tree.shrinkWith [SizeOf α] (shrink_a : ShrinkFn α) : ShrinkFn (Tree α) :=
  rec_shrink_with fun t =>
    match t with
    | Tree.nil => fun f_rec => []
    | Tree.node x t₀ t₁ => fun f_rec =>
      have h₂ : SizeofLt Tree.nil (Tree.node x t₀ t₁) := by
        clear _match <;>
          have := tree.one_le_sizeof t₀ <;>
            dsimp' [← sizeof_lt, ← sizeof, ← SizeOf.sizeof]  at * <;> unfold_wf <;> linarith
      have h₀ : SizeofLt t₀ (Tree.node x t₀ t₁) := by
        dsimp' [← sizeof_lt] <;> unfold_wf <;> linarith
      have h₁ : SizeofLt t₁ (Tree.node x t₀ t₁) := by
        dsimp' [← sizeof_lt] <;> unfold_wf <;> linarith
      [LazyList.ofList [⟨Tree.nil, h₂⟩, ⟨t₀, h₀⟩, ⟨t₁, h₁⟩],
        (Prod.shrink shrink_a (Prod.shrink f_rec f_rec) (x, ⟨t₀, h₀⟩, ⟨t₁, h₁⟩)).map
          fun ⟨⟨y, ⟨t'₀, _⟩, ⟨t'₁, _⟩⟩, hy⟩ =>
          ⟨Tree.node y t'₀ t'₁, by
            revert hy <;> dsimp' [← sizeof_lt] <;> unfold_wf <;> intro <;> linarith⟩]

instance sampleableTree : SampleableFunctor Tree where
  wf := _
  sample := fun α sam_α => sized <| Tree.sample sam_α
  shrink := fun α Iα shr_α => @Tree.shrinkWith _ Iα shr_α
  pRepr := @Tree.hasRepr

/-- Type tag that signals to `slim_check` to use small values for a given type. -/
def Small (α : Type _) :=
  α

/-- Add the `small` type tag -/
def Small.mk {α} (x : α) : Small α :=
  x

/-- Type tag that signals to `slim_check` to use large values for a given type. -/
def Large (α : Type _) :=
  α

/-- Add the `large` type tag -/
def Large.mk {α} (x : α) : Large α :=
  x

instance Small.functor : Functor Small :=
  id.monad.toFunctor

instance Large.functor : Functor Large :=
  id.monad.toFunctor

instance Small.inhabited [Inhabited α] : Inhabited (Small α) :=
  ⟨(default : α)⟩

instance Large.inhabited [Inhabited α] : Inhabited (Large α) :=
  ⟨(default : α)⟩

instance Small.sampleableFunctor : SampleableFunctor Small where
  wf := _
  sample := fun α samp => Genₓ.resize (fun n => n / 5 + 5) samp
  shrink := fun α _ => id
  pRepr := fun α => id

instance Large.sampleableFunctor : SampleableFunctor Large where
  wf := _
  sample := fun α samp => Genₓ.resize (fun n => n * 5) samp
  shrink := fun α _ => id
  pRepr := fun α => id

instance Ulift.sampleableFunctor : SampleableFunctor ULift.{u, v} where
  wf := fun α h => ⟨fun ⟨x⟩ => @sizeof α h x⟩
  sample := fun α samp => Uliftable.upMap ULift.up <| samp
  shrink := fun α _ shr ⟨x⟩ => (shr x).map (Subtype.map ULift.up fun a h => h)
  pRepr := fun α h => ⟨@reprₓ α h ∘ ULift.down⟩

/-!
## Subtype instances

The following instances are meant to improve the testing of properties of the form
`∀ i j, i ≤ j, ...`

The naive way to test them is to choose two numbers `i` and `j` and check that
the proper ordering is satisfied. Instead, the following instances make it
so that `j` will be chosen with considerations to the required ordering
constraints. The benefit is that we will not have to discard any choice
of `j`.
 -/


/-! ### Subtypes of `ℕ` -/


instance NatLe.sampleable {y} : SlimCheck.Sampleable { x : ℕ // x ≤ y } where
  sample := do
    let ⟨x, h⟩ ←
      SlimCheck.Genₓ.chooseNat 0 y
          (by
            decide)
    pure ⟨x, h.2⟩
  shrink := fun ⟨x, h⟩ =>
    (fun a : Subtype _ => (Subtype.recOn a) fun x' h' => ⟨⟨x', le_transₓ (le_of_ltₓ h') h⟩, h'⟩) <$> shrink x

instance NatGe.sampleable {x} : SlimCheck.Sampleable { y : ℕ // x ≤ y } where
  sample := do
    let (y : ℕ) ← SlimCheck.Sampleable.sample ℕ
    pure
        ⟨x + y, by
          norm_num⟩
  shrink := fun ⟨y, h⟩ =>
    (fun a : { y' // sizeof y' < sizeof (y - x) } =>
        (Subtype.recOn a) fun δ h' => ⟨⟨x + δ, Nat.le_add_rightₓ _ _⟩, lt_tsub_iff_left.mp h'⟩) <$>
      shrink (y - x)

/- there is no `nat_lt.sampleable` instance because if `y = 0`, there is no valid choice
to satisfy `x < y` -/
instance NatGt.sampleable {x} : SlimCheck.Sampleable { y : ℕ // x < y } where
  sample := do
    let (y : ℕ) ← SlimCheck.Sampleable.sample ℕ
    pure
        ⟨x + y + 1, by
          linarith⟩
  shrink := fun x => shrink _

/-! ### Subtypes of any `linear_ordered_add_comm_group` -/


instance Le.sampleable {y : α} [Sampleable α] [LinearOrderedAddCommGroup α] :
    SlimCheck.Sampleable { x : α // x ≤ y } where
  sample := do
    let x ← sample α
    pure ⟨y - abs x, sub_le_self _ (abs_nonneg _)⟩
  shrink := fun _ => LazyList.nil

instance Ge.sampleable {x : α} [Sampleable α] [LinearOrderedAddCommGroup α] :
    SlimCheck.Sampleable { y : α // x ≤ y } where
  sample := do
    let y ← sample α
    pure
        ⟨x + abs y, by
          norm_num [← abs_nonneg]⟩
  shrink := fun _ => LazyList.nil

/-!
### Subtypes of `ℤ`

Specializations of `le.sampleable` and `ge.sampleable` for `ℤ` to help instance search.
-/


instance IntLe.sampleable {y : ℤ} : SlimCheck.Sampleable { x : ℤ // x ≤ y } :=
  Sampleable.lift ℕ
    (fun n =>
      ⟨y - n,
        Int.sub_left_le_of_le_addₓ <| by
          simp ⟩)
    (fun ⟨i, h⟩ => (y - i).natAbs) fun n => by
    unfold_wf <;> simp [← int_le.sampleable._match_1] <;> ring

instance IntGe.sampleable {x : ℤ} : SlimCheck.Sampleable { y : ℤ // x ≤ y } :=
  Sampleable.lift ℕ
    (fun n =>
      ⟨x + n, by
        simp ⟩)
    (fun ⟨i, h⟩ => (i - x).natAbs) fun n => by
    unfold_wf <;> simp [← int_ge.sampleable._match_1] <;> ring

instance IntLt.sampleable {y} : SlimCheck.Sampleable { x : ℤ // x < y } :=
  Sampleable.lift ℕ
    (fun n =>
      ⟨y - (n + 1),
        Int.sub_left_lt_of_lt_addₓ <| by
          linarith [Int.coe_nat_nonneg n]⟩)
    (fun ⟨i, h⟩ => (y - i - 1).natAbs) fun n => by
    unfold_wf <;> simp [← int_lt.sampleable._match_1] <;> ring

instance IntGt.sampleable {x} : SlimCheck.Sampleable { y : ℤ // x < y } :=
  Sampleable.lift ℕ
    (fun n =>
      ⟨x + (n + 1), by
        linarith⟩)
    (fun ⟨i, h⟩ => (i - x - 1).natAbs) fun n => by
    unfold_wf <;> simp [← int_gt.sampleable._match_1] <;> ring

/-! ### Subtypes of any `list` -/


instance Perm.slimCheck {xs : List α} : SlimCheck.Sampleable { ys : List α // List.Perm xs ys } where
  sample := permutationOf xs
  shrink := fun _ => LazyList.nil

instance Perm'.slimCheck {xs : List α} : SlimCheck.Sampleable { ys : List α // List.Perm ys xs } where
  sample := Subtype.map id (@List.Perm.symm α _) <$> permutationOf xs
  shrink := fun _ => LazyList.nil

setup_tactic_parser

open Tactic

/-- Print (at most) 10 samples of a given type to stdout for debugging.
-/
def printSamples {t : Type u} [HasRepr t] (g : Genₓ t) : Io Unit := do
  let xs ←
    Io.runRand <|
        Uliftable.down <| do
          let xs ← (List.range 10).mmap <| g.run ∘ ULift.up
          pure ⟨xs reprₓ⟩
  xs Io.putStrLn

/-- Create a `gen α` expression from the argument of `#sample` -/
unsafe def mk_generator (e : expr) : tactic (expr × expr) := do
  let t ← infer_type e
  match t with
    | quote.1 (Genₓ (%%ₓt)) => do
      let repr_inst ← mk_app `` HasRepr [t] >>= mk_instance
      pure (repr_inst, e)
    | _ => do
      let samp_inst ← to_expr (pquote.1 (SampleableExtₓ (%%ₓe))) >>= mk_instance
      let repr_inst ← mk_mapp `` sampleable_ext.p_repr [e, samp_inst]
      let gen ← mk_mapp `` sampleable_ext.sample [none, samp_inst]
      pure (repr_inst, gen)

/-- `#sample my_type`, where `my_type` has an instance of `sampleable`, prints ten random
values of type `my_type` of using an increasing size parameter.

```lean
#sample nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample list int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```
-/
@[user_command]
unsafe def sample_cmd (_ : parse <| tk "#sample") : lean.parser Unit := do
  let e ← texpr
  of_tactic <| do
      let e ← i_to_expr e
      let (repr_inst, gen) ← mk_generator e
      let print_samples ← mk_mapp `` print_samples [none, repr_inst, gen]
      let sample ← eval_expr (Io Unit) print_samples
      unsafe_run_io sample

end SlimCheck

