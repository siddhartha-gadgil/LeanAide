/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.Tactic.FreshNames
import Mathbin.Tactic.ReassocAxiom
import Mathbin.Tactic.Slice

/-!
# Tools to reformulate category-theoretic lemmas in concrete categories

## The `elementwise` attribute

The `elementwise` attribute can be applied to a lemma

```lean
@[elementwise]
lemma some_lemma {C : Type*} [category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) : f ≫ g = h := ...
```

and will produce

```lean
lemma some_lemma_apply {C : Type*} [category C] [concrete_category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) (x : X) : g (f x) = h x := ...
```

Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f`, `g`, and `h` are being coerced to functions via `concrete_category.has_coe_to_fun`.
Further, we simplify the type using `concrete_category.coe_id : ((𝟙 X) : X → X) x = x` and
`concrete_category.coe_comp : (f ≫ g) x = g (f x)`,
replacing morphism composition with function composition.

The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.

## Implementation

This closely follows the implementation of the `@[reassoc]` attribute, due to Simon Hudon.
Thanks to Gabriel Ebner for help diagnosing universe issues.

-/


namespace Tactic

open Interactive Lean.Parser CategoryTheory

/-- From an expression `f = g`,
where `f g : X ⟶ Y` for some objects `X Y : V` with `[S : category V]`,
extract the expression for `S`.
-/
unsafe def extract_category : expr → tactic expr
  | quote.1 (@Eq (@Quiver.Hom _ (@CategoryStruct.toQuiver _ (@Category.toCategoryStruct _ (%%ₓS))) _ _) _ _) => pure S
  | _ => failed

/-- (internals for `@[elementwise]`)
Given a lemma of the form `f = g`, where `f g : X ⟶ Y` and `X Y : V`,
proves a new lemma of the form
`∀ (x : X), f x = g x`
if we are already in a concrete category, or
`∀ [concrete_category.{w} V] (x : X), f x = g x`
otherwise.

Returns the type and proof of this lemma,
and the universe parameter `w` for the `concrete_category` instance, if it was not synthesized.
-/
-- This is closely modelled on `reassoc_axiom`.
unsafe def prove_elementwise (h : expr) : tactic (expr × expr × Option Name) := do
  let (vs, t) ← infer_type h >>= open_pis
  let (f, g) ← match_eq t
  let S ← extract_category t <|> fail "no morphism equation found in statement"
  let quote.1 (@Quiver.Hom _ (%%ₓH) (%%ₓX) (%%ₓY)) ← infer_type f
  let C ← infer_type X
  let CC_type ← to_expr (pquote.1 (@ConcreteCategory (%%ₓC) (%%ₓS)))
  let (CC, CC_found) ←
    (do
          let CC ← mk_instance CC_type
          pure (CC, tt)) <|>
        do
        let CC ← mk_local' `I BinderInfo.inst_implicit CC_type
        pure (CC, ff)
  let CC_type
    ←-- This is need to fill in universe levels fixed by `mk_instance`:
        instantiate_mvars
        CC_type
  let x_type ←
    to_expr (pquote.1 (@coeSort (%%ₓC) _ (@CategoryTheory.ConcreteCategory.hasCoeToSort (%%ₓC) (%%ₓS) (%%ₓCC)) (%%ₓX)))
  let x ← mk_local_def `x x_type
  let t' ←
    to_expr
        (pquote.1
          (@coeFn (@Quiver.Hom (%%ₓC) (%%ₓH) (%%ₓX) (%%ₓY)) _
              (@CategoryTheory.ConcreteCategory.hasCoeToFun (%%ₓC) (%%ₓS) (%%ₓCC) (%%ₓX) (%%ₓY)) (%%ₓf) (%%ₓx) =
            @coeFn (@Quiver.Hom (%%ₓC) (%%ₓH) (%%ₓX) (%%ₓY)) _
              (@CategoryTheory.ConcreteCategory.hasCoeToFun (%%ₓC) (%%ₓS) (%%ₓCC) (%%ₓX) (%%ₓY)) (%%ₓg) (%%ₓx)))
  let c' := h.mk_app vs
  let (_, pr) ← solve_aux t' (andthen (rewrite_target c') reflexivity)
  let-- The codomain of forget lives in a new universe, which may be now a universe metavariable
    -- if we didn't synthesize an instance:
    [w, _, _]
    ← pure CC_type.get_app_fn.univ_levels
  let n
    ←-- We unify that with a fresh universe parameter.
      match w with
      | level.mvar _ => do
        let n ← get_unused_name_reserved [`w] mk_name_set
        unify (expr.sort (level.param n)) (expr.sort w)
        pure (Option.some n)
      | _ => pure Option.none
  let t' ← instantiate_mvars t'
  let CC ← instantiate_mvars CC
  let x ← instantiate_mvars x
  let-- Now the key step: replace morphism composition with function composition,
  -- and identity morphisms with nothing.
  s := simp_lemmas.mk
  let s ← s.add_simp `` id_apply
  let s ← s.add_simp `` comp_apply
  let (t'', pr', _) ← simplify s [] t' { failIfUnchanged := false }
  let pr' ← mk_eq_mp pr' pr
  let-- Further, if we're in `Type`, get rid of the coercions entirely.
  s := simp_lemmas.mk
  let s ← s.add_simp `` concrete_category.has_coe_to_fun_Type
  let (t'', pr'', _) ← simplify s [] t'' { failIfUnchanged := false }
  let pr'' ← mk_eq_mp pr'' pr'
  let t'' ← pis (vs ++ if CC_found then [x] else [CC, x]) t''
  let pr'' ← lambdas (vs ++ if CC_found then [x] else [CC, x]) pr''
  pure (t'', pr'', n)

/-- (implementation for `@[elementwise]`)
Given a declaration named `n` of the form `∀ ..., f = g`, proves a new lemma named `n'`
of the form `∀ ... [concrete_category V] (x : X), f x = g x`.
-/
unsafe def elementwise_lemma (n : Name) (n' : Name := n.appendSuffix "_apply") : tactic Unit := do
  let d ← get_decl n
  let c := @expr.const true n d.univ_levels
  let (t'', pr', l') ← prove_elementwise c
  let params := l'.toList ++ d.univ_params
  add_decl <| declaration.thm n' params t'' (pure pr')
  copy_attribute `simp n n'

/-- The `elementwise` attribute can be applied to a lemma

```lean
@[elementwise]
lemma some_lemma {C : Type*} [category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) : f ≫ g = h := ...
```

and will produce

```lean
lemma some_lemma_apply {C : Type*} [category C] [concrete_category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) (x : X) : g (f x) = h x := ...
```

Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f`, `g`, and `h` are being coerced to functions via `concrete_category.has_coe_to_fun`.
Further, we simplify the type using `concrete_category.coe_id : ((𝟙 X) : X → X) x = x` and
`concrete_category.coe_comp : (f ≫ g) x = g (f x)`,
replacing morphism composition with function composition.

The `[concrete_category C]` argument will be omitted if it is possible to synthesize an instance.

The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.
-/
@[user_attribute]
unsafe def elementwise_attr : user_attribute Unit (Option Name) where
  Name := `elementwise
  descr := "create a companion lemma for a morphism equation applied to an element"
  parser := optionalₓ ident
  after_set :=
    some fun n _ _ => do
      let some n' ← elementwise_attr.get_param n | elementwise_lemma n (n.appendSuffix "_apply")
      elementwise_lemma n <| n ++ n'

add_tactic_doc
  { Name := "elementwise", category := DocCategory.attr, declNames := [`tactic.elementwise_attr],
    tags := ["category theory"] }

namespace Interactive

setup_tactic_parser

/-- `elementwise h`, for assumption `w : ∀ ..., f ≫ g = h`, creates a new assumption
`w : ∀ ... (x : X), g (f x) = h x`.

`elementwise! h`, does the same but deletes the initial `h` assumption.
(You can also add the attribute `@[elementwise]` to lemmas to generate new declarations generalized
in this way.)
-/
unsafe def elementwise (del : parse (tk "!")?) (ns : parse ident*) : tactic Unit := do
  ns fun n => do
      let h ← get_local n
      let (t, pr, u) ← prove_elementwise h
      assertv n t pr
      when del (tactic.clear h)

end Interactive

/-- Auxiliary definition for `category_theory.elementwise_of`. -/
unsafe def derive_elementwise_proof : tactic Unit := do
  let quote.1 (CalculatedProp (%%ₓv) (%%ₓh)) ← target
  let (t, pr, n) ← prove_elementwise h
  unify v t
  exact pr

end Tactic

/-- With `w : ∀ ..., f ≫ g = h` (with universal quantifiers tolerated),
`elementwise_of w : ∀ ... (x : X), g (f x) = h x`.

The type and proof of `elementwise_of h` is generated by `tactic.derive_elementwise_proof`
which makes `elementwise_of` meta-programming adjacent. It is not called as a tactic but as
an expression. The goal is to avoid creating assumptions that are dismissed after one use:

```lean
example (M N K : Mon.{u}) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
  g (f m) = h m :=
begin
  rw elementwise_of w,
end
```
-/
theorem CategoryTheory.elementwise_of {α} (hh : α) {β}
    (x : Tactic.CalculatedProp β hh := by
      run_tac
        tactic.derive_elementwise_proof) :
    β :=
  x

/-- With `w : ∀ ..., f ≫ g = h` (with universal quantifiers tolerated),
`elementwise_of w : ∀ ... (x : X), g (f x) = h x`.

Although `elementwise_of` is not a tactic or a meta program, its type is generated
through meta-programming to make it usable inside normal expressions.
-/
add_tactic_doc
  { Name := "category_theory.elementwise_of", category := DocCategory.tactic,
    declNames := [`category_theory.elementwise_of], tags := ["category theory"] }

