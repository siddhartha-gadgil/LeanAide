/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.Tactic.FinCases
import Mathbin.Algebra.BigOperators.Fin

/-!
# Matrix and vector notation

This file includes `simp` lemmas for applying operations in `data.matrix.basic` to values built out
of the matrix notation `![a, b] = vec_cons a (vec_cons b vec_empty)` defined in
`data.fin.vec_notation`.

This also provides the new notation `!![a, b; c, d] = matrix.of ![![a, b], ![c, d]]`.
This notation also works for empty matrices; `!![,,,] : matrix (fin 0) (fin 3)` and
`!![;;;] : matrix (fin 3) (fin 0)`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

This file provide notation `!![a, b; c, d]` for matrices, which corresponds to
`matrix.of ![![a, b], ![c, d]]`.
A parser for `a, b; c, d`-style strings is provided as `matrix.entry_parser`, while
`matrix.notation` provides the hook for the `!!` notation.
Note that in lean 3 the pretty-printer will not show `!!` notation, instead showing the version
with `of ![![...]]`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/


namespace Matrix

universe u

variable {α : Type u} {o n m : ℕ} {m' n' o' : Type _}

open Matrix

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]
-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]
/-- Matrices can be reflected whenever their entries can. We insert an `@id (matrix m' n' α)` to
prevent immediate decay to a function. -/
unsafe instance matrix.reflect [reflected_univ.{u}] [reflected_univ.{u_1}] [reflected_univ.{u_2}] [reflected _ α]
    [reflected _ m'] [reflected _ n'] [h : has_reflect (m' → n' → α)] : has_reflect (Matrix m' n' α) := fun m =>
  (by
          trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]" :
          reflected _ @id.{max u_1 u_2 u + 1}).subst₂
      ((by
            trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `reflect_name #[]" :
            reflected _ @Matrix.{u_1, u_2, u}).subst₃
        (quote.1 _) (quote.1 _) (quote.1 _)) <|
    by
    dunfold Matrix
    exact h m

section Parser

open Lean

open Lean.Parser

open Interactive

open Interactive.Types

/-- Parse the entries of a matrix -/
unsafe def entry_parser {α : Type} (p : parser α) : parser (Σm n, Finₓ m → Finₓ n → α) := do
  let-- a list of lists if the matrix has at least one row, or the number of columns if the matrix has
  -- zero rows.
  p :
    parser (Sum (List (List α)) ℕ) :=-- empty rows
        Sum.inl <$>
        ((pure [] <* tk ";").repeat_at_least 1 <|> (sep_by_trailing (tk ";") <| sep_by_trailing (tk ",") p)) <|>
      Sum.inr <$> List.length <$> many (tk ",")
  let which
    ←-- empty columns
      p
  match which with
    | Sum.inl l => do
      let h :: tl ← pure l
      let n := h
      let l : List (Vector α n) ←
        l fun row =>
            if h : row = n then pure (⟨row, h⟩ : Vector α n) else interaction_monad.fail "Rows must be of equal length"
      pure ⟨l, n, fun i j => (l _ i).nth j⟩
    | Sum.inr n => pure ⟨0, n, finZeroElim⟩

-- Lean can't find this instance without some help. We only need it available in `Type 0`, and it is
-- a massive amount of effort to make it universe-polymorphic.
@[instance]
unsafe def sigma_sigma_fin_matrix_has_reflect {α : Type} [has_reflect α] [reflected _ α] :
    has_reflect (Σm n : ℕ, Finₓ m → Finₓ n → α) :=
  (@sigma.reflect.{0, 0} _ _ ℕ (fun m => Σn, Finₓ m → Finₓ n → α) _ _ _) fun i =>
    @sigma.reflect.{0, 0} _ _ ℕ _ _ _ _ fun j => inferInstance

/-- `!![a, b; c, d]` notation for matrices indexed by `fin m` and `fin n`. See the module docstring
for details. -/
@[user_notation]
unsafe def notation (_ : parse <| tk "!![") (val : parse (entry_parser (parser.pexpr 1) <* tk "]")) : parser pexpr := do
  let ⟨m, n, entries⟩ := val
  let entry_vals := pi_fin.to_pexpr (pi_fin.to_pexpr ∘ entries)
  pure ((pquote.1 (@Matrix.of (Finₓ (%%ₓquote.1 m)) (Finₓ (%%ₓquote.1 n)) _)).app entry_vals)

end Parser

variable (a b : ℕ)

/-- Use `![...]` notation for displaying a `fin`-indexed matrix, for example:

```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
instance [HasRepr α] :
    HasRepr
      (Matrix (Finₓ m) (Finₓ n)
        α) where repr := fun f =>
    "!![" ++
        (Stringₓ.intercalate "; " <|
          (List.finRange m).map fun i => Stringₓ.intercalate ", " <| (List.finRange n).map fun j => reprₓ (f i j)) ++
      "]"

@[simp]
theorem cons_val' (v : n' → α) (B : Finₓ m → n' → α) (i j) : vecCons v B i j = vecCons (v j) (fun i => B i j) i := by
  refine' Finₓ.cases _ _ i <;> simp

@[simp]
theorem head_val' (B : Finₓ m.succ → n' → α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl

@[simp]
theorem tail_val' (B : Finₓ m.succ → n' → α) (j : n') : (vecTail fun i => B i j) = fun i => vecTail B i j := by
  ext
  simp [← vec_tail]

section DotProduct

variable [AddCommMonoidₓ α] [Mul α]

@[simp]
theorem dot_product_empty (v w : Finₓ 0 → α) : dotProduct v w = 0 :=
  Finset.sum_empty

@[simp]
theorem cons_dot_product (x : α) (v : Finₓ n → α) (w : Finₓ n.succ → α) :
    dotProduct (vecCons x v) w = x * vecHead w + dotProduct v (vecTail w) := by
  simp [← dot_product, ← Finₓ.sum_univ_succ, ← vec_head, ← vec_tail]

@[simp]
theorem dot_product_cons (v : Finₓ n.succ → α) (x : α) (w : Finₓ n → α) :
    dotProduct v (vecCons x w) = vecHead v * x + dotProduct (vecTail v) w := by
  simp [← dot_product, ← Finₓ.sum_univ_succ, ← vec_head, ← vec_tail]

@[simp]
theorem cons_dot_product_cons (x : α) (v : Finₓ n → α) (y : α) (w : Finₓ n → α) :
    dotProduct (vecCons x v) (vecCons y w) = x * y + dotProduct v w := by
  simp

end DotProduct

section ColRow

@[simp]
theorem col_empty (v : Finₓ 0 → α) : colₓ v = vec_empty :=
  empty_eq _

@[simp]
theorem col_cons (x : α) (u : Finₓ m → α) : colₓ (vecCons x u) = vecCons (fun _ => x) (colₓ u) := by
  ext i j
  refine' Finₓ.cases _ _ i <;> simp [← vec_head, ← vec_tail]

@[simp]
theorem row_empty : rowₓ (vecEmpty : Finₓ 0 → α) = fun _ => vecEmpty := by
  ext
  rfl

@[simp]
theorem row_cons (x : α) (u : Finₓ m → α) : rowₓ (vecCons x u) = fun _ => vecCons x u := by
  ext
  rfl

end ColRow

section Transpose

@[simp]
theorem transpose_empty_rows (A : Matrix m' (Finₓ 0) α) : Aᵀ = of ![] :=
  empty_eq _

@[simp]
theorem transpose_empty_cols (A : Matrix (Finₓ 0) m' α) : Aᵀ = of fun i => ![] :=
  funext fun i => empty_eq _

@[simp]
theorem cons_transpose (v : n' → α) (A : Matrix (Finₓ m) n' α) :
    (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i) := by
  ext i j
  refine' Finₓ.cases _ _ j <;> simp

@[simp]
theorem head_transpose (A : Matrix m' (Finₓ n.succ) α) : vecHead (of.symm Aᵀ) = vec_head ∘ of.symm A :=
  rfl

@[simp]
theorem tail_transpose (A : Matrix m' (Finₓ n.succ) α) : vecTail (of.symm Aᵀ) = (vec_tail ∘ A)ᵀ := by
  ext i j
  rfl

end Transpose

section Mul

variable [Semiringₓ α]

@[simp]
theorem empty_mul [Fintype n'] (A : Matrix (Finₓ 0) n' α) (B : Matrix n' o' α) : A ⬝ B = of ![] :=
  empty_eq _

@[simp]
theorem empty_mul_empty (A : Matrix m' (Finₓ 0) α) (B : Matrix (Finₓ 0) o' α) : A ⬝ B = 0 :=
  rfl

@[simp]
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Finₓ 0) α) : A ⬝ B = of fun _ => ![] :=
  funext fun _ => empty_eq _

theorem mul_val_succ [Fintype n'] (A : Matrix (Finₓ m.succ) n' α) (B : Matrix n' o' α) (i : Finₓ m) (j : o') :
    (A ⬝ B) i.succ j = (of (vecTail (of.symm A)) ⬝ B) i j :=
  rfl

@[simp]
theorem cons_mul [Fintype n'] (v : n' → α) (A : Finₓ m → n' → α) (B : Matrix n' o' α) :
    of (vecCons v A) ⬝ B = of (vecCons (vecMulₓ v B) (of.symm (of A ⬝ B))) := by
  ext i j
  refine' Finₓ.cases _ _ i
  · rfl
    
  simp [← mul_val_succ]

end Mul

section VecMul

variable [Semiringₓ α]

@[simp]
theorem empty_vec_mul (v : Finₓ 0 → α) (B : Matrix (Finₓ 0) o' α) : vecMulₓ v B = 0 :=
  rfl

@[simp]
theorem vec_mul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Finₓ 0) α) : vecMulₓ v B = ![] :=
  empty_eq _

@[simp]
theorem cons_vec_mul (x : α) (v : Finₓ n → α) (B : Finₓ n.succ → o' → α) :
    vecMulₓ (vecCons x v) (of B) = x • vecHead B + vecMulₓ v (of <| vecTail B) := by
  ext i
  simp [← vec_mul]

@[simp]
theorem vec_mul_cons (v : Finₓ n.succ → α) (w : o' → α) (B : Finₓ n → o' → α) :
    vecMulₓ v (of <| vecCons w B) = vecHead v • w + vecMulₓ (vecTail v) (of B) := by
  ext i
  simp [← vec_mul]

@[simp]
theorem cons_vec_mul_cons (x : α) (v : Finₓ n → α) (w : o' → α) (B : Finₓ n → o' → α) :
    vecMulₓ (vecCons x v) (of <| vecCons w B) = x • w + vecMulₓ v (of B) := by
  simp

end VecMul

section MulVec

variable [Semiringₓ α]

@[simp]
theorem empty_mul_vec [Fintype n'] (A : Matrix (Finₓ 0) n' α) (v : n' → α) : mulVecₓ A v = ![] :=
  empty_eq _

@[simp]
theorem mul_vec_empty (A : Matrix m' (Finₓ 0) α) (v : Finₓ 0 → α) : mulVecₓ A v = 0 :=
  rfl

@[simp]
theorem cons_mul_vec [Fintype n'] (v : n' → α) (A : Finₓ m → n' → α) (w : n' → α) :
    mulVecₓ (of <| vecCons v A) w = vecCons (dotProduct v w) (mulVecₓ (of A) w) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp [← mul_vec]

@[simp]
theorem mul_vec_cons {α} [CommSemiringₓ α] (A : m' → Finₓ n.succ → α) (x : α) (v : Finₓ n → α) :
    mulVecₓ (of A) (vecCons x v) = x • vec_head ∘ A + mulVecₓ (of (vec_tail ∘ A)) v := by
  ext i
  simp [← mul_vec, ← mul_comm]

end MulVec

section VecMulVec

variable [Semiringₓ α]

@[simp]
theorem empty_vec_mul_vec (v : Finₓ 0 → α) (w : n' → α) : vecMulVecₓ v w = ![] :=
  empty_eq _

@[simp]
theorem vec_mul_vec_empty (v : m' → α) (w : Finₓ 0 → α) : vecMulVecₓ v w = fun _ => ![] :=
  funext fun i => empty_eq _

@[simp]
theorem cons_vec_mul_vec (x : α) (v : Finₓ m → α) (w : n' → α) :
    vecMulVecₓ (vecCons x v) w = vecCons (x • w) (vecMulVecₓ v w) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp [← vec_mul_vec]

@[simp]
theorem vec_mul_vec_cons (v : m' → α) (x : α) (w : Finₓ n → α) :
    vecMulVecₓ v (vecCons x w) = fun i => v i • vecCons x w := by
  ext i j
  rw [vec_mul_vec, Pi.smul_apply, smul_eq_mul]

end VecMulVec

section Smul

variable [Semiringₓ α]

@[simp]
theorem smul_mat_empty {m' : Type _} (x : α) (A : Finₓ 0 → m' → α) : x • A = ![] :=
  empty_eq _

@[simp]
theorem smul_mat_cons (x : α) (v : n' → α) (A : Finₓ m → n' → α) : x • vecCons v A = vecCons (x • v) (x • A) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp

end Smul

section Minor

@[simp]
theorem minor_empty (A : Matrix m' n' α) (row : Finₓ 0 → m') (col : o' → n') : minor A row col = ![] :=
  empty_eq _

@[simp]
theorem minor_cons_row (A : Matrix m' n' α) (i : m') (row : Finₓ m → m') (col : o' → n') :
    minor A (vecCons i row) col = vecCons (fun j => A i (col j)) (minor A row col) := by
  ext i j
  refine' Finₓ.cases _ _ i <;> simp [← minor]

end Minor

section Vec2AndVec3

section One

variable [Zero α] [One α]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem one_fin_two :
    (1 : Matrix (Finₓ 2) (Finₓ 2) α) =
      «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem one_fin_three :
    (1 : Matrix (Finₓ 3) (Finₓ 3) α) =
      «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end One

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem eta_fin_two (A : Matrix (Finₓ 2) (Finₓ 2) α) :
    A = «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem eta_fin_three (A : Matrix (Finₓ 3) (Finₓ 3) α) :
    A = «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem mul_fin_two [AddCommMonoidₓ α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" ⬝
        «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" =
      «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Matrix.mul, ← dot_product, ← Finₓ.sum_univ_succ]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem mul_fin_three [AddCommMonoidₓ α] [Mul α]
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
    «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" ⬝
        «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" =
      «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Matrix.mul, ← dot_product, ← Finₓ.sum_univ_succ, add_assocₓ]

theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  subst_vars

theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) : ![a₀, a₁, a₂] = ![b₀, b₁, b₂] :=
  by
  subst_vars

theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  rw [cons_add_cons, cons_add_cons, empty_add_empty]

theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) : ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  rw [cons_add_cons, cons_add_cons, cons_add_cons, empty_add_empty]

theorem smul_vec2 {R : Type _} [HasSmul R α] (x : R) (a₀ a₁ : α) : x • ![a₀, a₁] = ![x • a₀, x • a₁] := by
  rw [smul_cons, smul_cons, smul_empty]

theorem smul_vec3 {R : Type _} [HasSmul R α] (x : R) (a₀ a₁ a₂ : α) : x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] :=
  by
  rw [smul_cons, smul_cons, smul_cons, smul_empty]

variable [AddCommMonoidₓ α] [Mul α]

theorem vec2_dot_product' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, dot_product_empty, add_zeroₓ]

@[simp]
theorem vec2_dot_product (v w : Finₓ 2 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dot_product'

theorem vec3_dot_product' {a₀ a₁ a₂ b₀ b₁ b₂ : α} : ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, cons_dot_product_cons, dot_product_empty, add_zeroₓ, add_assocₓ]

@[simp]
theorem vec3_dot_product (v w : Finₓ 3 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dot_product'

end Vec2AndVec3

end Matrix

