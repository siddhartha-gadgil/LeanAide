/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

/-!

# Workaround for stack overflows with `has_reflect string`

The default `has_reflect string` instance in Lean only work for strings up to
few thousand characters.  Anything larger than that will trigger a stack overflow because
the string is represented as a very deeply nested expression:
https://github.com/leanprover-community/lean/issues/144

This file adds a higher-priority instance for `has_reflect string`, which
behaves exactly the same for small strings (up to 256 characters). Larger
strings are carefully converted into a call to `string.join`.

-/


/-- Splits a string into chunks of at most `size` characters.
-/
unsafe def string.to_chunks (size : ℕ) : Stringₓ → optParam (List Stringₓ) [] → List Stringₓ
  | s, Acc => if s.length ≤ size then s :: Acc else string.to_chunks (s.popnBack size) (s.backn size :: Acc)

section

attribute [local semireducible] reflected

unsafe instance {α} [has_reflect α] : has_reflect (Thunkₓ α)
  | a => expr.lam `x BinderInfo.default (reflect Unit) (reflect <| a ())

end

unsafe instance (priority := 2000) : has_reflect Stringₓ
  | s =>
    let chunk_size := 256
    if s.length ≤ chunk_size then reflect s
    else
      have ts : List (Thunkₓ Stringₓ) := (s.to_chunks chunk_size).map fun s _ => s
      have h : s = Stringₓ.join (ts.map fun t => t ()) := undefined
      suffices reflected _ (Stringₓ.join <| ts.map fun t => t ()) by
        rwa [h]
      quote.1 (Stringₓ.join <| List.map _ _)

