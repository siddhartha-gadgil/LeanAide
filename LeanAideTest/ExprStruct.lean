import LeanAide
import Lean

open Lean Meta Elab
open LeanAide Meta CodeGenerator


-- set_option pp.funBinderTypes true in
/--
info: Checking dependence: false
---
info: 2 sorries in let h₀ := sorry;
sorry with types:
---
info: let h₀ := sorry;
ℕ
---
info: ℕ
---
info: let h₀ := sorry;
sorry : ℕ
-/
#guard_msgs in
#check show_sorries (let h₀ : Nat := (sorry : Nat)
  sorry : Nat)

/--
info: 1 sorries in sorry with types:
---
info: True
---
info: sorry : True
-/
#guard_msgs in
#check show_sorries (sorry : True)

/--
info: Purged lets in ⏎
let a := sorry;
sorry
 to ⏎
sorry
---
info: sorry : ℕ
-/
#guard_msgs in
#check purge_lets (let a : Nat := (sorry : Nat)
  sorry : Nat)

/--
info: Purged lets in ⏎
let a := sorry;
sorry + a
 to ⏎
let a := sorry;
sorry + a
---
info: let a := sorry;
sorry + a : ℕ
-/
#guard_msgs in
#check purge_lets (let a : Nat := (sorry : Nat)
  sorry + a : Nat)

/--
info: Purged lets in ⏎
let a := sorry;
3
 to ⏎
3
---
info: 3 : ℕ
-/
#guard_msgs in
#check purge_lets (let a : Nat := (sorry : Nat)
  3 : Nat)

/--
info: Purged lets in ⏎
let a := sorry;
3 + a
 to ⏎
let a := sorry;
3 + a
---
info: let a := sorry;
3 + a : ℕ
-/
#guard_msgs in
#check purge_lets (let a : Nat := (sorry : Nat)
  3 + a : Nat)


elab "#exists_vars" type:term : command => do
  Command.liftTermElabM do
  match ← existsVarTypesStx type with
  | some vars =>
      logInfo s!"Vars: {vars.map (·.1)}"
      return
  | none =>
      logInfo s!"No vars"
      return

/-- info: Vars: #[`n, `m, `k] -/
#guard_msgs in
#exists_vars ∃ n m : Nat, ∃ k: Nat, n + m  = 3

/-- info: Vars: #[`n, `m, `k] -/
#guard_msgs in
#exists_vars ∃ (n : Nat) (m: Nat), ∃ k: Nat, n + m  = 3
