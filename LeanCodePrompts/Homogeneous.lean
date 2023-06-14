import Lean
import Mathlib
/-!
An attempt to give priority to homogeneous operations in the elaborator and make some other changes that allow expressions without too many type annotations.

* If the expected type is known, then `*`, `+`, `-` and `/` are elaborated by seeking terms of the expected type first.
-/

open Lean Meta Elab Term

namespace Homogeneous

attribute [-instance] Nat.instDivNat
example (n : ℕ) : ℚ := ((4 *((n*(n-1)/2 : ℚ)^3 : ℚ) - (((n*(n-1)/2 : ℚ)^2) : ℚ)) : ℚ)/3

scoped syntax  (name := homdiv) (priority := high) term:71 " / " term:70 : term
scoped syntax  (name := hommul) (priority := high) term:71 " * " term:70 : term
scoped syntax  (name := homadd) (priority := high) term:66 " + " term:65 : term
scoped syntax  (name := homsub) (priority := high) term:66 " - " term:65 : term

scoped syntax  (name := hompow) (priority := high) term:85 "^" term:86 : term

@[term_elab homdiv] def elabDiv : TermElab := fun stx expectedType? => do
  -- logInfo m!"elabDiv {stx} {expectedType?}"
  match stx with
  | `($x / $y) => do
    match expectedType? with
    | none =>
        let x ← elabTerm x none
        let y ← elabTerm y none
        mkAppM ``HDiv.hDiv #[x, y] 
    | some expectedType => 
        let x ← elabTermEnsuringType x (some expectedType)
        let y ← elabTermEnsuringType y (some expectedType)
        mkAppOptM ``HDiv.hDiv #[some expectedType, some expectedType, some expectedType, none, x, y]
  | _ => throwUnsupportedSyntax

@[term_elab hommul] def elabMul : TermElab := fun stx expectedType? => do
  -- logInfo m!"elabMul {stx} {expectedType?}"
  match stx with
  | `($x * $y) => do
    match expectedType? with
    | none =>
        let x ← elabTerm x none
        let y ← elabTerm y none
        mkAppM ``HMul.hMul #[x, y] 
    | some expectedType => 
        let x ← elabTermEnsuringType x (some expectedType)
        let y ← elabTermEnsuringType y (some expectedType)
        mkAppOptM ``HMul.hMul #[some expectedType, some expectedType, some expectedType, none, x, y]
  | _ => throwUnsupportedSyntax

#check @HAdd.hAdd

@[term_elab homadd] def elabAdd : TermElab := fun stx expectedType? => do
  -- logInfo m!"elabAdd {stx} {expectedType?}"
  match stx with
  | `($x + $y) => do
    match expectedType? with
    | none =>
        let x ← elabTerm x none
        let y ← elabTerm y none
        mkAppM ``HAdd.hAdd #[x, y] 
    | some expectedType => 
        let x ← elabTermEnsuringType x (some expectedType)
        let y ← elabTermEnsuringType y (some expectedType)
        mkAppOptM ``HAdd.hAdd 
          #[some expectedType, some expectedType, some expectedType, none, x, y]
  | _ => throwUnsupportedSyntax


@[term_elab homsub] def elabSub : TermElab := fun stx expectedType? => do
  -- logInfo m!"elabSub {stx} {expectedType?}"
  match stx with
  | `($x - $y) => do
    match expectedType? with
    | none =>
        let x ← elabTerm x none
        let y ← elabTerm y none
        mkAppM ``HSub.hSub #[x, y] 
    | some expectedType => 
        let x ← elabTermEnsuringType x (some expectedType)
        let y ← elabTermEnsuringType y (some expectedType)
        mkAppOptM ``HSub.hSub #[some expectedType, some expectedType, some expectedType, none, x, y]
  | _ => throwUnsupportedSyntax

@[term_elab hompow] def elabPow : TermElab := fun stx expectedType? => do
  -- logInfo m!"elabPow {stx} as {expectedType?}"
  match stx with
  | `($x ^ $y) => do
    -- logInfo m!"elabPow {x} to the power {y}"
    match expectedType? with
    | none =>
        let x ← elabTerm x none
        let y ← elabTerm y none
        mkAppM ``HPow.hPow #[x, y] 
    | some expectedType => 
        let x ← elabTermEnsuringType x (some expectedType)
        try 
          let y ← elabTerm y (mkConst ``Nat) 
          mkAppOptM ``HPow.hPow #[some expectedType, some (mkConst ``Nat), some expectedType, none, x, y]
        catch _ =>
          let y ← elabTerm y none
          mkAppOptM ``HPow.hPow #[some expectedType, none, some expectedType, none, x, y]
  | _ => throwUnsupportedSyntax

end Homogeneous

open Homogeneous

def eg1 (n : ℕ) : ℚ :=  (4*(n*(n-1)/2)^3-(n*(n-1)/2)^2)/3

set_option pp.all true in
#print eg1