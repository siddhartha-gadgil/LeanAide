/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

/-!
# Changing universes of types in meta-code

This file defines the meta type `uchange (α : Type v) : Type u`, which
permits us to change the universe of a type analogously to `ulift`.
However since `uchange` is meta, it can both lift and lower the universe.

The implementation of `uchange` is efficient. Both `uchange.up` and
`uchange.down` compile to no-ops.
-/


universe u v

/-- `unchecked_cast' a : β` performs an unchecked cast of `(a : α)` to `β`.

Unlike `unchecked_cast`, it can cast across universes. The VM implementation
is guaranteed to be the identity.
-/
@[inline]
unsafe irreducible_def unchecked_cast' {α : Sort u} {β : Sort v} (a : α) : β :=
  Plift.down <|
    @cast (α → β → Plift β) (β → α → Plift β) undefined (fun _ a => Plift.up a) (cast undefined PUnit.unit) a

/-- `uchange (α : Sort v) : Sort u` is an equivalent type in a different universe.

In the VM, both `α` and `uchange α` have the same representation.

This definition is `meta` because it collapses the universe hierarchy; if pure code could do
this then one could derive Girard's paradox.
-/
unsafe def uchange (α : Type v) : Type u :=
  unchecked_cast' α

namespace Uchange

variable {α : Type v} (a : α)

unsafe instance [DecidableEq α] : DecidableEq (uchange α) :=
  unchecked_cast'
    (by
      infer_instance : DecidableEq α)

/-- `uchange.down` embeds `α` to `uchange α`.

The VM implementation is guaranteed to be the identity.
-/
@[inline]
unsafe def down {α} (a : α) : uchange α :=
  unchecked_cast' a

/-- `uchange.up` extracts from `uchange α` an `α`.

The VM implementation is guaranteed to be the identity.
-/
@[inline]
unsafe def up {α} (a : uchange α) : α :=
  unchecked_cast' a

end Uchange

-- Sanity check
#eval do
  guardₓ <| (uchange.down.{0} 42).up = 42
  tactic.skip

