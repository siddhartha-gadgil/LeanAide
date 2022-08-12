/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Logic.Encodable.Basic
import Mathbin.Logic.Small

/-!
# All encodable types are small.

That is, any encodable type is equivalent to a type in any universe.
-/


universe w v

instance (priority := 100) small_of_encodable (α : Type v) [Encodable α] : Small.{w} α :=
  small_of_injective Encodable.encode_injective

