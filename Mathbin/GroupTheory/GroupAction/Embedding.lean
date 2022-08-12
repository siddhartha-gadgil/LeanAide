/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Group actions on embeddings

This file provides a `mul_action G (α ↪ β)` instance that agrees with the `mul_action G (α → β)`
instances defined by `pi.mul_action`.

Note that unlike the `pi` instance, this requires `G` to be a group.
-/


universe u v w

variable {G G' α β : Type _}

namespace Function.Embedding

@[to_additive Function.Embedding.hasVadd]
instance [Groupₓ G] [MulAction G β] : HasSmul G (α ↪ β) :=
  ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

@[to_additive]
theorem smul_def [Groupₓ G] [MulAction G β] (g : G) (f : α ↪ β) : g • f = f.trans (MulAction.toPerm g).toEmbedding :=
  rfl

@[simp, to_additive]
theorem smul_apply [Groupₓ G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
  rfl

@[to_additive]
theorem coe_smul [Groupₓ G] [MulAction G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • f :=
  rfl

instance [Groupₓ G] [Groupₓ G'] [HasSmul G G'] [MulAction G β] [MulAction G' β] [IsScalarTower G G' β] :
    IsScalarTower G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_assoc x y (z i)⟩

@[to_additive]
instance [Groupₓ G] [Groupₓ G'] [MulAction G β] [MulAction G' β] [SmulCommClass G G' β] : SmulCommClass G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_comm x y (z i)⟩

instance [Groupₓ G] [MulAction G β] [MulAction Gᵐᵒᵖ β] [IsCentralScalar G β] : IsCentralScalar G (α ↪ β) :=
  ⟨fun r m => Function.Embedding.ext fun i => op_smul_eq_smul _ _⟩

@[to_additive]
instance [Groupₓ G] [MulAction G β] : MulAction G (α ↪ β) :=
  FunLike.coe_injective.MulAction _ coe_smul

end Function.Embedding

