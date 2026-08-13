module

public import Mathlib.Algebra.Order.Group.PosPart

/-! # Positive part -/

@[expose] public section

variable {α : Type*} [Lattice α] [DivInvMonoid α]

-- even though it is almost a duplicate of `one_le_oneLePart`, it allows `simp` to work on its goal.
@[to_additive (attr := simp) posPart_fun_nonneg]
lemma one_le_oneLePart_fun {β : Type*} (f : β → α) (x : β) : 1 ≤ f⁺ᵐ x := one_le_oneLePart f x

@[to_additive (attr := simp) negPart_fun_nonneg]
lemma one_le_leOnePart_fun {β : Type*} (f : β → α) (x : β) : 1 ≤ f⁻ᵐ x := one_le_leOnePart f x
