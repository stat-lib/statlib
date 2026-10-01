/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/

module

public import Mathlib.Algebra.BigOperators.Expect
public import Statlib.Causal.PotentialResponse

/-!
# Potential-Response Contrasts

This module defines unit-level contrasts between two interventions and their averages over a finite
population. It introduces estimands but no assignment mechanism, causal assumption, identification
result, estimator, or statistical inference.
-/

@[expose] public section

open scoped BigOperators

namespace PotentialResponse

variable {Intervention Unit Value : Type*}

/-- The unit-level contrast between two interventions, first minus second.

The definition needs only `Sub Value`; laws involving zero and negation use `AddGroup Value`.
-/
def contrast [Sub Value]
    (response : PotentialResponse Intervention Unit Value)
    (intervention₁ intervention₀ : Intervention) :
    Unit → Value :=
  fun unit ↦ response intervention₁ unit - response intervention₀ unit

@[simp] theorem contrast_apply [Sub Value]
    (response : PotentialResponse Intervention Unit Value)
    (intervention₁ intervention₀ : Intervention)
    (unit : Unit) :
    response.contrast intervention₁ intervention₀ unit =
      response intervention₁ unit - response intervention₀ unit := rfl

/-- A unit's contrast with itself is zero. -/
theorem contrast_self [AddGroup Value]
    (response : PotentialResponse Intervention Unit Value)
    (intervention : Intervention) (unit : Unit) :
    response.contrast intervention intervention unit = 0 := by
  simp

/-- Swapping the interventions negates the unit-level contrast. -/
theorem contrast_swap [AddGroup Value]
    (response : PotentialResponse Intervention Unit Value)
    (intervention₁ intervention₀ : Intervention) (unit : Unit) :
    response.contrast intervention₁ intervention₀ unit =
      -response.contrast intervention₀ intervention₁ unit := by
  simp only [contrast_apply, neg_sub]

/-- The average unit-level contrast over a finite population.

The elements of `Unit` are the entire finite target population. The notation `𝔼` denotes the
uniform `Finset.expect` over `Finset.univ`, giving every unit equal weight. It introduces no
probability distribution, random sampling, or superpopulation expectation.

For empty `Unit`, this is zero by an algebraic convention of `Finset.expect`, not a substantive
claim about the causal effect in an empty population.

When the interventions encode two unit-level treatments, this is the conventional
finite-population average treatment effect. If they encode complete allocation vectors, it is
instead an average contrast between two allocation regimes; this definition does not assume
noninterference.
-/
def finitePopulationAverageContrast
    [Fintype Unit]
    [AddCommGroup Value] [Module ℚ≥0 Value]
    (response : PotentialResponse Intervention Unit Value)
    (intervention₁ intervention₀ : Intervention) :
    Value :=
  𝔼 unit, response.contrast intervention₁ intervention₀ unit

theorem finitePopulationAverageContrast_eq_sub
    [Fintype Unit]
    [AddCommGroup Value] [Module ℚ≥0 Value]
    (response : PotentialResponse Intervention Unit Value)
    (intervention₁ intervention₀ : Intervention) :
    response.finitePopulationAverageContrast intervention₁ intervention₀ =
      (𝔼 unit, response intervention₁ unit) -
        (𝔼 unit, response intervention₀ unit) := by
  simp [finitePopulationAverageContrast, Finset.expect_sub_distrib]

end PotentialResponse
