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

/-- The unit-level contrast between two interventions, first minus second. -/
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

/-- The average unit-level contrast over a finite population.

This is zero when the population is empty, following the convention for `Finset.expect`.
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
