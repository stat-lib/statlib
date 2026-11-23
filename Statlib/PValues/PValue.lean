/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# P-values for composite null hypotheses

A p-value is a measurable function taking values in [0, 1] that
uniformly has prescribed tail probability
under every probability measure in the null hypothesis.
-/

@[expose] public section

open scoped ENNReal

open MeasureTheory

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

namespace ProbabilityTheory

/-- A valid p-value for the composite null hypothesis `S`. -/
structure IsPValue (Pval : 𝓧 → ℝ≥0∞)
    (S : Set (ProbabilityMeasure 𝓧)) : Prop where
  measurable : Measurable Pval := by fun_prop
  le_one : ∀ ω, Pval ω ≤ 1
  s_uniform : ∀ μ ∈ S, ∀ α : ℝ≥0∞,
    (μ : Measure 𝓧) {ω | Pval ω ≤ α} ≤ α

end ProbabilityTheory
