/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Tests, error probabilities and the likelihood ratio

Foundational objects for binary hypothesis testing. Following Strasser,
*Mathematical Theory of Statistics* (Ch. 1), the likelihood ratio is based
**directly on the Radon–Nikodym / Lebesgue decomposition** rather than on a
common dominating measure (which Strasser calls arbitrary): for probability
measures `P, Q`, mathlib's `Measure.rnDeriv` is the density of the
absolutely-continuous part, and `Measure.singularPart` carries the singular
part, exactly Strasser's `(dQ/dP, N)`. Everything is `ℝ≥0∞`-valued using `∫⁻`,
matching the risk codomain of `Statlib.Inference`.

## Main definitions

* `Statlib.Testing.Test` — a randomized test (measurable `[0,1]`-valued function).
* `Statlib.Testing.typeIError` / `typeIIError` — the two error functionals.
* `Statlib.Testing.likelihoodRatio` — the Lebesgue-decomposition likelihood ratio
  `dP/dQ = P.rnDeriv Q` (no dominating measure).
* `Statlib.Testing.weightedRisk` — the Bayes/weighted error risk `a·α + b·β`.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace Statlib.Testing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A **(randomized) test** (critical function): a measurable function
`φ : Ω → ℝ≥0∞` valued in `[0,1]`. -/
structure Test (Ω : Type*) [MeasurableSpace Ω] where
  /-- The rejection-probability function. -/
  toFun : Ω → ℝ≥0∞
  /-- The rejection-probability function is measurable. -/
  measurable : Measurable toFun
  /-- The rejection probability is at most one. -/
  le_one : ∀ ω, toFun ω ≤ 1

/-- A test can be applied like a function: `φ ω` is `φ.toFun ω`. -/
instance : CoeFun (Test Ω) (fun _ => Ω → ℝ≥0∞) := ⟨Test.toFun⟩

/-- The **Type I error** (size) of a test `φ` under the null `P`: `∫⁻ φ dP`. -/
noncomputable def typeIError (φ : Ω → ℝ≥0∞) (P : Measure Ω) : ℝ≥0∞ := ∫⁻ ω, φ ω ∂P

/-- The **Type II error** of a test `φ` under the alternative `Q`: `∫⁻ (1 - φ) dQ`. -/
noncomputable def typeIIError (φ : Ω → ℝ≥0∞) (Q : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, (1 - φ ω) ∂Q

/-- The **likelihood ratio** `L = dP/dQ`, defined via the Lebesgue decomposition of
`P` with respect to `Q` as the Radon–Nikodym derivative `P.rnDeriv Q` (the density
of the absolutely-continuous part; the singular part of `P` w.r.t. `Q` is
`P.singularPart Q`). No common dominating measure is assumed. -/
noncomputable def likelihoodRatio (P Q : Measure Ω) : Ω → ℝ≥0∞ := P.rnDeriv Q

/-- The **weighted error risk** `R_{a,b}(φ) = a·α(φ) + b·β(φ)`. -/
noncomputable def weightedRisk (φ : Ω → ℝ≥0∞) (P Q : Measure Ω) (a b : ℝ≥0∞) : ℝ≥0∞ :=
  a * typeIError φ P + b * typeIIError φ Q

end Statlib.Testing
