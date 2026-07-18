/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib
import Statlib.Tweedie.GammaConvolution

/-!
# Compound Poisson construction (core, Mathlib-only)

This file isolates the construction of the compound-Poisson law and basic facts about it. It
deliberately depends only on `Mathlib` (and `GammaConvolution`), so that it does not import the
Tweedie development.
-/
open scoped BigOperators
open scoped Real
open scoped Pointwise
open scoped NNReal ENNReal
set_option maxRecDepth 4000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false


namespace CompoundPoisson
open MeasureTheory ProbabilityTheory
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℝ≥0)
/-- The base probability space: the first coordinate is the Poisson count `N`, the second is the
i.i.d. sequence of jumps with common law `μ`. -/
noncomputable def baseMeasure : Measure (ℕ × (ℕ → ℝ)) :=
  (poissonMeasure lam).prod (Measure.infinitePi (fun _ : ℕ => μ))
instance : IsProbabilityMeasure (baseMeasure μ lam) := by
  unfold baseMeasure; infer_instance
/-- The compound Poisson random variable: the sum of the first `N` jumps. -/
def jumpSum (p : ℕ × (ℕ → ℝ)) : ℝ := ∑ i ∈ Finset.range p.1, p.2 i
lemma measurable_jumpSum : Measurable (jumpSum : ℕ × (ℕ → ℝ) → ℝ) := by
  unfold jumpSum
  apply measurable_from_prod_countable_right
  intro n; simp only
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

/-- The compound Poisson law: the push-forward of the base measure under `jumpSum`. -/
noncomputable def compoundPoisson : Measure ℝ :=
  (baseMeasure μ lam).map jumpSum

instance : IsProbabilityMeasure (compoundPoisson μ lam) := by
  unfold compoundPoisson
  exact Measure.isProbabilityMeasure_map measurable_jumpSum.aemeasurable
end CompoundPoisson

open CompoundPoisson GammaConv
open MeasureTheory ProbabilityTheory

/-
Lintegral against a compound-Poisson law: a Poisson-weighted sum of the convolution powers of
the jump law.
-/
lemma compoundPoisson_lintegral (G : Measure ℝ) [IsProbabilityMeasure G] (lam : ℝ≥0)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(CompoundPoisson.compoundPoisson G lam)
      = ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / n.factorial)
          * ∫⁻ z, f z ∂(GammaConv.convPow G n) := by
  rw [compoundPoisson, MeasureTheory.lintegral_map hf CompoundPoisson.measurable_jumpSum,
    baseMeasure,
    MeasureTheory.lintegral_prod (fun a => f (jumpSum a)) (hf.comp measurable_jumpSum).aemeasurable,
    MeasureTheory.lintegral_countable']
  refine tsum_congr fun n => ?_
  rw [poissonMeasure_singleton, mul_comm]
  congr 1
  rw [← infinitePi_range_sum_eq_convPow,
    MeasureTheory.lintegral_map hf (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)]
  rfl
