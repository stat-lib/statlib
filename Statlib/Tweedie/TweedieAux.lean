/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib

/-!
# Mathlib-only auxiliary lemmas for the Tweedie / compound-Poisson equivalence

This file collects purely analytic facts (no dependence on the Tweedie development) used in the
proof that the Tweedie measure equals the compound-Poisson construction:

* `tw_scalar_identity`: the `rpow` bookkeeping identity relating the Poisson/gamma constants to the
  Tweedie series coefficients.
* `ae_summable_of_summable_integral_norm`: if the integral norms of a family of functions are
  summable, then the family is pointwise summable almost everywhere.
-/

open MeasureTheory Real
open scoped ENNReal NNReal

namespace TweedieAux

/-
The scalar `rpow` identity matching the Poisson-weighted gamma-rate term with the Tweedie series
coefficient. Here `α = (2-p)/(p-1)` (gamma shape), `γ = μ^(1-p)/(φ(p-1))` (gamma rate),
`λ = μ^(2-p)/(φ(2-p))` (Poisson rate), and `α' = (2-p)/(1-p) = -α`.
-/
lemma tw_scalar_identity (μ φ p : ℝ) (hμ : 0 < μ) (hφ : 0 < φ) (hp₁ : 1 < p) (hp₂ : p < 2)
    (j : ℕ) :
    (μ ^ (2 - p) / (φ * (2 - p))) ^ j
        * (μ ^ (1 - p) / (φ * (p - 1))) ^ ((j : ℝ) * ((2 - p) / (p - 1)))
      = (p - 1) ^ (((2 - p) / (1 - p)) * (j : ℝ))
          / (φ ^ ((j : ℝ) * (1 - (2 - p) / (1 - p))) * (2 - p) ^ j) := by
  -- Rewrite the left-hand side with positive bases
  have lhs_rewrite :
      (μ ^ (2 - p) / (φ * (2 - p))) ^ j * (μ ^ (1 - p) / (φ * (p - 1))) ^ (j * ((2 - p) / (p - 1)))
      = (μ ^ ((2 - p) * j) * φ ^ (-(j : ℝ)) * (2 - p) ^ (-(j : ℝ))) * (μ ^ ((1 - p) * (j * ((2 - p)
      / (p - 1)))) * φ ^ (-(j * ((2 - p) / (p - 1))) : ℝ)
      * (p - 1) ^ (-(j * ((2 - p) / (p - 1))) : ℝ)) := by
    congr 1;
    · rw [Real.rpow_mul (by positivity), Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
      ring_nf
      norm_cast; norm_num
      ring_nf
      rw [show - ( p * φ) + φ * 2 = φ * ( 2 - p) by ring, mul_inv]; ring;
    · rw [Real.div_rpow (by positivity) (mul_nonneg hφ.le (by linarith))];
      rw [← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) (by linarith),
        Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]; ring;
  convert lhs_rewrite using 1; norm_num [Real.rpow_def_of_pos, *]
  ring_nf
  rw [← Real.exp_neg, ← Real.exp_add]
  ring_nf
  rw [← Real.exp_log (by linarith : 0 < 2 - p)]; norm_num [← Real.exp_add, ← Real.exp_nat_mul]
  ring_nf
  rw [← Real.exp_neg, ← Real.exp_add]
  ring_nf
  grind

/-
If the family `F i` is integrable on `s` and the integral norms `∫_s ‖F i‖` are summable, then
for almost every `y ∈ s` the family `i ↦ F i y` is summable.
-/
lemma ae_summable_of_summable_integral_norm {ι : Type*} [Countable ι] {F : ι → ℝ → ℝ} {s : Set ℝ}
    (hF : ∀ i, IntegrableOn (F i) s)
    (hsum : Summable (fun i => ∫ y in s, ‖F i y‖)) :
    ∀ᵐ y ∂(volume.restrict s), Summable (fun i => F i y) := by
  -- The total integral of `∑ ‖F i‖` is finite, hence the sum is finite a.e.
  have h_fin : ∫⁻ y in s, ∑' i, ENNReal.ofReal (‖F i y‖) ∂volume < ⊤ := by
    rw [MeasureTheory.lintegral_tsum]
    · refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
        (Summable.tsum_ofReal_lt_top hsum)
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (MeasureTheory.Integrable.norm (hF i))
        (Filter.Eventually.of_forall fun x => norm_nonneg _)]
    · exact fun i => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        ((hF i).aemeasurable.norm)
  have h_ae : ∀ᵐ y ∂volume.restrict s, ∑' i, ENNReal.ofReal (‖F i y‖) < ⊤ := by
    refine MeasureTheory.ae_lt_top' ?_ (ne_of_lt h_fin)
    exact AEMeasurable.tsum (fun i => (hF i).aemeasurable.norm.ennreal_ofReal)
  filter_upwards [h_ae] with y hy
  refine Summable.of_norm ?_
  convert ENNReal.summable_toReal (ne_of_lt hy) with i
  rw [ENNReal.toReal_ofReal (norm_nonneg _)]

end TweedieAux
