/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Basic
public import Statlib.ForMathlib.Probability.Distributions.Bernoulli

/-!
# Rényi divergence between Bernoulli distributions

For `x ≠ y`, `q ∈ (0, 1)` and `a ∈ (0, 1)`, the Rényi divergence of order `a` between the
Bernoulli distributions `Ber(x, y, p)` and `Ber(x, y, q)` is
`(a - 1)⁻¹ * log (p ^ a * q ^ (1 - a) + (1 - p) ^ a * (1 - q) ^ (1 - a))`.

## Main statements

* `renyiDiv_bernoulliMeasure`: the Rényi divergence of order `a ∈ (0, 1)` between Bernoulli
  distributions.
* `renyiDiv_zero_bernoulliMeasure`: for `p, q ∈ (0, 1)`, the Rényi divergence of order `0` between
  `Ber(x, y, p)` and `Ber(x, y, q)` is `0`.
-/

@[expose] public section

open Real MeasureTheory unitInterval

open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧] {x y : 𝓧} {p q : I}
  {a : ℝ}

/-- The Rényi divergence of order `a ∈ (0, 1)` between the Bernoulli distributions `Ber(x, y, p)`
and `Ber(x, y, q)`, for `x ≠ y` and `q ∉ {0, 1}`. -/
theorem renyiDiv_bernoulliMeasure (ha0 : 0 < a) (ha1 : a < 1) (hxy : x ≠ y) (p : I) (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    renyiDiv a Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal ((a - 1)⁻¹
      * log ((p : ℝ) ^ a * (q : ℝ) ^ (1 - a) + (1 - (p : ℝ)) ^ a * (1 - (q : ℝ)) ^ (1 - a))) := by
  classical
  have hq0 : (0 : ℝ) < q := coe_pos.2 (unitInterval.pos_iff_ne_zero.2 hq)
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.2 (coe_lt_one.2 (unitInterval.lt_one_iff_ne_one.2 hq1))
  have hp0 : (0 : ℝ) ≤ p := p.property.1
  have hp1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.2 p.property.2
  have h_ms : ¬ Ber(x, y, p) ⟂ₘ Ber(x, y, q) := fun h ↦ IsProbabilityMeasure.ne_zero Ber(x, y, p)
    (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
      (bernoulliMeasure_absolutelyContinuous hxy p hq hq1) h)
  rw [renyiDiv_eq_log_integral_of_lt_one ha0 ha1 h_ms,
    integral_congr_ae ((rnDeriv_bernoulliMeasure hxy p hq hq1).mono fun z hz ↦ by rw [hz]),
    integral_bernoulliMeasure]
  simp only [ite_true, ite_eq_right hxy.symm, ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le),
    ENNReal.toReal_ofReal (div_nonneg hp1 hq1'.le), measure_univ, ENNReal.toReal_one, log_one,
    mul_zero, add_zero, sub_zero, smul_eq_mul]
  have h1 : (q : ℝ) * ((p : ℝ) / q) ^ a = (p : ℝ) ^ a * (q : ℝ) ^ (1 - a) := by
    rw [div_rpow hp0 hq0.le, rpow_sub hq0, rpow_one]
    ring
  have h2 : (1 - (q : ℝ)) * ((1 - (p : ℝ)) / (1 - q)) ^ a
      = (1 - (p : ℝ)) ^ a * (1 - (q : ℝ)) ^ (1 - a) := by
    rw [div_rpow hp1 hq1'.le, rpow_sub hq1', rpow_one]
    ring
  rw [h1, h2]

/-- For `x ≠ y` and `p, q ∉ {0, 1}`, the Rényi divergence of order `0` between the Bernoulli
distributions `Ber(x, y, p)` and `Ber(x, y, q)` is `0`: the Radon-Nikodym derivative is positive
everywhere. -/
lemma renyiDiv_zero_bernoulliMeasure (hxy : x ≠ y) (hp : p ≠ 0) (hp1 : p ≠ 1) (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    renyiDiv 0 Ber(x, y, p) Ber(x, y, q) = 0 := by
  classical
  have hp0 : (0 : ℝ) < p := coe_pos.2 (unitInterval.pos_iff_ne_zero.2 hp)
  have hp1' : (0 : ℝ) < 1 - p := sub_pos.2 (coe_lt_one.2 (unitInterval.lt_one_iff_ne_one.2 hp1))
  have hq0 : (0 : ℝ) < q := coe_pos.2 (unitInterval.pos_iff_ne_zero.2 hq)
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.2 (coe_lt_one.2 (unitInterval.lt_one_iff_ne_one.2 hq1))
  have h_pos : ∀ᵐ z ∂Ber(x, y, q), 0 < Ber(x, y, p).rnDeriv Ber(x, y, q) z := by
    filter_upwards [rnDeriv_bernoulliMeasure hxy p hq hq1] with z hz
    rw [hz]
    split_ifs
    · exact ENNReal.ofReal_pos.mpr (div_pos hp0 hq0)
    · exact ENNReal.ofReal_pos.mpr (div_pos hp1' hq1')
  rw [renyiDiv_zero, (mem_ae_iff_prob_eq_one
    (measurableSet_lt measurable_const (Measure.measurable_rnDeriv _ _))).mp h_pos, measure_univ,
    div_one, ENNReal.log_one, neg_zero, EReal.toENNReal_zero]

end ProbabilityTheory
