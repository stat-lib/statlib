/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Statlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.ForMathlib.Probability.Distributions.Bernoulli

/-!
# The Kullback-Leibler divergence between Bernoulli distributions

The Kullback-Leibler divergence between two Bernoulli distributions with parameters `p` and `q`
is `p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))` for `q ∈ (0, 1)`. We define it as the
real-valued function `klBerReal` given by that formula.

The definition, its basic API and its identification with `klDiv` between Bernoulli measures are
copied from LMLPapers (`LeanMachineLearning/ForMathlib/InformationTheory/KullbackLeibler/
Bernoulli.lean`), which also defines an `ℝ≥0∞`-valued version.

## Main definitions

* `InformationTheory.klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`: the
  binary Kullback-Leibler divergence, as a real number.

## Main statements

* `klBerReal_one_sub`: `klBerReal (1 - p) (1 - q) = klBerReal p q`.
* `klBerReal_nonneg`: Gibbs' inequality, `0 ≤ klBerReal p q` for `p ∈ [0, 1]` and `q ∈ (0, 1)`.
* `klDiv_bernoulliMeasure_eq_klBerReal`: for `x ≠ y` and `q ∉ {0, 1}`,
  `klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (klBerReal p q)`.
* `ofReal_klBerReal_le_klDiv_bernoulliMeasure`: for `x ≠ y` and any `p, q`,
  `ENNReal.ofReal (klBerReal p q) ≤ klDiv Ber(x, y, p) Ber(x, y, q)`.
* `klDiv_boolMeasure_ofReal_eq_klBerReal`: for `p ∈ [0, 1]` and `q ∈ (0, 1)`, the divergence
  between the priors `boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p))` and
  `boolMeasure (ENNReal.ofReal q) (ENNReal.ofReal (1 - q))` on `Bool` is
  `ENNReal.ofReal (klBerReal p q)`.
-/

@[expose] public section

open Real

namespace InformationTheory

variable {p q : ℝ}

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
`p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`. The formula is only meaningful for
`q ∈ (0, 1)`. -/
noncomputable def klBerReal (p q : ℝ) : ℝ := p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

/-- Unfolding lemma for `klBerReal`. -/
lemma klBerReal_apply (p q : ℝ) :
    klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := rfl

/-- The binary divergence from the parameter `0`. -/
@[simp] lemma klBerReal_zero_left : klBerReal 0 q = -log (1 - q) := by simp [klBerReal]

/-- The binary divergence from the parameter `1`. -/
@[simp] lemma klBerReal_one_left : klBerReal 1 q = -log q := by simp [klBerReal]

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBerReal_one_sub (p q : ℝ) : klBerReal (1 - p) (1 - q) = klBerReal p q := by
  simp only [klBerReal, sub_sub_cancel]
  ring

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBerReal_self (p : ℝ) : klBerReal p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  simp [klBerReal, div_self hp, sub_ne_zero.2 hp1.symm]

/-- The binary divergence written without divisions inside the logarithms. -/
lemma klBerReal_eq_of_ne (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) := by
  rw [klBerReal, mul_log_div hq, mul_log_div (sub_ne_zero.2 hq1.symm)]

/-- The binary divergence in terms of the binary entropy: for `q ∉ {0, 1}`,
`klBerReal p q = -binEntropy p - p log q - (1 - p) log (1 - q)`. -/
lemma klBerReal_eq_neg_binEntropy_sub (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = -binEntropy p - p * log q - (1 - p) * log (1 - q) := by
  rw [klBerReal_eq_of_ne hq hq1]
  simp only [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def]
  ring

/-- The binary Kullback-Leibler divergence to the parameter `1/2`. -/
lemma klBerReal_two_inv_right (p : ℝ) : klBerReal p 2⁻¹ = log 2 - binEntropy p := by
  rw [klBerReal_eq_neg_binEntropy_sub (by norm_num) (by norm_num)]
  have h : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  rw [h, Real.log_inv]
  ring

/-- **Gibbs' inequality** for Bernoulli distributions: the binary divergence is nonnegative. -/
lemma klBerReal_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ klBerReal p q := by
  have h₁ := sub_le_mul_log_div hp0 hq0
  have h₂ := sub_le_mul_log_div (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)
  rw [klBerReal]
  linarith

section BernoulliMeasure

open MeasureTheory ProbabilityTheory unitInterval

variable {𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧] {x y : 𝓧}

/-- The Kullback-Leibler divergence between the Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)`, for `x ≠ y` and `q ∉ {0, 1}`, is `klBerReal p q`. -/
lemma klDiv_bernoulliMeasure_eq_klBerReal (hxy : x ≠ y) (p : I) {q : I} (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (klBerReal p q) := by
  classical
  have hq0 : (0 : ℝ) < q := coe_pos.2 (unitInterval.pos_iff_ne_zero.2 hq)
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.2 (coe_lt_one.2 (unitInterval.lt_one_iff_ne_one.2 hq1))
  have hp0 : (0 : ℝ) ≤ p := p.property.1
  have hp1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.2 p.property.2
  rw [klDiv_eq_lintegral_klFun_of_ac (bernoulliMeasure_absolutelyContinuous hxy p hq hq1),
    lintegral_congr_ae ((rnDeriv_bernoulliMeasure hxy p hq hq1).mono fun z hz ↦ by rw [hz]),
    lintegral_bernoulliMeasure]
  simp only [ite_true, ite_eq_right hxy.symm, ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le),
    ENNReal.toReal_ofReal (div_nonneg hp1 hq1'.le)]
  rw [← ENNReal.ofReal_mul hq0.le, ← ENNReal.ofReal_mul hq1'.le, ← ENNReal.ofReal_add
      (mul_nonneg hq0.le (klFun_nonneg (div_nonneg hp0 hq0.le)))
      (mul_nonneg hq1'.le (klFun_nonneg (div_nonneg hp1 hq1'.le)))]
  congr 1
  simp only [klFun, klBerReal]
  field_simp
  ring

/-- The binary Kullback-Leibler divergence `klBerReal p q` is a lower bound for the
Kullback-Leibler divergence between the Bernoulli distributions with parameters `p` and `q`, with
equality for `q ∉ {0, 1}` (`klDiv_bernoulliMeasure_eq_klBerReal`). -/
lemma ofReal_klBerReal_le_klDiv_bernoulliMeasure (hxy : x ≠ y) (p q : I) :
    ENNReal.ofReal (klBerReal p q) ≤ klDiv Ber(x, y, p) Ber(x, y, q) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · -- `klBerReal p 0 = (1 - p) * log (1 - p) ≤ 0`
    refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
    simpa [klBerReal] using mul_log_nonpos (sub_nonneg.2 p.property.2) (sub_le_self _ p.property.1)
  rcases eq_or_ne q 1 with rfl | hq1
  · -- `klBerReal p 1 = p * log p ≤ 0`
    refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
    simpa [klBerReal] using mul_log_nonpos p.property.1 p.property.2
  rw [klDiv_bernoulliMeasure_eq_klBerReal hxy p hq0 hq1]

/-- The Kullback-Leibler divergence between two priors on `Bool` is the binary Kullback-Leibler
divergence between their parameters, for `p ∈ [0, 1]` and `q ∈ (0, 1)`. -/
lemma klDiv_boolMeasure_ofReal_eq_klBerReal {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q)
    (hq1 : q < 1) :
    klDiv (Measure.boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)))
      (Measure.boolMeasure (ENNReal.ofReal q) (ENNReal.ofReal (1 - q)))
      = ENNReal.ofReal (klBerReal p q) := by
  have hp := Measure.boolMeasure_ofReal_eq_bernoulliMeasure ⟨p, hp0, hp1⟩
  have hq := Measure.boolMeasure_ofReal_eq_bernoulliMeasure ⟨q, hq0.le, hq1.le⟩
  simp only at hp hq
  rw [hp, hq, klDiv_bernoulliMeasure_eq_klBerReal (by decide)]
  · simp only [ne_eq, Subtype.ext_iff, Set.Icc.coe_zero]
    exact hq0.ne'
  · simp only [ne_eq, Subtype.ext_iff, Set.Icc.coe_one]
    exact hq1.ne

end BernoulliMeasure

end InformationTheory
