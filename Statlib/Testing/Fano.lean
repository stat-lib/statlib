/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.JensenShannon.Variational
public import Statlib.Divergence.KullbackLeibler.Estimation
public import Statlib.Divergence.Renyi.Variational

/-!
# Binary Fano inequality and Rényi lower bound on the Bayes binary risk

Let `μ, ν` be probability measures and let `B_α(μ, ν)` be the Bayes binary risk of the simple
binary hypothesis testing problem between `μ` and `ν` with prior `π_α = (α, 1 - α)` on `Bool`
(`bayesBinaryRisk μ ν (boolMeasure α (1 - α))`). We prove two lower bounds on that risk.

* The **binary Fano inequality**: `h₂(α) - h₂(B_α(μ, ν)) ≤ JS_α(μ, ν)`, where `h₂` is the binary
  entropy and `JS_α` is the Jensen-Shannon divergence.
* A lower bound in terms of the Rényi divergence: for `β ∈ [0, 1/2]`,
  `β log (α / B_α(μ, ν)) + (1 - β) log ((1 - α) / (1 - B_α(μ, ν))) ≤ (1 - β) R_β(μ, ν)`, and as a
  consequence `log (α / B_α(μ, ν)) ≤ R_{1/2}(μ, ν) + log 2` for `α ≤ 1/2`.

Both bounds compare the testing problem between `μ` and `ν` with the trivial problem in which both
hypotheses have the same law `ζ` (lemmas
`ofReal_klBerReal_bayesBinaryRisk_min_le_klDiv_compProd_prod_add` and
`ofReal_klBerReal_min_bayesBinaryRisk_le_klDiv_prod_compProd_add`), then take an infimum over `ζ`
using the variational formulas for the Jensen-Shannon divergence
(`jensenShannon_eq_iInf_klDiv_compProd`) and for the Rényi divergence
(`mul_renyiDiv_eq_iInf_klDiv_prod`).

## Main statements

* `ofReal_binEntropy_sub_binEntropy_bayesBinaryRisk_le_jensenShannon`: binary Fano inequality.
* `ofReal_klBerReal_sub_klBerReal_le_mul_renyiDiv`:
  `kl(β, B_α(μ, ν)) - kl(β, α) ≤ (1 - β) R_β(μ, ν)` for `β ∈ [0, 1/2]`.
* `ofReal_mul_log_add_mul_log_le_mul_renyiDiv`: the same bound written with logarithms.
* `ofReal_mul_log_div_bayesBinaryRisk_le_mul_renyiDiv_add`:
  `β log (α / B_α(μ, ν)) ≤ (1 - β) (R_β(μ, ν) + log 2)`.
* `ofReal_log_div_bayesBinaryRisk_le_renyiDiv_add`: `log (α / B_α(μ, ν)) ≤ R_{1/2}(μ, ν) + log 2`.

## Implementation notes

The quantities on the left-hand sides are real numbers which may be negative, while the divergences
take values in `ℝ≥0∞`: we state the bounds with `ENNReal.ofReal` of the left-hand side. The Bayes
risk enters through `ENNReal.toReal`. Logarithms use Mathlib's convention `log 0 = 0`; the bounds
remain true (and trivial) when the Bayes risk vanishes.

The prior `(α, 1 - α)` is `boolMeasure α (1 - α)` with `α : ℝ≥0`, as in the Jensen-Shannon
divergence, while the variational formula for the Rényi divergence uses the prior
`boolMeasure (ENNReal.ofReal β) (ENNReal.ofReal (1 - β))` with `β : ℝ`. These priors are related
to each other by `Measure.boolMeasure_coe_eq_ofReal` and to the Bernoulli distribution
`Ber(false, true, p)` by `Measure.boolMeasure_ofReal_eq_bernoulliMeasure`.
-/

@[expose] public section

open MeasureTheory Real InformationTheory ProbabilityTheory unitInterval

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {α : ℝ≥0}

section Fano

/-- **Binary Fano inequality**: for probability measures `μ, ν` and `α ∈ [0, 1]`,
`h₂(α) - h₂(B_α(μ, ν)) ≤ JS_α(μ, ν)`, where `h₂` is the binary entropy, `B_α(μ, ν)` is the Bayes
binary risk for the prior `(α, 1 - α)` and `JS_α` is the Jensen-Shannon divergence. -/
theorem ofReal_binEntropy_sub_binEntropy_bayesBinaryRisk_le_jensenShannon (hα : α ≤ 1) :
    ENNReal.ofReal (binEntropy α - binEntropy
        (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal)
      ≤ jensenShannon α μ ν := by
  set ρ := Measure.boolMeasure (α : ℝ≥0∞) ((1 - α : ℝ≥0) : ℝ≥0∞) with hρ
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_boolMeasure_coe hα
  -- compare with the trivial problem `(ζ, ζ)` under the uniform prior `ξ`
  set ξ := Measure.boolMeasure (ENNReal.ofReal 2⁻¹) (ENNReal.ofReal (1 - 2⁻¹)) with hξ
  have : IsProbabilityMeasure ξ := Measure.isProbabilityMeasure_boolMeasure_ofReal
    (by norm_num) (by norm_num)
  rw [jensenShannon_eq_iInf_klDiv_compProd hα]
  refine le_iInf₂ fun ζ _ ↦ ?_
  have h := ofReal_klBerReal_bayesBinaryRisk_min_le_klDiv_compProd_prod_add μ ν ρ ξ ζ
  have h_min : (min (ξ {false}) (ξ {true})).toReal = 2⁻¹ := by
    rw [hξ, Measure.boolMeasure_apply_false, Measure.boolMeasure_apply_true]
    norm_num
  have h_kl : klDiv ρ ξ = ENNReal.ofReal (klBerReal α 2⁻¹) := by
    rw [hρ, Measure.boolMeasure_coe_eq_ofReal, hξ]
    exact klDiv_boolMeasure_ofReal_eq_klBerReal α.property (by exact_mod_cast hα) (by norm_num)
      (by norm_num)
  rw [h_min, h_kl, klBerReal_two_inv_right, klBerReal_two_inv_right] at h
  have h_nonneg : 0 ≤ log 2 - binEntropy α := sub_nonneg.2 binEntropy_le_log_two
  calc ENNReal.ofReal (binEntropy α - binEntropy (bayesBinaryRisk μ ν ρ).toReal)
  _ = ENNReal.ofReal ((log 2 - binEntropy (bayesBinaryRisk μ ν ρ).toReal)
      - (log 2 - binEntropy α)) := by ring_nf
  _ = ENNReal.ofReal (log 2 - binEntropy (bayesBinaryRisk μ ν ρ).toReal)
      - ENNReal.ofReal (log 2 - binEntropy α) := ENNReal.ofReal_sub _ h_nonneg
  _ ≤ klDiv (ρ ⊗ₘ Kernel.boolKernel μ ν) (ρ.prod ζ) := tsub_le_iff_right.2 h

end Fano

section Renyi

variable {β : ℝ}

/-- **Lower bound on the Bayes binary risk from the Rényi divergence**, in terms of the binary
Kullback-Leibler divergence: for `β ∈ [0, 1/2]` and `α ∈ [0, 1)`,
`kl(β, B_α(μ, ν)) - kl(β, α) ≤ (1 - β) R_β(μ, ν)`. -/
theorem ofReal_klBerReal_sub_klBerReal_le_mul_renyiDiv (hβ0 : 0 ≤ β) (hβ : β ≤ 2⁻¹)
    (hα1 : α < 1) :
    ENNReal.ofReal (klBerReal β
        (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal
      - klBerReal β α)
      ≤ ENNReal.ofReal (1 - β) * renyiDiv β μ ν := by
  rcases eq_or_ne α 0 with rfl | hα0
  · -- the prior is a Dirac mass: the Bayes risk vanishes
    rw [bayesBinaryRisk_of_measure_false_eq_zero _ _ (by simp)]
    simp
  replace hα0 : 0 < α := pos_iff_ne_zero.2 hα0
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  rcases hβ0.eq_or_lt with rfl | hβ0
  · -- for `β = 0`, the left-hand side is `log (1 - α) - log (1 - B_α(μ, ν)) ≤ 0`
    have hB_le := toReal_bayesBinaryRisk_boolMeasure_le μ ν α ((1 - α : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    rw [klBerReal_zero_left, klBerReal_zero_left, neg_sub_neg, sub_nonpos]
    exact Real.log_le_log (by linarith) (by linarith)
  set ξ := Measure.boolMeasure (α : ℝ≥0∞) ((1 - α : ℝ≥0) : ℝ≥0∞) with hξ
  have : IsProbabilityMeasure ξ := Measure.isProbabilityMeasure_boolMeasure_coe hα1.le
  -- compare with the trivial problem `(ζ, ζ)` under the prior `ρ = (β, 1 - β)`
  set ρ := Measure.boolMeasure (ENNReal.ofReal β) (ENNReal.ofReal (1 - β)) with hρ
  have hβ1 : β < 1 := by linarith
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_boolMeasure_ofReal hβ0.le hβ1.le
  rw [mul_renyiDiv_eq_iInf_klDiv_prod hβ0 hβ1]
  refine le_iInf₂ fun ζ _ ↦ ?_
  have h := ofReal_klBerReal_min_bayesBinaryRisk_le_klDiv_prod_compProd_add μ ν ρ ξ ζ
  have h_min : (min (ρ {false}) (ρ {true})).toReal = β := by
    rw [hρ, Measure.boolMeasure_apply_false, Measure.boolMeasure_apply_true,
      min_eq_left (ENNReal.ofReal_le_ofReal (by linarith)), ENNReal.toReal_ofReal hβ0.le]
  have h_kl : klDiv ρ ξ = ENNReal.ofReal (klBerReal β α) := by
    rw [hξ, Measure.boolMeasure_coe_eq_ofReal, hρ]
    exact klDiv_boolMeasure_ofReal_eq_klBerReal hβ0.le hβ1.le (by exact_mod_cast hα0) hα1'
  rw [h_min, h_kl] at h
  have h_nonneg : 0 ≤ klBerReal β α :=
    klBerReal_nonneg hβ0.le hβ1.le (by exact_mod_cast hα0) hα1'
  rw [ENNReal.ofReal_sub _ h_nonneg]
  exact tsub_le_iff_right.2 h

/-- **Lower bound on the Bayes binary risk from the Rényi divergence**: for `β ∈ [0, 1/2]` and
`α ∈ [0, 1]`, writing `B = B_α(μ, ν)`,
`β log (α / B) + (1 - β) log ((1 - α) / (1 - B)) ≤ (1 - β) R_β(μ, ν)`. -/
theorem ofReal_mul_log_add_mul_log_le_mul_renyiDiv (hβ0 : 0 ≤ β) (hβ : β ≤ 2⁻¹)
    (hα1 : α ≤ 1) :
    ENNReal.ofReal
        (β * log (α / (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal)
        + (1 - β) * log ((1 - α) /
          (1 - (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal)))
      ≤ ENNReal.ofReal (1 - β) * renyiDiv β μ ν := by
  rcases hα1.eq_or_lt with rfl | hα1
  · -- the prior is a Dirac mass: the Bayes risk and the left-hand side vanish
    rw [bayesBinaryRisk_of_measure_true_eq_zero _ _ (by simp)]
    simp
  set B := (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal with hB
  have hB_le : B ≤ α := toReal_bayesBinaryRisk_boolMeasure_le μ ν α _
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have hβ1 : β < 1 := by linarith
  rcases (show 0 ≤ B from ENNReal.toReal_nonneg).eq_or_lt with hB0 | hB0
  · -- the Bayes risk vanishes: the left-hand side is nonpositive
    rw [← hB0, div_zero, Real.log_zero, mul_zero, zero_add, sub_zero, div_one,
      ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (Real.log_nonpos (by linarith [α.property]) (by linarith [α.property]))
  have hα0' : (0 : ℝ) < α := hB0.trans_le hB_le
  have hB1 : B < 1 := hB_le.trans_lt hα1'
  have h := ofReal_klBerReal_sub_klBerReal_le_mul_renyiDiv μ ν hβ0 hβ hα1
  rw [← hB] at h
  convert h using 2
  rw [klBerReal_eq_of_ne hB0.ne' hB1.ne, klBerReal_eq_of_ne hα0'.ne' hα1'.ne,
    Real.log_div hα0'.ne' hB0.ne', Real.log_div (by linarith) (by linarith)]
  ring

/-- **Lower bound on the Bayes binary risk from the Rényi divergence**: for `β ∈ [0, 1/2]` and
`α ∈ [0, 1/2]`, `β log (α / B_α(μ, ν)) ≤ (1 - β) (R_β(μ, ν) + log 2)`. -/
theorem ofReal_mul_log_div_bayesBinaryRisk_le_mul_renyiDiv_add (hβ0 : 0 ≤ β) (hβ : β ≤ 2⁻¹)
    (hα : α ≤ 2⁻¹) :
    ENNReal.ofReal
        (β * log (α / (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal))
      ≤ ENNReal.ofReal (1 - β) * (renyiDiv β μ ν + ENNReal.ofReal (log 2)) := by
  have hα1 : α < 1 := hα.trans_lt (by norm_num)
  set B := (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal with hB
  have hB_le : B ≤ α := toReal_bayesBinaryRisk_boolMeasure_le μ ν α _
  have hα' : (α : ℝ) ≤ 2⁻¹ := by exact_mod_cast hα
  have hB1 : B < 1 := hB_le.trans_lt (by linarith)
  have hβ1 : β < 1 := by linarith
  have h := ofReal_mul_log_add_mul_log_le_mul_renyiDiv μ ν hβ0 hβ hα1.le
  rw [← hB] at h
  -- `log ((1 - α) / (1 - B)) ≥ - log 2` since `(1 - α) / (1 - B) ≥ 1 - α ≥ 1/2`
  have h_log : -log 2 ≤ log ((1 - α) / (1 - B)) := by
    rw [← Real.log_inv]
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ (by linarith)]
    have : 0 ≤ B := ENNReal.toReal_nonneg
    nlinarith
  calc ENNReal.ofReal (β * log (α / B))
  _ ≤ ENNReal.ofReal ((β * log (α / B) + (1 - β) * log ((1 - α) / (1 - B)))
      + (1 - β) * log 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  _ ≤ ENNReal.ofReal (β * log (α / B) + (1 - β) * log ((1 - α) / (1 - B)))
      + ENNReal.ofReal ((1 - β) * log 2) := ENNReal.ofReal_add_le
  _ ≤ ENNReal.ofReal (1 - β) * renyiDiv β μ ν
      + ENNReal.ofReal (1 - β) * ENNReal.ofReal (log 2) := by
    gcongr
    rw [ENNReal.ofReal_mul (by linarith)]
  _ = ENNReal.ofReal (1 - β) * (renyiDiv β μ ν + ENNReal.ofReal (log 2)) := by ring

/-- **Lower bound on the Bayes binary risk from the Rényi divergence of order `1/2`**: for
`α ∈ [0, 1/2]`, `log (α / B_α(μ, ν)) ≤ R_{1/2}(μ, ν) + log 2`. -/
theorem ofReal_log_div_bayesBinaryRisk_le_renyiDiv_add (hα : α ≤ 2⁻¹) :
    ENNReal.ofReal
        (log (α / (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal))
      ≤ renyiDiv 2⁻¹ μ ν + ENNReal.ofReal (log 2) := by
  have h := ofReal_mul_log_div_bayesBinaryRisk_le_mul_renyiDiv_add μ ν (β := 2⁻¹) (by norm_num)
    le_rfl hα
  set L := log (α / (bayesBinaryRisk μ ν (Measure.boolMeasure α ((1 - α : ℝ≥0) : ℝ≥0∞))).toReal)
  have h2 : ENNReal.ofReal L = 2 * ENNReal.ofReal (2⁻¹ * L) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
    norm_num
  rw [h2]
  calc 2 * ENNReal.ofReal (2⁻¹ * L)
  _ ≤ 2 * (ENNReal.ofReal (1 - 2⁻¹) * (renyiDiv 2⁻¹ μ ν + ENNReal.ofReal (log 2))) := by gcongr
  _ = renyiDiv 2⁻¹ μ ν + ENNReal.ofReal (log 2) := by
    rw [← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num

end Renyi

end ProbabilityTheory
