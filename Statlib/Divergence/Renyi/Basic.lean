/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.Hellinger.Basic
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Basic.Real.Sign
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Statlib.ForMathlib.MeasureTheory.Measure.Bool

/-!
# Rényi divergence

## Main definitions

* `renyiDiv a μ ν`: the Rényi divergence of order `a` between finite measures. It is the Rényi
  divergence of the normalized measures `(μ univ)⁻¹ • μ` and `(ν univ)⁻¹ • ν`, defined from the
  Hellinger divergence for `a ∉ {0, 1}` and separately for `a = 0` and `a = 1` (where it is the
  Kullback-Leibler divergence of the normalized measures).

## Main statements

* `renyiDiv_zero`, `renyiDiv_one`: the special cases.
* `renyiDiv_self`: `Rₐ(μ, μ) = 0` for a nonzero finite measure `μ` and every order `a`.
* `renyiDiv_smul_left`, `renyiDiv_smul_right`: invariance under scaling of the measures.
* `renyiDiv_eq_top_iff_mutuallySingular_of_lt_one`: for `a < 1`, the divergence is infinite iff the
  measures are mutually singular.
* `toReal_renyiDiv_of_ne_top`: for finite measures with `μ ≠ 0`, if `Rₐ(μ, ν) < ∞`, then
  `Rₐ(μ, ν) = (a - 1)⁻¹ * (log ∫ (∂μ/∂ν) ^ a ∂ν - (a * log μ(α) + (1 - a) * log ν(α)))`;
  `toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure`: for probability measures,
  `Rₐ(μ, ν) = (a - 1)⁻¹ * log ∫ (∂μ/∂ν) ^ a ∂ν`.
* `lintegral_rpow_rnDeriv_eq_mul_exp_renyiDiv`: for `a ∈ (0, 1)` and finite measures,
  `∫⁻ x, (∂μ/∂ν) x ^ a ∂ν = μ(univ) ^ a * ν(univ) ^ (1 - a) * exp (-(1 - a) * Rₐ(μ, ν))`.
* `le_renyiDiv_of_le_hellingerDiv`: for `a > 0` and measures with the same masses, an inequality
  between Hellinger divergences of order `a` gives the same inequality between Rényi divergences.
  The data-processing inequalities are deduced from it in `Statlib.Divergence.Renyi.DataProcessing`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α} {a : ℝ}

/-- Weighted average `(1 - a) * ν univ + a * μ univ` of the masses of `μ` and `ν`, as a real
number. -/
noncomputable
abbrev avgMass (a : ℝ) (μ ν : Measure α) : ℝ := (1 - a) * (ν .univ).toReal + a * (μ .univ).toReal

lemma avgMass_nonneg_of_lt_one (ha_nonneg : 0 ≤ a) (ha_le : a ≤ 1) :
    0 ≤ avgMass a μ ν :=
  add_nonneg (mul_nonneg (sub_nonneg_of_le ha_le) ENNReal.toReal_nonneg)
    (mul_nonneg ha_nonneg ENNReal.toReal_nonneg)

open Classical in
/-- Rényi divergence of order `a` between finite measures. It is the Rényi divergence of the
normalized measures `(μ univ)⁻¹ • μ` and `(ν univ)⁻¹ • ν` (see `renyiDiv_smul_left` and
`renyiDiv_smul_right`): for `a ∉ {0, 1}`,
`Rₐ(μ, ν) = (a - 1)⁻¹ * (log (∫ x, ((∂μ/∂ν) x) ^ a ∂ν) - log (μ(univ) ^ a * ν(univ) ^ (1 - a)))`,
which is the usual `(a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x) ^ a ∂ν)` for probability measures.
The integral is written as `(1 - a) * ν(univ) + a * μ(univ) + (a - 1) * Hₐ(μ, ν)` in terms of the
Hellinger divergence, which makes the Rényi divergence a monotone function of the Hellinger
divergence for fixed masses. For `a = 1` it is the Kullback-Leibler divergence of the normalized
measures and for `a = 0` it is `- log (ν {∂μ/∂ν > 0} / ν(univ))`.
We use ENNReal.log instead of Real.log, because it is monotone on `ℝ≥0∞`, while the real log is
monotone only on `(0, ∞)` (`Real.log 0 = 0`). This allows us to transfer inequalities from the
Hellinger divergence to the Rényi divergence. -/
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if a = 0 then (- ENNReal.log (ν {x | 0 < (∂μ/∂ν) x} / ν .univ)).toENNReal
  else if a = 1 then klDiv ((μ .univ)⁻¹ • μ) ((ν .univ)⁻¹ • ν)
  else ((a - 1)⁻¹ * ENNReal.log
    (((avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν)).toENNReal)
      - (a - 1)⁻¹ * (a * Real.log (μ .univ).toReal
        + (1 - a) * Real.log (ν .univ).toReal)).toENNReal

lemma avgMass_add_mul_hellingerDiv_eq_ofReal (h : hellingerDiv a μ ν ≠ ∞) :
    (avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν)
      = (avgMass a μ ν + (a - 1) * (hellingerDiv a μ ν).toReal : ℝ) := by
  rw [← EReal.coe_ennreal_toReal h]
  norm_cast

lemma avgMass_add_mul_hellingerDiv_eq_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_one : a ≠ 1) (h : hellingerDiv a μ ν = ∞) :
    (avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν) = ⊤ := by
  have ha_lt : 1 < a := by
    by_contra ha
    exact hellingerDiv_ne_top_of_lt_one (lt_of_le_of_ne (not_lt.mp ha) ha_one) _ _ h
  rw [h]
  norm_cast
  have : (((a - 1) : ℝ) : EReal) * ⊤ = ⊤ := by
    simp only [EReal.coe_sub, EReal.coe_one, EReal.mul_eq_top, not_top_lt, and_false, top_ne_bot,
      EReal.zero_lt_top, and_true, false_or]
    right
    exact mod_cast sub_pos_of_lt ha_lt
  rw [this, EReal.add_top_of_ne_bot]
  exact EReal.coe_ne_bot _

lemma avgMass_add_mul_hellingerDiv_nonneg (ha_pos : 0 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ (avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν) := by
  by_cases ha_one : a = 1
  · simp only [ha_one, EReal.coe_add, sub_self, zero_mul, EReal.coe_zero, one_mul, ne_eq,
      measure_ne_top, not_false_eq_true, EReal.coe_ennreal_toReal, zero_add, EReal.coe_one,
      hellingerDiv_one]
    rw [EReal.sub_self]
    · simp only [zero_mul, add_zero]
      exact EReal.coe_ennreal_nonneg _
    · exact EReal.coe_ne_top _
    · exact EReal.coe_ne_bot _
  by_cases h_top : hellingerDiv a μ ν = ∞
  · rw [avgMass_add_mul_hellingerDiv_eq_top ha_one h_top]
    simp
  · rw [avgMass_add_mul_hellingerDiv_eq_ofReal h_top]
    norm_cast
    rw [mul_hellingerDiv_add_meas_eq_integral ha_pos ha_one h_top]
    exact integral_rpow_rnDeriv_nonneg

lemma avgMass_add_mul_hellingerDiv_nonneg' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (h_top : hellingerDiv a μ ν ≠ ∞) :
    0 ≤ avgMass a μ ν + (a - 1) * (hellingerDiv a μ ν).toReal := by
  have h := avgMass_add_mul_hellingerDiv_nonneg ha_pos (μ := μ) (ν := ν)
  rw [← EReal.coe_ennreal_toReal h_top] at h
  norm_cast at h

lemma avgMass_add_mul_hellingerDiv_nonneg'_of_lt_one (ha_pos : 0 < a) (ha_lt : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ avgMass a μ ν + (a - 1) * (hellingerDiv a μ ν).toReal := by
  by_cases h_top : hellingerDiv a μ ν = ∞
  · simp only [h_top, ENNReal.toReal_top, mul_zero, add_zero]
    exact avgMass_nonneg_of_lt_one ha_pos.le ha_lt.le
  · exact avgMass_add_mul_hellingerDiv_nonneg' ha_pos h_top

lemma avgMass_add_mul_hellingerDiv_eq_zero_iff_mutuallySingular'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha_pos : 0 < a) (ha_lt : a < 1) :
    avgMass a μ ν + (a - 1) * (hellingerDiv a μ ν).toReal = 0 ↔ μ ⟂ₘ ν := by
  rw [← toReal_hellingerDiv_eq_add_measure_univ_iff_of_lt_one ha_pos ha_lt]
  have ha : 1 - a ≠ 0 := sub_ne_zero_of_ne ha_lt.ne'
  rw [add_eq_zero_iff_eq_neg, ← neg_mul, neg_sub, avgMass, ← inv_mul_eq_iff_eq_mul₀ ha, mul_add,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, mul_comm _ a, eq_comm]

lemma avgMass_add_mul_hellingerDiv_eq_zero_iff_mutuallySingular
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha_pos : 0 < a) (ha_lt : a < 1) :
    (avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν) = 0 ↔ μ ⟂ₘ ν := by
  rw [avgMass_add_mul_hellingerDiv_eq_ofReal]
  swap; · exact hellingerDiv_ne_top_of_lt_one ha_lt _ _
  norm_cast
  exact avgMass_add_mul_hellingerDiv_eq_zero_iff_mutuallySingular' ha_pos ha_lt

lemma avgMass_add_mul_hellingerDiv_ne_zero_of_one_lt
    [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_lt : 1 < a) (h : hellingerDiv a μ ν ≠ ∞) :
    avgMass a μ ν + (a - 1) * (hellingerDiv a μ ν).toReal ≠ 0 := by
  have h' := toReal_hellingerDiv_ne_add_measure_univ_of_one_lt ha_lt h
  have ha : 1 - a ≠ 0 := sub_ne_zero_of_ne ha_lt.ne
  rwa [ne_eq, add_eq_zero_iff_eq_neg, ← neg_mul, neg_sub, avgMass, ← inv_mul_eq_iff_eq_mul₀ ha,
    mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, mul_comm _ a, eq_comm]

open Classical in
@[simp]
lemma renyiDiv_zero (μ ν : Measure α) :
    renyiDiv 0 μ ν = (- ENNReal.log (ν {x | 0 < (∂μ/∂ν) x} / ν .univ)).toENNReal :=
  ite_eq_left rfl

@[simp]
lemma renyiDiv_one (μ ν : Measure α) :
    renyiDiv 1 μ ν = klDiv ((μ .univ)⁻¹ • μ) ((ν .univ)⁻¹ • ν) := by
  rw [renyiDiv, ite_eq_right one_ne_zero, ite_eq_left rfl]

lemma renyiDiv_one_of_isProbabilityMeasure (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    renyiDiv 1 μ ν = klDiv μ ν := by
  simp [renyiDiv_one]

lemma renyiDiv_one_eq_top_iff [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv 1 μ ν = ∞ ↔ klDiv μ ν = ∞ := by
  rw [renyiDiv_one]
  rcases eq_or_ne ν 0 with rfl | hν
  · simp only [FunLike.coe_zero, Pi.zero_apply, ENNReal.inv_zero, smul_zero, klDiv_zero_right]
  have : NeZero ν := ⟨hν⟩
  rw [klDiv_smul_right_eq_top_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      (ENNReal.inv_ne_top.mpr (NeZero.ne _)),
    klDiv_smul_left_eq_top_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      (ENNReal.inv_ne_top.mpr (NeZero.ne _))]

lemma renyiDiv_of_ne_one (ha_zero : a ≠ 0) (ha_ne_one : a ≠ 1) (μ ν : Measure α) :
    renyiDiv a μ ν = ((a - 1)⁻¹ * ENNReal.log
      (((avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν)).toENNReal)
      - (a - 1)⁻¹ * (a * Real.log (μ .univ).toReal
        + (1 - a) * Real.log (ν .univ).toReal)).toENNReal := by
  rw [renyiDiv, ite_eq_right ha_zero, ite_eq_right ha_ne_one]

/-- The Rényi divergence of order `a ∉ {0, 1}` between probability measures, as a function of the
Hellinger divergence: `Rₐ(μ, ν) = (a - 1)⁻¹ * log (1 + (a - 1) * Hₐ(μ, ν))`. -/
lemma renyiDiv_of_ne_one_of_isProbabilityMeasure (ha0 : a ≠ 0) (ha1 : a ≠ 1) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    renyiDiv a μ ν = (((a - 1)⁻¹ : ℝ) * ENNReal.log
      ((1 + ((a - 1 : ℝ) : EReal) * hellingerDiv a μ ν).toENNReal) : EReal).toENNReal := by
  rw [renyiDiv_of_ne_one ha0 ha1]
  simp [avgMass, EReal.coe_sub]

lemma renyiDiv_eq_top_of_hellingerDiv_eq_top [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : hellingerDiv a μ ν = ∞) :
    renyiDiv a μ ν = ∞ := by
  by_cases ha_one : a = 1
  · rw [ha_one, hellingerDiv_one] at h
    rw [ha_one, renyiDiv_one_eq_top_iff]
    exact h
  have ha_lt : 1 < a := by
    by_contra ha
    exact hellingerDiv_ne_top_of_lt_one (lt_of_le_of_ne (not_lt.mp ha) ha_one) _ _ h
  have ha_pos : 0 < a := zero_lt_one.trans ha_lt
  rw [renyiDiv_of_ne_one ha_pos.ne' ha_lt.ne']
  rw [avgMass_add_mul_hellingerDiv_eq_top ha_lt.ne' h]
  simp only [EReal.toENNReal_top, ENNReal.log_top, EReal.toENNReal_eq_top_iff]
  have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊤ = ⊤ := by simp [EReal.mul_eq_top, ha_lt]
  rw [this, sub_eq_add_neg, EReal.top_add_of_ne_bot]
  simp only [ne_eq, EReal.neg_eq_bot_iff]
  norm_cast
  exact EReal.coe_ne_top _

section IntegralForm

open Classical in
lemma renyiDiv_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha_pos : 0 < a) (ha_lt : a < 1) :
    renyiDiv a μ ν =
      if μ ⟂ₘ ν then ∞
      else ENNReal.ofReal ((a - 1)⁻¹
        * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
          - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal))) := by
  rw [renyiDiv_of_ne_one ha_pos.ne' ha_lt.ne]
  split_ifs with h
  · rw [(avgMass_add_mul_hellingerDiv_eq_zero_iff_mutuallySingular ha_pos ha_lt).mpr h]
    simp only [ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_zero, ENNReal.ofReal_zero, ENNReal.log_zero, EReal.toENNReal_eq_top_iff]
    have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊥ = ⊤ := by simp [EReal.mul_eq_top, ha_lt]
    rw [this, sub_eq_add_neg, EReal.top_add_of_ne_bot]
    simp only [ne_eq, EReal.neg_eq_bot_iff]
    norm_cast
    exact EReal.coe_ne_top _
  · rw [← mul_hellingerDiv_add_meas_eq_integral_of_lt_one ha_pos ha_lt,
      avgMass_add_mul_hellingerDiv_eq_ofReal (hellingerDiv_ne_top_of_lt_one ha_lt _ _),
      EReal.real_coe_toENNReal, ENNReal.log_ofReal, ite_eq_right]
    · norm_cast
      rw [EReal.real_coe_toENNReal, mul_sub]
    · rw [not_le]
      refine lt_of_le_of_ne ?_ ?_
      · exact avgMass_add_mul_hellingerDiv_nonneg'_of_lt_one ha_pos ha_lt
      · rw [← avgMass_add_mul_hellingerDiv_eq_zero_iff_mutuallySingular' ha_pos ha_lt] at h
        exact Ne.symm h

lemma renyiDiv_of_one_lt [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha_lt : 1 < a) :
    renyiDiv a μ ν =
      if hellingerDiv a μ ν = ∞ then ∞
      else ENNReal.ofReal ((a - 1)⁻¹
        * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
          - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal))) := by
  have ha_pos : 0 < a := zero_lt_one.trans ha_lt
  split_ifs with h
  · exact renyiDiv_eq_top_of_hellingerDiv_eq_top h
  rw [renyiDiv_of_ne_one ha_pos.ne' ha_lt.ne', avgMass_add_mul_hellingerDiv_eq_ofReal h,
    EReal.real_coe_toENNReal, ENNReal.log_ofReal, ite_eq_right]
  · norm_cast
    rw [EReal.real_coe_toENNReal, mul_sub,
      ← mul_hellingerDiv_add_meas_eq_integral ha_pos ha_lt.ne' h]
  · rw [not_le]
    refine lt_of_le_of_ne ?_ ?_
    · exact avgMass_add_mul_hellingerDiv_nonneg' ha_pos h
    · symm
      exact avgMass_add_mul_hellingerDiv_ne_zero_of_one_lt ha_lt h


/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`. Version for `a < 1`. -/
lemma renyiDiv_eq_log_integral_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) (h_ms : ¬ μ ⟂ₘ ν) :
    renyiDiv a μ ν = ENNReal.ofReal ((a - 1)⁻¹
      * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal))) := by
  rw [renyiDiv_of_lt_one ha_pos ha_lt, ite_eq_right h_ms]

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`. Version for `1 < a`. -/
lemma renyiDiv_eq_log_integral_of_one_lt [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_lt : 1 < a) (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (h_ac : μ ≪ ν) :
    renyiDiv a μ ν = ENNReal.ofReal ((a - 1)⁻¹
      * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal))) := by
  rw [renyiDiv_of_one_lt ha_lt, ite_eq_right]
  exact (hellingerDiv_ne_top_iff_of_one_lt ha_lt _ _).mpr ⟨h_int, h_ac⟩

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`. Version for `a < 1`. -/
lemma renyiDiv_eq_log_integral_of_lt_one' [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) (h_ac : μ ≪ ν) :
    renyiDiv a μ ν = ENNReal.ofReal ((a - 1)⁻¹
      * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ (a - 1) ∂μ)
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal))) := by
  rw [renyiDiv_eq_log_integral_of_lt_one ha_pos ha_lt,
    integral_rpow_rnDeriv_eq_integral_rpow_sub_one ha_pos ha_lt.ne h_ac]
  exact fun h ↦ NeZero.ne μ (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h_ac h)

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`. Version for `1 < a`. -/
lemma renyiDiv_eq_log_integral_of_one_lt' [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_lt : 1 < a) (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (h_ac : μ ≪ ν) :
    renyiDiv a μ ν = ENNReal.ofReal ((a - 1)⁻¹
      * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ (a - 1) ∂μ)
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal))) := by
  rw [renyiDiv_eq_log_integral_of_one_lt ha_lt h_int h_ac,
    integral_rpow_rnDeriv_eq_integral_rpow_sub_one (zero_lt_one.trans ha_lt) ha_lt.ne' h_ac]

lemma toReal_renyiDiv_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) (h_ms : ¬ μ ⟂ₘ ν) :
    (renyiDiv a μ ν).toReal
      = (a - 1)⁻¹ * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal)) := by
  rw [renyiDiv_eq_log_integral_of_lt_one ha_pos ha_lt h_ms, ENNReal.toReal_ofReal]
  exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr (by linarith))
    (sub_nonpos.mpr (log_integral_rpow_rnDeriv_le_of_lt_one ha_pos ha_lt h_ms))

lemma toReal_renyiDiv_of_one_lt [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_lt : 1 < a) (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (h_ac : μ ≪ ν) :
    (renyiDiv a μ ν).toReal
      = (a - 1)⁻¹ * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal)) := by
  rw [renyiDiv_eq_log_integral_of_one_lt ha_lt h_int h_ac, ENNReal.toReal_ofReal]
  exact mul_nonneg (inv_nonneg.mpr (by linarith)) (sub_nonneg.mpr
    (le_log_integral_rpow_rnDeriv_of_one_lt ha_lt
      ((hellingerDiv_ne_top_iff_of_one_lt ha_lt _ _).mpr ⟨h_int, h_ac⟩)))

end IntegralForm

@[simp]
lemma renyiDiv_zero_measure_left (ha_nonneg : 0 ≤ a) (ha : a ≠ 1) (ν : Measure α)
    [IsFiniteMeasure ν] :
    renyiDiv a 0 ν = if a < 1 then ∞ else 0 := by
  by_cases ha_zero : a = 0
  · subst ha_zero
    rw [renyiDiv_zero, ite_eq_left zero_lt_one]
    have h_set : ν {x | 0 < (∂(0 : Measure α)/∂ν) x} = 0 := by
      have : {x | 0 < (∂(0 : Measure α)/∂ν) x} = {x | ¬ (∂(0 : Measure α)/∂ν) x = 0} :=
        Set.ext fun x ↦ show 0 < (∂(0 : Measure α)/∂ν) x ↔ ¬ (∂(0 : Measure α)/∂ν) x = 0 from
          pos_iff_ne_zero
      rw [this, ← ae_iff]
      filter_upwards [ν.rnDeriv_zero] with x hx
      simp [hx]
    rw [h_set, ENNReal.zero_div, ENNReal.log_zero, EReal.neg_bot, EReal.toENNReal_top]
  rw [renyiDiv_of_ne_one ha_zero ha]
  simp only [EReal.coe_add, EReal.coe_mul, EReal.coe_sub, EReal.coe_one, ne_eq, measure_ne_top,
    not_false_eq_true, EReal.coe_ennreal_toReal, FunLike.coe_zero, Pi.zero_apply,
    ENNReal.toReal_zero, mul_zero, EReal.coe_zero, add_zero, log_zero, zero_add,
    hellingerDiv_zero_measure_left (ha_nonneg.lt_of_ne' ha_zero)]
  have : (1 - (a : EReal)) * (ν Set.univ) + (a - 1) * (ν Set.univ) = 0 := by
    rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
    norm_cast
    ring
  simp only [this, ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
    EReal.toReal_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
  rcases lt_or_gt_of_ne ha with ha_lt | ha_lt
  · simp only [ha_lt, ↓reduceIte, EReal.toENNReal_eq_top_iff]
    have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊥ = ⊤ := by simp [EReal.mul_eq_top, ha_lt]
    rw [this, sub_eq_add_neg, EReal.top_add_of_ne_bot]
    simp only [ne_eq, EReal.neg_eq_bot_iff]
    norm_cast
    exact EReal.coe_ne_top _
  · have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊥ = ⊥ := by simp [EReal.mul_eq_bot, ha_lt]
    simp [this, not_lt.mpr ha_lt.le]

@[simp]
lemma renyiDiv_zero_measure_right (ha_nonneg : 0 ≤ a)
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ] :
    renyiDiv a μ 0 = ∞ := by
  by_cases ha_zero : a = 0
  · simp [ha_zero]
  have ha_pos : 0 < a := ha_nonneg.lt_of_ne' ha_zero
  rcases lt_trichotomy a 1 with (ha | rfl | ha)
  · rw [renyiDiv_of_ne_one ha_zero ha.ne, hellingerDiv_zero_measure_right_of_lt_one ha_pos ha]
    simp only [EReal.coe_add, FunLike.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, mul_zero,
      EReal.coe_zero, EReal.coe_mul, zero_add, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
      EReal.toENNReal_eq_top_iff, log_zero, add_zero]
    have : (a : EReal) * (μ Set.univ).toReal + (a - 1) * ((max (a * (1 - a)⁻¹) 0) * (μ Set.univ))
        = 0 := by
      rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
      norm_cast
      rw [max_eq_left, mul_comm a (1 - a)⁻¹, ← mul_assoc, ← mul_assoc, ← neg_sub 1 a, neg_mul,
        mul_inv_cancel₀]
      · ring
      · exact sub_ne_zero_of_ne ha.ne'
      · refine mul_nonneg ha_pos.le ?_
        simp [ha.le]
    simp only [this, ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
    simp only [EReal.coe_neg', inv_neg'', sub_neg.mpr ha, EReal.mul_bot_of_neg]
    rw [sub_eq_add_neg, EReal.top_add_of_ne_bot]
    simp only [ne_eq, EReal.neg_eq_bot_iff]
    norm_cast
    exact EReal.coe_ne_top _
  · rw [renyiDiv_one]
    simp only [FunLike.coe_zero, Pi.zero_apply, ENNReal.inv_zero, smul_zero]
    exact klDiv_zero_right
  · rw [renyiDiv_of_ne_one ha_zero ha.ne', hellingerDiv_zero_measure_right_of_one_le ha.le]
    simp only [EReal.coe_add, FunLike.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, mul_zero,
      EReal.coe_zero, EReal.coe_mul, zero_add, EReal.coe_ennreal_top, EReal.toENNReal_eq_top_iff,
      log_zero, add_zero]
    have : ((a : EReal) - 1) * ⊤ = ⊤ := by
      norm_cast
      simp only [EReal.coe_sub, EReal.coe_one, EReal.mul_eq_top, not_top_lt, and_false, top_ne_bot,
        EReal.zero_lt_top, and_true, false_or]
      right
      exact mod_cast (sub_pos_of_lt ha)
    rw [this, EReal.add_top_of_ne_bot]
    swap; · norm_cast; exact EReal.coe_ne_bot _
    simp only [EReal.toENNReal_top, ENNReal.log_top]
    have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊤ = ⊤ := by simp [EReal.mul_eq_top, ha]
    rw [this, sub_eq_add_neg, EReal.top_add_of_ne_bot]
    simp only [ne_eq, EReal.neg_eq_bot_iff]
    norm_cast
    exact EReal.coe_ne_top _

/-- The Rényi divergence between a nonzero finite measure and itself is zero. -/
@[simp]
lemma renyiDiv_self (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ] : renyiDiv a μ μ = 0 := by
  rcases eq_or_ne a 0 with rfl | ha0
  · have h : μ {x | 0 < (∂μ/∂μ) x} = μ .univ :=
      (ae_iff_measure_eq (measurableSet_lt measurable_const
        (μ.measurable_rnDeriv μ)).nullMeasurableSet).mp (Measure.rnDeriv_pos .rfl)
    simp [renyiDiv_zero, h, ENNReal.div_self (NeZero.ne _) (measure_ne_top _ _)]
  rcases eq_or_ne a 1 with rfl | ha1
  · rw [renyiDiv_one, klDiv_self]
  -- for `a ∉ {0, 1}`, `Hₐ(μ, μ) = 0` and both terms of the definition are `log μ(univ) / (a - 1)`
  have hm : 0 < (μ .univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) (measure_ne_top _ _)
  rw [renyiDiv_of_ne_one ha0 ha1, hellingerDiv_self, EReal.coe_ennreal_zero, mul_zero, add_zero,
    show avgMass a μ μ = (μ .univ).toReal by ring, EReal.real_coe_toENNReal,
    ENNReal.log_ofReal_of_pos hm]
  norm_cast
  simp [← add_mul]

section RenyiEq

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt
    [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha : 1 < a) :
    renyiDiv a μ ν = ∞ ↔ hellingerDiv a μ ν = ∞ := by
  refine ⟨fun h ↦ ?_, fun h ↦ renyiDiv_eq_top_of_hellingerDiv_eq_top h⟩
  contrapose! h
  rw [renyiDiv_of_one_lt ha]
  simp [h]

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (ha : 1 ≤ a)
    [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ ↔ hellingerDiv a μ ν = ∞ := by
  by_cases ha_one : a = 1
  · rw [ha_one, hellingerDiv_one]
    exact renyiDiv_one_eq_top_iff
  · exact renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt
      (lt_of_le_of_ne ha fun h ↦ ha_one h.symm)

lemma renyiDiv_eq_top_iff_of_one_lt (ha : 1 < a) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
  simp_rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le ha.le,
    hellingerDiv_eq_top_iff_of_one_lt ha]

lemma renyiDiv_ne_top_iff_of_one_lt (ha : 1 < a) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ∞ ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∧ μ ≪ ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_of_one_lt ha]
  simp

lemma renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ ↔ μ ⟂ₘ ν := by
  by_cases ha_zero : a = 0
  · subst ha_zero
    rw [renyiDiv_zero, EReal.toENNReal_eq_top_iff, EReal.neg_eq_top_iff, ENNReal.log_eq_bot_iff,
      ENNReal.div_eq_zero_iff, or_iff_left (measure_ne_top _ _)]
    have : {x | 0 < (∂μ/∂ν) x} = {x | ¬ (∂μ/∂ν) x = 0} :=
      Set.ext fun x ↦ show 0 < (∂μ/∂ν) x ↔ ¬ (∂μ/∂ν) x = 0 from pos_iff_ne_zero
    rw [this, ← ae_iff]
    exact Measure.rnDeriv_eq_zero μ ν
  rw [renyiDiv_of_lt_one (ha_nonneg.lt_of_ne' ha_zero) ha]
  simp

lemma renyiDiv_of_mutuallySingular (ha_nonneg : 0 ≤ a) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    renyiDiv a μ ν = ∞ := by
  by_cases ha : a < 1
  · rw [renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha]
    exact hμν
  · rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (le_of_not_gt ha)]
    exact hellingerDiv_of_mutuallySingular_of_one_le (le_of_not_gt ha) hμν

lemma renyiDiv_of_one_le_of_not_ac (ha : 1 ≤ a) (h_ac : ¬ μ ≪ ν)
    [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one_eq_top_iff]
    exact klDiv_of_not_ac h_ac
  replace ha : 1 < a := lt_of_le_of_ne ha fun h ↦ ha_one h.symm
  rw [renyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr h_ac

lemma absolutelyContinuous_of_renyiDiv_ne_top (ha : 1 ≤ a) (h : renyiDiv a μ ν ≠ ∞)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ ≪ ν := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · exact Measure.AbsolutelyContinuous.zero ν
  have : NeZero μ := ⟨hμ⟩
  by_contra h_ac
  exact h (renyiDiv_of_one_le_of_not_ac ha h_ac)

end RenyiEq

section HellingerIntegral

/-! ### The Rényi divergence and the Hellinger integral `∫ (∂μ/∂ν) ^ a ∂ν` -/

/-- For finite measures with `μ ≠ 0` and finite Rényi divergence of order
`a ∈ (0, 1) ∪ (1, ∞)`,
`Rₐ(μ, ν) = (a - 1)⁻¹ * (log ∫ (∂μ/∂ν) ^ a ∂ν - (a * log μ(α) + (1 - a) * log ν(α)))`. -/
lemma toReal_renyiDiv_of_ne_top [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha0 : 0 < a)
    (ha1 : a ≠ 1) (h : renyiDiv a μ ν ≠ ∞) :
    (renyiDiv a μ ν).toReal
      = (a - 1)⁻¹ * (log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)
        - (a * log (μ .univ).toReal + (1 - a) * log (ν .univ).toReal)) := by
  rcases ha1.lt_or_gt with ha1 | ha1
  · exact toReal_renyiDiv_of_lt_one ha0 ha1
      ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).not.mp h)
  · obtain ⟨h_int, h_ac⟩ := (renyiDiv_ne_top_iff_of_one_lt ha1).mp h
    exact toReal_renyiDiv_of_one_lt ha1 h_int h_ac

/-- For probability measures with finite Rényi divergence of order `a ∈ (0, 1) ∪ (1, ∞)`,
`Rₐ(μ, ν) = (a - 1)⁻¹ * log ∫ (∂μ/∂ν) ^ a ∂ν`. -/
lemma toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ha0 : 0 < a) (ha1 : a ≠ 1) (h : renyiDiv a μ ν ≠ ∞) :
    (renyiDiv a μ ν).toReal = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) := by
  simp [toReal_renyiDiv_of_ne_top ha0 ha1 h]

/-- For finite measures and `a ≥ 0`, if `Rₐ(μ, ν) < ∞`, then `(∂μ/∂ν) ^ a` is `ν`-integrable. -/
lemma integrable_rpow_rnDeriv_of_renyiDiv_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 0 ≤ a) (h : renyiDiv a μ ν ≠ ∞) :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  rcases lt_or_ge a 1 with ha1 | ha1
  · exact integrable_rpow_rnDeriv_of_lt_one ha ha1
  rcases ha1.eq_or_lt with rfl | ha1
  · simpa using Measure.integrable_toReal_rnDeriv
  rcases eq_zero_or_neZero μ with rfl | hμ
  · refine (integrable_zero α ℝ ν).congr ?_
    filter_upwards [ν.rnDeriv_zero] with x hx
    simp [hx, Real.zero_rpow (by linarith : a ≠ 0)]
  exact ((renyiDiv_ne_top_iff_of_one_lt ha1).mp h).1

/-- For finite measures with `μ ≠ 0` and finite Rényi divergence of order `a > 0`, the Hellinger
integral `∫ (∂μ/∂ν) ^ a ∂ν` is positive. -/
lemma integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top [IsFiniteMeasure μ] [NeZero μ]
    [IsFiniteMeasure ν] (ha : 0 < a) (h : renyiDiv a μ ν ≠ ∞) :
    0 < ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν :=
  (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha.ne'
    (integrable_rpow_rnDeriv_of_renyiDiv_ne_top ha.le h)).mpr
      fun h_ms ↦ h (renyiDiv_of_mutuallySingular ha.le h_ms)

/-- For `a ∈ (0, 1)` and finite measures, `∫⁻ x, (∂μ/∂ν) x ^ a ∂ν` is
`μ(univ) ^ a * ν(univ) ^ (1 - a) * exp (-(1 - a) * Rₐ(μ, ν))`. Both sides vanish when the
measures are mutually singular. -/
lemma lintegral_rpow_rnDeriv_eq_mul_exp_renyiDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∫⁻ x, (∂μ/∂ν) x ^ a ∂ν
      = μ .univ ^ a * ν .univ ^ (1 - a)
        * EReal.exp (-(((1 - a : ℝ) : EReal) * renyiDiv a μ ν)) := by
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(lintegral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha0).mpr h_ms,
      (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).mpr h_ms, EReal.coe_ennreal_top,
      EReal.coe_mul_top_of_pos (by simpa using ha1), EReal.neg_top, EReal.exp_bot, mul_zero]
  have hμ : μ ≠ 0 := fun h ↦ h_ms (h ▸ Measure.MutuallySingular.zero_left)
  have hν : ν ≠ 0 := fun h ↦ h_ms (h ▸ Measure.MutuallySingular.zero_right)
  have hμ_pos : 0 < (μ .univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top _ _)
  have hν_pos : 0 < (ν .univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)
  have h_int := integrable_rpow_rnDeriv_of_lt_one ha0.le ha1 (μ := μ) (ν := ν)
  have h_pos : 0 < ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν :=
    (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha0.ne' h_int).mpr h_ms
  have h_ne_top : renyiDiv a μ ν ≠ ∞ :=
    fun h ↦ h_ms ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).mp h)
  -- the lintegral is the `ofReal` of the integral
  have h_lint : ∫⁻ x, (∂μ/∂ν) x ^ a ∂ν = ENNReal.ofReal (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν) := by
    rw [integral_rpow_rnDeriv_eq_toReal_lintegral ha0.le,
      ENNReal.ofReal_toReal ((integrable_rpow_rnDeriv_iff_lintegral_ne_top ha0.le).mp h_int)]
  -- the integral in terms of the Rényi divergence
  have h_renyi := toReal_renyiDiv_of_lt_one ha0 ha1 h_ms
  have h_log : Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν)
      = -(1 - a) * (renyiDiv a μ ν).toReal + a * Real.log (μ .univ).toReal
        + (1 - a) * Real.log (ν .univ).toReal := by
    rw [h_renyi]
    have : a - 1 ≠ 0 := by linarith
    field_simp
    ring
  have h_eq : ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
      = (μ .univ).toReal ^ a * (ν .univ).toReal ^ (1 - a)
        * Real.exp (-(1 - a) * (renyiDiv a μ ν).toReal) := by
    rw [← Real.exp_log h_pos, h_log, Real.rpow_def_of_pos hμ_pos, Real.rpow_def_of_pos hν_pos,
      ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have h_exp : EReal.exp (-(((1 - a : ℝ) : EReal) * renyiDiv a μ ν))
      = ENNReal.ofReal (Real.exp (-(1 - a) * (renyiDiv a μ ν).toReal)) := by
    rw [← EReal.coe_ennreal_toReal h_ne_top, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe,
      neg_mul]
  rw [h_lint, h_eq, h_exp, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ha0.le,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by linarith),
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]

end HellingerIntegral

lemma toReal_renyiDiv_symm (ha_pos : 0 < a) (ha_lt : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * (renyiDiv a μ ν).toReal = a * (renyiDiv (1 - a) ν μ).toReal := by
  rw [renyiDiv_of_lt_one ha_pos ha_lt, renyiDiv_of_lt_one]
  rotate_left
  · linarith
  · linarith
  rw [show ν ⟂ₘ μ ↔ μ ⟂ₘ ν from ⟨.symm, .symm⟩]
  split_ifs with h
  · simp
  have h1 : 1 - a = (ENNReal.ofReal (1 - a)).toReal :=
    (ENNReal.toReal_ofReal (sub_nonneg_of_le ha_lt.le)).symm
  have h2 : a = (ENNReal.ofReal a).toReal := (ENNReal.toReal_ofReal ha_pos.le).symm
  rw [h1, h2, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  congr 1
  simp_rw [← h2, ← h1]
  rw [← ENNReal.ofReal_mul ha_pos.le, ← ENNReal.ofReal_mul (sub_nonneg_of_le ha_lt.le)]
  congr 1
  rw [integral_rpow_rnDeriv_symm ha_pos ha_lt.ne]
  simp only [sub_sub_cancel_left, sub_sub_cancel]
  have h_eq : (1 - a) * (a - 1)⁻¹ = a * (-a)⁻¹ := by
    rw [← neg_sub a 1, neg_mul, mul_inv_cancel₀ (sub_ne_zero_of_ne ha_lt.ne), inv_neg, mul_neg,
      mul_inv_cancel₀ ha_pos.ne']
  rw [← mul_assoc, ← mul_assoc, h_eq, add_comm ((1 - a) * Real.log (ν .univ).toReal)]

lemma renyiDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (1 - a) * renyiDiv a μ ν = ENNReal.ofReal a * renyiDiv (1 - a) ν μ := by
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_pos.le ha).mpr h_ms,
      (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by linarith) (by linarith)).mpr h_ms.symm,
      ENNReal.mul_top (by simp [ha]), ENNReal.mul_top (by simp [ha_pos])]
  · have h1 : renyiDiv a μ ν ≠ ∞ := by
      rwa [ne_eq, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_pos.le ha]
    have h2 : renyiDiv (1 - a) ν μ ≠ ∞ := by
      rw [ne_eq, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by linarith) (by linarith)]
      exact fun h ↦ h_ms h.symm
    rw [← ENNReal.ofReal_toReal h1, ← ENNReal.ofReal_toReal h2, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_mul ha_pos.le, toReal_renyiDiv_symm ha_pos ha]

section Scaling

/-! ### Invariance under scaling of the measures -/

lemma renyiDiv_smul_left (ha_nonneg : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ≥0) (hc : c ≠ 0) :
    renyiDiv a (c • μ) ν = renyiDiv a μ ν := by
  have hc' : (c : ℝ≥0∞) ≠ 0 := by simpa using hc
  have hc_pos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have hm : 0 < (μ .univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top _ _)
  have h_mass : ((c • μ) .univ).toReal = c * (μ .univ).toReal := by
    rw [Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal]
  -- `a = 0`: the sets where `∂(c • μ)/∂ν` and `∂μ/∂ν` are positive agree `ν`-a.e.
  by_cases ha_zero : a = 0
  · subst ha_zero
    have h_set : ν {x | 0 < (∂(c • μ)/∂ν) x} = ν {x | 0 < (∂μ/∂ν) x} := by
      refine measure_congr ?_
      filter_upwards [Measure.rnDeriv_smul_left' μ ν c] with x hx
      show 0 < (∂(c • μ)/∂ν) x ↔ 0 < (∂μ/∂ν) x
      rw [hx, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.mul_pos_iff,
        ENNReal.coe_pos]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨pos_iff_ne_zero.mpr hc, h⟩⟩
    rw [renyiDiv_zero, renyiDiv_zero, h_set]
  -- `a = 1`: the KL divergence of the normalized measures does not see `c`
  by_cases ha_one : a = 1
  · subst ha_one
    rw [renyiDiv_one, renyiDiv_one, Measure.coe_nnreal_smul_apply, ENNReal.smul_def, smul_smul,
      ENNReal.mul_inv (Or.inl hc') (Or.inl ENNReal.coe_ne_top), mul_right_comm,
      ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, one_mul]
  -- Otherwise, scaling `μ` by `c` multiplies the integral `∫ (∂μ/∂ν) ^ a ∂ν` by `c ^ a` and the
  -- mass of `μ` by `c`. These factors cancel in the formula for `renyiDiv`.
  have ha_pos : 0 < a := ha_nonneg.lt_of_ne' ha_zero
  have h_log (I : ℝ) (hI : 0 < I) :
      (a - 1)⁻¹ * (Real.log (c ^ a * I)
        - (a * Real.log (c * (μ .univ).toReal) + (1 - a) * Real.log (ν .univ).toReal))
      = (a - 1)⁻¹ * (Real.log I
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal)) := by
    rw [Real.log_mul (rpow_pos_of_pos hc_pos a).ne' hI.ne', Real.log_rpow hc_pos,
      Real.log_mul hc_pos.ne' hm.ne']
    ring
  rcases lt_or_gt_of_ne ha_one with ha_lt | ha_lt
  -- `a < 1`: the divergence is `∞` iff the measures are mutually singular, which `c` does not
  -- change. Otherwise the integral is positive and we apply `h_log`.
  · have h_ms : c • μ ⟂ₘ ν ↔ μ ⟂ₘ ν :=
      ⟨fun h ↦ h.mono_ac (Measure.absolutelyContinuous_smul hc') .rfl, fun h ↦ h.smul_nnreal c⟩
    rw [renyiDiv_of_lt_one ha_pos ha_lt, renyiDiv_of_lt_one ha_pos ha_lt]
    split_ifs with h1 h h
    · rfl
    · exact absurd (h_ms.mp h1) h
    · exact absurd (h_ms.mpr h) h1
    rw [integral_rpow_rnDeriv_smul_left, h_mass, h_log]
    exact (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha_pos.ne'
      (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha_lt)).mpr h
  -- `1 < a`: the divergence is `∞` iff the Hellinger divergence is, which `c` does not change.
  -- Otherwise `μ ≪ ν` and `μ ≠ 0`, so the integral is positive and we apply `h_log`.
  · have : NeZero μ := ⟨hμ⟩
    have : NeZero (c • μ) := ⟨fun h ↦ hμ (by simpa [hc] using h)⟩
    rw [renyiDiv_of_one_lt ha_lt, renyiDiv_of_one_lt ha_lt]
    simp only [hellingerDiv_smul_left_eq_top_iff ha_one c hc]
    split_ifs with h
    · rfl
    have h' := (hellingerDiv_ne_top_iff_of_one_lt ha_lt _ _).mp h
    rw [integral_rpow_rnDeriv_smul_left, h_mass, h_log]
    exact (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha_pos.ne' h'.1).mpr
      fun h_ms ↦ hμ (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h'.2 h_ms)

lemma renyiDiv_smul_right (ha_nonneg : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ≥0) (hc : c ≠ 0) :
    renyiDiv a μ (c • ν) = renyiDiv a μ ν := by
  have hc' : (c : ℝ≥0∞) ≠ 0 := by simpa using hc
  have hc_pos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  have h_mass : ((c • ν) .univ).toReal = c * (ν .univ).toReal := by
    rw [Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal]
  -- `a = 0`: the sets where `∂μ/∂(c • ν)` and `∂μ/∂ν` are positive agree `ν`-a.e., and the
  -- factor `c` in their `c • ν` measure cancels with the one in `(c • ν) univ`.
  by_cases ha_zero : a = 0
  · subst ha_zero
    have h_set : (c • ν) {x | 0 < (∂μ/∂(c • ν)) x} = c * ν {x | 0 < (∂μ/∂ν) x} := by
      rw [Measure.coe_nnreal_smul_apply]
      congr 1
      refine measure_congr ?_
      filter_upwards [Measure.rnDeriv_smul_right' μ ν hc] with x hx
      show 0 < (∂μ/∂(c • ν)) x ↔ 0 < (∂μ/∂ν) x
      rw [hx, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.mul_pos_iff,
        ENNReal.coe_pos]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨pos_iff_ne_zero.mpr (inv_ne_zero hc), h⟩⟩
    rw [renyiDiv_zero, renyiDiv_zero, h_set, Measure.coe_nnreal_smul_apply,
      ENNReal.mul_div_mul_left _ _ hc' ENNReal.coe_ne_top]
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  have hn : 0 < (ν .univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)
  -- `a = 1`: the KL divergence of the normalized measures does not see `c`
  by_cases ha_one : a = 1
  · subst ha_one
    rw [renyiDiv_one, renyiDiv_one, Measure.coe_nnreal_smul_apply, ENNReal.smul_def, smul_smul,
      ENNReal.mul_inv (Or.inl hc') (Or.inl ENNReal.coe_ne_top), mul_right_comm,
      ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, one_mul]
  -- Otherwise, scaling `ν` by `c` multiplies the integral `∫ (∂μ/∂ν) ^ a ∂ν` by `c ^ (1 - a)` and
  -- the mass of `ν` by `c`. These factors cancel in the formula for `renyiDiv`.
  have ha_pos : 0 < a := ha_nonneg.lt_of_ne' ha_zero
  have h_log (I : ℝ) (hI : 0 < I) :
      (a - 1)⁻¹ * (Real.log (c ^ (1 - a) * I)
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (c * (ν .univ).toReal)))
      = (a - 1)⁻¹ * (Real.log I
        - (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal)) := by
    rw [Real.log_mul (rpow_pos_of_pos hc_pos _).ne' hI.ne', Real.log_rpow hc_pos,
      Real.log_mul hc_pos.ne' hn.ne']
    ring
  rcases lt_or_gt_of_ne ha_one with ha_lt | ha_lt
  -- `a < 1`: the divergence is `∞` iff the measures are mutually singular, which `c` does not
  -- change. Otherwise the integral is positive and we apply `h_log`.
  · have h_ms : μ ⟂ₘ c • ν ↔ μ ⟂ₘ ν :=
      ⟨fun h ↦ h.mono_ac .rfl (Measure.absolutelyContinuous_smul hc'),
        fun h ↦ (h.symm.smul_nnreal c).symm⟩
    rw [renyiDiv_of_lt_one ha_pos ha_lt, renyiDiv_of_lt_one ha_pos ha_lt]
    split_ifs with h1 h h
    · rfl
    · exact absurd (h_ms.mp h1) h
    · exact absurd (h_ms.mpr h) h1
    rw [integral_rpow_rnDeriv_smul_right c (fun h ↦ absurd h hc), h_mass, h_log]
    exact (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha_pos.ne'
      (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha_lt)).mpr h
  -- `1 < a`: the divergence is `∞` iff the Hellinger divergence is, which `c` does not change.
  -- Otherwise `μ ≪ ν` and `μ ≠ 0`, so the integral is positive and we apply `h_log`.
  · rcases eq_or_ne μ 0 with rfl | hμ
    · rw [renyiDiv_zero_measure_left ha_nonneg ha_one, renyiDiv_zero_measure_left ha_nonneg ha_one]
    have : NeZero μ := ⟨hμ⟩
    rw [renyiDiv_of_one_lt ha_lt, renyiDiv_of_one_lt ha_lt]
    simp only [hellingerDiv_smul_right_eq_top_iff ha_one c hc]
    split_ifs with h
    · rfl
    have h' := (hellingerDiv_ne_top_iff_of_one_lt ha_lt _ _).mp h
    rw [integral_rpow_rnDeriv_smul_right c (fun h ↦ absurd h hc), h_mass, h_log]
    exact (integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha_pos.ne' h'.1).mpr
      fun h_ms ↦ hμ (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h'.2 h_ms)

lemma renyiDiv_smul_left' (ha_nonneg : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    renyiDiv a (c • μ) ν = renyiDiv a μ ν := by
  lift c to ℝ≥0 using hc_top
  rw [← ENNReal.smul_def]
  exact renyiDiv_smul_left ha_nonneg c (by simpa using hc)

lemma renyiDiv_smul_right' (ha_nonneg : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    renyiDiv a μ (c • ν) = renyiDiv a μ ν := by
  lift c to ℝ≥0 using hc_top
  rw [← ENNReal.smul_def]
  exact renyiDiv_smul_right ha_nonneg c (by simpa using hc)

lemma renyiDiv_smul_smul (ha_nonneg : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c c' : ℝ≥0∞} (hc : c ≠ 0) (hc_top : c ≠ ∞) (hc' : c' ≠ 0) (hc'_top : c' ≠ ∞) :
    renyiDiv a (c • μ) (c' • ν) = renyiDiv a μ ν := by
  lift c to ℝ≥0 using hc_top
  rw [← ENNReal.smul_def, renyiDiv_smul_right' ha_nonneg hc' hc'_top,
    renyiDiv_smul_left ha_nonneg c (by simpa using hc)]

/-- The Rényi divergence between finite measures is the Rényi divergence between the normalized
measures. -/
lemma renyiDiv_eq_renyiDiv_inv_smul (ha_nonneg : 0 ≤ a) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = renyiDiv a ((μ .univ)⁻¹ • μ) ((ν .univ)⁻¹ • ν) := by
  rcases eq_zero_or_neZero ν with rfl | _
  · rcases eq_zero_or_neZero μ with rfl | _
    · simp
    have := μ.smul_finite (ENNReal.inv_ne_top.mpr (NeZero.ne (μ .univ)))
    have : NeZero ((μ .univ)⁻¹ • μ) := ⟨by simp [NeZero.ne μ, measure_ne_top]⟩
    simp only [smul_zero, renyiDiv_zero_measure_right ha_nonneg]
  rcases eq_zero_or_neZero μ with rfl | _
  · have := ν.smul_finite (ENNReal.inv_ne_top.mpr (NeZero.ne (ν .univ)))
    rcases eq_or_ne a 1 with rfl | ha1
    · simp [renyiDiv_one, ENNReal.inv_mul_cancel (NeZero.ne (ν .univ)) (measure_ne_top _ _)]
    · simp only [smul_zero, renyiDiv_zero_measure_left ha_nonneg ha1]
  exact (renyiDiv_smul_smul ha_nonneg (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _)) (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))).symm

end Scaling

section CGF

/-- The cumulant generating function of the log-likelihood ratio under `ν` is given by the Rényi
divergence, for `a < 1`. The hypothesis `ν ≪ μ` is needed because `llr μ ν x = 0` when
`(∂μ/∂ν) x = 0`, and then `exp (llr μ ν x) = 1 ≠ 0 = (∂μ/∂ν) x`. -/
lemma cgf_llr_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha_pos : 0 < a) (ha_lt : a < 1)
    (hνμ : ν ≪ μ) (h_ms : ¬ μ ⟂ₘ ν) :
    cgf (llr μ ν) ν a = (a - 1) * (renyiDiv a μ ν).toReal
      + (a * Real.log (μ .univ).toReal + (1 - a) * Real.log (ν .univ).toReal) := by
  rw [toReal_renyiDiv_of_lt_one ha_pos ha_lt h_ms, ← mul_assoc,
    mul_inv_cancel₀ (sub_ne_zero.mpr ha_lt.ne), one_mul, sub_add_cancel, cgf, mgf,
    integral_congr_ae (exp_mul_llr_of_ac' hνμ)]

/-- The cumulant generating function of the log-likelihood ratio under `μ` is given by the Rényi
divergence of order `1 + a`, for probability measures. -/
lemma cgf_llr' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ha_pos : 0 < a)
    (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν) (hμν : μ ≪ ν) :
    cgf (llr μ ν) μ a = a * (renyiDiv (1 + a) μ ν).toReal := by
  have h1a : 1 < 1 + a := by linarith
  have h_avg : (1 + a) * Real.log (μ .univ).toReal + (1 - (1 + a)) * Real.log (ν .univ).toReal
      = 0 := by
    simp
  have h_eq : ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂μ = ∫ x, ((∂μ/∂ν) x).toReal ^ (1 + a) ∂ν := by
    rw [← integral_rnDeriv_smul hμν]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [smul_eq_mul]
    rw [add_comm, rpow_add_one' ENNReal.toReal_nonneg (by linarith), mul_comm]
  have h_one_le : 1 ≤ ∫ x, ((∂μ/∂ν) x).toReal ^ (1 + a) ∂ν := by
    rw [← mul_hellingerDiv_add_meas_eq_integral (by linarith) h1a.ne'
      ((hellingerDiv_ne_top_iff_of_one_lt h1a _ _).mpr ⟨h_int, hμν⟩)]
    simp only [measure_univ, ENNReal.toReal_one, mul_one]
    have : 0 ≤ (1 + a - 1) * (hellingerDiv (1 + a) μ ν).toReal :=
      mul_nonneg (by linarith) ENNReal.toReal_nonneg
    linarith
  rw [renyiDiv_eq_log_integral_of_one_lt h1a h_int hμν, h_avg, sub_zero,
    ENNReal.toReal_ofReal, ← mul_assoc, add_sub_cancel_left, mul_inv_cancel₀ ha_pos.ne', one_mul,
    cgf, mgf, integral_congr_ae (exp_mul_llr_of_ac hμν), h_eq]
  exact mul_nonneg (inv_nonneg.mpr (by linarith)) (Real.log_nonneg h_one_le)

end CGF

section DataProcessingInequality

/-- For `a > 0` and measures with the same masses, an inequality between Hellinger divergences of
order `a` gives the same inequality between Rényi divergences of order `a`. -/
lemma le_renyiDiv_of_le_hellingerDiv {a : ℝ} {μ₁ ν₁ : Measure α} {μ₂ ν₂ : Measure β}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (ha_pos : 0 < a) (h_eq_μ : μ₁ .univ = μ₂ .univ)
    (h_eq_ν : ν₁ .univ = ν₂ .univ) (h_le : hellingerDiv a μ₁ ν₁ ≤ hellingerDiv a μ₂ ν₂) :
    renyiDiv a μ₁ ν₁ ≤ renyiDiv a μ₂ ν₂ := by
  have h_avg_eq : avgMass a μ₁ ν₁ = avgMass a μ₂ ν₂ := by simp [avgMass, h_eq_ν, h_eq_μ]
  rcases lt_trichotomy a 1 with (ha | rfl | ha)
  · simp_rw [renyiDiv_of_ne_one ha_pos.ne' ha.ne, h_avg_eq, h_eq_μ, h_eq_ν]
    refine EReal.toENNReal_le_toENNReal ?_
    refine EReal.sub_le_sub ?_ le_rfl
    apply EReal.neg_le_neg_iff.mp
    simp_rw [← neg_mul, ← EReal.coe_neg, neg_inv, neg_sub]
    gcongr _ * ENNReal.log (EReal.toENNReal ?_)
    gcongr _ + ?_
    apply EReal.neg_le_neg_iff.mp
    norm_cast
    simp_rw [← neg_mul, ← EReal.coe_neg, neg_sub]
    gcongr
  · simp only [renyiDiv_one, hellingerDiv_one] at h_le ⊢
    exact klDiv_inv_smul_le_of_le h_eq_μ h_eq_ν h_le
  · simp_rw [renyiDiv_of_ne_one ha_pos.ne' ha.ne', h_avg_eq, h_eq_μ, h_eq_ν]
    refine EReal.toENNReal_le_toENNReal ?_
    refine EReal.sub_le_sub ?_ le_rfl
    gcongr
    norm_cast
    linarith

end DataProcessingInequality

end ProbabilityTheory
