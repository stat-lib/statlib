/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Renyi.Order

/-!
# Limits and continuity of the Rényi divergence in its order

We prove that the Rényi divergence of order `1` (the normalized Kullback-Leibler divergence) is the
limit of `Rₐ(μ, ν)` as `a → 1⁻` (always) and as `a → 1⁺` (when `R_b(μ, ν)` is finite for some
`b > 1`). Together with the limit `Rₐ(μ, ν) → R₀(μ, ν)` as `a → 0⁺` (`tendsto_renyiDiv_nhdsGT_zero`)
and the monotonicity of `a ↦ Rₐ(μ, ν)`, we deduce that `a ↦ Rₐ(μ, ν)` is continuous on `[0, 1]`
and on `[0, b]` whenever `R_b(μ, ν) < ∞`.

The proofs use the secant slopes `(t ^ a - t) / (a - 1)` of the convex function `s ↦ t ^ s`, which
are monotone in `a` and tend to `t * log t` as `a → 1`. Since
`∫ (∂μ/∂ν) ^ a ∂ν - ∫ ∂μ/∂ν ∂ν = (a - 1) * ∫ ((∂μ/∂ν) ^ a - ∂μ/∂ν) / (a - 1) ∂ν`, monotone or
dominated convergence of these slopes gives the behaviour of `Rₐ(μ, ν)` near `a = 1`.

## Main statements

* `tendsto_renyiDiv_nhdsLT_one`: `Rₐ(μ, ν) → R₁(μ, ν)` as `a → 1⁻`.
* `tendsto_renyiDiv_nhdsGT_one`: if `R_b(μ, ν) < ∞` for some `b > 1`, then `Rₐ(μ, ν) → R₁(μ, ν)`
  as `a → 1⁺`.
* `continuousOn_renyiDiv_Icc`: `a ↦ Rₐ(μ, ν)` is continuous on `[0, 1]`.
* `continuousOn_renyiDiv_Icc_of_ne_top`: if `R_b(μ, ν) < ∞`, then `a ↦ Rₐ(μ, ν)` is continuous on
  `[0, b]`.

## Implementation notes

All statements are proved for probability measures, then extended to finite measures with
`renyiDiv_eq_renyiDiv_inv_smul`. They require `μ ≠ 0`: `R₁(0, ν) = 1` if `ν ≠ 0`, while
`Rₐ(0, ν) = ∞` for `a < 1` and `Rₐ(0, ν) = 0` for `a > 1`.

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014), Theorems 5 and 7.
-/

@[expose] public section

open MeasureTheory Filter Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a b : ℝ}

section IntegralRPow

/-- The integral of the secant slopes `((∂μ/∂ν) ^ a - ∂μ/∂ν) / (a - 1)`. -/
private lemma integral_rpow_sub_self_div_sub_one [IsFiniteMeasure μ]
    (ha_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    ∫ x, (((∂μ/∂ν) x).toReal ^ a - ((∂μ/∂ν) x).toReal) / (a - 1) ∂ν
      = (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - ∫ x, ((∂μ/∂ν) x).toReal ∂ν) / (a - 1) := by
  rw [integral_div, integral_sub ha_int Measure.integrable_toReal_rnDeriv]

private lemma integrable_rpow_sub_self_div_sub_one [IsFiniteMeasure μ]
    (ha_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    Integrable (fun x ↦ (((∂μ/∂ν) x).toReal ^ a - ((∂μ/∂ν) x).toReal) / (a - 1)) ν :=
  (ha_int.sub Measure.integrable_toReal_rnDeriv).div_const _

end IntegralRPow

section Probability

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- For `a ∈ (0, 1)`, `(1 - ∫ (∂μ/∂ν) ^ a ∂ν) / (1 - a) ≤ Rₐ(μ, ν)`. -/
private lemma one_sub_integral_rpow_div_le_toReal_renyiDiv (ha0 : 0 < a) (ha1 : a < 1)
    (h_ms : ¬ μ ⟂ₘ ν) :
    (1 - ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) / (1 - a) ≤ (renyiDiv a μ ν).toReal := by
  have h_top : renyiDiv a μ ν ≠ ∞ :=
    fun h ↦ h_ms ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha1).mp h)
  have hI := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha0 h_top
  rw [toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha0 ha1.ne h_top, ← div_eq_inv_mul,
    show a - 1 = -(1 - a) by ring, div_neg, ← neg_div]
  exact div_le_div_of_nonneg_right (by linarith [Real.log_le_sub_one_of_pos hI]) (by linarith)

/-- If the Kullback-Leibler divergence is infinite, the Rényi divergences of orders `a < 1` are
unbounded. -/
private lemma exists_lt_renyiDiv_of_klDiv_eq_top (h : klDiv μ ν = ∞) (M : ℝ≥0) :
    ∃ a ∈ Ioo (0 : ℝ) 1, (M : ℝ≥0∞) < renyiDiv a μ ν := by
  by_cases h_ms : μ ⟂ₘ ν
  · refine ⟨2⁻¹, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)).mpr h_ms]
    exact ENNReal.coe_lt_top
  -- it suffices to find `a` with `M < (1 - I a) / (1 - a)`
  suffices ∃ a ∈ Ico (2⁻¹ : ℝ) 1,
      (M : ℝ) < (1 - ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) / (1 - a) by
    obtain ⟨a, ha, hM⟩ := this
    have ha0 : 0 < a := by linarith [ha.1]
    refine ⟨a, ⟨ha0, ha.2⟩, ?_⟩
    have h_top : renyiDiv a μ ν ≠ ∞ :=
      fun h ↦ h_ms ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha0.le ha.2).mp h)
    have h_lt := hM.trans_le (one_sub_integral_rpow_div_le_toReal_renyiDiv ha0 ha.2 h_ms)
    rw [← ENNReal.ofReal_toReal h_top, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨h_lt, M.property.trans_lt h_lt⟩)
  set c := ∫ x, ((∂μ/∂ν) x).toReal ∂ν with hc_def
  -- decomposition `(1 - I a) / (1 - a) = (1 - c) / (1 - a) + ∫ slope`
  have h_decomp : ∀ a ∈ Ico (2⁻¹ : ℝ) 1, (1 - ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) / (1 - a)
      = (1 - c) / (1 - a)
        + ∫ x, (((∂μ/∂ν) x).toReal ^ a - ((∂μ/∂ν) x).toReal) / (a - 1) ∂ν := by
    intro a ha
    have h1a : 1 - a ≠ 0 := by linarith [ha.2]
    have ha1 : a - 1 ≠ 0 := by linarith [ha.2]
    rw [integral_rpow_sub_self_div_sub_one
      (integrable_rpow_rnDeriv_of_lt_one (by linarith [ha.1]) ha.2), ← hc_def]
    field_simp
    ring
  have h_slope_ge : ∀ a ∈ Ico (2⁻¹ : ℝ) 1,
      -2⁻¹ ≤ ∫ x, (((∂μ/∂ν) x).toReal ^ a - ((∂μ/∂ν) x).toReal) / (a - 1) ∂ν := by
    intro a ha
    calc -2⁻¹ = ∫ _, -2⁻¹ ∂ν := by simp
    _ ≤ _ := integral_mono (integrable_const _)
        (integrable_rpow_sub_self_div_sub_one
          (integrable_rpow_rnDeriv_of_lt_one (by linarith [ha.1]) ha.2))
        fun x ↦ Real.neg_inv_two_le_rpow_sub_self_div_sub_one ENNReal.toReal_nonneg ha.1 ha.2.ne
  by_cases h_ac : μ ≪ ν
  swap
  · -- `c < 1` since `μ` has a nonzero singular part with respect to `ν`
    have hc_lt : c < 1 := by
      have h_sing : μ.singularPart ν ≠ 0 :=
        fun h0 ↦ h_ac ((Measure.singularPart_eq_zero μ ν).mp h0)
      rw [hc_def, Measure.integral_toReal_rnDeriv', probReal_univ, sub_lt_self_iff]
      exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr h_sing) (measure_ne_top _ _)
    have h_tend : Tendsto (fun a : ℝ ↦ (1 - c) / (1 - a)) (𝓝[<] 1) atTop := by
      have h1 : Tendsto (fun a : ℝ ↦ 1 - a) (𝓝[<] 1) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Tendsto (fun a : ℝ ↦ 1 - a) (𝓝 1) (𝓝 (1 - 1)) :=
            tendsto_const_nhds.sub tendsto_id
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with a ha
          simpa using ha
      simp_rw [div_eq_mul_inv]
      exact Tendsto.const_mul_atTop (by linarith) (tendsto_inv_nhdsGT_zero.comp h1)
    obtain ⟨a, ha_gt, ha⟩ := ((h_tend.eventually_gt_atTop ((M : ℝ) + 2⁻¹)).and
      (Ico_mem_nhdsLT (show (2⁻¹ : ℝ) < 1 by norm_num))).exists
    refine ⟨a, ha, ?_⟩
    rw [h_decomp a ha]
    linarith [h_slope_ge a ha]
  -- `μ ≪ ν` and the log-likelihood ratio is not integrable: monotone convergence
  have h_int : ¬ Integrable (llr μ ν) μ := klDiv_eq_top_iff.mp h h_ac
  have hc1 : c = 1 := by rw [hc_def, Measure.integral_toReal_rnDeriv h_ac]; simp
  by_contra h_contra
  simp only [not_exists, not_and, not_lt] at h_contra
  refine h_int ((integrable_rnDeriv_mul_log_iff h_ac).mp ?_)
  obtain ⟨s, hs_mono, hs_mem, hs_lim⟩ :=
    exists_seq_strictMono_tendsto' (show (2⁻¹ : ℝ) < 1 by norm_num)
  replace hs_mem n : s n ∈ Ico (2⁻¹ : ℝ) 1 := Ioo_subset_Ico_self (hs_mem n)
  have hs_tendsto : Tendsto s atTop (𝓝[≠] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs_lim, .of_forall fun n ↦ (hs_mem n).2.ne⟩
  have h_lim : Tendsto (fun n ↦ ∫⁻ x, ENNReal.ofReal
        ((((∂μ/∂ν) x).toReal ^ s n - ((∂μ/∂ν) x).toReal) / (s n - 1) + 2⁻¹) ∂ν) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal
        (((∂μ/∂ν) x).toReal * Real.log ((∂μ/∂ν) x).toReal + 2⁻¹) ∂ν)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n ↦ ?_) ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp (((((μ.measurable_rnDeriv ν).ennreal_toReal.pow_const
        _).sub (μ.measurable_rnDeriv ν).ennreal_toReal).div_const _).add_const _)).aemeasurable
    · filter_upwards with x
      intro n m hnm
      refine ENNReal.ofReal_le_ofReal ?_
      gcongr ?_ + _
      exact Real.rpow_sub_self_div_sub_one_le ENNReal.toReal_nonneg
        (by linarith [(hs_mem n).1]) (hs_mem n).2.ne (hs_mem m).2.ne (hs_mono.monotone hnm)
    · filter_upwards with x
      refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      exact ((Real.tendsto_rpow_sub_self_div_sub_one _).comp hs_tendsto).add_const _
  have h_bound : ∀ n, ∫⁻ x, ENNReal.ofReal
      ((((∂μ/∂ν) x).toReal ^ s n - ((∂μ/∂ν) x).toReal) / (s n - 1) + 2⁻¹) ∂ν
        ≤ ENNReal.ofReal (M + 2⁻¹) := by
    intro n
    have h_int_n := integrable_rpow_sub_self_div_sub_one
      (integrable_rpow_rnDeriv_of_lt_one (μ := μ) (ν := ν) (by linarith [(hs_mem n).1])
        (hs_mem n).2)
    have h_int_n' : Integrable (fun x ↦
        (((∂μ/∂ν) x).toReal ^ s n - ((∂μ/∂ν) x).toReal) / (s n - 1) + 2⁻¹) ν :=
      h_int_n.add (integrable_const _)
    rw [← ofReal_integral_eq_lintegral_ofReal h_int_n' (.of_forall fun x ↦ by
      have := Real.neg_inv_two_le_rpow_sub_self_div_sub_one (t := ((∂μ/∂ν) x).toReal)
        ENNReal.toReal_nonneg (hs_mem n).1 (hs_mem n).2.ne
      simp only [Pi.zero_apply]
      linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_add h_int_n (integrable_const _)]
    have := h_contra (s n) (hs_mem n)
    rw [h_decomp (s n) (hs_mem n), hc1, sub_self, zero_div, zero_add] at this
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  have h_fin : ∫⁻ x, ENNReal.ofReal
      (((∂μ/∂ν) x).toReal * Real.log ((∂μ/∂ν) x).toReal + 2⁻¹) ∂ν ≤ ENNReal.ofReal (M + 2⁻¹) :=
    le_of_tendsto' h_lim h_bound
  have h_nonneg : 0 ≤ᵐ[ν]
      fun x ↦ ((∂μ/∂ν) x).toReal * Real.log ((∂μ/∂ν) x).toReal + 2⁻¹ := .of_forall fun x ↦ by
    have := Real.neg_inv_two_le_mul_log (t := ((∂μ/∂ν) x).toReal) ENNReal.toReal_nonneg
    simp only [Pi.zero_apply]
    linarith
  have h_int' : Integrable
      (fun x ↦ ((∂μ/∂ν) x).toReal * Real.log ((∂μ/∂ν) x).toReal + 2⁻¹) ν :=
    ⟨(((μ.measurable_rnDeriv ν).ennreal_toReal.mul
      (μ.measurable_rnDeriv ν).ennreal_toReal.log).add_const _).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal h_nonneg).mpr (h_fin.trans_lt ENNReal.ofReal_lt_top)⟩
  exact (h_int'.sub (integrable_const (2⁻¹ : ℝ))).congr (.of_forall fun x ↦ by simp)

/-- For probability measures, `Rₐ(μ, ν) → R₁(μ, ν) = KL(μ, ν)` as `a → 1⁻`. -/
private lemma tendsto_renyiDiv_nhdsLT_one_of_isProbabilityMeasure :
    Tendsto (fun a ↦ renyiDiv a μ ν) (𝓝[<] 1) (𝓝 (renyiDiv 1 μ ν)) := by
  have h_mem : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  rw [renyiDiv_one_of_isProbabilityMeasure]
  by_cases h_top : klDiv μ ν = ∞
  · rw [h_top, ENNReal.tendsto_nhds_top_iff_nnreal]
    intro M
    obtain ⟨a₀, ha₀, hM⟩ := exists_lt_renyiDiv_of_klDiv_eq_top h_top M
    filter_upwards [Ioo_mem_nhdsLT ha₀.2] with a ha
    exact hM.trans_le (renyiDiv_le_renyiDiv_of_le ha₀.1.le ha.1.le)
  obtain ⟨h_ac, h_int⟩ := klDiv_ne_top_iff.mp h_top
  rw [← ENNReal.ofReal_toReal h_top, toReal_klDiv_of_measure_eq h_ac (by simp)]
  refine (ENNReal.tendsto_ofReal (tendsto_mul_log_integral_rpow_rnDeriv h_ac h_int)).congr' ?_
  filter_upwards [h_mem] with a ha
  have ha_top : renyiDiv a μ ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (renyiDiv_le_renyiDiv_of_le ha.1.le ha.2.le)
    rwa [renyiDiv_one_of_isProbabilityMeasure]
  rw [← ENNReal.ofReal_toReal ha_top,
    toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ha.1 ha.2.ne ha_top]

/-- For probability measures, if `R_b(μ, ν) < ∞` for some `b > 1`, then
`Rₐ(μ, ν) → R₁(μ, ν) = KL(μ, ν)` as `a → 1⁺`. -/
private lemma tendsto_renyiDiv_nhdsGT_one_of_isProbabilityMeasure (hb : 1 < b)
    (hb_top : renyiDiv b μ ν ≠ ∞) :
    Tendsto (fun a ↦ renyiDiv a μ ν) (𝓝[>] 1) (𝓝 (renyiDiv 1 μ ν)) := by
  obtain ⟨hb_int, h_ac⟩ := (renyiDiv_ne_top_iff_of_one_lt hb).mp hb_top
  have h_llr := integrable_llr_of_integrable_rpow_rnDeriv hb h_ac hb_int
  have h_kl_top : klDiv μ ν ≠ ∞ := klDiv_ne_top h_ac h_llr
  have h_mem : Ioc (1 : ℝ) b ∈ 𝓝[>] (1 : ℝ) := Ioc_mem_nhdsGT hb
  have h_kl_eq : renyiDiv 1 μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ) := by
    rw [renyiDiv_one_of_isProbabilityMeasure, ← ENNReal.ofReal_toReal h_kl_top,
      toReal_klDiv_of_measure_eq h_ac (by simp)]
  -- the integral of the slopes tends to `KL(μ, ν)` by dominated convergence
  have h_tendsto : Tendsto (fun a ↦ ∫ x, (((∂μ/∂ν) x).toReal ^ a - ((∂μ/∂ν) x).toReal) / (a - 1) ∂ν)
      (𝓝[>] 1) (𝓝 (∫ x, llr μ ν x ∂μ)) := by
    rw [← integral_rnDeriv_mul_log h_ac]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ |((∂μ/∂ν) x).toReal * Real.log ((∂μ/∂ν) x).toReal|
        + |(((∂μ/∂ν) x).toReal ^ b - ((∂μ/∂ν) x).toReal) / (b - 1)|) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun a ↦ ((((μ.measurable_rnDeriv ν).ennreal_toReal.pow_const
        _).sub (μ.measurable_rnDeriv ν).ennreal_toReal).div_const _).aestronglyMeasurable
    · filter_upwards [h_mem] with a ha
      refine Eventually.of_forall fun x ↦ ?_
      rw [Real.norm_eq_abs]
      have h1 := Real.mul_log_le_rpow_sub_self_div_sub_one (t := ((∂μ/∂ν) x).toReal)
        ENNReal.toReal_nonneg ha.1
      have h2 := Real.rpow_sub_self_div_sub_one_le (t := ((∂μ/∂ν) x).toReal)
        ENNReal.toReal_nonneg (by linarith [ha.1]) ha.1.ne' hb.ne' ha.2
      exact (abs_le_max_abs_abs h1 h2).trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))
    · exact ((integrable_rnDeriv_mul_log_iff h_ac).mpr h_llr).abs.add
        (integrable_rpow_sub_self_div_sub_one hb_int).abs
    · exact Eventually.of_forall fun x ↦
        (Real.tendsto_rpow_sub_self_div_sub_one _).mono_left
          (nhdsWithin_mono _ fun y hy ↦ ne_of_gt (Set.mem_Ioi.mp hy))
  -- `Rₐ(μ, ν)` is bounded above by the integral of the slopes
  have h_upper : ∀ᶠ a in 𝓝[>] (1 : ℝ), renyiDiv a μ ν
      ≤ ENNReal.ofReal (∫ x, (((∂μ/∂ν) x).toReal ^ a - ((∂μ/∂ν) x).toReal) / (a - 1) ∂ν) := by
    filter_upwards [h_mem] with a ha
    have ha_top : renyiDiv a μ ν ≠ ∞ :=
      ne_top_of_le_ne_top hb_top (renyiDiv_le_renyiDiv_of_le (by linarith [ha.1]) ha.2)
    have hI := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top (by linarith [ha.1]) ha_top
    rw [← ENNReal.ofReal_toReal ha_top,
      toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure (by linarith [ha.1]) ha.1.ne' ha_top,
      ← div_eq_inv_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_rpow_sub_self_div_sub_one (integrable_rpow_rnDeriv_of_renyiDiv_ne_top
      (by linarith [ha.1]) ha_top), Measure.integral_toReal_rnDeriv h_ac]
    simp only [probReal_univ]
    exact div_le_div_of_nonneg_right (Real.log_le_sub_one_of_pos hI) (by linarith [ha.1])
  rw [h_kl_eq]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (ENNReal.tendsto_ofReal h_tendsto) ?_ h_upper
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact h_kl_eq ▸ renyiDiv_le_renyiDiv_of_le zero_le_one (le_of_lt ha)

/-- For probability measures, `a ↦ Rₐ(μ, ν)` is continuous within `s` at `a ∈ s` with
`a ∉ {0, 1}` if it is finite near `a` in `s` and `t ↦ ∫ (∂μ/∂ν) ^ t ∂ν` is continuous within `s`
at `a`. -/
private lemma continuousWithinAt_renyiDiv_of_isProbabilityMeasure {s : Set ℝ} (ha : a ∈ s)
    (ha0 : 0 < a) (ha1 : a ≠ 1) (h_top : ∀ᶠ t in 𝓝[s] a, renyiDiv t μ ν ≠ ∞)
    (hI : ContinuousWithinAt (fun t ↦ ∫ x, ((∂μ/∂ν) x).toReal ^ t ∂ν) s a) :
    ContinuousWithinAt (fun t ↦ renyiDiv t μ ν) s a := by
  have hIa := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top ha0 (h_top.self_of_nhdsWithin ha)
  have h_cont : ContinuousWithinAt
      (fun t ↦ ENNReal.ofReal (Real.log (∫ x, ((∂μ/∂ν) x).toReal ^ t ∂ν) / (t - 1))) s a :=
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((hI.log hIa.ne').div (continuousWithinAt_id.sub continuousWithinAt_const)
        (sub_ne_zero.mpr ha1))
  refine h_cont.congr_of_eventuallyEq_of_mem ?_ ha
  filter_upwards [h_top, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha0),
    mem_nhdsWithin_of_mem_nhds (eventually_ne_nhds ha1)] with t ht ht0 ht1
  rw [← ENNReal.ofReal_toReal ht, toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure ht0 ht1 ht,
    div_eq_inv_mul]

/-- For probability measures, `a ↦ Rₐ(μ, ν)` is continuous on `[0, 1]`. -/
private lemma continuousOn_renyiDiv_Icc_of_isProbabilityMeasure :
    ContinuousOn (fun a ↦ renyiDiv a μ ν) (Icc 0 1) := by
  intro a ha
  rcases ha.1.eq_or_lt with rfl | ha0
  · exact (continuousWithinAt_Icc_iff_Ici zero_lt_one).mpr
      (continuousWithinAt_Ioi_iff_Ici.mp tendsto_renyiDiv_nhdsGT_zero)
  rcases ha.2.eq_or_lt with rfl | ha1
  · exact (continuousWithinAt_Icc_iff_Iic zero_lt_one).mpr
      (continuousWithinAt_Iio_iff_Iic.mp tendsto_renyiDiv_nhdsLT_one_of_isProbabilityMeasure)
  have h_mem : Ioo 0 1 ∈ 𝓝[Icc 0 1] a := mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ha0 ha1)
  by_cases h_ms : μ ⟂ₘ ν
  · refine (continuousWithinAt_const (b := ∞)).congr_of_eventuallyEq_of_mem ?_ ha
    filter_upwards [h_mem] with t ht
    exact (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ht.1.le ht.2).mpr h_ms
  refine continuousWithinAt_renyiDiv_of_isProbabilityMeasure ha ha0 ha1.ne ?_ ?_
  · filter_upwards [h_mem] with t ht
    exact fun h ↦ h_ms ((renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ht.1.le ht.2).mp h)
  · exact (continuousOn_integral_rpow_rnDeriv (by simpa using Measure.integrable_toReal_rnDeriv)
      a ⟨ha0, ha.2⟩).mono_of_mem_nhdsWithin (mem_of_superset h_mem Ioo_subset_Ioc_self)

/-- For probability measures, if `R_b(μ, ν) < ∞`, then `a ↦ Rₐ(μ, ν)` is continuous on
`[0, b]`. -/
private lemma continuousOn_renyiDiv_Icc_of_ne_top_of_isProbabilityMeasure
    (hb_top : renyiDiv b μ ν ≠ ∞) :
    ContinuousOn (fun a ↦ renyiDiv a μ ν) (Icc 0 b) := by
  rcases le_or_gt b 1 with hb1 | hb1
  · exact continuousOn_renyiDiv_Icc_of_isProbabilityMeasure.mono (Icc_subset_Icc_right hb1)
  obtain ⟨hb_int, h_ac⟩ := (renyiDiv_ne_top_iff_of_one_lt hb1).mp hb_top
  intro a ha
  rcases lt_trichotomy a 1 with ha1 | rfl | ha1
  · refine (continuousOn_renyiDiv_Icc_of_isProbabilityMeasure a ⟨ha.1, ha1.le⟩)
      |>.mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.mpr ⟨Iio 1, isOpen_Iio, ha1, fun x hx ↦ ⟨hx.2.1, hx.1.le⟩⟩
  · refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_iff_continuous_left_right.mpr
      ⟨continuousWithinAt_Iio_iff_Iic.mp tendsto_renyiDiv_nhdsLT_one_of_isProbabilityMeasure,
        continuousWithinAt_Ioi_iff_Ici.mp
          (tendsto_renyiDiv_nhdsGT_one_of_isProbabilityMeasure hb1 hb_top)⟩
  -- for `a ∈ (1, b]`, `Rₐ(μ, ν) ≤ R_b(μ, ν) < ∞` and `t ↦ ∫ (∂μ/∂ν) ^ t ∂ν` is continuous on
  -- `(0, b]`
  have ha0 : 0 < a := zero_lt_one.trans ha1
  refine continuousWithinAt_renyiDiv_of_isProbabilityMeasure ha ha0 ha1.ne' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ne_top_of_le_ne_top hb_top (renyiDiv_le_renyiDiv_of_le ht.1 ht.2)
  · exact (continuousOn_integral_rpow_rnDeriv hb_int a ⟨ha0, ha.2⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Ioi 0, isOpen_Ioi, ha0, fun x hx ↦ ⟨hx.1, hx.2.2⟩⟩)

end Probability

/-- For finite measures with `μ ≠ 0`, `Rₐ(μ, ν) → R₁(μ, ν)` as `a → 1⁻`. -/
theorem tendsto_renyiDiv_nhdsLT_one [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ] :
    Tendsto (fun a ↦ renyiDiv a μ ν) (𝓝[<] 1) (𝓝 (renyiDiv 1 μ ν)) := by
  have h_mem : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  rcases eq_zero_or_neZero ν with rfl | hν
  · rw [renyiDiv_zero_measure_right zero_le_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h_mem] with a ha
    rw [renyiDiv_zero_measure_right ha.1.le]
  rw [renyiDiv_eq_renyiDiv_inv_smul zero_le_one]
  refine tendsto_renyiDiv_nhdsLT_one_of_isProbabilityMeasure.congr' ?_
  filter_upwards [h_mem] with a ha
  exact (renyiDiv_eq_renyiDiv_inv_smul ha.1.le).symm

/-- For finite measures with `μ ≠ 0`, if `R_b(μ, ν) < ∞` for some `b > 1`, then
`Rₐ(μ, ν) → R₁(μ, ν)` as `a → 1⁺`. -/
theorem tendsto_renyiDiv_nhdsGT_one [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ]
    (hb : 1 < b) (hb_top : renyiDiv b μ ν ≠ ∞) :
    Tendsto (fun a ↦ renyiDiv a μ ν) (𝓝[>] 1) (𝓝 (renyiDiv 1 μ ν)) := by
  have h_mem : Ioi (0 : ℝ) ∈ 𝓝[>] (1 : ℝ) := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)
  rcases eq_zero_or_neZero ν with rfl | hν
  · rw [renyiDiv_zero_measure_right zero_le_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h_mem] with a ha
    rw [renyiDiv_zero_measure_right (le_of_lt ha)]
  rw [renyiDiv_eq_renyiDiv_inv_smul zero_le_one]
  rw [renyiDiv_eq_renyiDiv_inv_smul (by linarith)] at hb_top
  refine (tendsto_renyiDiv_nhdsGT_one_of_isProbabilityMeasure hb hb_top).congr' ?_
  filter_upwards [h_mem] with a ha
  exact (renyiDiv_eq_renyiDiv_inv_smul (le_of_lt ha)).symm

/-- For finite measures with `μ ≠ 0`, `a ↦ Rₐ(μ, ν)` is continuous on `[0, 1]`. -/
theorem continuousOn_renyiDiv_Icc [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ] :
    ContinuousOn (fun a ↦ renyiDiv a μ ν) (Icc 0 1) := by
  rcases eq_zero_or_neZero ν with rfl | hν
  · exact continuousOn_const.congr fun a ha ↦ renyiDiv_zero_measure_right ha.1 μ
  exact continuousOn_renyiDiv_Icc_of_isProbabilityMeasure.congr
    fun a ha ↦ renyiDiv_eq_renyiDiv_inv_smul ha.1

/-- For finite measures with `μ ≠ 0`, if `R_b(μ, ν) < ∞`, then `a ↦ Rₐ(μ, ν)` is continuous on
`[0, b]`. Since `Rₐ(μ, ν) < ∞` for all `a ∈ [0, b]` by monotonicity, this gives continuity on the
set of orders `a ≥ 0` with `Rₐ(μ, ν) < ∞`, an interval `[0, s)` or `[0, s]`. -/
theorem continuousOn_renyiDiv_Icc_of_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ]
    (hb_top : renyiDiv b μ ν ≠ ∞) :
    ContinuousOn (fun a ↦ renyiDiv a μ ν) (Icc 0 b) := by
  rcases lt_or_ge b 0 with hb0 | hb0
  · simp [Icc_eq_empty_of_lt hb0]
  rcases eq_zero_or_neZero ν with rfl | hν
  · exact continuousOn_const.congr fun a ha ↦ renyiDiv_zero_measure_right ha.1 μ
  rw [renyiDiv_eq_renyiDiv_inv_smul hb0] at hb_top
  exact (continuousOn_renyiDiv_Icc_of_ne_top_of_isProbabilityMeasure hb_top).congr
    fun a ha ↦ renyiDiv_eq_renyiDiv_inv_smul ha.1

end ProbabilityTheory
