/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Statlib.Divergence.FDiv.Basic
public import Statlib.Divergence.StatInfo.Basic

/-!
# Total variation distance, statistical information and f-divergences

Mathlib's total variation distance `MeasureTheory.tvDist μ ν` (and its `ℝ≥0∞`-valued version
`MeasureTheory.etvDist μ ν`) is, up to a factor `2` and a correction for the difference of the
masses of `μ` and `ν`, the statistical information `statInfo μ ν (boolMeasure 1 1)` for the prior
`(1, 1)` (the counting measure on `Bool`). We use this to transfer results about the statistical
information to the total variation distance.

## Main definitions

* `tvDivFun`: the `DivFunction` `x ↦ |1 - x|`.

## Main statements

* `tvDist_eq_two_mul_toReal_statInfo_add_abs`: for finite measures,
  `tvDist μ ν = 2 * (statInfo μ ν (boolMeasure 1 1)).toReal + |μ.real univ - ν.real univ|`.
* `etvDist_eq_two_mul_statInfo`, `tvDist_eq_two_mul_toReal_statInfo`: for finite measures with the
  same mass, in particular for probability measures, the total variation distance is twice the
  statistical information for the prior `(1, 1)`.
* `bayesBinaryRisk_one_one_eq_add_sub_etvDist_div_two`: for finite measures, the Bayes binary risk
  for the prior `(1, 1)` is `(μ(𝒳) + ν(𝒳) - etvDist μ ν) / 2`.
  `bayesBinaryRisk_one_one_eq_ofReal_one_sub_tvDist_div_two` is the case of probability measures.
* `tvDist_comp_le`, `etvDist_comp_le`: **data processing inequality** for the total variation
  distance. `tvDist_map_le`, `etvDist_map_le` are its versions for measurable maps, and
  `tvDist_boolMeasure_le`, `etvDist_boolMeasure_le` its applications to the indicator of an event.
* `lintegral_one_sub_rnDeriv_eq_etvDist_div_two`: for finite measures with the same mass,
  `∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = etvDist μ ν / 2`.
* `fDiv_tvDivFun`: for finite measures, `etvDist μ ν` is the f-divergence for the function
  `tvDivFun = x ↦ |1 - x|`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds), where the total variation distance was
defined as the statistical information for the prior `(1, 1)`.
-/

@[expose] public section

open MeasureTheory Filter Set

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳}

/-- The total variation distance in terms of the statistical information for the prior `(1, 1)`. -/
lemma tvDist_eq_two_mul_toReal_statInfo_add_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν
      = 2 * (statInfo μ ν (Measure.boolMeasure 1 1)).toReal + |μ.real .univ - ν.real .univ| := by
  rw [toReal_statInfo_eq_integral_abs, tvDist_eq_integral_abs_rnDeriv_add_singularPart]
  simp only [Measure.boolMeasure_apply_false, Measure.boolMeasure_apply_true, one_mul,
    ENNReal.toReal_one, Measure.real, abs_sub_comm _ (1 : ℝ)]
  ring

/-- For finite measures with the same mass, in particular probability measures, the total variation
distance is twice the statistical information for the prior `(1, 1)`. -/
lemma tvDist_eq_two_mul_toReal_statInfo [IsFiniteMeasure μ] (h : μ .univ = ν .univ) :
    tvDist μ ν = 2 * (statInfo μ ν (Measure.boolMeasure 1 1)).toReal := by
  have : IsFiniteMeasure ν := ⟨h ▸ measure_lt_top μ _⟩
  rw [tvDist_eq_two_mul_toReal_statInfo_add_abs, measureReal_def, h, ← measureReal_def, sub_self,
    abs_zero, add_zero]

/-- For finite measures with the same mass, in particular probability measures, the total variation
distance is twice the statistical information for the prior `(1, 1)`. -/
lemma etvDist_eq_two_mul_statInfo [IsFiniteMeasure μ] (h : μ .univ = ν .univ) :
    etvDist μ ν = 2 * statInfo μ ν (Measure.boolMeasure 1 1) := by
  have : IsFiniteMeasure ν := ⟨h ▸ measure_lt_top μ _⟩
  rw [← ofReal_tvDist, tvDist_eq_two_mul_toReal_statInfo h, ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal (statInfo_ne_top _ _ _)]

/-- For finite measures, the Bayes binary risk for the prior `(1, 1)` is
`(μ(𝒳) + ν(𝒳) - etvDist μ ν) / 2`. -/
lemma bayesBinaryRisk_one_one_eq_add_sub_etvDist_div_two (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    bayesBinaryRisk μ ν (Measure.boolMeasure 1 1) = (μ .univ + ν .univ - etvDist μ ν) / 2 := by
  have hB_le : bayesBinaryRisk μ ν (Measure.boolMeasure 1 1) ≤ min (μ .univ) (ν .univ) := by
    simpa using bayesBinaryRisk_le_min μ ν (Measure.boolMeasure 1 1)
  have h_tv := tvDist_eq_two_mul_toReal_statInfo_add_abs μ ν
  rw [statInfo_eq_min_sub] at h_tv
  simp only [Measure.boolMeasure_apply_false, Measure.boolMeasure_apply_true, one_mul] at h_tv
  rw [ENNReal.toReal_sub_of_le hB_le (ne_top_of_le_ne_top (measure_ne_top μ _) (min_le_left _ _)),
    ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def] at h_tv
  -- compare the real parts of both sides
  rw [← ENNReal.toReal_eq_toReal_iff' (bayesBinaryRisk_ne_top μ ν _) (by finiteness),
    ENNReal.toReal_div, ENNReal.toReal_sub_of_le etvDist_le_add (by finiteness),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, ← tvDist, h_tv, ENNReal.toReal_ofNat, ← max_sub_min_eq_abs',
    ← min_add_max (μ.real .univ) (ν.real .univ)]
  ring

/-- For probability measures, the Bayes binary risk for the prior `(1, 1)` is `1 - TV(μ, ν)`, where
`TV(μ, ν) = tvDist μ ν / 2`. -/
lemma bayesBinaryRisk_one_one_eq_ofReal_one_sub_tvDist_div_two (μ ν : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    bayesBinaryRisk μ ν (Measure.boolMeasure 1 1) = ENNReal.ofReal (1 - tvDist μ ν / 2) := by
  rw [bayesBinaryRisk_one_one_eq_add_sub_etvDist_div_two, measure_univ, measure_univ,
    one_add_one_eq_two, ← ofReal_tvDist, sub_div' two_ne_zero, one_mul,
    ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_sub _ tvDist_nonneg, ENNReal.ofReal_ofNat]

/-- **Data processing inequality** for the total variation distance. -/
lemma tvDist_comp_le (μ ν : Measure 𝒳) (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [tvDist_eq_two_mul_toReal_statInfo_add_abs, tvDist_eq_two_mul_toReal_statInfo_add_abs]
    simp only [measureReal_def, Measure.comp_apply_univ]
    gcongr
    · exact statInfo_ne_top _ _ _
    · exact statInfo_comp_le μ ν _ κ
  · have h_comp : ¬ (IsFiniteMeasure (κ ∘ₘ μ) ∧ IsFiniteMeasure (κ ∘ₘ ν)) := by
      rwa [isFiniteMeasure_iff (μ := κ ∘ₘ μ), isFiniteMeasure_iff (μ := κ ∘ₘ ν),
        Measure.comp_apply_univ, Measure.comp_apply_univ, ← isFiniteMeasure_iff,
        ← isFiniteMeasure_iff]
    rw [tvDist_of_not_isFiniteMeasure h_comp]
    exact tvDist_nonneg

/-- **Data processing inequality** for the total variation distance and a measurable map. -/
lemma tvDist_map_le (μ ν : Measure 𝒳) {g : 𝒳 → 𝒳'} (hg : Measurable g) :
    tvDist (μ.map g) (ν.map g) ≤ tvDist μ ν := by
  simpa [Measure.deterministic_comp_eq_map hg] using tvDist_comp_le μ ν (Kernel.deterministic g hg)

/-- **Data processing inequality** for the total variation distance, applied to the indicator of an
event `E`: the distance between the laws of `x ↦ decide (x ∈ E)` under `μ` and `ν` is at most
`tvDist μ ν`. For probability measures, those laws are the Bernoulli distributions with means
`μ E` and `ν E`. -/
lemma tvDist_boolMeasure_le (μ ν : Measure 𝒳) {E : Set 𝒳} (hE : MeasurableSet E) :
    tvDist (Measure.boolMeasure (μ Eᶜ) (μ E)) (Measure.boolMeasure (ν Eᶜ) (ν E))
      ≤ tvDist μ ν := by
  classical
  rw [← Measure.map_decide_mem_eq_boolMeasure μ hE, ← Measure.map_decide_mem_eq_boolMeasure ν hE]
  exact tvDist_map_le μ ν (measurable_decide_mem hE)

/-- **Data processing inequality** for the total variation distance. -/
lemma etvDist_comp_le (μ ν : Measure 𝒳) (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    etvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [← ofReal_tvDist, ← ofReal_tvDist]
    exact ENNReal.ofReal_le_ofReal (tvDist_comp_le μ ν κ)
  · rw [etvDist_of_not_isFiniteMeasure h]
    exact le_top

/-- **Data processing inequality** for the total variation distance and a measurable map. -/
lemma etvDist_map_le (μ ν : Measure 𝒳) {g : 𝒳 → 𝒳'} (hg : Measurable g) :
    etvDist (μ.map g) (ν.map g) ≤ etvDist μ ν := by
  simpa [Measure.deterministic_comp_eq_map hg] using etvDist_comp_le μ ν (Kernel.deterministic g hg)

/-- **Data processing inequality** for the total variation distance, applied to the indicator of an
event `E`: the distance between the laws of `x ↦ decide (x ∈ E)` under `μ` and `ν` is at most
`etvDist μ ν`. For probability measures, those laws are the Bernoulli distributions with means
`μ E` and `ν E`. -/
lemma etvDist_boolMeasure_le (μ ν : Measure 𝒳) {E : Set 𝒳} (hE : MeasurableSet E) :
    etvDist (Measure.boolMeasure (μ Eᶜ) (μ E)) (Measure.boolMeasure (ν Eᶜ) (ν E))
      ≤ etvDist μ ν := by
  classical
  rw [← Measure.map_decide_mem_eq_boolMeasure μ hE, ← Measure.map_decide_mem_eq_boolMeasure ν hE]
  exact etvDist_map_le μ ν (measurable_decide_mem hE)

/-- For the prior `(1, 1)`, the statistical information is `∫⁻ x, 1 - (∂μ/∂ν) x ∂ν`, provided that
`ν` has at most the mass of `μ`. -/
lemma lintegral_one_sub_rnDeriv_eq_statInfo [IsFiniteMeasure μ] (h : ν .univ ≤ μ .univ) :
    ∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = statInfo μ ν (Measure.boolMeasure 1 1) := by
  have : IsFiniteMeasure ν := ⟨h.trans_lt (measure_lt_top μ _)⟩
  simp [statInfo_eq_lintegral_of_ge (π := Measure.boolMeasure 1 1) (by simpa using h)]

/-- For finite measures with the same mass, in particular probability measures,
`∫⁻ x, 1 - (∂μ/∂ν) x ∂ν` is half the total variation distance. -/
lemma lintegral_one_sub_rnDeriv_eq_etvDist_div_two [IsFiniteMeasure μ] (h : μ .univ = ν .univ) :
    ∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = etvDist μ ν / 2 := by
  rw [lintegral_one_sub_rnDeriv_eq_statInfo h.ge, etvDist_eq_two_mul_statInfo h, mul_comm,
    ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

section FDiv

/-! ### The total variation distance as an f-divergence -/

/-- The `DivFunction` `x ↦ |1 - x|`. Its f-divergence is the total variation distance
(`fDiv_tvDivFun`). -/
noncomputable def tvDivFun : DivFunction :=
  DivFunction.ofReal (fun x ↦ |1 - x|)
    ((convexOn_dist (1 : ℝ) (convex_Ioi 0)).congr fun x _ ↦ abs_sub_comm x 1)
    (by simp)

lemma tvDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) : tvDivFun x = ENNReal.ofReal |1 - x.toReal| :=
  DivFunction.ofReal_apply_of_continuousWithinAt
    (continuous_abs.comp (continuous_sub_left 1)).continuousWithinAt hx

@[simp] lemma tvDivFun_zero : tvDivFun 0 = 1 := by simp [tvDivFun_apply]

@[simp]
lemma tvDivFun_apply_top : tvDivFun ∞ = ∞ := by
  refine DivFunction.ofReal_apply_top_of_tendsto_atTop ?_
  have h : Tendsto (fun x : ℝ ↦ x - 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  exact (tendsto_abs_atTop_atTop.comp h).congr fun x ↦ by simp [abs_sub_comm]

@[simp] lemma derivAtTop_tvDivFun : tvDivFun.derivAtTop = 1 := by
  -- for `x > 1`, the derivative of `y ↦ |1 - y|` at `x` is `1`
  have h : Tendsto (fun x ↦ derivWithin (fun y : ℝ ↦ |1 - y|) (Ioi x) x) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have h_eq : (fun y : ℝ ↦ |1 - y|) =ᶠ[𝓝 x] fun y ↦ y - 1 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      rw [abs_of_neg (sub_neg.mpr hy), neg_sub]
    exact ((((hasDerivAt_id' x).sub_const 1).congr_of_eventuallyEq h_eq).hasDerivWithinAt
      |>.derivWithin (uniqueDiffWithinAt_Ioi x)).symm
  rw [tvDivFun, DivFunction.derivAtTop_ofReal_of_tendsto_nhds h, ENNReal.ofReal_one]

/-- The total variation distance between finite measures is the f-divergence for the function
`x ↦ |1 - x|`. -/
lemma fDiv_tvDivFun (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv tvDivFun μ ν = etvDist μ ν := by
  rw [fDiv, derivAtTop_tvDivFun, one_mul, etvDist_eq_lintegral_eNorm_rnDeriv_add_singularPart]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  rw [tvDivFun_apply hx, ← Real.norm_eq_abs, ofReal_norm]

end FDiv

end ProbabilityTheory
