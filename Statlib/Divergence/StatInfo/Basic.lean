/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Risk.RiskIncrease
public import Statlib.ForMathlib.ENNReal
public import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Statlib.Testing.Binary

/-!
# Statistical information

The statistical information of two measures `μ` and `ν` with respect to a prior `π` on `Bool` is
the decrease of the Bayes risk of the simple binary hypothesis testing problem between `μ` and `ν`
obtained by observing the data. It is a divergence between `μ` and `ν` which satisfies the
data-processing inequality. The total variation distance is a statistical information (see
`Statlib.Divergence.TotalVariation`), and every f-divergence is an integral of statistical
informations (Liese and Vajda, see `Statlib.Divergence.FDiv.IntegralRepresentation`).

## Main definitions

* `statInfo μ ν π`: the statistical information of the measures `μ` and `ν` with respect to the
  prior `π` on `Bool`, the difference between the Bayes risks of the testing problem without and
  with observations.

## Main statements

* `statInfo_eq_statInfo_one_one`: the statistical information for a prior `π` is the statistical
  information for the prior `(1, 1)` of the measures weighted by `π`.
* `statInfo_smul_prior`: the statistical information is positively homogeneous in the prior.
* `statInfo_comp_le`: **data-processing inequality** for the statistical information.
* `statInfo_eq_lintegral_add_of_le`, `statInfo_eq_lintegral_of_ge`: the statistical information as
  an integral with respect to `ν`, plus a contribution of the singular part of `μ`.
* `toReal_statInfo_eq_integral_max_of_le`, `toReal_statInfo_eq_integral_max_of_ge`,
  `toReal_statInfo_eq_integral_abs`: integral forms of the statistical information.

## References

* M. H. DeGroot, *Uncertainty, information, and sequential experiments*, Ann. Math. Statist. 33
  (1962).
* F. Liese, I. Vajda, *On divergences and informations in statistics and information theory*,
  IEEE Trans. Inform. Theory 52 (2006).

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {π : Measure Bool}

/-- The statistical information of the measures `μ` and `ν` with respect to the prior `π` on
`Bool`: the increase of the Bayes risk of the binary testing problem between `μ` and `ν` when the
observation is discarded. -/
noncomputable
def statInfo (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  riskIncrease zeroOneLoss (Kernel.boolKernel μ ν) π

lemma statInfo_eq_riskIncrease (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π = riskIncrease zeroOneLoss (Kernel.boolKernel μ ν) π := rfl

lemma statInfo_eq_min_sub (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ) - bayesBinaryRisk μ ν π := by
  rw [statInfo, riskIncrease_eq_iInf_sub' measurable_zeroOneLoss, iInf_bool_eq]
  simp [lintegral_bool, bayesBinaryRisk, mul_comm]

/-- The statistical information for a prior `π` is the statistical information for the prior
`(1, 1)` (the counting measure on `Bool`) of the measures weighted by `π`. -/
lemma statInfo_eq_statInfo_one_one (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π = statInfo (π {false} • μ) (π {true} • ν) (Measure.boolMeasure 1 1) := by
  rw [statInfo_eq_min_sub, statInfo_eq_min_sub, bayesBinaryRisk_eq_bayesBinaryRisk_one_one]
  simp

/-- The statistical information is positively homogeneous in the prior: scaling the prior by a
finite factor scales the statistical information by the same factor. -/
lemma statInfo_smul_prior (μ ν : Measure 𝒳) (π : Measure Bool) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    statInfo μ ν (c • π) = c * statInfo μ ν π := by
  rw [statInfo_eq_min_sub, statInfo_eq_min_sub, bayesBinaryRisk_smul_prior μ ν π hc,
    smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc, mul_assoc,
    ← mul_min, ENNReal.mul_sub fun _ _ ↦ hc]

@[simp] lemma statInfo_zero_left : statInfo 0 ν π = 0 := by simp [statInfo_eq_min_sub]

@[simp] lemma statInfo_zero_right : statInfo μ 0 π = 0 := by simp [statInfo_eq_min_sub]

@[simp] lemma statInfo_zero_prior : statInfo μ ν 0 = 0 := by simp [statInfo_eq_min_sub]

@[simp] lemma statInfo_self : statInfo μ μ π = 0 := by
  simp [statInfo_eq_min_sub, min_mul_mul_right]

lemma statInfo_le_min (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π ≤ min (π {false} * μ univ) (π {true} * ν univ) :=
  statInfo_eq_min_sub μ ν π ▸ tsub_le_self

lemma statInfo_ne_top (μ ν : Measure 𝒳) [IsFiniteMeasure μ] (π : Measure Bool)
    [IsFiniteMeasure π] :
    statInfo μ ν π ≠ ∞ :=
  ((statInfo_le_min μ ν π).trans_lt <| min_lt_iff.mpr <| Or.inl
    <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)).ne

lemma statInfo_symm : statInfo μ ν π = statInfo ν μ (π.map Bool.not) := by
  have h_false : π.map Bool.not {false} = π {true} := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    simp [Set.preimage]
  have h_true : π.map Bool.not {true} = π {false} := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    simp [Set.preimage]
  rw [statInfo_eq_min_sub, statInfo_eq_min_sub, bayesBinaryRisk_symm μ ν π, h_false, h_true,
    min_comm]

lemma statInfo_of_measure_true_eq_zero (μ ν : Measure 𝒳) (hπ : π {true} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm ((statInfo_le_min μ ν π).trans (by simp [hπ])) zero_le

lemma statInfo_of_measure_false_eq_zero (μ ν : Measure 𝒳) (hπ : π {false} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm ((statInfo_le_min μ ν π).trans (by simp [hπ])) zero_le

/-- **Data processing inequality** for the statistical information. -/
lemma statInfo_comp_le (μ ν : Measure 𝒳) (π : Measure Bool) (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    statInfo (η ∘ₘ μ) (η ∘ₘ ν) π ≤ statInfo μ ν π := by
  simpa [statInfo, Kernel.comp_boolKernel]
    using riskIncrease_comp_le zeroOneLoss (Kernel.boolKernel μ ν) π η

/-- **Data processing inequality** for the statistical information, applied to the indicator of an
event `E`. -/
lemma statInfo_boolMeasure_le (μ ν : Measure 𝒳) (π : Measure Bool) {E : Set 𝒳}
    (hE : MeasurableSet E) :
    statInfo (Measure.boolMeasure (μ Eᶜ) (μ E)) (Measure.boolMeasure (ν Eᶜ) (ν E)) π
      ≤ statInfo μ ν π := by
  classical
  have h := statInfo_comp_le μ ν π (Kernel.deterministic _ (measurable_decide_mem hE))
  rwa [Measure.deterministic_comp_eq_map, Measure.deterministic_comp_eq_map,
    Measure.map_decide_mem_eq_boolMeasure μ hE, Measure.map_decide_mem_eq_boolMeasure ν hE] at h

lemma statInfo_eq_min_sub_lintegral (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_lintegral_min]

lemma statInfo_eq_min_sub_lintegral' {ζ : Measure 𝒳} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (π : Measure Bool) [IsFiniteMeasure π] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * (∂μ/∂ζ) x) (π {true} * (∂ν/∂ζ) x) ∂ζ := by
  by_cases h_false : π {false} = 0
  · simp [statInfo_eq_min_sub, h_false, bayesBinaryRisk_of_measure_false_eq_zero]
  by_cases h_true : π {true} = 0
  · simp [statInfo_eq_min_sub, h_true, bayesBinaryRisk_of_measure_true_eq_zero]
  have hμac : μ ≪ (Kernel.boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_left μ ν h_false
  have hνac : ν ≪ (Kernel.boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_right μ ν h_true
  have hacζ : (Kernel.boolKernel μ ν ∘ₘ π) ≪ ζ :=
    boolKernel_comp_measure _ _ _ ▸ (hνζ.smul_left _).add_left (hμζ.smul_left _)
  rw [statInfo_eq_min_sub_lintegral, ← lintegral_rnDeriv_mul hacζ (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv hμac, Measure.rnDeriv_mul_rnDeriv hνac] with x hxμ hxν
  rw [mul_min, mul_comm, mul_comm _ (π _ * _), mul_assoc, mul_assoc]
  congr

/-- The statistical information `I_{(a, b)}(μ, ν)` for the prior `(a, b)` is a measurable function
of `(a, b)`. -/
lemma measurable_statInfo_boolMeasure_ofReal (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Measurable fun p : ℝ × ℝ ↦
      statInfo μ ν (Measure.boolMeasure (ENNReal.ofReal p.1) (ENNReal.ofReal p.2)) := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have h_eq (p : ℝ × ℝ) :
      statInfo μ ν (Measure.boolMeasure (ENNReal.ofReal p.1) (ENNReal.ofReal p.2))
        = min (ENNReal.ofReal p.1 * μ univ) (ENNReal.ofReal p.2 * ν univ)
          - ∫⁻ x, min (ENNReal.ofReal p.1 * (∂μ/∂(μ + ν)) x)
            (ENNReal.ofReal p.2 * (∂ν/∂(μ + ν)) x) ∂(μ + ν) := by
    simpa using statInfo_eq_min_sub_lintegral'
      (Measure.boolMeasure (ENNReal.ofReal p.1) (ENNReal.ofReal p.2)) hμ hν
  simp_rw [h_eq]
  exact Measurable.sub (by fun_prop) (Measurable.lintegral_prod_right (by fun_prop))

lemma toReal_statInfo_eq_min_sub_integral (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    (statInfo μ ν π).toReal = min (π {false} * μ univ).toReal (π {true} * ν univ).toReal
      - ∫ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
        ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  have hμ : π {false} * μ univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top μ _)
  have hν : π {true} * ν univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top ν _)
  rw [statInfo_eq_min_sub, ENNReal.toReal_sub_of_le (bayesBinaryRisk_le_min μ ν π)]
  swap; · simp only [ne_eq, min_eq_top, hμ, hν, and_self, not_false_eq_true]
  rw [toReal_bayesBinaryRisk_eq_integral_min,
    MonotoneOn.map_min (s := {x : ℝ≥0∞ | x ≠ ∞})
      (fun _ _ _ hb hab ↦ ENNReal.toReal_mono hb hab) hμ hν]

/-- The statistical information as an integral with respect to `ν`, when
`π {false} * μ univ ≤ π {true} * ν univ`. -/
lemma statInfo_eq_lintegral_add_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (h : π {false} * μ univ ≤ π {true} * ν univ) :
    statInfo μ ν π = ∫⁻ x, π {false} * (∂μ/∂ν) x - π {true} ∂ν
      + π {false} * μ.singularPart ν univ := by
  have h_le : ∫⁻ x, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν
      ≤ ∫⁻ x, π {false} * (∂μ/∂ν) x ∂ν := lintegral_mono fun _ ↦ min_le_left _ _
  have h_fin : ∫⁻ x, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ h_le
    rw [lintegral_const_mul _ (μ.measurable_rnDeriv ν)]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (Measure.lintegral_rnDeriv_lt_top μ ν).ne
  rw [statInfo_eq_min_sub, min_eq_left h, bayesBinaryRisk_eq_lintegral_min_rnDeriv,
    ← Measure.singularPart_add_lintegral_rnDeriv μ ν, mul_add,
    ← lintegral_const_mul _ (μ.measurable_rnDeriv ν),
    (ENNReal.cancel_of_ne h_fin).add_tsub_assoc_of_le h_le,
    ← lintegral_sub (by fun_prop) h_fin (ae_of_all _ fun _ ↦ min_le_left _ _), add_comm]
  simp_rw [tsub_min]

/-- The statistical information as an integral with respect to `ν`, when
`π {true} * ν univ ≤ π {false} * μ univ`. -/
lemma statInfo_eq_lintegral_of_ge [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (h : π {true} * ν univ ≤ π {false} * μ univ) :
    statInfo μ ν π = ∫⁻ x, π {true} - π {false} * (∂μ/∂ν) x ∂ν := by
  have h_fin : ∫⁻ x, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun _ ↦ min_le_right _ _)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [statInfo_eq_min_sub, min_eq_right h, bayesBinaryRisk_eq_lintegral_min_rnDeriv,
    ← lintegral_const, ← lintegral_sub (by fun_prop) h_fin (ae_of_all _ fun _ ↦ min_le_right _ _)]
  simp_rw [min_comm _ (π {true}), tsub_min]

/-- Integral form of the statistical information, when `π {false} * μ univ ≤ π {true} * ν univ`. -/
lemma toReal_statInfo_eq_integral_max_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h : π {false} * μ univ ≤ π {true} * ν univ) :
    (statInfo μ ν π).toReal
      = ∫ x, max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal) ∂ν
        + (π {false} * μ.singularPart ν univ).toReal := by
  have h_fin : ∫⁻ x, π {false} * (∂μ/∂ν) x - π {true} ∂ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun _ ↦ tsub_le_self)
    rw [lintegral_const_mul _ (μ.measurable_rnDeriv ν)]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (Measure.lintegral_rnDeriv_lt_top μ ν).ne
  have h_int : ∫ x, max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal) ∂ν
      = (∫⁻ x, π {false} * (∂μ/∂ν) x - π {true} ∂ν).toReal := by
    rw [← integral_toReal (by fun_prop)]
    · refine integral_congr_ae ?_
      filter_upwards [μ.rnDeriv_ne_top ν] with x hx
      rw [ENNReal.toReal_sub_eq_max_zero (by finiteness) (measure_ne_top _ _)]
    · filter_upwards [μ.rnDeriv_ne_top ν] with x hx
      exact tsub_le_self.trans_lt (by finiteness)
  rw [statInfo_eq_lintegral_add_of_le h, ENNReal.toReal_add h_fin (by finiteness), h_int]

/-- Integral form of the statistical information, when `π {true} * ν univ ≤ π {false} * μ univ`. -/
lemma toReal_statInfo_eq_integral_max_of_ge [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h : π {true} * ν univ ≤ π {false} * μ univ) :
    (statInfo μ ν π).toReal
      = ∫ x, max 0 ((π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal) ∂ν := by
  rw [statInfo_eq_lintegral_of_ge h, ← integral_toReal (by fun_prop)]
  · refine integral_congr_ae ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx
    rw [ENNReal.toReal_sub_eq_max_zero (measure_ne_top _ _) (by finiteness)]
  · exact ae_of_all _ fun _ ↦ tsub_le_self.trans_lt (measure_lt_top _ _)

lemma toReal_statInfo_eq_integral_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {π : Measure Bool} [IsFiniteMeasure π] :
    (statInfo μ ν π).toReal
      = 2⁻¹ * (-|(π {false} * μ univ).toReal - (π {true} * ν univ).toReal|
        + ∫ x, |(π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal| ∂ν
        + (π {false} * (μ.singularPart ν) univ).toReal) := by
  rcases le_total (π {false} * μ univ) (π {true} * ν univ) with (h | h)
  · rw [abs_of_nonpos]
    swap
    · refine sub_nonpos.mpr <| (ENNReal.toReal_le_toReal ?_ ?_).mpr h
        <;> simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
    simp_rw [toReal_statInfo_eq_integral_max_of_le h, sup_eq_half_smul_add_add_abs_sub' ℝ,
      smul_eq_mul, zero_add, sub_zero, integral_const_mul]
    calc
      _ = 2⁻¹ * (∫ x, (π {false} * (∂μ/∂ν) x).toReal ∂ν - ∫ _, (π {true}).toReal ∂ν
            + ∫ x, |(π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal| ∂ν)
          + (π {false} * (μ.singularPart ν) univ).toReal := by
        simp_rw [ENNReal.toReal_mul]
        have : Integrable (fun x ↦ (π {false}).toReal * ((∂μ/∂ν) x).toReal - (π {true}).toReal) ν :=
          (Measure.integrable_toReal_rnDeriv.const_mul _).sub (integrable_const _)
        rw [integral_add this this.abs, integral_sub
          (Measure.integrable_toReal_rnDeriv.const_mul _) (integrable_const _)]
      _ = 2⁻¹ * ((π {false} * μ univ).toReal - (π {false} * (μ.singularPart ν) univ).toReal
            - (π {true} * ν univ).toReal
            + ∫ x, |(π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal| ∂ν)
          + (π {false} * (μ.singularPart ν) univ).toReal := by
        congr
        · simp_rw [ENNReal.toReal_mul, integral_const_mul, Measure.integral_toReal_rnDeriv',
          measureReal_def, mul_sub]
        · rw [integral_const, smul_eq_mul, measureReal_def, ENNReal.toReal_mul, mul_comm]
      _ = _ := by ring
  · rw [abs_of_nonneg]
    swap
    · refine sub_nonneg.mpr <| (ENNReal.toReal_le_toReal ?_ ?_).mpr h
        <;> simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
    simp_rw [toReal_statInfo_eq_integral_max_of_ge h, sup_eq_half_smul_add_add_abs_sub' ℝ,
      smul_eq_mul, zero_add, sub_zero, integral_const_mul]
    calc
      _ = 2⁻¹ * (∫ _, (π {true}).toReal ∂ν - ∫ x, (π {false} * (∂μ/∂ν) x).toReal ∂ν
            + ∫ x, |(π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal| ∂ν) := by
        simp_rw [ENNReal.toReal_mul]
        have : Integrable (fun x ↦ (π {true}).toReal - (π {false}).toReal * ((∂μ/∂ν) x).toReal) ν :=
          (integrable_const _).sub (Measure.integrable_toReal_rnDeriv.const_mul _)
        rw [integral_add this this.abs, integral_sub (integrable_const _)
          (Measure.integrable_toReal_rnDeriv.const_mul _)]
      _ = 2⁻¹ * ((π {true} * ν univ).toReal - (π {false} * μ univ).toReal
            + (π {false} * (μ.singularPart ν) univ).toReal
            + ∫ x, |(π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal| ∂ν) := by
        simp_rw [ENNReal.toReal_mul, integral_const_mul, Measure.integral_toReal_rnDeriv',
          measureReal_def, mul_sub]
        rw [integral_const, smul_eq_mul, measureReal_def, ← sub_add, mul_comm (ν univ).toReal]
      _ = _ := by
        simp_rw [abs_sub_comm]
        ring

lemma statInfo_eq_min_sub_iInf_measurableSet (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_iInf_measurableSet]

end ProbabilityTheory
