/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.TotalVariation

/-!
# Integral forms of the total variation distance

Mathlib's `tvDist μ ν` is the total variation norm of `μ - ν`. Mathlib gives its expression in
terms of the Radon-Nikodym derivative `∂μ/∂ν` and of the singular part of `μ` with respect to `ν`
(`tvDist_eq_integral_abs_rnDeriv_add_singularPart`). We give other integral forms, and the
variational formula as a supremum over functions bounded by `1`.

## Main statements

* `tvDist_eq_add_sub_two_mul_integral_min`: for any measure `ζ` dominating `μ` and `ν`,
  `tvDist μ ν = μ(𝒳) + ν(𝒳) - 2 * ∫ min (∂μ/∂ζ) (∂ν/∂ζ) ∂ζ`.
* `tvDist_eq_integral_abs_sub_rnDeriv`: for any measure `ζ` dominating `μ` and `ν`,
  `tvDist μ ν = ∫ |∂μ/∂ζ - ∂ν/∂ζ| ∂ζ`.
* `tvDist_eq_two_mul_integral_max_one_sub_add`, `tvDist_eq_two_mul_integral_max_sub_one_add`:
  one-sided integral forms with respect to `ν`.
* `integral_sub_integral_le_tvDist`: for `f` with `|f| ≤ 1` (almost everywhere),
  `∫ f ∂μ - ∫ f ∂ν ≤ tvDist μ ν`.
* `tvDist_eq_iSup_integral_sub`: the total variation distance is the supremum of
  `∫ f ∂μ - ∫ f ∂ν` over measurable functions with `|f| ≤ 1`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν ζ : Measure 𝒳}

/-- For finite measures `μ, ν` and any measure `ζ` with `μ ≪ ζ` and `ν ≪ ζ`,
`tvDist μ ν = μ(𝒳) + ν(𝒳) - 2 * ∫ min (∂μ/∂ζ) (∂ν/∂ζ) ∂ζ`. -/
theorem tvDist_eq_add_sub_two_mul_integral_min [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    tvDist μ ν = μ.real univ + ν.real univ
      - 2 * ∫ x, min ((∂μ/∂ζ) x).toReal ((∂ν/∂ζ) x).toReal ∂ζ := by
  have h_stat := statInfo_eq_min_sub_lintegral' (Measure.boolMeasure 1 1) hμζ hνζ
  simp only [Measure.boolMeasure_apply_false, Measure.boolMeasure_apply_true, one_mul] at h_stat
  have h_le : ∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ ≤ min (μ univ) (ν univ) := by
    refine le_min ?_ ?_
    · exact (lintegral_mono fun _ ↦ min_le_left _ _).trans_eq (Measure.lintegral_rnDeriv hμζ)
    · exact (lintegral_mono fun _ ↦ min_le_right _ _).trans_eq (Measure.lintegral_rnDeriv hνζ)
  have h_int : (∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ).toReal
      = ∫ x, min ((∂μ/∂ζ) x).toReal ((∂ν/∂ζ) x).toReal ∂ζ := by
    rw [← integral_toReal
      ((Measure.measurable_rnDeriv μ ζ).min (Measure.measurable_rnDeriv ν ζ)).aemeasurable]
    · refine integral_congr_ae ?_
      filter_upwards [Measure.rnDeriv_lt_top μ ζ, Measure.rnDeriv_lt_top ν ζ] with x hμ hν
      exact ENNReal.toReal_min hμ.ne hν.ne
    · filter_upwards [Measure.rnDeriv_lt_top μ ζ] with x hx using (min_le_left _ _).trans_lt hx
  rw [tvDist_eq_two_mul_toReal_statInfo_add_abs, h_stat,
    ENNReal.toReal_sub_of_le h_le (by simp), h_int,
    ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, ← max_sub_min_eq_abs', ← min_add_max (μ.real univ) (ν.real univ)]
  ring

/-- For finite measures `μ, ν` and any measure `ζ` with `μ ≪ ζ` and `ν ≪ ζ`,
`tvDist μ ν = ∫ |∂μ/∂ζ - ∂ν/∂ζ| ∂ζ`. -/
theorem tvDist_eq_integral_abs_sub_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    tvDist μ ν = ∫ x, |((∂μ/∂ζ) x).toReal - ((∂ν/∂ζ) x).toReal| ∂ζ := by
  have hp : Integrable (fun x ↦ ((∂μ/∂ζ) x).toReal) ζ := Measure.integrable_toReal_rnDeriv
  have hq : Integrable (fun x ↦ ((∂ν/∂ζ) x).toReal) ζ := Measure.integrable_toReal_rnDeriv
  have h_min : Integrable (fun x ↦ min ((∂μ/∂ζ) x).toReal ((∂ν/∂ζ) x).toReal) ζ := hp.inf hq
  have h_abs : ∀ x, |((∂μ/∂ζ) x).toReal - ((∂ν/∂ζ) x).toReal|
      = ((∂μ/∂ζ) x).toReal + ((∂ν/∂ζ) x).toReal
        - 2 * min ((∂μ/∂ζ) x).toReal ((∂ν/∂ζ) x).toReal := fun x ↦ by
    rw [← max_sub_min_eq_abs', ← min_add_max ((∂μ/∂ζ) x).toReal]
    ring
  have h_add : Integrable (fun x ↦ ((∂μ/∂ζ) x).toReal + ((∂ν/∂ζ) x).toReal) ζ := hp.add hq
  simp_rw [h_abs]
  rw [integral_sub h_add (h_min.const_mul 2), integral_add hp hq, integral_const_mul,
    Measure.integral_toReal_rnDeriv hμζ, Measure.integral_toReal_rnDeriv hνζ,
    tvDist_eq_add_sub_two_mul_integral_min hμζ hνζ]

/-- One-sided integral form of the total variation distance:
`tvDist μ ν = 2 * ∫ max 0 (1 - ∂μ/∂ν) ∂ν + μ(𝒳) - ν(𝒳)`. -/
theorem tvDist_eq_two_mul_integral_max_one_sub_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = 2 * ∫ x, max 0 (1 - ((∂μ/∂ν) x).toReal) ∂ν + μ.real univ - ν.real univ := by
  have hr : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal) ν := Measure.integrable_toReal_rnDeriv
  have h1 : Integrable (fun x ↦ 1 - ((∂μ/∂ν) x).toReal) ν := (integrable_const 1).sub hr
  have h_abs : ∀ x, |1 - ((∂μ/∂ν) x).toReal|
      = 2 * max 0 (1 - ((∂μ/∂ν) x).toReal) - (1 - ((∂μ/∂ν) x).toReal) := by
    intro x
    rcases le_total 0 (1 - ((∂μ/∂ν) x).toReal) with h | h
    · rw [max_eq_right h, abs_of_nonneg h]
      ring
    · rw [max_eq_left h, abs_of_nonpos h]
      ring
  have h_pos : Integrable (fun x ↦ max 0 (1 - ((∂μ/∂ν) x).toReal)) ν := by
    simpa only [max_comm] using h1.pos_part
  rw [tvDist_eq_integral_abs_rnDeriv_add_singularPart]
  simp_rw [h_abs]
  rw [integral_sub (h_pos.const_mul 2) h1, integral_const_mul,
    integral_sub (integrable_const 1) hr, Measure.integral_toReal_rnDeriv', integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

/-- One-sided integral form of the total variation distance:
`tvDist μ ν = 2 * (∫ max 0 (∂μ/∂ν - 1) ∂ν + μ⟂ν(𝒳)) + ν(𝒳) - μ(𝒳)`. -/
theorem tvDist_eq_two_mul_integral_max_sub_one_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = 2 * (∫ x, max 0 (((∂μ/∂ν) x).toReal - 1) ∂ν + (μ.singularPart ν).real univ)
      + ν.real univ - μ.real univ := by
  have hr : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal) ν := Measure.integrable_toReal_rnDeriv
  have h1 : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal - 1) ν := hr.sub (integrable_const 1)
  have h_abs : ∀ x, |1 - ((∂μ/∂ν) x).toReal|
      = 2 * max 0 (((∂μ/∂ν) x).toReal - 1) - (((∂μ/∂ν) x).toReal - 1) := by
    intro x
    rcases le_total 0 (((∂μ/∂ν) x).toReal - 1) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      ring
  have h_pos : Integrable (fun x ↦ max 0 (((∂μ/∂ν) x).toReal - 1)) ν := by
    simpa only [max_comm] using h1.pos_part
  rw [tvDist_eq_integral_abs_rnDeriv_add_singularPart]
  simp_rw [h_abs]
  rw [integral_sub (h_pos.const_mul 2) h1, integral_const_mul,
    integral_sub hr (integrable_const 1), Measure.integral_toReal_rnDeriv', integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

/-! ### Variational formula -/

/-- For a function `f` with `|f| ≤ 1` almost everywhere with respect to `μ` and `ν`,
`∫ f ∂μ - ∫ f ∂ν ≤ tvDist μ ν`. -/
theorem integral_sub_integral_le_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : 𝒳 → ℝ}
    (hf : AEStronglyMeasurable f (μ + ν)) (hf_le : ∀ᵐ x ∂(μ + ν), |f x| ≤ 1) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ tvDist μ ν := by
  have hμζ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνζ : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hf_int (ξ : Measure 𝒳) [IsFiniteMeasure ξ] (hξ : ξ ≪ μ + ν) : Integrable f ξ := by
    refine Integrable.of_bound (hf.mono_ac hξ) 1 ?_
    filter_upwards [hξ.ae_le hf_le] with x hx using by simpa using hx
  have hμ_int := (integrable_rnDeriv_smul_iff hμζ).mpr (hf_int μ hμζ)
  have hν_int := (integrable_rnDeriv_smul_iff hνζ).mpr (hf_int ν hνζ)
  rw [← integral_rnDeriv_smul hμζ, ← integral_rnDeriv_smul hνζ, ← integral_sub hμ_int hν_int,
    tvDist_eq_integral_abs_sub_rnDeriv hμζ hνζ]
  refine integral_mono_ae (hμ_int.sub hν_int)
    (Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv).abs ?_
  filter_upwards [hf_le] with x hx
  simp only [smul_eq_mul, ← sub_mul]
  exact (le_abs_self _).trans ((abs_mul _ _).trans_le (mul_le_of_le_one_right (abs_nonneg _) hx))

/-- **Variational formula** for the total variation distance: `tvDist μ ν` is the supremum of
`∫ f ∂μ - ∫ f ∂ν` over measurable functions `f` with `|f| ≤ 1`. -/
theorem tvDist_eq_iSup_integral_sub [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = ⨆ f : {f : 𝒳 → ℝ // Measurable f ∧ ∀ x, |f x| ≤ 1},
      (∫ x, f.val x ∂μ - ∫ x, f.val x ∂ν) := by
  have h_bdd : BddAbove (range fun f : {f : 𝒳 → ℝ // Measurable f ∧ ∀ x, |f x| ≤ 1} ↦
      ∫ x, f.val x ∂μ - ∫ x, f.val x ∂ν) := by
    refine ⟨tvDist μ ν, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact integral_sub_integral_le_tvDist f.property.1.aestronglyMeasurable
      (ae_of_all _ f.property.2)
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine le_antisymm ?_ ?_
  · -- the supremum is attained at `f = 1` on `sᶜ` and `f = -1` on `s`
    let f : 𝒳 → ℝ := fun x ↦ sᶜ.indicator (fun _ ↦ (1 : ℝ)) x - s.indicator (fun _ ↦ 1) x
    have hf_meas : Measurable f :=
      ((measurable_const.indicator hs.measurableSet.compl).sub
        (measurable_const.indicator hs.measurableSet))
    have hf_le : ∀ x, |f x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ s <;> simp [f, hx]
    refine le_ciSup_of_le h_bdd ⟨f, hf_meas, hf_le⟩ (le_of_eq ?_)
    have h_int (ξ : Measure 𝒳) [IsFiniteMeasure ξ] :
        ∫ x, f x ∂ξ = ξ.real sᶜ - ξ.real s := by
      rw [integral_sub ((integrable_const 1).indicator hs.measurableSet.compl)
        ((integrable_const 1).indicator hs.measurableSet),
        integral_indicator_const _ hs.measurableSet.compl,
        integral_indicator_const _ hs.measurableSet, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    rw [h_int μ, h_int ν, hs.tvDist_eq]
    ring
  · have : Nonempty {f : 𝒳 → ℝ // Measurable f ∧ ∀ x, |f x| ≤ 1} :=
      ⟨⟨0, measurable_const, fun _ ↦ by simp⟩⟩
    exact ciSup_le fun f ↦
      integral_sub_integral_le_tvDist f.property.1.aestronglyMeasurable
        (ae_of_all _ f.property.2)

end ProbabilityTheory
