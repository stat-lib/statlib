/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Statlib.EValues.DPI
public import Statlib.EValues.EVarClass
public import Statlib.EValues.Utility.Log

/-!
# Numeraire

Let `𝓔` be a class of `ℝ≥0∞`-valued random variables, for example the e-variables for a set of
measures, and let `U` be a utility function. A numeraire for `U` in `𝓔` under `P` is an element
`X ∈ 𝓔` which satisfies the first-order optimality condition for the maximization of the expected
utility over `𝓔`: `∫ U'(X) (Y - X) ∂P ≤ 0` for all `Y ∈ 𝓔`. A numeraire maximizes the expected
utility, and it is almost surely unique if `U` is strictly concave.

For the logarithmic utility and a finite measure, the first-order condition is equivalent to
`∫⁻ Y / X ∂P ≤ P X.fsupport` for all `Y ∈ 𝓔`. For the class of e-variables for a set of measures
`S`, this is the numeraire e-variable of Larsson, Ramdas and Ruf (`IsNumeraire`, `isNumeraire_iff`).
Several of its properties need the constant `1` to be an e-variable for `S`, which means that the
measures of `S` have mass at most one (`isEVar_one_iff`).


The existence of the numeraire is proved in `Statlib.EValues.NumeraireExistence`.

## Main definitions

* `IsNumeraireFor U X 𝓔 P`: `X ∈ 𝓔` satisfies the first-order optimality condition
  `∫ U'(X) (Y - X) ∂P ≤ 0` for the utility function `U`, for all `Y ∈ 𝓔`.
* `IsLogNumeraireFor X 𝓔 P`: `IsNumeraireFor` for the logarithmic utility.
* `IsNumeraire X S μ`: the numeraire e-variable, that is `IsLogNumeraireFor` for the class of
  e-variables for `S`.

## Main statements

* `IsNumeraireFor.eintegral_utility_le`: a numeraire for `U` maximizes the expected utility.
* `isNumeraireFor_iff`: if `∫⁻ U'(X) X` is finite, `X` is a numeraire for `U` iff
  `∫⁻ U'(X) Y ≤ ∫⁻ U'(X) X` for all `Y ∈ 𝓔`.
* `IsNumeraireFor.ae_unique`: the numeraire for a strictly concave utility is almost surely
  unique.
* `isLogNumeraireFor_iff`: for a finite measure, a numeraire for the logarithmic utility is
  characterized by `∫⁻ Y / X ≤ P X.fsupport` for all `Y ∈ 𝓔`.
* `isNumeraire_iff`: for a finite measure, `X` is a numeraire for `S` iff it is an e-variable and
  `∫⁻ Y / X ∂μ ≤ μ X.fsupport` for all e-variables `Y` for `S`.
* `IsNumeraire.ae_unique`: the numeraire e-variable is almost surely unique.
* `IsNumeraire.eintegral_log_le`: the numeraire e-variable maximizes the expected logarithm.
* `IsNumeraireFor.maxUtility_eq_eintegral`, `IsNumeraire.maxUtility_eq_eintegral`: a numeraire in
  the class of e-variables attains the maximum utility `maxUtility`.

## References

* M. Larsson, A. Ramdas, J. Ruf, *The numeraire e-variable and reverse information projection*
  (2025).
-/

@[expose] public section

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure 𝓧}
  {S : Set (Measure 𝓧)} {𝓔 : Set (𝓧 → ℝ≥0∞)} {U : Utility} {X Y : 𝓧 → ℝ≥0∞}

/-! ### Numeraire for a utility function -/

/-- `X` is a numeraire for the utility function `U` in the class `𝓔` under `P` if `X ∈ 𝓔` and
the first-order optimality condition `∫ U'(X) (Y - X) ∂P ≤ 0` holds for all `Y ∈ 𝓔`, where the
integral is also required not to be `⊥`. -/
structure IsNumeraireFor (U : Utility) (X : 𝓧 → ℝ≥0∞) (𝓔 : Set (𝓧 → ℝ≥0∞)) (P : Measure 𝓧) :
    Prop where
  mem : X ∈ 𝓔
  eintegral_deriv_mul_ne_bot : ∀ ⦃Y⦄, Y ∈ 𝓔 → ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≠ ⊥
  eintegral_deriv_mul_le : ∀ ⦃Y⦄, Y ∈ 𝓔 → ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≤ 0

/-- The first-order term `∫ U'(X) (Y - X)` is the difference of `∫⁻ U'(X) Y` and
`∫⁻ U'(X) X`, if the latter is finite. -/
lemma eintegral_deriv_mul_sub (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h_ne_top : ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P ≠ ∞) :
    ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P
      = ∫⁻ ω, (U.deriv (X ω)).toENNReal * Y ω ∂P
        - ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P := by
  simp_rw [U.deriv_mul_sub_eq]
  exact eintegral_coe_ennreal_sub (by fun_prop) (by fun_prop) (.inr h_ne_top)

namespace IsNumeraireFor

lemma congr (hX : IsNumeraireFor U X 𝓔 P) (hY_mem : Y ∈ 𝓔) (hYX : Y =ᵐ[P] X) :
    IsNumeraireFor U Y 𝓔 P where
  mem := hY_mem
  eintegral_deriv_mul_ne_bot Z hZ := by
    convert hX.eintegral_deriv_mul_ne_bot hZ using 1
    refine eintegral_congr_ae ?_
    filter_upwards [hYX] with ω hω using by rw [hω]
  eintegral_deriv_mul_le Z hZ := by
    refine le_trans (le_of_eq ?_) (hX.eintegral_deriv_mul_le hZ)
    refine eintegral_congr_ae ?_
    filter_upwards [hYX] with ω hω using by rw [hω]

/-- A numeraire in a class is a numeraire in any subclass which contains it. -/
lemma subset (hX : IsNumeraireFor U X 𝓔 P) {𝓔' : Set (𝓧 → ℝ≥0∞)} (h𝓔 : 𝓔' ⊆ 𝓔)
    (hX' : X ∈ 𝓔') :
    IsNumeraireFor U X 𝓔' P where
  mem := hX'
  eintegral_deriv_mul_ne_bot _ hY := hX.eintegral_deriv_mul_ne_bot (h𝓔 hY)
  eintegral_deriv_mul_le _ hY := hX.eintegral_deriv_mul_le (h𝓔 hY)

/-- A numeraire `X` maximizes the expected utility over the class `𝓔`. -/
lemma eintegral_utility_le (hX : IsNumeraireFor U X 𝓔 P) (hY_mem : Y ∈ 𝓔)
    (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P) :
    ∫ᵉ ω, U (Y ω) ∂P ≤ ∫ᵉ ω, U (X ω) ∂P := by
  have h_foc := hX.eintegral_deriv_mul_le hY_mem
  have h_ne_bot : ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≠ ⊥ := hX.eintegral_deriv_mul_ne_bot hY_mem
  have h_ne_top : ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) h_foc
  have h_meas : AEMeasurable (fun ω ↦ U.deriv (X ω) * ((Y ω : EReal) - X ω)) P := by fun_prop
  calc ∫ᵉ ω, U (Y ω) ∂P
  _ ≤ ∫ᵉ ω, U (X ω) + U.deriv (X ω) * (Y ω - X ω) ∂P := by
    refine eintegral_mono_ae ?_
    filter_upwards [ae_ne_bot_of_eintegral_ne_bot h_meas h_ne_bot,
      ae_ne_top_of_eintegral_ne_top h_meas (eintegrable_of_eintegral_ne_bot h_ne_bot) h_ne_top]
      with ω h_bot h_top
    exact U.le_add_deriv_mul' h_bot h_top
  _ = ∫ᵉ ω, U (X ω) ∂P + ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P :=
    eintegral_add' (by fun_prop) h_meas h_ne_top h_ne_bot
  _ ≤ ∫ᵉ ω, U (X ω) ∂P := by grw [h_foc]; simp

/-- If `1 ∈ 𝓔`, the expected utility of a numeraire is at least `U 1 * P univ`. -/
lemma mul_measure_univ_le_eintegral_utility (hX : IsNumeraireFor U X 𝓔 P) (h_one : 1 ∈ 𝓔)
    (hX_meas : AEMeasurable X P) :
    U 1 * P univ ≤ ∫ᵉ ω, U (X ω) ∂P := by
  simpa [eintegral_const] using hX.eintegral_utility_le h_one hX_meas (by fun_prop)

lemma eintegral_utility_ne_bot [IsFiniteMeasure P] (hX : IsNumeraireFor U X 𝓔 P)
    (h_one : 1 ∈ 𝓔) (hX_meas : AEMeasurable X P) :
    ∫ᵉ ω, U (X ω) ∂P ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot ?_ (hX.mul_measure_univ_le_eintegral_utility h_one hX_meas)
  rw [← U.coe_real_toReal one_ne_zero ENNReal.one_ne_top,
    ← EReal.coe_ennreal_toReal (measure_ne_top P univ)]
  exact_mod_cast EReal.coe_ne_bot _

protected lemma eintegrable_utility [IsFiniteMeasure P] (hX : IsNumeraireFor U X 𝓔 P)
    (h_one : 1 ∈ 𝓔) (hX_meas : AEMeasurable X P) :
    EIntegrable (fun ω ↦ U (X ω)) P :=
  eintegrable_of_eintegral_ne_bot (hX.eintegral_utility_ne_bot h_one hX_meas)

/-- A numeraire `X` for `U` satisfies `∫⁻ U'(X) Y ≤ ∫⁻ U'(X) X` for all `Y ∈ 𝓔`.
See `isNumeraireFor_iff` for the converse. -/
lemma lintegral_deriv_mul_le (hX : IsNumeraireFor U X 𝓔 P) (hY : Y ∈ 𝓔)
    (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P) :
    ∫⁻ ω, (U.deriv (X ω)).toENNReal * Y ω ∂P ≤ ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P := by
  by_cases h_top : ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P = ∞
  · simp [h_top]
  have h := hX.eintegral_deriv_mul_le hY
  rwa [eintegral_deriv_mul_sub hX_meas hY_meas h_top, EReal.sub_nonpos,
    EReal.coe_ennreal_le_coe_ennreal_iff] at h

lemma ae_deriv_mul_sub_ne_bot (hX : IsNumeraireFor U X 𝓔 P) (hY : Y ∈ 𝓔)
    (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P) :
    ∀ᵐ ω ∂P, U.deriv (X ω) * (Y ω - X ω) ≠ ⊥ :=
  ae_ne_bot_of_eintegral_ne_bot (by fun_prop) (hX.eintegral_deriv_mul_ne_bot hY)

lemma ae_deriv_mul_sub_ne_top (hX : IsNumeraireFor U X 𝓔 P) (hY : Y ∈ 𝓔)
    (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P) :
    ∀ᵐ ω ∂P, U.deriv (X ω) * (Y ω - X ω) ≠ ⊤ :=
  ae_ne_top_of_eintegral_ne_top (by fun_prop)
    (eintegrable_of_eintegral_ne_bot (hX.eintegral_deriv_mul_ne_bot hY))
    (ne_top_of_le_ne_top (by simp) (hX.eintegral_deriv_mul_le hY))

/-- If `U'(0) = ∞` and `1 ∈ 𝓔`, a numeraire is almost surely positive. -/
lemma ae_ne_zero (hX : IsNumeraireFor U X 𝓔 P) (hU : U.deriv 0 = ⊤) (h_one : 1 ∈ 𝓔)
    (hX_meas : AEMeasurable X P) :
    ∀ᵐ ω ∂P, X ω ≠ 0 := by
  filter_upwards [hX.ae_deriv_mul_sub_ne_top h_one hX_meas (by fun_prop)] with ω hω hX0
  simp [hX0, hU] at hω

/-- If `U` is strictly increasing (`U'(x) > 0` for `x < ∞`), a numeraire is infinite wherever
an element of `𝓔` is infinite. -/
lemma ae_eq_top_of_eq_top (hX : IsNumeraireFor U X 𝓔 P) (hU : ∀ x, x ≠ ∞ → 0 < U.deriv x)
    (hY : Y ∈ 𝓔) (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P) :
    ∀ᵐ ω ∂P, Y ω = ∞ → X ω = ∞ := by
  filter_upwards [hX.ae_deriv_mul_sub_ne_top hY hX_meas hY_meas] with ω hω hY_top
  by_contra hX_top
  rw [hY_top, EReal.coe_ennreal_top, EReal.top_sub (by simpa using hX_top),
    EReal.mul_top_of_pos (hU _ hX_top)] at hω
  exact hω rfl

/-- If `U'(∞) ≠ 0`, a numeraire is almost surely finite. -/
lemma ae_ne_top (hX : IsNumeraireFor U X 𝓔 P) (hU : U.deriv ∞ ≠ 0) (hX_meas : AEMeasurable X P) :
    ∀ᵐ ω ∂P, X ω ≠ ∞ := by
  filter_upwards [hX.ae_deriv_mul_sub_ne_bot hX.mem hX_meas hX_meas] with ω hω hX_top
  rw [hX_top, EReal.coe_ennreal_top, EReal.sub_top,
    EReal.mul_bot_of_pos ((U.deriv_nonneg ∞).lt_of_ne' hU)] at hω
  exact hω rfl

/-- **Uniqueness of the numeraire**: for a strictly concave utility, the numeraire is almost
surely unique. -/
theorem ae_unique (hX : IsNumeraireFor U X 𝓔 P) (hY : IsNumeraireFor U Y 𝓔 P)
    (hU : StrictAntiOn U.deriv (Iio ∞)) (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P) :
    X =ᵐ[P] Y := by
  -- Sum the first-order conditions of `X` against `Y` and of `Y` against `X`: the integrand
  -- `U'(X) (Y - X) + U'(Y) (X - Y)` is nonnegative with nonpositive integral, hence zero, and
  -- it is positive where `X ≠ Y`.
  have h_int : ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) + U.deriv (Y ω) * (X ω - Y ω) ∂P ≤ 0 := by
    rw [eintegral_add' (by fun_prop) (by fun_prop)
      (ne_top_of_le_ne_top (by simp) (hY.eintegral_deriv_mul_le hX.mem))
      (hY.eintegral_deriv_mul_ne_bot hX.mem)]
    exact add_nonpos (hX.eintegral_deriv_mul_le hY.mem) (hY.eintegral_deriv_mul_le hX.mem)
  have h_top := hX.ae_deriv_mul_sub_ne_top hY.mem hX_meas hY_meas
  have h_top' := hY.ae_deriv_mul_sub_ne_top hX.mem hY_meas hX_meas
  have h_nonneg : ∀ᵐ ω ∂P, 0 ≤ U.deriv (X ω) * (Y ω - X ω) + U.deriv (Y ω) * (X ω - Y ω) := by
    filter_upwards [hX.ae_deriv_mul_sub_ne_bot hY.mem hX_meas hY_meas, h_top, h_top']
      with ω h1 h2 h3
    exact U.deriv_mul_sub_add_deriv_mul_sub_nonneg h1 h2 h3
  rw [eintegral_eq_lintegral_of_nonneg_ae h_nonneg] at h_int
  have h_zero := le_antisymm h_int (EReal.coe_ennreal_nonneg _)
  rw [EReal.coe_ennreal_eq_zero, lintegral_eq_zero_iff' (by fun_prop)] at h_zero
  filter_upwards [h_zero, h_top, h_top'] with ω hω h2 h3
  by_contra h_ne
  rw [Pi.zero_apply, EReal.toENNReal_eq_zero_iff] at hω
  exact (U.deriv_mul_sub_add_deriv_mul_sub_pos hU h_ne h2 h3).not_ge hω

protected lemma smul (hX : IsNumeraireFor U X 𝓔 P) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    IsNumeraireFor U X 𝓔 (c • P) where
  mem := hX.mem
  eintegral_deriv_mul_ne_bot Y hY := by
    rw [eintegral_smul_measure hc, EReal.mul_ne_bot]
    exact ⟨.inl (by simp), .inr (hX.eintegral_deriv_mul_ne_bot hY), .inl (by simp [hc]),
      .inl (by positivity)⟩
  eintegral_deriv_mul_le Y hY := by
    rw [eintegral_smul_measure hc]
    exact EReal.mul_nonpos_iff.mpr (.inl ⟨by positivity, hX.eintegral_deriv_mul_le hY⟩)

/-- The numeraire property transports along a measurable equivalence. -/
lemma comp_measurableEquiv (e : 𝓧 ≃ᵐ 𝓨) {X : 𝓨 → ℝ≥0∞} {𝓔 : Set (𝓨 → ℝ≥0∞)}
    (hX : IsNumeraireFor U X 𝓔 (P.map e)) :
    IsNumeraireFor U (X ∘ e) ((· ∘ e) '' 𝓔) P where
  mem := ⟨X, hX.mem, rfl⟩
  eintegral_deriv_mul_ne_bot := by
    rintro _ ⟨Y, hY, rfl⟩
    simpa [eintegral_map_equiv] using hX.eintegral_deriv_mul_ne_bot hY
  eintegral_deriv_mul_le := by
    rintro _ ⟨Y, hY, rfl⟩
    simpa [eintegral_map_equiv] using hX.eintegral_deriv_mul_le hY

end IsNumeraireFor

lemma isNumeraireFor_of_lintegral_deriv_mul_le (hX : X ∈ 𝓔)
    (h𝓔 : ∀ ⦃Y⦄, Y ∈ 𝓔 → AEMeasurable Y P)
    (h_ne_top : ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P ≠ ∞)
    (h : ∀ ⦃Y⦄, Y ∈ 𝓔 →
      ∫⁻ ω, (U.deriv (X ω)).toENNReal * Y ω ∂P ≤ ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P) :
    IsNumeraireFor U X 𝓔 P where
  mem := hX
  eintegral_deriv_mul_ne_bot Y hY := by
    rw [eintegral_deriv_mul_sub (h𝓔 hX) (h𝓔 hY) h_ne_top, sub_eq_add_neg, EReal.add_ne_bot_iff]
    simpa using h_ne_top
  eintegral_deriv_mul_le Y hY := by
    rw [eintegral_deriv_mul_sub (h𝓔 hX) (h𝓔 hY) h_ne_top, EReal.sub_nonpos,
      EReal.coe_ennreal_le_coe_ennreal_iff]
    exact h hY

/-- If `∫⁻ U'(X) X` is finite, `X` is a numeraire for `U` iff `X ∈ 𝓔` and
`∫⁻ U'(X) Y ≤ ∫⁻ U'(X) X` for all `Y ∈ 𝓔`. -/
lemma isNumeraireFor_iff (h𝓔 : ∀ ⦃Y⦄, Y ∈ 𝓔 → AEMeasurable Y P)
    (h_ne_top : ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P ≠ ∞) :
    IsNumeraireFor U X 𝓔 P ↔ X ∈ 𝓔 ∧ ∀ ⦃Y⦄, Y ∈ 𝓔 →
      ∫⁻ ω, (U.deriv (X ω)).toENNReal * Y ω ∂P ≤ ∫⁻ ω, (U.deriv (X ω)).toENNReal * X ω ∂P :=
  ⟨fun hX ↦ ⟨hX.mem, fun _ hY ↦ hX.lintegral_deriv_mul_le hY (h𝓔 hX.mem) (h𝓔 hY)⟩,
    fun h ↦ isNumeraireFor_of_lintegral_deriv_mul_le h.1 h𝓔 h_ne_top h.2⟩

/-- If `U'(∞) = 0`, an almost surely infinite element of `𝓔` is a numeraire. -/
lemma isNumeraireFor_of_ae_eq_top (hU : U.deriv ∞ = 0) (hX : X ∈ 𝓔)
    (hX_top : ∀ᵐ ω ∂P, X ω = ∞) :
    IsNumeraireFor U X 𝓔 P := by
  have h_zero (Y : 𝓧 → ℝ≥0∞) : ∫ᵉ ω, U.deriv (X ω) * (Y ω - X ω) ∂P = 0 := by
    rw [← eintegral_zero P]
    refine eintegral_congr_ae ?_
    filter_upwards [hX_top] with ω hω
    simp [hω, hU]
  exact ⟨hX, fun Y _ ↦ by simp [h_zero Y], fun Y _ ↦ by simp [h_zero Y]⟩

/-- Under a probability measure `P`, the constant `1` is a numeraire for `U` in a class `𝓔` iff
`U'(1) = 0` or every element of `𝓔` is an e-variable for `{P}`. -/
lemma isNumeraireFor_one_iff_isEVar [IsProbabilityMeasure P] (h𝓔 : IsEVarClass 𝓔) :
    IsNumeraireFor U (1 : 𝓧 → ℝ≥0∞) 𝓔 P ↔
      U.deriv 1 = 0 ∨ ∀ Y ∈ 𝓔, IsEVar Y {P} := by
  have h_ne_top : (U.deriv 1).toENNReal ≠ ∞ := by simp [Utility.deriv]
  rw [isNumeraireFor_iff (fun _ hY ↦ (h𝓔.measurable hY).aemeasurable) (by simpa using h_ne_top)]
  simp only [Pi.one_apply, mul_one, lintegral_const, measure_univ, h𝓔.one_mem, true_and]
  by_cases h_zero : U.deriv 1 = 0
  · simp [h_zero]
  have h_ne_zero : (U.deriv 1).toENNReal ≠ 0 := by
    simpa [EReal.toENNReal_eq_zero_iff] using lt_of_le_of_ne' (U.deriv_nonneg 1) h_zero
  simp only [h_zero, false_or]
  refine forall₂_congr fun Y hY ↦ ?_
  have hY_meas : Measurable Y := h𝓔.measurable hY
  calc ∫⁻ ω, (U.deriv 1).toENNReal * Y ω ∂P ≤ (U.deriv 1).toENNReal
  _ ↔ (U.deriv 1).toENNReal * ∫⁻ ω, Y ω ∂P ≤ (U.deriv 1).toENNReal * 1 := by
    rw [lintegral_const_mul _ hY_meas, mul_one]
  _ ↔ ∫⁻ ω, Y ω ∂P ≤ 1 := ENNReal.mul_le_mul_iff_right h_ne_zero h_ne_top
  _ ↔ IsEVar Y {P} := ⟨fun h ↦ ⟨hY_meas, fun μ hμ ↦ by rwa [mem_singleton_iff.mp hμ]⟩,
    fun h ↦ h.lintegral_le_one rfl⟩

/-! ### Numeraire for the logarithmic utility -/

/-- A numeraire for the logarithmic utility: `IsNumeraireFor` specialized to `logUtility`.

If the elements of `𝓔` are measurable and the finite support of `X` has finite measure,
this means that `X ∈ 𝓔` and `∫⁻ ω, Y ω / X ω ∂μ ≤ μ X.fsupport` for all `Y ∈ 𝓔`
(see `isLogNumeraireFor_iff`). -/
abbrev IsLogNumeraireFor (X : 𝓧 → ℝ≥0∞) (𝓔 : Set (𝓧 → ℝ≥0∞)) (μ : Measure 𝓧) : Prop :=
  IsNumeraireFor logUtility X 𝓔 μ

/-- A numeraire `X` for the logarithmic utility satisfies `∫⁻ Y / X ≤ P X.fsupport` for all
`Y ∈ 𝓔`. This holds even if `P X.fsupport = ∞`, unlike the converse
`isLogNumeraireFor_of_lintegral_div_le`. -/
lemma IsLogNumeraireFor.lintegral_div_le_measure_fsupport (hX : IsLogNumeraireFor X 𝓔 P)
    (hX_meas : AEMeasurable X P) (hY : Y ∈ 𝓔) (hY_meas : AEMeasurable Y P) :
    ∫⁻ ω, Y ω / X ω ∂P ≤ P X.fsupport := by
  simpa [toENNReal_deriv_logUtility, ← ENNReal.div_eq_inv_mul,
    lintegral_div_self_eq_measure_fsupport hX_meas]
    using hX.lintegral_deriv_mul_le hY hX_meas hY_meas

lemma isLogNumeraireFor_of_lintegral_div_le (hX : X ∈ 𝓔)
    (h𝓔 : ∀ ⦃Y⦄, Y ∈ 𝓔 → AEMeasurable Y P) (hX_fsupport : P X.fsupport ≠ ∞)
    (h : ∀ ⦃Y⦄, Y ∈ 𝓔 → ∫⁻ ω, Y ω / X ω ∂P ≤ P X.fsupport) :
    IsLogNumeraireFor X 𝓔 P := by
  have h_eq (Y : 𝓧 → ℝ≥0∞) : ∫⁻ ω, (logUtility.deriv (X ω)).toENNReal * Y ω ∂P
      = ∫⁻ ω, Y ω / X ω ∂P := by
    simp [toENNReal_deriv_logUtility, ← ENNReal.div_eq_inv_mul]
  refine isNumeraireFor_of_lintegral_deriv_mul_le hX h𝓔 ?_ fun Y hY ↦ ?_
  · rwa [h_eq, lintegral_div_self_eq_measure_fsupport (h𝓔 hX)]
  · rw [h_eq, h_eq, lintegral_div_self_eq_measure_fsupport (h𝓔 hX)]
    exact h hY

lemma isLogNumeraireFor_iff [IsFiniteMeasure P] (h𝓔 : ∀ ⦃Y⦄, Y ∈ 𝓔 → AEMeasurable Y P) :
    IsLogNumeraireFor X 𝓔 P ↔ X ∈ 𝓔 ∧ ∀ ⦃Y⦄, Y ∈ 𝓔 → ∫⁻ ω, Y ω / X ω ∂P ≤ P X.fsupport :=
  ⟨fun hX ↦ ⟨hX.mem, fun _ hY ↦ hX.lintegral_div_le_measure_fsupport (h𝓔 hX.mem) hY (h𝓔 hY)⟩,
    fun h ↦ isLogNumeraireFor_of_lintegral_div_le h.1 h𝓔 (measure_ne_top _ _) h.2⟩

lemma lintegral_div_self_le_iff_isLogNumeraireFor [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔)
    (hY_evar : Y ∈ 𝓔) :
    (∀ X, X ∈ 𝓔 → ∫⁻ ω, X ω / Y ω ∂P ≤ ∫⁻ ω, Y ω / Y ω ∂P) ↔ IsLogNumeraireFor Y 𝓔 P := by
  simp_rw [lintegral_div_self_eq_measure_fsupport (h𝓔.measurable hY_evar).aemeasurable,
    isLogNumeraireFor_iff fun _ hY ↦ (h𝓔.measurable hY).aemeasurable, and_iff_right hY_evar]

/-! ### Numeraire for a set of measures -/

/-- A numeraire for the logarithmic utility in the class of e-variables for `S`, under `μ`: the
numeraire e-variable. For a finite measure, `X` is a numeraire iff it is an e-variable and
`∫⁻ ω, Y ω / X ω ∂μ ≤ μ X.fsupport` for every e-variable `Y` (`isNumeraire_iff`). -/
abbrev IsNumeraire (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) (μ : Measure 𝓧) : Prop :=
  IsLogNumeraireFor X {Y | IsEVar Y S} μ

lemma isNumeraire_of_lintegral_div_le (hX : IsEVar X S) (hX_fsupport : P X.fsupport ≠ ∞)
    (h : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂P ≤ P X.fsupport) :
    IsNumeraire X S P :=
  isLogNumeraireFor_of_lintegral_div_le hX (fun _ hY ↦ hY.measurable.aemeasurable) hX_fsupport h

/-- For a finite measure, `X` is a numeraire iff it is an e-variable and the expectation of the
ratio of any e-variable `Y` over `X` is at most the measure of the finite support of `X`. -/
lemma isNumeraire_iff [IsFiniteMeasure P] :
    IsNumeraire X S P ↔ IsEVar X S ∧ ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂P ≤ P X.fsupport :=
  isLogNumeraireFor_iff fun _ hY ↦ hY.measurable.aemeasurable

/-- For a given e-variable `Y` and a finite measure, the property of being a numeraire is
equivalent to the property that the expectation of the ratio of any e-variable `X` over `Y` is
at most the expectation of the ratio of `Y` over itself. -/
lemma lintegral_div_self_le_iff_isNumeraire [IsFiniteMeasure P] (hY_evar : IsEVar Y S) :
    (∀ X, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ ∫⁻ ω, Y ω / Y ω ∂P) ↔ IsNumeraire Y S P := by
  simp_rw [lintegral_div_self_eq_measure_fsupport hY_evar.measurable.aemeasurable, isNumeraire_iff,
    and_iff_right hY_evar]

/-- A numeraire for `U` in the class of e-variables for `S` attains the maximum utility. -/
lemma IsNumeraireFor.maxUtility_eq_eintegral (hX : IsNumeraireFor U X {Y | IsEVar Y S} P) :
    maxUtility P S U = ∫ᵉ x, U (X x) ∂P :=
  le_antisymm (iSup₂_le fun _ hY ↦ hX.eintegral_utility_le hY hX.mem.measurable.aemeasurable
      hY.measurable.aemeasurable)
    (le_iSup₂ (f := fun Y _ ↦ ∫ᵉ x, (U ∘ Y) x ∂P) X hX.mem)

/-- If the measures of `S` have mass at most one, the constant function `1` is a numeraire for `S`
at any probability measure of `S`. -/
lemma isNumeraire_one [IsProbabilityMeasure P] (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) (hPS : P ∈ S) :
    IsNumeraire 1 S P :=
  isNumeraire_of_lintegral_div_le (isEVar_one hS) (measure_ne_top _ _) fun Y hY ↦ by
    simpa [Function.fsupport] using hY.lintegral_le_one hPS

/-- If the measures of `S` have mass at most one, the maximum log utility of a probability measure
of `S` is zero. -/
lemma maxUtility_eq_zero_of_mem [IsProbabilityMeasure P] (hS : ∀ μ ∈ S, μ Set.univ ≤ 1)
    (hPS : P ∈ S) :
    maxUtility P S logUtility = 0 := by
  rw [(isNumeraire_one hS hPS).maxUtility_eq_eintegral]
  simp [logUtility]

/-- If `S` is empty, every measurable function is an e-variable, and an almost everywhere
infinite function is a numeraire. -/
lemma isNumeraire_of_isEmpty (hS : IsEmpty S) (hX : Measurable X) (hX_top : ∀ᵐ x ∂P, X x = ∞) :
    IsNumeraire X S P :=
  isNumeraireFor_of_ae_eq_top (by simp [deriv_logUtility_eq_ennreal])
    ⟨hX, by simp_all⟩ hX_top

namespace IsNumeraire

variable {μ : Measure 𝓧}

lemma isEVar (hX : IsNumeraire X S μ) : IsEVar X S := hX.mem

protected lemma measurable (hX : IsNumeraire X S μ) : Measurable X := hX.isEVar.measurable

lemma lintegral_div_le_measure_fsupport (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ ≤ μ X.fsupport :=
  IsLogNumeraireFor.lintegral_div_le_measure_fsupport hX hX.measurable.aemeasurable hY
    hY.measurable.aemeasurable

lemma lintegral_inv_le_measure_fsupport (hX : IsNumeraire X S μ)
    (hS : ∀ ν ∈ S, ν Set.univ ≤ 1) :
    ∫⁻ ω, (X ω)⁻¹ ∂μ ≤ μ X.fsupport := by
  simpa using hX.lintegral_div_le_measure_fsupport (isEVar_one hS)

lemma lintegral_div_le_measure_univ (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ ≤ μ univ :=
  (hX.lintegral_div_le_measure_fsupport hY).trans (measure_mono (by simp))

lemma lintegral_div_le_one [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ ≤ 1 := by
  simpa using hX.lintegral_div_le_measure_univ hY

lemma ae_ne_zero (hX : IsNumeraire X S μ) (hS : ∀ ν ∈ S, ν Set.univ ≤ 1) : ∀ᵐ ω ∂μ, X ω ≠ 0 :=
  IsNumeraireFor.ae_ne_zero hX deriv_logUtility_zero (isEVar_one hS) hX.measurable.aemeasurable

lemma ae_pos (hX : IsNumeraire X S μ) (hS : ∀ ν ∈ S, ν Set.univ ≤ 1) : ∀ᵐ ω ∂μ, 0 < X ω := by
  filter_upwards [hX.ae_ne_zero hS] with ω hω using pos_iff_ne_zero.mpr hω

/-- A numeraire is either almost everywhere infinite, or its finite support has positive
measure. -/
lemma measure_fsupport_ne_zero_or_ae_top (hX : IsNumeraire X S μ)
    (hS : ∀ ν ∈ S, ν Set.univ ≤ 1) :
    μ X.fsupport ≠ 0 ∨ X =ᵐ[μ] fun _ ↦ ∞ := by
  by_contra! h
  rcases h with ⟨h, h_top⟩
  rw [← compl_compl X.fsupport] at h
  have h' : ∀ᵐ x ∂μ, x ∈ X.fsupportᶜ := by rwa [ae_iff]
  refine h_top ?_
  filter_upwards [h', hX.ae_ne_zero hS] with ω hω_mem hω_ne_zero
  simpa [hω_ne_zero] using hω_mem

/-- The numeraire property transports along a measurable equivalence. -/
lemma comp_measurableEquiv (e : 𝓧 ≃ᵐ 𝓨) {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)}
    (hY : IsNumeraire Y (Measure.map e '' S) (μ.map e)) :
    IsNumeraire (Y ∘ e) S μ := by
  have h_image : Measure.map e.symm '' (Measure.map e '' S) = S := by
    rw [← Set.image_comp]
    have h : (Measure.map e.symm ∘ Measure.map e) = id := by
      funext σ
      simp only [Function.comp_apply, id]
      rw [Measure.map_map e.symm.measurable e.measurable]
      simp
    rw [h, Set.image_id]
  refine (IsNumeraireFor.comp_measurableEquiv e hY).subset (fun Z hZ ↦ ?_)
    (hY.isEVar.comp e.measurable)
  have hZ_meas := hZ.measurable
  refine ⟨Z ∘ e.symm, IsEVar.comp e.symm.measurable ?_, by ext; simp⟩
  rwa [show {ρ.map e.symm | ρ ∈ Measure.map e '' S}
    = Measure.map e.symm '' (Measure.map e '' S) from rfl, h_image]

/-- If an e-variable `Y` is infinite at a point, then the numeraire `X` is also infinite there,
almost surely. -/
lemma ae_eq_top_of_eq_top (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∀ᵐ ω ∂μ, Y ω = ∞ → X ω = ∞ :=
  IsNumeraireFor.ae_eq_top_of_eq_top hX
    (fun _ hx ↦ logUtility.deriv_pos_of_strictAntiOn strictAntiOn_deriv_logUtility hx) hY
    hX.measurable.aemeasurable hY.measurable.aemeasurable

/-- **Uniqueness of the numeraire**: the numeraire is almost everywhere unique. -/
theorem ae_unique (hX : IsNumeraire X S μ) (hY : IsNumeraire Y S μ) : X =ᵐ[μ] Y :=
  IsNumeraireFor.ae_unique hX hY strictAntiOn_deriv_logUtility hX.measurable.aemeasurable
    hY.measurable.aemeasurable

/-- Two numeraires have equal finite support measures. -/
lemma measure_fsupport_eq_measure_fsupport (hX : IsNumeraire X S μ) (hY : IsNumeraire Y S μ) :
    μ X.fsupport = μ Y.fsupport := by
  refine measure_congr ?_
  filter_upwards [hX.ae_unique hY] with ω hω
  simp [hω]

section LogOptimal

private lemma eintegral_log_div_nonpos_of_isProbabilityMeasure [IsProbabilityMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ ≤ 0 := by
  calc ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ
  _ ≤ ENNReal.log (∫⁻ ω, Y ω / X ω ∂μ) := by
    refine Utility.eintegral_le_map logUtility ?_
    exact hY.measurable.aemeasurable.div hX.measurable.aemeasurable
  _ ≤ 0 := by
    simp only [ENNReal.log_le_zero_iff]
    exact hX.lintegral_div_le_one hY

-- todo: prove that log-optimal implies numeraire
/-- A numeraire is log-optimal: `∫ log (Y / X) ≤ 0` for every e-variable `Y`. -/
theorem eintegral_log_div_nonpos [IsFiniteMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ ≤ 0 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  suffices ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ[|univ] ≤ 0 by
    rw [cond, eintegral_smul_measure (by simpa), Measure.restrict_univ, EReal.mul_nonpos_iff]
      at this
    cases this with
    | inl h => exact h.2
    | inr h =>
      norm_cast at h
      simp at h
  have : IsProbabilityMeasure μ[|univ] := cond_isProbabilityMeasure_of_finite (by simpa) (by simp)
  refine eintegral_log_div_nonpos_of_isProbabilityMeasure ?_ hY
  rw [cond, Measure.restrict_univ]
  exact IsNumeraireFor.smul hX (by simpa)

/-- The first-order optimality condition of the numeraire for the logarithmic utility. -/
lemma eintegral_sub_div_nonpos (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, (Y ω - X ω) / X ω ∂μ ≤ 0 := by
  refine le_trans (eintegral_mono fun ω ↦ ?_) (hX.eintegral_deriv_mul_le hY)
  rw [deriv_logUtility_eq_ennreal]
  rcases eq_or_ne (X ω) 0 with h0 | h0
  · simp only [h0, EReal.coe_ennreal_zero, sub_zero, ENNReal.div_zero one_ne_zero,
      EReal.coe_ennreal_top, EReal.div_zero]
    exact EReal.mul_nonneg (by simp) (EReal.coe_ennreal_nonneg _)
  · rw [div_eq_mul_inv, mul_comm, EReal.inv_coe_ennreal h0, one_div]

/-- A numeraire maximizes the integral of the logarithm. -/
theorem eintegral_log_le (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂μ ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ :=
  IsNumeraireFor.eintegral_utility_le hX hY hX.measurable.aemeasurable hY.measurable.aemeasurable

/-- The numeraire attains the maximum logarithmic utility. -/
lemma maxUtility_eq_eintegral (hX : IsNumeraire X S μ) :
    maxUtility μ S logUtility = ∫ᵉ x, ENNReal.log (X x) ∂μ :=
  IsNumeraireFor.maxUtility_eq_eintegral hX

lemma eintegral_log_nonneg (hX : IsNumeraire X S μ) (hS : ∀ ν ∈ S, ν Set.univ ≤ 1) :
    0 ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  simpa using hX.eintegral_log_le (isEVar_one hS)

lemma eintegral_log_ne_bot (hX : IsNumeraire X S μ) (hS : ∀ ν ∈ S, ν Set.univ ≤ 1) :
    ∫ᵉ ω, ENNReal.log (X ω) ∂μ ≠ ⊥ :=
  ne_bot_of_le_ne_bot (by simp) (hX.eintegral_log_nonneg hS)

/-- The logarithm of the numeraire is integrable. -/
protected lemma eintegrable_log (hX : IsNumeraire X S μ) (hS : ∀ ν ∈ S, ν Set.univ ≤ 1) :
    EIntegrable (fun ω ↦ ENNReal.log (X ω)) μ :=
  eintegrable_of_eintegral_ne_bot (hX.eintegral_log_ne_bot hS)

end LogOptimal

end IsNumeraire

end ProbabilityTheory
