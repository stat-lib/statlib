/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Statlib.ForMathlib.MeasureTheory.Integral.Layercake
public import Statlib.ForMathlib.Probability.Process.Stopping
public import Statlib.ForMathlib.Probability.ProductMeasure

/-!
# Wald's identity

Let `X : ℕ → Ω → ℝ` be integrable random variables and `τ : Ω → ℕ` a random time. Suppose that
for all `n`, `∫ ω in {n ≤ τ}, X n ω = P {n ≤ τ} * ∫ X n` (which holds if `X n` is independent of
the event `{n ≤ τ}`, for example if `τ` is a stopping time and `X n` is independent of the past
before `n`) and that `∑ n, ∫ ω in {n ≤ τ}, |X n ω| < ∞`. Then the stopped sums
`S = ∑ n ≤ τ, X n` and `T = ∑ n ≤ τ, ∫ X n` are integrable and have the same integral.

We then specialize to i.i.d. sequences: for `μ^ℕ = Measure.infinitePi (fun _ : ℕ ↦ μ)` and a
stopping time `τ` for the filtration `Filtration.piLE` of the first coordinates, with values in `ℕ`
and integrable, the number of observations at time `τ` is `τ + 1` and
`∫ ω, ∑ n ≤ τ ω, f (ω n) ∂μ^ℕ = (∫ ω, (τ ω + 1) ∂μ^ℕ) * ∫ f ∂μ`.

## Main statements

* `integrable_sum_Iic_of_summable`, `integrable_sum_Iic_integral_of_summable`: the stopped sums
  `ω ↦ ∑ n ≤ τ ω, X n ω` and `ω ↦ ∑ n ≤ τ ω, ∫ X n` are integrable.
* `integral_sum_Iic_eq_integral_sum_Iic_integral` (**Wald's identity**):
  `∫ ω, ∑ n ≤ τ ω, X n ω = ∫ ω, ∑ n ≤ τ ω, ∫ X n`.
* `integral_sum_comp_stoppingTime` (**Wald's identity** for i.i.d. sequences):
  `∫ ω, ∑ n ≤ τ ω, f (ω n) ∂μ^ℕ = (∫ ω, (τ ω + 1) ∂μ^ℕ) * ∫ f ∂μ`. Its proof uses the tail-sum
  formula `∑ n, P {n ≤ σ} = ∫ (σ + 1) ∂P` (`MeasureTheory.hasSum_measureReal_le`).

## References

* A. Wald, *On cumulative sums of random variables*, Annals of Mathematical Statistics 15(3)
  (1944).
-/

@[expose] public section

open MeasureTheory Filter Filtration

open scoped ENNReal Topology

namespace ProbabilityTheory

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ} {τ : Ω → ℕ}

private lemma integrable_indicator_le (hτ : Measurable τ)
    (hX : ∀ n, IntegrableOn (X n) {ω | n ≤ τ ω} P) (n : ℕ) :
    Integrable ({ω | n ≤ τ ω}.indicator (X n)) P :=
  (integrable_indicator_iff (measurableSet_le measurable_const hτ)).mpr (hX n)

private lemma summable_integral_norm_indicator (hτ : Measurable τ)
    (h_sum : Summable fun n ↦ ∫ ω in {ω | n ≤ τ ω}, |X n ω| ∂P) :
    Summable fun n ↦ ∫ ω, ‖{ω | n ≤ τ ω}.indicator (X n) ω‖ ∂P := by
  convert h_sum using 2 with n
  rw [← integral_indicator (measurableSet_le measurable_const hτ)]
  congr with ω
  rw [norm_indicator_eq_indicator_norm]
  rfl

/-- The stopped sum `ω ↦ ∑ n ≤ τ ω, X n ω` is integrable if each `X n` is integrable on `{n ≤ τ}`
and `∑ n, ∫ ω in {n ≤ τ}, |X n ω| < ∞`. -/
lemma integrable_sum_Iic_of_summable (hX : ∀ n, IntegrableOn (X n) {ω | n ≤ τ ω} P)
    (hτ : Measurable τ) (h_sum : Summable fun n ↦ ∫ ω in {ω | n ≤ τ ω}, |X n ω| ∂P) :
    Integrable (fun ω ↦ ∑ n ∈ Finset.Iic (τ ω), X n ω) P := by
  simp_rw [sum_Iic_eq_tsum_indicator]
  set F := fun n ↦ {ω | n ≤ τ ω}.indicator (X n)
  have hF_int := integrable_indicator_le hτ hX
  have hF_sum := summable_integral_norm_indicator hτ h_sum
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N ω ↦ ∑ n ∈ Finset.range N, F n ω)
      (fun N ↦ Finset.aestronglyMeasurable_fun_sum _ fun n _ ↦ (hF_int n).1) ?_
    refine ae_of_all _ fun ω ↦ ?_
    refine (summable_of_ne_finset_zero (s := Finset.Iic (τ ω)) fun n hn ↦ ?_).hasSum
      |>.tendsto_sum_nat
    simp only [F]
    rw [Set.indicator_of_notMem]
    simpa using hn
  · calc ∫⁻ ω, ‖∑' n, F n ω‖ₑ ∂P
    _ ≤ ∫⁻ ω, ∑' n, ‖F n ω‖ₑ ∂P := lintegral_mono fun ω ↦ eNorm_tsum_le_tsum_eNorm
    _ = ∑' n, ∫⁻ ω, ‖F n ω‖ₑ ∂P :=
      lintegral_tsum fun n ↦ (hF_int n).1.eNorm
    _ = ∑' n, ENNReal.ofReal (∫ ω, ‖F n ω‖ ∂P) := by
      congr with n
      rw [ofReal_integral_norm_eq_lintegral_eNorm (hF_int n)]
    _ = ENNReal.ofReal (∑' n, ∫ ω, ‖F n ω‖ ∂P) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) hF_sum).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Under the hypotheses of Wald's identity, `∑ n, ∫ ω in {n ≤ τ}, |∫ X n| < ∞`: indeed
`P {n ≤ τ} * |∫ X n| = |∫ ω in {n ≤ τ}, X n ω| ≤ ∫ ω in {n ≤ τ}, |X n ω|`. -/
private lemma summable_setIntegral_abs_integral
    (h_indep : ∀ n, ∫ ω in {ω | n ≤ τ ω}, X n ω ∂P = P.real {ω | n ≤ τ ω} * ∫ ω, X n ω ∂P)
    (h_sum : Summable fun n ↦ ∫ ω in {ω | n ≤ τ ω}, |X n ω| ∂P) :
    Summable fun n ↦ ∫ _ in {ω | n ≤ τ ω}, |∫ ω, X n ω ∂P| ∂P := by
  refine h_sum.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) fun n ↦ ?_
  calc ∫ _ in {ω | n ≤ τ ω}, |∫ ω, X n ω ∂P| ∂P
  _ = |∫ ω in {ω | n ≤ τ ω}, X n ω ∂P| := by
    rw [setIntegral_const, smul_eq_mul, h_indep n, abs_mul, abs_of_nonneg measureReal_nonneg]
  _ ≤ ∫ ω in {ω | n ≤ τ ω}, |X n ω| ∂P := abs_integral_le_integral_abs

/-- Under the hypotheses of Wald's identity, the sum `ω ↦ ∑ n ≤ τ ω, ∫ X n` is integrable. -/
lemma integrable_sum_Iic_integral_of_summable [IsFiniteMeasure P] (hτ : Measurable τ)
    (h_indep : ∀ n, ∫ ω in {ω | n ≤ τ ω}, X n ω ∂P = P.real {ω | n ≤ τ ω} * ∫ ω, X n ω ∂P)
    (h_sum : Summable fun n ↦ ∫ ω in {ω | n ≤ τ ω}, |X n ω| ∂P) :
    Integrable (fun ω ↦ ∑ n ∈ Finset.Iic (τ ω), ∫ ω', X n ω' ∂P) P :=
  integrable_sum_Iic_of_summable (X := fun n _ ↦ ∫ ω', X n ω' ∂P)
    (fun _ ↦ integrableOn_const) hτ (summable_setIntegral_abs_integral h_indep h_sum)

/-- **Wald's identity**. Let `X : ℕ → Ω → ℝ` be integrable and `τ : Ω → ℕ` measurable. Suppose
that for all `n`, `∫ ω in {n ≤ τ}, X n ω = P {n ≤ τ} * ∫ X n` and that
`∑ n, ∫ ω in {n ≤ τ}, |X n ω| < ∞`. Then
`∫ ω, ∑ n ≤ τ ω, X n ω = ∫ ω, ∑ n ≤ τ ω, ∫ X n`. Both stopped sums are integrable, by
`integrable_sum_Iic_of_summable` and `integrable_sum_Iic_integral_of_summable`. -/
theorem integral_sum_Iic_eq_integral_sum_Iic_integral [IsFiniteMeasure P]
    (hX : ∀ n, Integrable (X n) P) (hτ : Measurable τ)
    (h_indep : ∀ n, ∫ ω in {ω | n ≤ τ ω}, X n ω ∂P = P.real {ω | n ≤ τ ω} * ∫ ω, X n ω ∂P)
    (h_sum : Summable fun n ↦ ∫ ω in {ω | n ≤ τ ω}, |X n ω| ∂P) :
    ∫ ω, ∑ n ∈ Finset.Iic (τ ω), X n ω ∂P
      = ∫ ω, ∑ n ∈ Finset.Iic (τ ω), ∫ ω', X n ω' ∂P ∂P := by
  have h_meas (n : ℕ) : MeasurableSet {ω | n ≤ τ ω} := measurableSet_le measurable_const hτ
  simp_rw [sum_Iic_eq_tsum_indicator (fun n _ ↦ ∫ ω', X n ω' ∂P), sum_Iic_eq_tsum_indicator X]
  rw [← integral_tsum_of_summable_integral_norm
      (integrable_indicator_le hτ fun n ↦ (hX n).integrableOn)
      (summable_integral_norm_indicator hτ h_sum),
    ← integral_tsum_of_summable_integral_norm
      (integrable_indicator_le (X := fun n _ ↦ ∫ ω', X n ω' ∂P) hτ fun _ ↦ integrableOn_const)
      (summable_integral_norm_indicator hτ (summable_setIntegral_abs_integral h_indep h_sum))]
  congr with n
  rw [integral_indicator (h_meas n), integral_indicator (h_meas n), setIntegral_const, h_indep n,
    smul_eq_mul]

end General

section IID

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} [IsProbabilityMeasure μ]
  {τ : (ℕ → 𝓧) → ℕ}

/-- For an event `A` determined by the first `n + 1` coordinates of an i.i.d. sequence,
`∫ ω in A, f (ω (n + 1)) ∂μ^ℕ = μ^ℕ A * ∫ f ∂μ`, since the coordinate `n + 1` is independent of
`A`. -/
lemma setIntegral_comp_eval_succ {f : 𝓧 → ℝ} (hf : AEStronglyMeasurable f μ) (n : ℕ)
    {A : Set (ℕ → 𝓧)} (hA : MeasurableSet[piLE (X := fun _ : ℕ ↦ 𝓧) n] A) :
    ∫ ω in A, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ)
      = (Measure.infinitePi fun _ ↦ μ).real A * ∫ x, f x ∂μ := by
  have h_indep : Indep (piLE (X := fun _ : ℕ ↦ 𝓧) n) (m𝓧.comap fun ω : ℕ → 𝓧 ↦ ω (n + 1))
      (Measure.infinitePi fun _ ↦ μ) := by
    have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
      fun _ ↦ measurable_id).indepFun_finset (Finset.Iic n) {n + 1} (by simp)
      fun i ↦ measurable_pi_apply i
    have h' : (fun ω : ℕ → 𝓧 ↦ Preorder.frestrictLe n ω)
        ⟂ᵢ[Measure.infinitePi fun _ ↦ μ] fun ω ↦ ω (n + 1) := by
      exact h.comp measurable_id (measurable_pi_apply ⟨n + 1, by simp⟩)
    rw [piLE_eq_comap_frestrictLe]
    exact (IndepFun_iff_Indep _ _ _).mp h'
  rw [Indep.setIntegral_eq_mul ((piLE (X := fun _ : ℕ ↦ 𝓧)).le n) h_indep
    (measurable_pi_apply _).aemeasurable hA, integral_comp_eval_infinitePi hf]
  rwa [(measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) (n + 1)).map_eq]

/-- For a stopping time `τ`, `∫ ω in {n ≤ τ}, f (ω n) ∂μ^ℕ = μ^ℕ {n ≤ τ} * ∫ f ∂μ`, since the
coordinate `n` of an i.i.d. sequence is independent of the event `{n ≤ τ} = {τ ≤ n - 1}ᶜ`. -/
lemma setIntegral_comp_eval_le_stoppingTime {f : 𝓧 → ℝ} (hf : AEStronglyMeasurable f μ)
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ))) (n : ℕ) :
    ∫ ω in {ω | n ≤ τ ω}, f (ω n) ∂(Measure.infinitePi fun _ ↦ μ)
      = (Measure.infinitePi fun _ ↦ μ).real {ω | n ≤ τ ω} * ∫ x, f x ∂μ := by
  rcases n with _ | n
  · simp [integral_comp_eval_infinitePi (μ := fun _ ↦ μ) hf]
  · have h_set : {ω | n + 1 ≤ τ ω} = {ω | (τ ω : WithTop ℕ) ≤ n}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Nat.cast_le, not_le]
      omega
    rw [h_set]
    exact setIntegral_comp_eval_succ hf n (hτ n).compl

private lemma summable_setIntegral_abs_le_stoppingTime {f : 𝓧 → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ)))
    (hτ_int : Integrable (fun ω ↦ (τ ω : ℝ)) (Measure.infinitePi fun _ ↦ μ)) :
    Summable fun n ↦ ∫ ω in {ω | n ≤ τ ω}, |f (ω n)| ∂(Measure.infinitePi fun _ ↦ μ) := by
  simp_rw [setIntegral_comp_eval_le_stoppingTime (f := fun x ↦ |f x|)
    (continuous_abs.comp_aestronglyMeasurable hf) hτ]
  exact (hasSum_measureReal_le hτ_int).summable.mul_right _

/-- The sum of the values of a function at the observations of an i.i.d. sequence up to an
integrable stopping time is integrable. -/
lemma integrable_sum_comp_stoppingTime {f : 𝓧 → ℝ} (hf : Integrable f μ)
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ)))
    (hτ_int : Integrable (fun ω ↦ (τ ω : ℝ)) (Measure.infinitePi fun _ ↦ μ)) :
    Integrable (fun ω ↦ ∑ n ∈ Finset.Iic (τ ω), f (ω n)) (Measure.infinitePi fun _ ↦ μ) :=
  integrable_sum_Iic_of_summable (X := fun n ω ↦ f (ω n))
    (fun n ↦ ((measurePreserving_eval_infinitePi _ n).integrable_comp_of_integrable hf)
      |>.integrableOn)
    (measurable_of_isStoppingTime (τ := τ) hτ)
    (summable_setIntegral_abs_le_stoppingTime hf.aestronglyMeasurable hτ hτ_int)

/-- **Wald's identity** for i.i.d. sequences: for an integrable stopping time `τ`,
`∫ ω, ∑ n ≤ τ ω, f (ω n) ∂μ^ℕ = (∫ ω, (τ ω + 1) ∂μ^ℕ) * ∫ f ∂μ`. -/
theorem integral_sum_comp_stoppingTime {f : 𝓧 → ℝ} (hf : Integrable f μ)
    (hτ : IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (τ ω : WithTop ℕ)))
    (hτ_int : Integrable (fun ω ↦ (τ ω : ℝ)) (Measure.infinitePi fun _ ↦ μ)) :
    ∫ ω, ∑ n ∈ Finset.Iic (τ ω), f (ω n) ∂(Measure.infinitePi fun _ ↦ μ)
      = (∫ ω, (τ ω + 1 : ℝ) ∂(Measure.infinitePi fun _ ↦ μ)) * ∫ x, f x ∂μ := by
  rw [integral_sum_Iic_eq_integral_sum_Iic_integral (X := fun n ω ↦ f (ω n))
    (fun n ↦ (measurePreserving_eval_infinitePi _ n).integrable_comp_of_integrable hf)
    (measurable_of_isStoppingTime (τ := τ) hτ)
    (fun n ↦ by rw [setIntegral_comp_eval_le_stoppingTime hf.aestronglyMeasurable hτ n,
      integral_comp_eval_infinitePi hf.aestronglyMeasurable])
    (summable_setIntegral_abs_le_stoppingTime hf.aestronglyMeasurable hτ hτ_int)]
  simp_rw [integral_comp_eval_infinitePi (μ := fun _ ↦ μ) hf.aestronglyMeasurable, Finset.sum_const,
    Nat.card_Iic, nsmul_eq_mul]
  rw [integral_mul_const]
  push_cast
  -- the two sides differ only in the instance paths of the integrals
  rfl

end IID

end ProbabilityTheory
