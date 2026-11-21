/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.Basic
public import Statlib.Divergence.MutualInformation.Basic

/-!
# Mutual information is at most maximal leakage

Let `X ∼ μ` be an input on a countable alphabet and `Y` the output of a channel `κ` with a finite
output alphabet. Lemma 2 of Issa, Wagner and Kamath states that the mutual information is at most
the maximal leakage: `I(X; Y) ≤ L(X → Y) = log ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`.

## Main statements

* `mutualInfo_compProd_le_ofReal_maxLeakage`: `I(X; Y) ≤ L(X → Y)`, in `ℝ≥0∞`.
* `mutualInfo_compProd_ne_top`: in particular `I(X; Y)` is finite.
* `toReal_mutualInfo_compProd_le_maxLeakage`: `I(X; Y) ≤ L(X → Y)`, in `ℝ`.

## Implementation notes

Instead of applying Jensen's inequality to a finite-sum formula for `I(X; Y)`, we compare the
joint law with `μ × ν`, where `ν {y} ∝ max_{x ∈ supp μ} κ x {y}`. The compensation identity gives
`I(X; Y) ≤ KL(μ ⊗ κ, μ × ν) = ∫ KL(κ x, ν) dμ(x)`. Writing `S = ∑_y max_{x ∈ supp μ} κ x {y}`, every
atom `x` of `μ` satisfies `κ x {y} ≤ S * ν {y}`, so the log-likelihood ratio of `κ x` with respect
to `ν` is bounded by `log S` and `KL(κ x, ν) ≤ log S = L(X → Y)`.

## References

* I. Issa, A. B. Wagner, S. Kamath, *An operational approach to information leakage*,
  IEEE Trans. Inf. Theory 66(3), 2020, Lemma 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}

section Auxiliary

/- General-purpose lemmas, independent of maximal leakage; candidates for Mathlib. -/

/-- A nonzero measure on a countable space has an atom. -/
lemma _root_.MeasureTheory.Measure.exists_measure_singleton_ne_zero [Countable α]
    (μ : Measure α) [NeZero μ] :
    ∃ x, μ {x} ≠ 0 := by
  by_contra! h
  exact NeZero.ne μ <| Measure.measure_univ_eq_zero.1 <|
    (measure_null_iff_singleton Set.countable_univ).2 fun x _ ↦ h x

/-- On a finite space, if `μ {y} ≤ c * ν {y}` for every `y`, then the Kullback-Leibler divergence
between the probability measures `μ` and `ν` is at most `log c`. -/
lemma klDiv_le_ofReal_log_of_forall_le [Finite β] [MeasurableSingletonClass β]
    {μ ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : ∀ y, μ {y} ≤ c * ν {y}) :
    klDiv μ ν ≤ ENNReal.ofReal (Real.log c.toReal) := by
  have hac : μ ≪ ν := fun s hs ↦ by
    rw [measure_eq_zero_iff_ae_notMem, ae_iff_of_countable] at hs ⊢
    exact fun y hy ↦ hs y fun hνy ↦ hy (by simpa [hνy] using h y)
  have h_int : Integrable (llr μ ν) μ := .of_finite
  -- At every atom `y` of `μ`, the density `dμ/dν` is positive and at most `c`.
  have h_llr : ∀ᵐ y ∂μ, llr μ ν y ≤ Real.log c.toReal := by
    refine ae_iff_of_countable.2 fun y hy ↦ ?_
    have hy_eq : μ {y} = μ.rnDeriv ν y * ν {y} := by
      rw [← Measure.setLIntegral_rnDeriv hac, lintegral_singleton]
    have h_pos : μ.rnDeriv ν y ≠ 0 := fun h0 ↦ hy (by simp [hy_eq, h0])
    have hνy : ν {y} ≠ 0 := fun h0 ↦ hy (by simp [hy_eq, h0])
    have h_le : μ.rnDeriv ν y ≤ c :=
      (ENNReal.mul_le_mul_iff_left hνy (measure_ne_top ν _)).1 (hy_eq ▸ h y)
    exact Real.log_le_log (ENNReal.toReal_pos h_pos (ne_top_of_le_ne_top hc h_le))
      (ENNReal.toReal_mono hc h_le)
  calc klDiv μ ν = ENNReal.ofReal (∫ y, llr μ ν y ∂μ) := by
        simp [klDiv_of_ac_of_integrable hac h_int]
    _ ≤ ENNReal.ofReal (∫ _, Real.log c.toReal ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae h_int (integrable_const _) h_llr)
    _ = ENNReal.ofReal (Real.log c.toReal) := by simp

end Auxiliary

variable [Countable α] [Fintype β] [MeasurableSingletonClass β] [IsProbabilityMeasure μ]
  [IsMarkovKernel κ]

/-- **Mutual information is at most maximal leakage** (Issa–Wagner–Kamath, Lemma 2):
`I(X; Y) ≤ L(X → Y)` for `X ∼ μ` on a countable alphabet and `Y` the output of the channel `κ`. -/
theorem mutualInfo_compProd_le_ofReal_maxLeakage :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal (maxLeakage μ κ) := by
  obtain ⟨x₀, hx₀⟩ := MeasureTheory.Measure.exists_measure_singleton_ne_zero μ
  set S := maxLeakageSum μ κ
  have hS₀ : S ≠ 0 := (zero_lt_one.trans_le (one_le_maxLeakageSum hx₀)).ne'
  have hS : S ≠ ∞ := maxLeakageSum_ne_top
  -- The output law `ν {y} = S⁻¹ * max_{x ∈ supp μ} κ x {y}`.
  let ν : Measure β := S⁻¹ • Measure.sum fun y ↦ (⨆ (x) (_ : μ {x} ≠ 0), κ x {y}) • .dirac y
  have hν (y : β) : ν {y} = S⁻¹ * ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} := by
    simp only [ν, smul_apply, Measure.sum_smul_dirac_singleton, smul_eq_mul]
  have : IsProbabilityMeasure ν :=
    ⟨by simpa [ν, S, maxLeakageSum] using ENNReal.inv_mul_cancel hS₀ hS⟩
  calc mutualInfo (μ ⊗ₘ κ) ≤ klDiv (μ ⊗ₘ κ) (μ.prod ν) :=
        le_self_add.trans_eq (klDiv_compProd_prod_eq_mutualInfo_add μ κ ν).symm
    _ = ∫⁻ x, klDiv (κ x) ν ∂μ := by
        rw [← Measure.compProd_const, ← condKL, condKL_eq_lintegral]
        simp
    _ ≤ ∫⁻ _, ENNReal.ofReal (maxLeakage μ κ) ∂μ := by
        refine lintegral_mono_ae <| ae_iff_of_countable.2 fun x hx ↦ ?_
        refine klDiv_le_ofReal_log_of_forall_le hS fun y ↦ ?_
        rw [hν, ENNReal.mul_inv_cancel_left hS₀ hS]
        exact le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y}) x hx
    _ = ENNReal.ofReal (maxLeakage μ κ) := by simp

omit [Fintype β] in
/-- The mutual information between an input on a countable alphabet and the output of a channel
with a finite output alphabet is finite. -/
theorem mutualInfo_compProd_ne_top [Finite β] : mutualInfo (μ ⊗ₘ κ) ≠ ∞ := by
  have := Fintype.ofFinite β
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top mutualInfo_compProd_le_ofReal_maxLeakage

/-- **Mutual information is at most maximal leakage** (Issa–Wagner–Kamath, Lemma 2), real-valued
version: `I(X; Y) ≤ L(X → Y)`. -/
theorem toReal_mutualInfo_compProd_le_maxLeakage :
    (mutualInfo (μ ⊗ₘ κ)).toReal ≤ maxLeakage μ κ := by
  obtain ⟨x, hx⟩ := MeasureTheory.Measure.exists_measure_singleton_ne_zero μ
  exact ENNReal.toReal_le_of_le_ofReal (maxLeakage_nonneg hx)
    mutualInfo_compProd_le_ofReal_maxLeakage

end InformationTheory
