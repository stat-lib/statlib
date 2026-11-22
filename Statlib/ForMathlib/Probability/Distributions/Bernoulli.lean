/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Statlib.ForMathlib.MeasureTheory.Measure.Bool

/-!
# Bernoulli distribution: integrals, symmetry and the Bernoulli kernel

Complements to `Mathlib.Probability.Distributions.Bernoulli`: the Lebesgue integral against
`Ber(x, y, p)`, its masses at `x` and `y`, Bernoulli distributions on `Bool`, and the Markov
kernel from the unit interval which maps `p` to `Ber(x, y, p)`.

## Main definitions

* `bernoulliKernel x y`: the Markov kernel `p ↦ Ber(x, y, p)` from the unit interval.

## Main statements

* `lintegral_bernoulliMeasure`: the Lebesgue integral against `Ber(x, y, p)`.
* `bernoulliMeasure_swap`: `Ber(y, x, σ p) = Ber(x, y, p)`.
* `bernoulliMeasure_eq_dirac_of_dirac_eq`: if `dirac x = dirac y`, then `Ber(x, y, p) = dirac x`.
* `eq_bernoulliMeasure_real_true`: every probability measure on `Bool` is a Bernoulli distribution.
* `MeasureTheory.Measure.boolMeasure_ofReal_eq_bernoulliMeasure`: the prior
  `boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p))` on `Bool` is `Ber(false, true, p)`.
* `bernoulliMeasure_eq_smul_add_smul`: a Bernoulli distribution whose parameter is a convex
  combination of `a` and `b` is the corresponding mixture of `Ber(x, y, a)` and `Ber(x, y, b)`.
* `bernoulliMeasure_eq_withDensity`: for `x ≠ y` and `q ∉ {0, 1}`, `Ber(x, y, p)` has density
  `p / q` at `x` and `(1 - p) / (1 - q)` at `y` with respect to `Ber(x, y, q)`; hence
  `Ber(x, y, p) ≪ Ber(x, y, q)` (`bernoulliMeasure_absolutelyContinuous`) and the Radon-Nikodym
  derivative is that density (`rnDeriv_bernoulliMeasure`).
* `bernoulliKernel_comp_apply_singleton_left`: for `x ≠ y`, the composition of `bernoulliKernel x y`
  with a measure `μ` on the unit interval gives mass `∫⁻ p, p ∂μ` to `x`.
* `bernoulliKernel_comp_eq_bernoulliMeasure`: the composition of `bernoulliKernel x y` with a
  probability measure on the unit interval with mean `p` is `Ber(x, y, p)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace unitInterval

lemma coe_toNNReal_eq_ofReal (p : I) : (toNNReal p : ℝ≥0∞) = ENNReal.ofReal p := by
  rw [ENNReal.ofReal, show Real.toNNReal p = toNNReal p from Real.toNNReal_of_nonneg p.property.1]

lemma coe_toNNReal_symm_eq_ofReal (p : I) :
    (toNNReal (σ p) : ℝ≥0∞) = ENNReal.ofReal (1 - p) := by
  rw [coe_toNNReal_eq_ofReal, coe_symm_eq]

/-- The inclusion of the unit interval in `ℝ` is integrable with respect to any finite measure. -/
lemma integrable_coe (μ : Measure I) [IsFiniteMeasure μ] : Integrable (fun p : I ↦ (p : ℝ)) μ :=
  .of_bound (by fun_prop) 1
    (ae_of_all _ fun p ↦ by simpa [abs_of_nonneg p.property.1] using p.property.2)

end unitInterval

open unitInterval

namespace ProbabilityTheory

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

lemma bernoulliMeasure_swap (x y : 𝓧) (p : I) : Ber(y, x, σ p) = Ber(x, y, p) := by
  rw [bernoulliMeasure_def, bernoulliMeasure_def, symm_symm, add_comm]

/-- If no measurable set separates `x` and `y`, that is `dirac x = dirac y`, then
`Ber(x, y, p) = dirac x`. This generalizes `bernoulliMeasure_self_eq_dirac`. -/
lemma bernoulliMeasure_eq_dirac_of_dirac_eq {x y : 𝓧} (h : Measure.dirac x = Measure.dirac y)
    (p : I) :
    Ber(x, y, p) = Measure.dirac x := by
  simp [bernoulliMeasure_def, ← h, ← add_smul]

lemma lintegral_bernoulliMeasure [MeasurableSingletonClass 𝓧] (x y : 𝓧) (p : I)
    (f : 𝓧 → ℝ≥0∞) :
    ∫⁻ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, ENNReal.smul_def, ENNReal.smul_def, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
    coe_toNNReal_eq_ofReal, coe_toNNReal_symm_eq_ofReal, smul_eq_mul, smul_eq_mul]

/-- Version of `lintegral_bernoulliMeasure` for a measurable function, without
`MeasurableSingletonClass`. -/
lemma lintegral_bernoulliMeasure' (x y : 𝓧) (p : I) {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, ENNReal.smul_def, ENNReal.smul_def, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac' _ hf, lintegral_dirac' _ hf,
    coe_toNNReal_eq_ofReal, coe_toNNReal_symm_eq_ofReal, smul_eq_mul, smul_eq_mul]

lemma bernoulliMeasure_apply_singleton_left [MeasurableSingletonClass 𝓧] {x y : 𝓧} (hxy : x ≠ y)
    (p : I) :
    Ber(x, y, p) {x} = ENNReal.ofReal p := by
  rw [bernoulliMeasure_apply_of_mem_of_notMem p (.singleton _) rfl hxy.symm,
    coe_toNNReal_eq_ofReal]

lemma bernoulliMeasure_apply_singleton_right [MeasurableSingletonClass 𝓧] {x y : 𝓧} (hxy : x ≠ y)
    (p : I) :
    Ber(x, y, p) {y} = ENNReal.ofReal (1 - p) := by
  rw [bernoulliMeasure_apply_of_notMem_of_mem p (.singleton _) hxy rfl,
    coe_toNNReal_symm_eq_ofReal]

/-- A probability measure on `Bool` is the Bernoulli distribution with parameter its mass at
`true`. -/
lemma eq_bernoulliMeasure_real_true (R : Measure Bool) [IsProbabilityMeasure R] :
    R = Ber(true, false,
      ⟨R.real {true}, Set.mem_Icc.mpr ⟨measureReal_nonneg, measureReal_le_one⟩⟩) := by
  have h_false : R {false} = 1 - R {true} := by
    rw [← measure_univ (μ := R), ← measure_add_measure_compl (MeasurableSet.singleton true),
      show ({true} : Set Bool)ᶜ = {false} by ext b; simp, ENNReal.add_sub_cancel_left
        (measure_ne_top _ _)]
  refine Measure.ext_of_singleton fun b ↦ ?_
  cases b
  · rw [h_false, bernoulliMeasure_apply_singleton_right (by decide),
      ENNReal.ofReal_sub _ measureReal_nonneg, ENNReal.ofReal_one, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [bernoulliMeasure_apply_singleton_left (by decide)]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- A Bernoulli distribution whose parameter is a convex combination of `a` and `b` is the
corresponding mixture of Bernoulli distributions. -/
lemma bernoulliMeasure_eq_smul_add_smul (x y : 𝓧) {a b c : I} {t : ℝ≥0} (ht : t ≤ 1)
    (hc : (c : ℝ) = t * a + (1 - t) * b) :
    Ber(x, y, c) = t • Ber(x, y, a) + (1 - t) • Ber(x, y, b) := by
  have h1 : toNNReal c = t * toNNReal a + (1 - t) * toNNReal b := by
    ext
    simp [hc, NNReal.coe_sub ht]
  have h2 : toNNReal (σ c) = t * toNNReal (σ a) + (1 - t) * toNNReal (σ b) := by
    ext
    simp only [coe_toNNReal, coe_symm_eq, hc, NNReal.coe_add, NNReal.coe_mul,
      NNReal.coe_sub ht, NNReal.coe_one]
    ring
  simp only [bernoulliMeasure_def, smul_add, smul_smul, h1, h2, add_smul]
  abel

/-! ### Densities of Bernoulli distributions

The following lemmas are copied from LMLPapers
(`LeanMachineLearning/ForMathlib/Probability/Distributions/Bernoulli.lean`). -/

section Density

variable [MeasurableSingletonClass 𝓧] {x y : 𝓧} {q : I}

/-- For `x ≠ y` and `q ∉ {0, 1}`, the Bernoulli measure `Ber(x, y, p)` has density `p / q` at `x`
and `(1 - p) / (1 - q)` at `y` with respect to `Ber(x, y, q)`. -/
lemma bernoulliMeasure_eq_withDensity [DecidableEq 𝓧] (hxy : x ≠ y) (p : I) (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    Ber(x, y, p) = Ber(x, y, q).withDensity
      (fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))) := by
  have hq0 : (q : ℝ) ≠ 0 := coe_ne_zero.2 hq
  have hq1' : (1 : ℝ) - q ≠ 0 := sub_ne_zero.2 (coe_ne_one.2 hq1).symm
  rw [bernoulliMeasure_def, bernoulliMeasure_def, withDensity_add_measure]
  simp_rw [ENNReal.smul_def]
  rw [withDensity_smul_measure, withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
    ite_eq_left rfl, ite_eq_right hxy.symm, smul_smul, smul_smul]
  simp only [coe_toNNReal_eq_ofReal, coe_symm_eq]
  congr 1 <;> congr 1
  · rw [← ENNReal.ofReal_mul q.property.1]
    congr 1
    field_simp
  · rw [← ENNReal.ofReal_mul (sub_nonneg.2 q.property.2)]
    congr 1
    field_simp

/-- For `x ≠ y` and `q ∉ {0, 1}`, `Ber(x, y, p) ≪ Ber(x, y, q)`. -/
lemma bernoulliMeasure_absolutelyContinuous (hxy : x ≠ y) (p : I) (hq : q ≠ 0) (hq1 : q ≠ 1) :
    Ber(x, y, p) ≪ Ber(x, y, q) := by
  classical
  rw [bernoulliMeasure_eq_withDensity hxy p hq hq1]
  exact withDensity_absolutelyContinuous _ _

/-- The Radon-Nikodym derivative of `Ber(x, y, p)` with respect to `Ber(x, y, q)`, for `x ≠ y` and
`q ∉ {0, 1}`. -/
lemma rnDeriv_bernoulliMeasure [DecidableEq 𝓧] (hxy : x ≠ y) (p : I) (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    Ber(x, y, p).rnDeriv Ber(x, y, q) =ᵐ[Ber(x, y, q)]
      fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q)) := by
  rw [bernoulliMeasure_eq_withDensity hxy p hq hq1]
  exact Measure.rnDeriv_withDensity _
    (Measurable.ite (measurableSet_singleton x) measurable_const measurable_const)

end Density

/-- The Markov kernel from the unit interval to `𝓧` which maps `p` to the Bernoulli distribution
`Ber(x, y, p)`. -/
noncomputable def bernoulliKernel (x y : 𝓧) : Kernel I 𝓧 where
  toFun p := Ber(x, y, p)
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp_rw [bernoulliMeasure_apply _ hs]
    split_ifs <;> fun_prop

lemma bernoulliKernel_apply (x y : 𝓧) (p : I) : bernoulliKernel x y p = Ber(x, y, p) := rfl

instance (x y : 𝓧) : IsMarkovKernel (bernoulliKernel x y) :=
  ⟨fun p ↦ by rw [bernoulliKernel_apply]; infer_instance⟩

/-- The mass at `x` of the composition of `bernoulliKernel x y` with a measure on the unit interval
is the integral of the identity. -/
lemma bernoulliKernel_comp_apply_singleton_left [MeasurableSingletonClass 𝓧] {x y : 𝓧}
    (hxy : x ≠ y) (μ : Measure I) :
    (bernoulliKernel x y ∘ₘ μ) {x} = ∫⁻ p, ENNReal.ofReal p ∂μ := by
  rw [Measure.bind_apply (MeasurableSet.singleton x) (bernoulliKernel x y).aemeasurable]
  simp_rw [bernoulliKernel_apply, bernoulliMeasure_apply_singleton_left hxy]

/-- The mass at `x` of the composition of `bernoulliKernel x y` with a finite measure on the unit
interval is the integral of the identity. -/
lemma bernoulliKernel_comp_real_apply_singleton_left [MeasurableSingletonClass 𝓧] {x y : 𝓧}
    (hxy : x ≠ y) (μ : Measure I) [IsFiniteMeasure μ] :
    (bernoulliKernel x y ∘ₘ μ).real {x} = ∫ p, (p : ℝ) ∂μ := by
  rw [measureReal_def, bernoulliKernel_comp_apply_singleton_left hxy,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_coe μ) (ae_of_all _ fun p ↦ p.property.1),
    ENNReal.toReal_ofReal (integral_nonneg fun p ↦ p.property.1)]

/-- The composition of `bernoulliKernel x y` with a probability measure on the unit interval with
mean `p` is `Ber(x, y, p)`. -/
lemma bernoulliKernel_comp_eq_bernoulliMeasure (x y : 𝓧) (μ : Measure I) [IsProbabilityMeasure μ]
    {p : I} (hp : (p : ℝ) = ∫ q, (q : ℝ) ∂μ) :
    bernoulliKernel x y ∘ₘ μ = Ber(x, y, p) := by
  have h_int := integrable_coe μ
  have h1 : ∫⁻ q, ENNReal.ofReal q ∂μ = ENNReal.ofReal p := by
    rw [hp, ofReal_integral_eq_lintegral_ofReal h_int (ae_of_all _ fun q ↦ q.property.1)]
  have h2 : ∫⁻ q, ENNReal.ofReal (1 - q) ∂μ = ENNReal.ofReal (1 - p) := by
    have h_int' : Integrable (fun q : I ↦ 1 - (q : ℝ)) μ := (integrable_const 1).sub h_int
    rw [← ofReal_integral_eq_lintegral_ofReal h_int'
        (ae_of_all _ fun q ↦ sub_nonneg.mpr q.property.2),
      integral_sub (integrable_const 1) h_int, hp]
    simp
  ext s hs
  rw [Measure.bind_apply hs (bernoulliKernel x y).aemeasurable]
  simp_rw [bernoulliKernel_apply, bernoulliMeasure_def, add_apply, smul_apply,
    ENNReal.smul_def, smul_eq_mul, coe_toNNReal_eq_ofReal, coe_symm_eq]
  rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
    lintegral_mul_const _ (by fun_prop), h1, h2]

end ProbabilityTheory

namespace MeasureTheory.Measure

open ProbabilityTheory

/-- The prior `boolMeasure p (1 - p)` on `Bool` is the Bernoulli distribution
`Ber(false, true, p)`. -/
lemma boolMeasure_ofReal_eq_bernoulliMeasure (p : I) :
    boolMeasure (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)) = Ber(false, true, p) := by
  refine ext_bool ?_ ?_
  · rw [boolMeasure_apply_false, bernoulliMeasure_apply_singleton_left (by decide)]
  · rw [boolMeasure_apply_true, bernoulliMeasure_apply_singleton_right (by decide)]

end MeasureTheory.Measure
