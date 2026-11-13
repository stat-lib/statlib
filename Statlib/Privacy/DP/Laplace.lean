/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.DP.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Probability.Kernel.WithDensity

/-!
# The Laplace mechanism

The Laplace mechanism of C. Dwork, F. McSherry, K. Nissim and A. Smith, *Calibrating noise to
sensitivity in private data analysis*, TCC 2006, releases a real-valued query `f(x)` with additive
Laplace noise whose scale is calibrated to the sensitivity of `f`. We follow C. Dwork and
A. Roth, *The Algorithmic Foundations of Differential Privacy*, Found. Trends Theor. Comput. Sci.
9(3–4), 2014, Section 3.3 (result numbers refer to this book).

The Laplace distribution `Lap(μ, b)` with location `μ` and scale `b > 0` has density
`(2b)⁻¹ exp (-|y - μ| / b)` with respect to Lebesgue measure. The Laplace mechanism with scale `b`
is the kernel `x ↦ Lap(f(x), b)`, i.e. `f(x) + Y` with `Y ∼ Lap(b)`. It is built as
`Kernel.withDensity` of the constant kernel `x ↦ volume`; it is a Markov kernel as soon as `f` is
measurable (`isMarkovKernel_laplaceMechanism`), and then its output law at `x` is
`Lap(f(x), b)` (`laplaceMechanism_apply`). The privacy and accuracy theorems assume `f`
measurable.

Privacy is measured with `IsEpsDeltaDP` from `Statlib.Privacy.DP.Basic` at `δ = 0` (pure
`ε`-differential privacy) for an arbitrary neighbouring relation `Adj` on datasets. The
sensitivity is a hypothesis: `Δ > 0` is any upper bound on `|f(x) - f(x')|` (respectively on the
`ℓ₁` distance `∑_i |f(x)_i - f(x')_i|` for vector-valued queries) over neighbouring `x, x'`
(Dwork–Roth use the exact `ℓ₁`-sensitivity `Δf`, Definition 3.1, the smallest such bound).
Vector-valued queries `f : 𝒟 → (ι → ℝ)` (Dwork–Roth's `ℝ^k`, with `k = |ι|`) get i.i.d. noise in
each coordinate: the output law is the measure with the product Laplace density on `ι → ℝ`, which
is the product measure `∏_i Lap(f(x)_i, b)` (`laplaceMechanismPi_apply`).

## Main definitions

* `laplacePDFReal μ b`, `laplacePDF μ b`: the Laplace density (Definition 3.2), real- and
  `ℝ≥0∞`-valued.
* `laplaceMeasure μ b`: the Laplace distribution `Lap(μ, b)` on `ℝ`.
* `laplaceMechanism f b`: the Laplace mechanism `x ↦ f(x) + Lap(b)` for a real-valued query
  (Definition 3.3 with `k = 1`, the scale `b = Δf / ε` left as a parameter).
* `laplacePiPDFReal μ b`: the product Laplace density on `ι → ℝ`.
* `laplaceMechanismPi f b`: the Laplace mechanism `x ↦ f(x) + (Y_i)_{i ∈ ι}`, `Y_i` i.i.d.
  `Lap(b)`, for a vector-valued query (Definition 3.3); its output law is
  `Measure.pi fun i ↦ laplaceMeasure (f x i) b` (`laplaceMechanismPi_apply`).

## Main statements (source result → Lean name)

* The Laplace density integrates to one: `integral_laplacePDFReal_eq_one`,
  `lintegral_laplacePDF_eq_one`; `laplaceMeasure μ b` is a probability measure:
  `isProbabilityMeasure_laplaceMeasure`; the mechanisms are Markov kernels:
  `isMarkovKernel_laplaceMechanism`, `isMarkovKernel_laplaceMechanismPi`.
* Theorem 3.6 (privacy): `isEpsDeltaDP_laplaceMechanismPi` (vector-valued queries, `ℓ₁`
  sensitivity) and its scalar case `isEpsDeltaDP_laplaceMechanism`; the latter also in the form
  `isEpsDeltaDP_laplaceMechanism_of_le` for an arbitrary scale `b ≥ Δ / ε`.
* Fact 3.7 (tail of the Laplace distribution): `laplaceMeasure_real_le_abs_sub`.
* Theorem 3.8 (accuracy): `laplaceMechanismPi_real_le_norm_sub` (vector-valued queries, sup
  norm, `k = |ι| ≥ 1`), and its scalar case `laplaceMechanism_real_le_abs_sub`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace InformationTheory

variable {𝒟 : Type*}

namespace Laplace

/-- A kernel `x ↦ μ.withDensity (f x)` with jointly measurable, normalizable densities
satisfying the pointwise bound `f x ≤ e^ε f x'` on neighbours is `ε`-differentially private. -/
lemma isEpsDeltaDP_withDensity_const {𝒟 Y : Type*} [MeasurableSpace 𝒟] [MeasurableSpace Y]
    {μ : Measure Y} [SFinite μ] {f : 𝒟 → Y → ℝ≥0∞} {Adj : 𝒟 → 𝒟 → Prop} {ε : ℝ}
    (hf : Measurable (Function.uncurry f)) (hfin : ∀ x, ∫⁻ y, f x y ∂μ ≠ ∞)
    (h : ∀ ⦃x x'⦄, Adj x x' → ∀ y, f x y ≤ ENNReal.ofReal (exp ε) * f x' y) :
    IsEpsDeltaDP ((Kernel.const 𝒟 μ).withDensity f) Adj ε 0 := by
  intro x x' hx E
  simp only [Kernel.withDensity_apply _ hf, Kernel.const_apply, add_zero]
  have hle : μ.withDensity (f x) E ≤ ENNReal.ofReal (exp ε) * μ.withDensity (f x') E := by
    have hμ : μ.withDensity (f x) ≤ ENNReal.ofReal (exp ε) • μ.withDensity (f x') := by
      rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      exact withDensity_mono (ae_of_all _ (h hx))
    simpa using hμ E
  have hfin' : μ.withDensity (f x') E ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ E))
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hfin x'
  rw [measureReal_def, measureReal_def, ← ENNReal.toReal_ofReal (exp_pos ε).le,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin') hle

end Laplace

open Laplace

/-! ### The Laplace distribution -/

section LaplacePDF

variable {μ b : ℝ}

/-- The density `(2b)⁻¹ exp (-|y - μ| / b)` of the Laplace distribution with location `μ` and
scale `b` (Dwork–Roth, Definition 3.2, there with `μ = 0`). It is a probability density for
`b > 0`. -/
noncomputable def laplacePDFReal (μ b y : ℝ) : ℝ :=
  (2 * b)⁻¹ * exp (-|y - μ| / b)

/-- The Laplace density as an `ℝ≥0∞`-valued function. -/
noncomputable def laplacePDF (μ b y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (laplacePDFReal μ b y)

lemma laplacePDFReal_pos (hb : 0 < b) (y : ℝ) : 0 < laplacePDFReal μ b y := by
  unfold laplacePDFReal
  positivity

@[fun_prop]
lemma measurable_laplacePDFReal (μ b : ℝ) : Measurable (laplacePDFReal μ b) := by
  unfold laplacePDFReal
  fun_prop

@[fun_prop]
lemma measurable_laplacePDF (μ b : ℝ) : Measurable (laplacePDF μ b) := by
  unfold laplacePDF
  fun_prop

/-- The Laplace density integrates to one. -/
lemma integral_laplacePDFReal_eq_one (μ : ℝ) (hb : 0 < b) : ∫ y, laplacePDFReal μ b y = 1 := by
  have hI : ∫ y in Ioi (0 : ℝ), exp (-b⁻¹ * y) = b := by
    rw [integral_exp_mul_Ioi (neg_lt_zero.2 (inv_pos.2 hb)), mul_zero, exp_zero]
    field_simp
  unfold laplacePDFReal
  rw [integral_const_mul, integral_sub_right_eq_self (fun y ↦ exp (-|y| / b)) μ,
    integral_comp_abs (f := fun y ↦ exp (-y / b))]
  simp_rw [neg_div, div_eq_inv_mul, ← neg_mul]
  rw [hI]
  field_simp

lemma integrable_laplacePDFReal (μ : ℝ) (hb : 0 < b) : Integrable (laplacePDFReal μ b) :=
  Integrable.of_integral_ne_zero (by simp [integral_laplacePDFReal_eq_one μ hb])

/-- The Laplace density integrates to one. -/
lemma lintegral_laplacePDF_eq_one (μ : ℝ) (hb : 0 < b) : ∫⁻ y, laplacePDF μ b y = 1 := by
  unfold laplacePDF
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun y ↦ (laplacePDFReal_pos hb y).le) (by fun_prop),
    integral_laplacePDFReal_eq_one μ hb]

/-- The Laplace distribution `Lap(μ, b)` with location `μ` and scale `b`: the measure on `ℝ`
with density `laplacePDF μ b` with respect to Lebesgue measure. It is a probability measure for
`b > 0` (`isProbabilityMeasure_laplaceMeasure`). -/
noncomputable def laplaceMeasure (μ b : ℝ) : Measure ℝ :=
  volume.withDensity (laplacePDF μ b)

lemma isProbabilityMeasure_laplaceMeasure (μ : ℝ) (hb : 0 < b) :
    IsProbabilityMeasure (laplaceMeasure μ b) :=
  ⟨by rw [laplaceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_laplacePDF_eq_one μ hb]⟩

/-- **Likelihood ratio of shifted Laplace densities**: if `|μ - μ'| ≤ ε b`, then
`Lap(y | μ, b) ≤ e^ε Lap(y | μ', b)` for every `y` (the computation in the proof of Dwork–Roth,
Theorem 3.6). -/
lemma laplacePDFReal_le_exp_mul {μ' ε : ℝ} (hb : 0 < b) (h : |μ - μ'| ≤ ε * b) (y : ℝ) :
    laplacePDFReal μ b y ≤ exp ε * laplacePDFReal μ' b y := by
  unfold laplacePDFReal
  rw [mul_left_comm, ← exp_add]
  gcongr
  have h₁ : |y - μ'| ≤ |y - μ| + |μ - μ'| := abs_sub_le y μ μ'
  rw [← sub_nonneg, show ε + -|y - μ'| / b - -|y - μ| / b = (ε * b - |y - μ'| + |y - μ|) / b by
    field_simp; ring]
  exact div_nonneg (by linarith) hb.le

/-- **Dwork–Roth, Fact 3.7**: if `Y ∼ Lap(μ, b)` with `b > 0`, then `P[|Y - μ| ≥ t b] = e^{-t}`
for every `t ≥ 0`. -/
theorem laplaceMeasure_real_le_abs_sub (μ : ℝ) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    (laplaceMeasure μ b).real {y | t * b ≤ |y - μ|} = exp (-t) := by
  have := isProbabilityMeasure_laplaceMeasure μ hb
  rcases ht.eq_or_lt with rfl | ht
  · simp
  set c := t * b with hc_def
  have hE : MeasurableSet {y : ℝ | c ≤ |y - μ|} := measurableSet_le measurable_const (by fun_prop)
  -- pass to a Bochner integral of `k (|y - μ|)`
  set k : ℝ → ℝ := fun s ↦ if c ≤ s then (2 * b)⁻¹ * exp (-b⁻¹ * s) else 0 with hk
  have h₁ : (laplaceMeasure μ b).real {y | c ≤ |y - μ|} = ∫ y, k |y - μ| := by
    rw [measureReal_def, laplaceMeasure, withDensity_apply _ hE]
    unfold laplacePDF
    rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y ↦ (laplacePDFReal_pos hb y).le)
        (by fun_prop), ← integral_indicator hE]
    congr 1
    ext y
    simp only [Set.indicator, Set.mem_ofPred_eq, k, laplacePDFReal, div_eq_inv_mul, mul_neg,
      neg_mul]
  -- on `(0, ∞)`, `k` is the restriction of the exponential density to `[c, ∞)`
  have h₂ : ∫ s in Ioi 0, k s = ∫ s in Ici c, (2 * b)⁻¹ * exp (-b⁻¹ * s) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ici]
    congr 1
    ext s
    have : 0 < c := mul_pos ht hb
    simp only [Set.indicator, mem_Ioi, mem_Ici, k]
    split_ifs <;> first | rfl | linarith
  rw [h₁, integral_sub_right_eq_self (fun y ↦ k |y|) μ, integral_comp_abs (f := k), h₂,
    integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (neg_lt_zero.2 (inv_pos.2 hb)), hc_def]
  field_simp

end LaplacePDF

/-! ### The Laplace mechanism -/

section Mechanism

variable [MeasurableSpace 𝒟] {f : 𝒟 → ℝ} {b ε Δ : ℝ}

/-- **The Laplace mechanism** `M_L(x, f, ε) = f(x) + Lap(b)` (Dwork–Roth, Definition 3.3, case
`k = 1`), with the noise scale `b` as a parameter (Dwork–Roth take `b = Δf / ε`): on dataset `x`
it outputs a sample of `Lap(f(x), b)`. It is built as the kernel with density
`(x, y) ↦ laplacePDF (f x) b y` with respect to the constant kernel `x ↦ volume`, which is the
intended kernel when `f` is measurable (`laplaceMechanism_apply`) and the zero kernel otherwise. -/
noncomputable def laplaceMechanism (f : 𝒟 → ℝ) (b : ℝ) : Kernel 𝒟 ℝ :=
  (Kernel.const 𝒟 volume).withDensity fun x ↦ laplacePDF (f x) b

lemma measurable_uncurry_laplacePDF (hf : Measurable f) (b : ℝ) :
    Measurable (Function.uncurry fun x ↦ laplacePDF (f x) b) := by
  unfold laplacePDF laplacePDFReal
  fun_prop

lemma laplaceMechanism_apply (hf : Measurable f) (b : ℝ) (x : 𝒟) :
    laplaceMechanism f b x = laplaceMeasure (f x) b := by
  rw [laplaceMechanism, Kernel.withDensity_apply _ (measurable_uncurry_laplacePDF hf b),
    Kernel.const_apply, laplaceMeasure]

/-- The Laplace mechanism with a measurable query and positive scale is a Markov kernel. -/
lemma isMarkovKernel_laplaceMechanism (hf : Measurable f) (hb : 0 < b) :
    IsMarkovKernel (laplaceMechanism f b) :=
  ⟨fun x ↦ by rw [laplaceMechanism_apply hf]; exact isProbabilityMeasure_laplaceMeasure _ hb⟩

/-- The Laplace mechanism with scale `b > 0` is `ε`-differentially private as soon as
`|f(x) - f(x')| ≤ ε b` for all neighbouring `x, x'` (a form of Dwork–Roth, Theorem 3.6, `k = 1`,
for any scale `b ≥ Δ / ε`). -/
theorem isEpsDeltaDP_laplaceMechanism_of_le {Adj : 𝒟 → 𝒟 → Prop} (hf : Measurable f)
    (hb : 0 < b) (hΔf : ∀ ⦃x x'⦄, Adj x x' → |f x - f x'| ≤ ε * b) :
    IsEpsDeltaDP (laplaceMechanism f b) Adj ε 0 := by
  refine isEpsDeltaDP_withDensity_const (measurable_uncurry_laplacePDF hf b) (fun x ↦ ?_)
    fun x x' hx y ↦ ?_
  · rw [lintegral_laplacePDF_eq_one _ hb]
    exact ENNReal.one_ne_top
  · rw [laplacePDF, laplacePDF, ← ENNReal.ofReal_mul (exp_pos ε).le]
    exact ENNReal.ofReal_le_ofReal (laplacePDFReal_le_exp_mul hb (hΔf hx) y)

/-- **Dwork–Roth, Theorem 3.6** (Dwork–McSherry–Nissim–Smith), for real-valued queries (`k = 1`):
the Laplace mechanism with noise scale `Δ / ε` is `(ε, 0)`-differentially private, for a
measurable query `f`, `ε > 0` and any bound `Δ > 0` on the sensitivity of `f`,
`|f(x) - f(x')| ≤ Δ` for all neighbouring `x, x'`. -/
theorem isEpsDeltaDP_laplaceMechanism {Adj : 𝒟 → 𝒟 → Prop} (hf : Measurable f) (hε : 0 < ε)
    (hΔ : 0 < Δ) (hΔf : ∀ ⦃x x'⦄, Adj x x' → |f x - f x'| ≤ Δ) :
    IsEpsDeltaDP (laplaceMechanism f (Δ / ε)) Adj ε 0 :=
  isEpsDeltaDP_laplaceMechanism_of_le hf (by positivity) fun x x' hx ↦ by
    rw [mul_div_cancel₀ _ hε.ne']
    exact hΔf hx

/-- **Dwork–Roth, Theorem 3.8**, case `k = 1` (accuracy of the Laplace mechanism): for a
measurable query `f`, every dataset `x` and `δ ∈ (0, 1]`, the output `y` of the Laplace mechanism
with scale `b > 0` satisfies `P[|f(x) - y| ≥ ln (1/δ) · b] ≤ δ` (with equality). Dwork–Roth take
`b = Δf / ε`. -/
theorem laplaceMechanism_real_le_abs_sub (hf : Measurable f) (hb : 0 < b) (x : 𝒟) {δ : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (laplaceMechanism f b x).real {y | log (1 / δ) * b ≤ |f x - y|} ≤ δ := by
  rw [laplaceMechanism_apply hf]
  simp_rw [abs_sub_comm (f x)]
  rw [laplaceMeasure_real_le_abs_sub _ hb (log_nonneg (one_le_one_div hδ₀ hδ₁)),
    log_div one_ne_zero hδ₀.ne', log_one, zero_sub, neg_neg, exp_log hδ₀]

end Mechanism

/-! ### The `ℓ₁` Laplace mechanism for vector-valued queries -/

section MechanismPi

variable {ι : Type*} [Fintype ι] {b ε Δ : ℝ}

/-- The density `y ↦ ∏_i Lap(y_i | μ_i, b)` on `ι → ℝ` of a vector of independent Laplace
variables with locations `μ_i` and common scale `b`. -/
noncomputable def laplacePiPDFReal (μ : ι → ℝ) (b : ℝ) (y : ι → ℝ) : ℝ :=
  ∏ i, laplacePDFReal (μ i) b (y i)

lemma laplacePiPDFReal_pos (μ : ι → ℝ) (hb : 0 < b) (y : ι → ℝ) :
    0 < laplacePiPDFReal μ b y :=
  Finset.prod_pos fun i _ ↦ laplacePDFReal_pos hb (y i)

/-- The product Laplace density integrates to one. -/
lemma integral_laplacePiPDFReal_eq_one (μ : ι → ℝ) (hb : 0 < b) :
    ∫ y, laplacePiPDFReal μ b y = 1 := by
  unfold laplacePiPDFReal
  rw [integral_fintype_prod_volume_eq_prod (fun i ↦ laplacePDFReal (μ i) b)]
  exact Finset.prod_eq_one fun i _ ↦ integral_laplacePDFReal_eq_one (μ i) hb

lemma integrable_laplacePiPDFReal (μ : ι → ℝ) (hb : 0 < b) :
    Integrable (laplacePiPDFReal μ b) :=
  Integrable.of_integral_ne_zero (by simp [integral_laplacePiPDFReal_eq_one μ hb])

/-- The product Laplace density integrates to one. -/
lemma lintegral_laplacePiPDFReal_eq_one (μ : ι → ℝ) (hb : 0 < b) :
    ∫⁻ y, ENNReal.ofReal (laplacePiPDFReal μ b y) = 1 := by
  have hm : Measurable (laplacePiPDFReal μ b) := by
    unfold laplacePiPDFReal laplacePDFReal
    fun_prop
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun y ↦ (laplacePiPDFReal_pos μ hb y).le) hm.aestronglyMeasurable,
    integral_laplacePiPDFReal_eq_one μ hb]

/-- **Likelihood ratio of shifted product Laplace densities**: if `‖μ - μ'‖₁ ≤ ε b`, then
`p_μ(y) ≤ e^ε p_{μ'}(y)` for every `y` (the computation in the proof of Dwork–Roth,
Theorem 3.6). -/
lemma laplacePiPDFReal_le_exp_mul {μ μ' : ι → ℝ} (hb : 0 < b) (h : ∑ i, |μ i - μ' i| ≤ ε * b)
    (y : ι → ℝ) : laplacePiPDFReal μ b y ≤ exp ε * laplacePiPDFReal μ' b y := by
  have h₁ (i : ι) : laplacePDFReal (μ i) b (y i) ≤
      exp (|μ i - μ' i| / b) * laplacePDFReal (μ' i) b (y i) :=
    laplacePDFReal_le_exp_mul hb (by rw [div_mul_cancel₀ _ hb.ne']) (y i)
  unfold laplacePiPDFReal
  calc ∏ i, laplacePDFReal (μ i) b (y i)
      ≤ ∏ i, (exp (|μ i - μ' i| / b) * laplacePDFReal (μ' i) b (y i)) :=
        Finset.prod_le_prod₀ (fun i _ ↦ (laplacePDFReal_pos hb _).le) fun i _ ↦ h₁ i
    _ = exp (∑ i, |μ i - μ' i| / b) * ∏ i, laplacePDFReal (μ' i) b (y i) := by
        rw [Finset.prod_mul_distrib, exp_sum]
    _ ≤ exp ε * ∏ i, laplacePDFReal (μ' i) b (y i) := by
        gcongr
        · exact Finset.prod_nonneg fun i _ ↦ (laplacePDFReal_pos hb _).le
        · rwa [← Finset.sum_div, div_le_iff₀ hb]

variable [MeasurableSpace 𝒟] {f : 𝒟 → ι → ℝ}

/-- **The Laplace mechanism for vector-valued queries** `M_L(x, f, ε) = f(x) + (Y_1, …, Y_k)`
with `Y_i` i.i.d. `Lap(b)` (Dwork–Roth, Definition 3.3, with the coordinates indexed by a finite
type `ι` and the noise scale `b` as a parameter; Dwork–Roth take `b = Δf / ε`). It is built as
`Kernel.withDensity` of the constant kernel `x ↦ volume` on `ι → ℝ` with density
`(x, y) ↦ ∏_i Lap(y_i | f(x)_i, b)`. This is the intended mechanism, with output law
`∏_i Lap(f(x)_i, b)`, when that density is jointly measurable (for instance when `f` is
measurable, `laplaceMechanismPi_apply`) and `b > 0` (so that it is normalized,
`isMarkovKernel_laplaceMechanismPi`); `Kernel.withDensity` returns the **zero kernel** when the
density is not jointly measurable. -/
noncomputable def laplaceMechanismPi (f : 𝒟 → ι → ℝ) (b : ℝ) : Kernel 𝒟 (ι → ℝ) :=
  (Kernel.const 𝒟 volume).withDensity fun x y ↦ ENNReal.ofReal (laplacePiPDFReal (f x) b y)

lemma measurable_uncurry_laplacePiPDFReal (hf : Measurable f) (b : ℝ) :
    Measurable (Function.uncurry fun x y ↦ ENNReal.ofReal (laplacePiPDFReal (f x) b y)) := by
  unfold laplacePiPDFReal laplacePDFReal
  fun_prop

/-- For a measurable query and `b > 0`, the output law of the vector Laplace mechanism is the
product of the Laplace laws `Lap(f(x)_i, b)`: the noise coordinates are i.i.d. `Lap(b)`. -/
lemma laplaceMechanismPi_apply (hf : Measurable f) (hb : 0 < b) (x : 𝒟) :
    laplaceMechanismPi f b x = Measure.pi fun i ↦ laplaceMeasure (f x i) b := by
  have := fun i ↦ isProbabilityMeasure_laplaceMeasure (f x i) hb
  set g : ι → ℝ → ℝ := fun i ↦ laplacePDFReal (f x i) b
  have hg (i : ι) : Integrable (g i) := integrable_laplacePDFReal _ hb
  have hg₀ (i : ι) (y : ℝ) : 0 ≤ g i y := (laplacePDFReal_pos hb y).le
  rw [laplaceMechanismPi, Kernel.withDensity_apply _ (measurable_uncurry_laplacePiPDFReal hf b),
    Kernel.const_apply]
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  -- each factor is `∫_{s i} g i`
  have hfac (i : ι) :
      laplaceMeasure (f x i) b (s i) = ENNReal.ofReal (∫ y, (s i).indicator (g i) y) := by
    rw [laplaceMeasure, withDensity_apply _ (hs i), integral_indicator (hs i),
      ofReal_integral_eq_lintegral_ofReal (hg i).integrableOn (ae_of_all _ fun y ↦ hg₀ i y)]
    rfl
  -- the indicator of the box is the product of the coordinate indicators
  have hind (y : ι → ℝ) : (Set.univ.pi s).indicator (laplacePiPDFReal (f x) b) y =
      ∏ i, (s i).indicator (g i) (y i) := by
    by_cases hy : y ∈ Set.univ.pi s
    · rw [indicator_of_mem hy]
      exact Finset.prod_congr rfl fun i _ ↦ (indicator_of_mem (hy i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ s i := by simpa [Set.mem_univ_pi] using hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  have hint : Integrable (fun y : ι → ℝ ↦ ∏ i, (s i).indicator (g i) (y i)) :=
    Integrable.fintype_prod fun i ↦ (hg i).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_laplacePiPDFReal (f x) hb).integrableOn)
      (ae_of_all _ fun y ↦ (laplacePiPDFReal_pos _ hb y).le),
    ← integral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind, hfac]
  rw [integral_fintype_prod_volume_eq_prod (fun i ↦ (s i).indicator (g i)),
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ integral_nonneg fun y ↦ indicator_nonneg
      (fun y _ ↦ hg₀ i y) y]

/-- The vector Laplace mechanism with a measurable query and positive scale is a Markov
kernel. -/
lemma isMarkovKernel_laplaceMechanismPi (hf : Measurable f) (hb : 0 < b) :
    IsMarkovKernel (laplaceMechanismPi f b) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  rw [laplaceMechanismPi, Kernel.withDensity_apply _ (measurable_uncurry_laplacePiPDFReal hf b),
    Kernel.const_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_laplacePiPDFReal_eq_one _ hb]

/-- **Dwork–Roth, Theorem 3.6** (Dwork–McSherry–Nissim–Smith): the Laplace mechanism for a
measurable vector-valued query `f : 𝒟 → (ι → ℝ)` with noise scale `Δ / ε` is
`(ε, 0)`-differentially private, for `ε > 0` and any bound `Δ > 0` on the `ℓ₁`-sensitivity of
`f`, `∑_i |f(x)_i - f(x')_i| ≤ Δ` for all neighbouring `x, x'`. -/
theorem isEpsDeltaDP_laplaceMechanismPi {Adj : 𝒟 → 𝒟 → Prop} (hf : Measurable f) (hε : 0 < ε)
    (hΔ : 0 < Δ) (hΔf : ∀ ⦃x x'⦄, Adj x x' → ∑ i, |f x i - f x' i| ≤ Δ) :
    IsEpsDeltaDP (laplaceMechanismPi f (Δ / ε)) Adj ε 0 := by
  have hb : 0 < Δ / ε := div_pos hΔ hε
  refine isEpsDeltaDP_withDensity_const (measurable_uncurry_laplacePiPDFReal hf _)
    (fun x ↦ ?_) fun x x' hx y ↦ ?_
  · rw [lintegral_laplacePiPDFReal_eq_one _ hb]
    exact ENNReal.one_ne_top
  · rw [← ENNReal.ofReal_mul (exp_pos ε).le]
    refine ENNReal.ofReal_le_ofReal (laplacePiPDFReal_le_exp_mul hb ?_ y)
    rw [mul_div_cancel₀ _ hε.ne']
    exact hΔf hx

/-- **Dwork–Roth, Theorem 3.8** (accuracy of the Laplace mechanism): for a measurable query
`f : 𝒟 → (ι → ℝ)` with `k = |ι| ≥ 1` coordinates, every dataset `x` and `δ ∈ (0, 1]`, the output
`y` of the Laplace mechanism with scale `b > 0` satisfies
`P[‖f(x) - y‖_∞ ≥ ln (k/δ) · b] ≤ δ`, where `‖·‖` is the sup norm on `ι → ℝ`. Dwork–Roth take
`b = Δf / ε`. -/
theorem laplaceMechanismPi_real_le_norm_sub [Nonempty ι] (hf : Measurable f) (hb : 0 < b)
    (x : 𝒟) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (laplaceMechanismPi f b x).real
      {y | log (Fintype.card ι / δ) * b ≤ ‖f x - y‖} ≤ δ := by
  have := fun i ↦ isProbabilityMeasure_laplaceMeasure (f x i) hb
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set t := log (Fintype.card ι / δ)
  have ht : 0 ≤ t := log_nonneg (by rw [le_div_iff₀ hδ₀]; linarith)
  -- the event is covered by the coordinate events `|y_i - f(x)_i| ≥ t b`
  have hsub : {y : ι → ℝ | t * b ≤ ‖f x - y‖} ⊆
      ⋃ i, (fun y ↦ y i) ⁻¹' {z | t * b ≤ |z - f x i|} := by
    intro y hy
    by_contra h
    simp only [mem_iUnion, mem_preimage, Set.mem_ofPred_eq, not_exists, not_le] at h
    have hpos : 0 < t * b := (abs_nonneg _).trans_lt (h (Classical.arbitrary ι))
    have : ‖f x - y‖ < t * b := (pi_norm_lt_iff hpos).2 fun i ↦ by
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
      exact h i
    exact absurd hy (not_le.2 this)
  -- each coordinate event has probability `e^{-t} = δ / k` (Fact 3.7)
  have hcoord (i : ι) : (Measure.pi fun i ↦ laplaceMeasure (f x i) b).real
      ((fun y ↦ y i) ⁻¹' {z | t * b ≤ |z - f x i|}) = δ / Fintype.card ι := by
    rw [(measurePreserving_eval _ i).measureReal_preimage
      (measurableSet_le measurable_const (by fun_prop)).nullMeasurableSet,
      laplaceMeasure_real_le_abs_sub _ hb ht, exp_neg, exp_log (by positivity), inv_div]
  rw [laplaceMechanismPi_apply hf hb]
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_iUnion_fintype_le _
    _ = δ := by
      simp_rw [hcoord]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

end MechanismPi

end InformationTheory
