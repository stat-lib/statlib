/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.DP.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The geometric mechanism

The geometric mechanism (the discrete analogue of the Laplace mechanism) of A. Ghosh,
T. Roughgarden and M. Sundararajan, *Universally utility-maximizing privacy mechanisms*,
STOC 2009 / SIAM J. Comput. 41(6), 2012 ([arXiv:0811.2841](https://arxiv.org/abs/0811.2841);
numbering follows arXiv v3), releases an integer-valued query `f(x) ∈ ℤ` with additive two-sided
geometric noise: for `α ∈ [0, 1)` the noise `Z` has law `P[Z = z] = (1 - α) / (1 + α) · α^{|z|}`
on `ℤ`, so the mechanism outputs `z ∈ ℤ` with probability proportional to `α^{|z - f(x)|}`
(Example 2.1). Ghosh–Roughgarden–Sundararajan measure privacy multiplicatively: a mechanism is
`α`-differentially private if all likelihood ratios on neighbouring databases lie in
`[α, 1/α]`, which is `(-ln α, 0)`-differential privacy in the usual additive convention. Example
2.1 states that for count queries (sensitivity `1`) the `α`-geometric mechanism is
`α`-differentially private in their sense. More generally, for an integer-valued query of
sensitivity at most `Δ`, the choice `α = e^{-ε/Δ}` gives `ε`-differential privacy.

The mechanism is a Markov kernel `𝒟 → ℤ`, built as `Kernel.withDensity` of the constant kernel
`x ↦ count` (counting measure on `ℤ`); it is a Markov kernel as soon as `f` is measurable
(`isMarkovKernel_geometricMechanism`), and then it is the mechanism of Example 2.1
(`geometricMechanism_apply`); the privacy theorems assume `f` measurable.
Privacy is measured with `IsEpsDeltaDP` from `Statlib.Privacy.DP.Basic` at `δ = 0` (pure
`ε`-differential privacy, over all events) for an arbitrary neighbouring relation `Adj` on
datasets.

## Main definitions

* `twoSidedGeometricPMFReal α μ z = (1 - α) / (1 + α) · α^{|z - μ|}`: the two-sided geometric
  (discrete Laplace) probability mass function on `ℤ`, centred at `μ`.
* `twoSidedGeometricMeasure α μ`: the corresponding measure on `ℤ`.
* `geometricMechanism f α`: the `α`-geometric mechanism `x ↦ f(x) + Z` (Example 2.1).

## Main statements (source result → Lean name)

* The two-sided geometric masses sum to one: `hasSum_twoSidedGeometricPMFReal`; the measure is a
  probability measure: `isProbabilityMeasure_twoSidedGeometricMeasure`; the mechanism is a
  Markov kernel: `isMarkovKernel_geometricMechanism`.
* Example 2.1 (privacy of the `α`-geometric mechanism for queries of sensitivity `1`, `0 < α < 1`,
  privacy level `-ln α`): `isEpsDeltaDP_geometricMechanism_neg_log`.
* Its generalization to sensitivity `Δ` with `α = e^{-ε/Δ}`: `isEpsDeltaDP_geometricMechanism`.

## Remark on the range of `α`

The paper states its results for every privacy level `α ∈ [0, 1]` and sets aside `α = 0, 1` as
degenerate cases at the start of Section 5 (arXiv v3). At `α = 1` the displayed untruncated mass
formula `(1 - α) / (1 + α) · α^{|z|}` of Example 2.1 is identically `0`, so this formula gives no
`1`-geometric mechanism to formalize (perfect privacy, `α = 1`, is achieved by data-independent
mechanisms, which are not geometric mechanisms of this form). At `α = 0` the mechanism releases
`f(x)` exactly; the additive privacy level `-log α` tends to `+∞` as `α ↓ 0`, and exact release
has no finite privacy bound when neighbouring answers differ. (In Lean, `Real.log 0 = 0`, so the
formula `-log α` must not be evaluated at `α = 0`.) This is a degenerate boundary convention, not
an error in the paper's privacy or optimality results. We therefore assume `0 ≤ α < 1` for the
distribution and `0 < α < 1` for the privacy statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {𝒟 : Type*}

namespace Geometric

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

end Geometric

open Geometric

/-! ### The two-sided geometric distribution -/

section PMF

variable {α : ℝ}

/-- The two-sided geometric (discrete Laplace) probability mass function on `ℤ` with parameter
`α` centred at `μ`: `z ↦ (1 - α) / (1 + α) · α^{|z - μ|}`. It is a probability mass function for
`0 ≤ α < 1` (`hasSum_twoSidedGeometricPMFReal`). -/
noncomputable def twoSidedGeometricPMFReal (α : ℝ) (μ z : ℤ) : ℝ :=
  (1 - α) / (1 + α) * α ^ (z - μ).natAbs

lemma twoSidedGeometricPMFReal_nonneg (hα₀ : 0 ≤ α) (hα₁ : α < 1) (μ z : ℤ) :
    0 ≤ twoSidedGeometricPMFReal α μ z := by
  unfold twoSidedGeometricPMFReal
  have : 0 ≤ 1 - α := by linarith
  positivity

/-- `∑_{z ∈ ℤ} α^{|z|} = (1 + α) / (1 - α)` for `0 ≤ α < 1`. -/
lemma Geometric.hasSum_pow_natAbs (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    HasSum (fun z : ℤ ↦ α ^ z.natAbs) ((1 + α) / (1 - α)) := by
  have h₁ : HasSum (fun n : ℕ ↦ α ^ (n : ℤ).natAbs) (1 - α)⁻¹ := by
    simp only [Int.natAbs_natCast]
    exact hasSum_geometric_of_lt_one hα₀ hα₁
  have h₂ : HasSum (fun n : ℕ ↦ α ^ (-(n + 1 : ℤ)).natAbs) (α * (1 - α)⁻¹) := by
    have : (fun n : ℕ ↦ α ^ (-(n + 1 : ℤ)).natAbs) = fun n : ℕ ↦ α * α ^ n := by
      ext n
      rw [Int.natAbs_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        Int.natAbs_natCast, pow_succ']
    rw [this]
    exact (hasSum_geometric_of_lt_one hα₀ hα₁).mul_left α
  have h := HasSum.of_nat_of_neg_add_one (f := fun z : ℤ ↦ α ^ z.natAbs) h₁ h₂
  rwa [show (1 - α)⁻¹ + α * (1 - α)⁻¹ = (1 + α) / (1 - α) by rw [div_eq_mul_inv]; ring] at h

/-- **The two-sided geometric masses sum to one** (for `0 ≤ α < 1`). -/
lemma hasSum_twoSidedGeometricPMFReal (hα₀ : 0 ≤ α) (hα₁ : α < 1) (μ : ℤ) :
    HasSum (twoSidedGeometricPMFReal α μ) 1 := by
  have h := ((Equiv.subRight μ).hasSum_iff (f := fun z : ℤ ↦ α ^ z.natAbs)).2
    (Geometric.hasSum_pow_natAbs hα₀ hα₁)
  have h1 : 1 - α ≠ 0 := by linarith
  have h2 : 1 + α ≠ 0 := by linarith
  convert h.mul_left ((1 - α) / (1 + α)) using 1
  · ext z
    simp [twoSidedGeometricPMFReal]
  · field_simp

/-- The two-sided geometric distribution on `ℤ` with parameter `α` centred at `μ`: the measure
with density `twoSidedGeometricPMFReal α μ` with respect to the counting measure. It is a
probability measure for `0 ≤ α < 1` (`isProbabilityMeasure_twoSidedGeometricMeasure`). -/
noncomputable def twoSidedGeometricMeasure (α : ℝ) (μ : ℤ) : Measure ℤ :=
  Measure.count.withDensity fun z ↦ ENNReal.ofReal (twoSidedGeometricPMFReal α μ z)

lemma lintegral_twoSidedGeometricPMFReal (hα₀ : 0 ≤ α) (hα₁ : α < 1) (μ : ℤ) :
    ∫⁻ z, ENNReal.ofReal (twoSidedGeometricPMFReal α μ z) ∂Measure.count = 1 := by
  rw [lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg
    (twoSidedGeometricPMFReal_nonneg hα₀ hα₁ μ)
    (hasSum_twoSidedGeometricPMFReal hα₀ hα₁ μ).summable,
    (hasSum_twoSidedGeometricPMFReal hα₀ hα₁ μ).tsum_eq, ENNReal.ofReal_one]

lemma isProbabilityMeasure_twoSidedGeometricMeasure (hα₀ : 0 ≤ α) (hα₁ : α < 1) (μ : ℤ) :
    IsProbabilityMeasure (twoSidedGeometricMeasure α μ) :=
  ⟨by rw [twoSidedGeometricMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_twoSidedGeometricPMFReal hα₀ hα₁]⟩

lemma twoSidedGeometricMeasure_real_singleton (hα₀ : 0 ≤ α) (hα₁ : α < 1) (μ z : ℤ) :
    (twoSidedGeometricMeasure α μ).real {z} = twoSidedGeometricPMFReal α μ z := by
  rw [measureReal_def, twoSidedGeometricMeasure, withDensity_apply _ (MeasurableSet.singleton z),
    Measure.restrict_singleton, Measure.count_singleton, one_smul, lintegral_dirac,
    ENNReal.toReal_ofReal (twoSidedGeometricPMFReal_nonneg hα₀ hα₁ μ z)]

/-- **Likelihood ratio of shifted two-sided geometric masses**: if `α = e^{-ε/Δ}` with `ε ≥ 0`,
`Δ > 0` and `|μ - μ'| ≤ Δ`, then `P_μ(z) ≤ e^ε P_{μ'}(z)` for every `z ∈ ℤ`. -/
lemma twoSidedGeometricPMFReal_le_exp_mul {ε : ℝ} (hε : 0 ≤ ε) {Δ : ℕ} (hΔ : 0 < Δ) {μ μ' : ℤ}
    (h : (μ - μ').natAbs ≤ Δ) (z : ℤ) :
    twoSidedGeometricPMFReal (exp (-ε / Δ)) μ z ≤
      exp ε * twoSidedGeometricPMFReal (exp (-ε / Δ)) μ' z := by
  set α := exp (-ε / Δ) with hα
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hα₀ : 0 ≤ α := (exp_pos _).le
  have hα₁ : α ≤ 1 := exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hε) hΔ'.le)
  have hαΔ : α ^ Δ = exp (-ε) := by
    rw [hα, ← exp_nat_mul]
    congr 1
    field_simp
  have hab : (z - μ').natAbs ≤ (z - μ).natAbs + Δ := by
    have := Int.natAbs_add_le (z - μ) (μ - μ')
    rw [show z - μ + (μ - μ') = z - μ' by ring] at this
    omega
  have key : α ^ (z - μ).natAbs ≤ exp ε * α ^ (z - μ').natAbs :=
    calc α ^ (z - μ).natAbs = exp ε * α ^ ((z - μ).natAbs + Δ) := by
          rw [pow_add, hαΔ, mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
      _ ≤ exp ε * α ^ (z - μ').natAbs :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα₀ hα₁ hab) (exp_pos ε).le
  have hc : 0 ≤ (1 - α) / (1 + α) := div_nonneg (by linarith) (by linarith)
  unfold twoSidedGeometricPMFReal
  calc (1 - α) / (1 + α) * α ^ (z - μ).natAbs
      ≤ (1 - α) / (1 + α) * (exp ε * α ^ (z - μ').natAbs) := mul_le_mul_of_nonneg_left key hc
    _ = exp ε * ((1 - α) / (1 + α) * α ^ (z - μ').natAbs) := by ring

end PMF

/-! ### The geometric mechanism -/

section Mechanism

variable [MeasurableSpace 𝒟] {f : 𝒟 → ℤ} {α ε : ℝ}

/-- **The `α`-geometric mechanism** (Ghosh–Roughgarden–Sundararajan, Example 2.1): on dataset
`x` it outputs `f(x) + Z` with `Z` two-sided geometric with parameter `α`, i.e. `z ∈ ℤ` with
probability `(1 - α) / (1 + α) · α^{|z - f(x)|}`. It is built as the kernel with density
`(x, z) ↦ twoSidedGeometricPMFReal α (f x) z` with respect to the constant kernel `x ↦ count`,
which is the intended kernel when `f` is measurable (`geometricMechanism_apply`) and the zero
kernel otherwise. -/
noncomputable def geometricMechanism (f : 𝒟 → ℤ) (α : ℝ) : Kernel 𝒟 ℤ :=
  (Kernel.const 𝒟 Measure.count).withDensity
    fun x z ↦ ENNReal.ofReal (twoSidedGeometricPMFReal α (f x) z)

lemma measurable_uncurry_twoSidedGeometricPMFReal (hf : Measurable f) (α : ℝ) :
    Measurable (Function.uncurry fun x z ↦ ENNReal.ofReal (twoSidedGeometricPMFReal α (f x) z)) :=
  measurable_from_prod_countable_left fun z ↦ (measurable_of_countable
    fun μ ↦ ENNReal.ofReal (twoSidedGeometricPMFReal α μ z)).comp hf

lemma geometricMechanism_apply (hf : Measurable f) (α : ℝ) (x : 𝒟) :
    geometricMechanism f α x = twoSidedGeometricMeasure α (f x) := by
  rw [geometricMechanism,
    Kernel.withDensity_apply _ (measurable_uncurry_twoSidedGeometricPMFReal hf α),
    Kernel.const_apply, twoSidedGeometricMeasure]

/-- The geometric mechanism with a measurable query and `0 ≤ α < 1` is a Markov kernel. -/
lemma isMarkovKernel_geometricMechanism (hf : Measurable f) (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    IsMarkovKernel (geometricMechanism f α) :=
  ⟨fun x ↦ by
    rw [geometricMechanism_apply hf]
    exact isProbabilityMeasure_twoSidedGeometricMeasure hα₀ hα₁ _⟩

/-- **The geometric mechanism is `ε`-differentially private**: for a measurable integer-valued
query `f` whose sensitivity is at most `Δ > 0` (`|f(x) - f(x')| ≤ Δ` for all neighbouring
`x, x'`) and `ε > 0`, the geometric mechanism with `α = e^{-ε/Δ}` is
`(ε, 0)`-differentially private. -/
theorem isEpsDeltaDP_geometricMechanism {Adj : 𝒟 → 𝒟 → Prop} {Δ : ℕ} (hf : Measurable f)
    (hε : 0 < ε) (hΔ : 0 < Δ) (hΔf : ∀ ⦃x x'⦄, Adj x x' → (f x - f x').natAbs ≤ Δ) :
    IsEpsDeltaDP (geometricMechanism f (exp (-ε / Δ))) Adj ε 0 := by
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hα₁ : exp (-ε / Δ) < 1 := exp_lt_one_iff.2 (div_neg_of_neg_of_pos (neg_lt_zero.2 hε) hΔ')
  refine isEpsDeltaDP_withDensity_const (measurable_uncurry_twoSidedGeometricPMFReal hf _)
    (fun x ↦ ?_) fun x x' hx z ↦ ?_
  · rw [lintegral_twoSidedGeometricPMFReal (exp_pos _).le hα₁]
    exact ENNReal.one_ne_top
  · rw [← ENNReal.ofReal_mul (exp_pos ε).le]
    exact ENNReal.ofReal_le_ofReal (twoSidedGeometricPMFReal_le_exp_mul hε.le hΔ (hΔf hx) z)

/-- **Ghosh–Roughgarden–Sundararajan, Example 2.1**: for a measurable query `f` of sensitivity at
most `1` (for instance a count query) and `0 < α < 1`, the `α`-geometric mechanism is
`α`-differentially private in the multiplicative convention of the paper, i.e.
`(-ln α, 0)`-differentially private. -/
theorem isEpsDeltaDP_geometricMechanism_neg_log {Adj : 𝒟 → 𝒟 → Prop} (hf : Measurable f)
    (hα₀ : 0 < α) (hα₁ : α < 1) (hΔf : ∀ ⦃x x'⦄, Adj x x' → (f x - f x').natAbs ≤ 1) :
    IsEpsDeltaDP (geometricMechanism f α) Adj (-log α) 0 := by
  have h := isEpsDeltaDP_geometricMechanism hf (neg_pos.2 (log_neg hα₀ hα₁)) one_pos hΔf
  rwa [Nat.cast_one, div_one, neg_neg, exp_log hα₀] at h

end Mechanism

end InformationTheory
