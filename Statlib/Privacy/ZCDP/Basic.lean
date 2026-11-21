/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.DP.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian
public import Statlib.Divergence.Renyi.ChainRule
public import Statlib.Divergence.Renyi.Prod

/-!
# Zero-concentrated differential privacy

This file formalizes the basic theory of zero-concentrated differential privacy from M. Bun and
T. Steinke, *Concentrated differential privacy: simplifications, extensions, and lower bounds*,
TCC 2016 ([arXiv:1605.02065](https://arxiv.org/abs/1605.02065), v1; result numbers follow it).

A mechanism is a kernel `M : Kernel 𝒟 Y` from datasets to outputs, and `Adj : 𝒟 → 𝒟 → Prop` is
an arbitrary neighbouring relation (the paper's "differ in a single entry"). The Rényi divergence
`D_α` is Statlib's `renyiDiv`, which for probability measures is the paper's Definition 2.1 (and
is `∞` when `M S` is not absolutely continuous with respect to `M S'`, as in footnote 10).
`(ε, δ)`-differential privacy is `IsEpsDeltaDP` from `Statlib.Privacy.DP.Basic`.

**Scope.** Nothing here assumes finite alphabets: all results hold for arbitrary measurable
output spaces, except that adaptive composition assumes the first output space countable or the
second countably generated (`CountableOrCountablyGenerated`).

## Main definitions

* `IsZCDP M Adj ξ ρ`: `(ξ, ρ)`-zCDP (Definition 1.1); the paper's `ρ`-zCDP is `IsZCDP M Adj 0 ρ`.
* `ZCDP.piKernel M`: the product `S ↦ ∏ i, M i S` of finitely many Markov kernels.
* `ZCDP.gaussianKernel q hq v`: the Gaussian mechanism `S ↦ N(q S, v)`.

## Main statements (paper result → Lean name)

* Lemma 1.8 (post-processing): `IsZCDP.comp` (Markov kernels), `IsZCDP.map` (measurable maps).
* Lemma 1.7 (composition): `IsZCDP.prod`; iterated, `IsZCDP.pi` and `IsZCDP.piKernel` (for the
  product kernel `ZCDP.piKernel`).
* Lemma 2.3 (adaptive composition): `IsZCDP.snd_compProd`, and `IsZCDP.compProd` for the
  mechanism that releases both outputs. It combines Statlib's chain rule with
  `ZCDP.condRenyiDiv_le`, a bound on the conditional term.
* Proposition 1.3: `IsZCDP.isEpsDeltaDP'`; Lemma 3.5 (its `(ξ, ρ)` form): `IsZCDP.isEpsDeltaDP`.
* Lemma 3.2 (`ε`-DP iff `(ε, 0)`-zCDP): `isZCDP_iff_isEpsDeltaDP`.
* Proposition 1.4 (`ε`-DP implies `(ε² / 2)`-zCDP): `IsEpsDeltaDP.isZCDP`; Proposition 3.3 (its
  form for two measures): `ZCDP.renyiDiv_le_sq_of_le_smul`.
* Composition of `k` pure-DP mechanisms is `(k ε² / 2)`-zCDP (Proposition 1.4 with Lemma 1.7):
  `isZCDP_pi_of_isEpsDeltaDP`; hence `(k ε² / 2 + ε √(2 k log (1 / δ)), δ)`-DP, a bound not
  stated in the paper that follows with Proposition 1.3: `isEpsDeltaDP_pi_of_isEpsDeltaDP`.
* Lemma 2.4 (Rényi divergence between Gaussians, orders `α > 1`): `ZCDP.renyiDiv_gaussianReal`;
  Proposition 1.6 (Gaussian mechanism): `isZCDP_of_gaussianReal`, `ZCDP.isZCDP_gaussianKernel`.

## Implementation notes

* The bound `D_α ≤ ξ + ρ α` of `IsZCDP` is compared in `EReal`, so that it is exactly the paper's
  condition for all real `ξ`, `ρ` (an infinite divergence or a negative bound fails it);
  `isZCDP_iff_toReal` and `isZCDP_iff_le_ofReal` give the `ℝ` and `ℝ≥0∞` forms.
* Proofs that differ from the paper's: Lemma 3.5 uses the Hölder bound
  `μ(T) ^ α ≤ exp ((α - 1) D_α(μ ‖ ν)) ν(T) ^ (α - 1)` (`ZCDP.measureReal_rpow_le`) instead of
  the privacy-loss/Markov argument, at the paper's order `α = 1 + √(log (1 / δ) / ρ)`;
  Proposition 3.3 applies Hoeffding's lemma (Mathlib's `hasSubgaussianMGF_of_mem_Icc`) twice to
  the privacy loss instead of the `sinh` inequality of Lemma B.1; Lemma 2.4 uses the Gaussian
  moment generating function instead of completing the square.
* Mathlib has no product of a finite family of kernels; `ZCDP.piKernel` constructs it.
* `IsZCDP` is meant for Markov kernels: `renyiDiv` normalizes finite measures, so for other
  kernels the condition is not the paper's (e.g. the zero kernel is `(0, 0)`-zCDP). All results
  below assume Markov (or finite) kernels.
* `IsEpsDeltaDP` quantifies over all sets `E`, with `(M S).real E` an outer measure for
  non-measurable `E`. For probability measures this is equivalent to quantifying over measurable
  sets, by taking a measurable hull (`isEpsDeltaDP_iff_forall_measurableSet` in
  `Statlib.Privacy.DP.Basic`); `IsZCDP.isEpsDeltaDP` handles arbitrary `E` directly through
  `toMeasurable`.
* Lemma 3.5 and Proposition 1.3 (remark): the paper's proof chooses the order
  `α = (ε - ξ + ρ) / 2ρ`, which excludes the edge cases `ρ = 0` and `δ > 1` (where the argument
  of `√(4 ρ log (1 / δ))` is negative; in Lean `√` of a negative number is `0`). Both are
  immediate: `δ ≥ 1` is trivial, and `ρ = 0` is the limit `ρ ↓ 0`.
* Proposition 1.4 assumes the neighbouring relation symmetric (`[Std.Symm Adj]`), as the paper's
  is; the other results need no symmetry.

## Not formalized

The privacy-loss formulation (Definition 1.2, equation (2)), the `(ε, δ)` refinements and the
converse (Lemmas 3.6 and 3.7), mean-concentrated DP (Section 4), group privacy (Section 5), the
lower bounds (Sections 6 and 7), approximate zCDP (Section 8), the multivariate Gaussian
(Lemma 2.5), and Lemma 2.4 at order `α = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace InformationTheory

variable {𝒟 Y Z : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z}

/-- **Zero-concentrated differential privacy** (Definition 1.1 of Bun–Steinke): a mechanism
`M : Kernel 𝒟 Y` is `(ξ, ρ)`-zCDP for the neighbouring relation `Adj` if
`D_α(M S ‖ M S') ≤ ξ + ρ α` for all neighbours `Adj S S'` and all orders `α ∈ (1, ∞)`, where
`D_α` is Statlib's Rényi divergence `renyiDiv`. The comparison is made in `EReal`, so that, as in
the paper, an infinite divergence violates the bound and a negative right-hand side cannot be
met. The paper's `ρ`-zCDP is `IsZCDP M Adj 0 ρ`.

The definition is meant for Markov kernels: `renyiDiv` normalizes finite measures, so for other
kernels it does not express the paper's condition (e.g. the zero kernel is `(0, 0)`-zCDP). -/
def IsZCDP (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (ξ ρ : ℝ) : Prop :=
  ∀ ⦃S S'⦄, Adj S S' → ∀ α : ℝ, 1 < α →
    (renyiDiv α (M S) (M S') : EReal) ≤ ((ξ + ρ * α : ℝ) : EReal)

namespace ZCDP

/-- An extended nonnegative real is at most a real number `r`, as elements of `EReal`, iff it is
finite and its real value is at most `r`. -/
lemma coe_ennreal_le_coe_iff {R : ℝ≥0∞} {r : ℝ} :
    (R : EReal) ≤ (r : EReal) ↔ R ≠ ∞ ∧ R.toReal ≤ r := by
  rcases eq_or_ne R ∞ with rfl | hR
  · simp
  · rw [← EReal.coe_ennreal_toReal hR, EReal.coe_le_coe_iff]
    simp [hR]

/-- For `r ≥ 0`, the `EReal` comparison `R ≤ r` is the `ℝ≥0∞` comparison `R ≤ ofReal r`. -/
lemma coe_ennreal_le_coe_iff_le_ofReal {R : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    (R : EReal) ≤ (r : EReal) ↔ R ≤ ENNReal.ofReal r := by
  rw [coe_ennreal_le_coe_iff]
  constructor
  · rintro ⟨hR, h⟩
    exact (ENNReal.le_ofReal_iff_toReal_le hR hr).2 h
  · intro h
    exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, ENNReal.toReal_le_of_le_ofReal hr h⟩

end ZCDP

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop} {ξ ρ ξ' ρ' : ℝ}

/-- `(ξ, ρ)`-zCDP in real form: each divergence is finite with real value at most `ξ + ρ α`. -/
lemma isZCDP_iff_toReal : IsZCDP M Adj ξ ρ ↔ ∀ ⦃S S'⦄, Adj S S' → ∀ α : ℝ, 1 < α →
    renyiDiv α (M S) (M S') ≠ ∞ ∧ (renyiDiv α (M S) (M S')).toReal ≤ ξ + ρ * α := by
  simp_rw [IsZCDP, ZCDP.coe_ennreal_le_coe_iff]

/-- For nonnegative parameters, `(ξ, ρ)`-zCDP is the bound `D_α(M S ‖ M S') ≤ ξ + ρ α` in
`ℝ≥0∞`. -/
lemma isZCDP_iff_le_ofReal (hξ : 0 ≤ ξ) (hρ : 0 ≤ ρ) : IsZCDP M Adj ξ ρ ↔ ∀ ⦃S S'⦄, Adj S S' →
    ∀ α : ℝ, 1 < α → renyiDiv α (M S) (M S') ≤ ENNReal.ofReal (ξ + ρ * α) := by
  refine forall₂_congr fun S S' ↦ forall_congr' fun _ ↦ forall₂_congr fun α hα ↦ ?_
  exact ZCDP.coe_ennreal_le_coe_iff_le_ofReal (by nlinarith)

namespace IsZCDP

/-- Under zCDP, the Rényi divergences between neighbours are finite. -/
lemma renyiDiv_ne_top (h : IsZCDP M Adj ξ ρ) {S S' : 𝒟} (hS : Adj S S') {α : ℝ} (hα : 1 < α) :
    renyiDiv α (M S) (M S') ≠ ∞ :=
  (isZCDP_iff_toReal.1 h hS α hα).1

/-- Under `(ξ, ρ)`-zCDP, `D_α(M S ‖ M S') ≤ ξ + ρ α` in `ℝ`. -/
lemma toReal_renyiDiv_le (h : IsZCDP M Adj ξ ρ) {S S' : 𝒟} (hS : Adj S S') {α : ℝ}
    (hα : 1 < α) : (renyiDiv α (M S) (M S')).toReal ≤ ξ + ρ * α :=
  (isZCDP_iff_toReal.1 h hS α hα).2

/-- Under `(ξ, ρ)`-zCDP, `D_α(M S ‖ M S') ≤ ξ + ρ α` in `ℝ≥0∞`. -/
lemma renyiDiv_le_ofReal (h : IsZCDP M Adj ξ ρ) {S S' : 𝒟} (hS : Adj S S') {α : ℝ}
    (hα : 1 < α) : renyiDiv α (M S) (M S') ≤ ENNReal.ofReal (ξ + ρ * α) :=
  (ENNReal.le_ofReal_iff_toReal_le (h.renyiDiv_ne_top hS hα)
    (ENNReal.toReal_nonneg.trans (h.toReal_renyiDiv_le hS hα))).2 (h.toReal_renyiDiv_le hS hα)

/-- `(ξ, ρ)`-zCDP is monotone in both parameters. -/
lemma mono (h : IsZCDP M Adj ξ ρ) (hξ : ξ ≤ ξ') (hρ : ρ ≤ ρ') : IsZCDP M Adj ξ' ρ' :=
  isZCDP_iff_toReal.2 fun _ _ hS α hα ↦ ⟨h.renyiDiv_ne_top hS hα,
    (h.toReal_renyiDiv_le hS hα).trans (by nlinarith)⟩

/-- A divergence bound for a modified mechanism by the divergence of `M` transfers zCDP. -/
lemma of_renyiDiv_le {N : Kernel 𝒟 Z} (h : IsZCDP M Adj ξ ρ)
    (hle : ∀ ⦃S S'⦄, Adj S S' → ∀ α : ℝ, 1 < α →
      renyiDiv α (N S) (N S') ≤ renyiDiv α (M S) (M S')) :
    IsZCDP N Adj ξ ρ := fun _ _ hS α hα ↦
  (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hle hS α hα)).trans (h hS α hα)

/-- **Post-processing** (Lemma 1.8 of Bun–Steinke, randomized form): if `M` is `(ξ, ρ)`-zCDP and
`κ` is a Markov kernel, then `κ ∘ₖ M` is `(ξ, ρ)`-zCDP. -/
theorem comp [IsFiniteKernel M] (h : IsZCDP M Adj ξ ρ) (κ : Kernel Y Z) [IsMarkovKernel κ] :
    IsZCDP (κ ∘ₖ M) Adj ξ ρ :=
  h.of_renyiDiv_le fun S S' _ α hα ↦ by
    simpa only [Kernel.comp_apply] using renyiDiv_comp_right_le (by linarith) (M S) (M S') κ

/-- **Post-processing** (Lemma 1.8 of Bun–Steinke) by a measurable map `f`. -/
theorem map [IsFiniteKernel M] (h : IsZCDP M Adj ξ ρ) {f : Y → Z} (hf : Measurable f) :
    IsZCDP (M.map f) Adj ξ ρ :=
  h.of_renyiDiv_le fun S S' _ α hα ↦ by
    simpa only [Kernel.map_apply _ hf] using renyiDiv_map_le (by linarith) (M S) (M S') hf

/-! ### Composition -/

/-- **Composition** (Lemma 1.7 of Bun–Steinke, with the `(ξ, ρ)` parameters of Lemma 2.3): if `M`
is `(ξ, ρ)`-zCDP and `M₂` is `(ξ', ρ')`-zCDP, then releasing both outputs, `S ↦ M S × M₂ S`
(`M ×ₖ M₂`), is `(ξ + ξ', ρ + ρ')`-zCDP. -/
theorem prod [IsMarkovKernel M] {M₂ : Kernel 𝒟 Z} [IsMarkovKernel M₂] (h : IsZCDP M Adj ξ ρ)
    (h₂ : IsZCDP M₂ Adj ξ' ρ') : IsZCDP (M ×ₖ M₂) Adj (ξ + ξ') (ρ + ρ') := by
  refine isZCDP_iff_toReal.2 fun S S' hS α hα ↦ ?_
  rw [Kernel.prod_apply, Kernel.prod_apply, renyiDiv_prod (by linarith)]
  have h₁ := h.renyiDiv_ne_top hS hα
  have h₂' := h₂.renyiDiv_ne_top hS hα
  refine ⟨ENNReal.add_ne_top.2 ⟨h₁, h₂'⟩, ?_⟩
  rw [ENNReal.toReal_add h₁ h₂']
  linarith [h.toReal_renyiDiv_le hS hα, h₂.toReal_renyiDiv_le hS hα]

end IsZCDP

namespace ZCDP

/-- The product `S ↦ ∏ i, M i S` of finitely many Markov kernels, which releases independent
outputs of all of them. Its measurability is checked on the π-system of boxes. -/
noncomputable def piKernel {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (M : ∀ i, Kernel 𝒟 (Y i)) [∀ i, IsMarkovKernel (M i)] : Kernel 𝒟 (∀ i, Y i) where
  toFun S := Measure.pi fun i ↦ M i S
  measurable' := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm
      isPiSystem_pi ?_
    rintro _ ⟨s, hs, rfl⟩
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ ↦ Kernel.measurable_coe (M i) (hs i (Set.mem_univ i))

/-- The value of the product kernel at a dataset. -/
lemma piKernel_apply {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (M : ∀ i, Kernel 𝒟 (Y i)) [∀ i, IsMarkovKernel (M i)] (S : 𝒟) :
    piKernel M S = Measure.pi fun i ↦ M i S := rfl

instance {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (M : ∀ i, Kernel 𝒟 (Y i)) [∀ i, IsMarkovKernel (M i)] : IsMarkovKernel (piKernel M) :=
  ⟨fun S ↦ by rw [piKernel_apply]; infer_instance⟩

end ZCDP

namespace IsZCDP

/-- **Composition of finitely many mechanisms** (Lemma 1.7 of Bun–Steinke, iterated as the paper
indicates after Lemma 2.3, non-adaptive form): if each `M i` is `(ξ i, ρ i)`-zCDP, then a
mechanism `K` releasing independent outputs of all of them, `K S = ∏ i, M i S`, is
`(∑ ξ i, ∑ ρ i)`-zCDP. Such a `K` is `ZCDP.piKernel M` (see `IsZCDP.piKernel`). -/
theorem pi {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)] {K : Kernel 𝒟 (∀ i, Y i)}
    (hK : ∀ S, K S = Measure.pi fun i ↦ M i S) {ξ ρ : ι → ℝ}
    (h : ∀ i, IsZCDP (M i) Adj (ξ i) (ρ i)) : IsZCDP K Adj (∑ i, ξ i) (∑ i, ρ i) := by
  refine isZCDP_iff_toReal.2 fun S S' hS α hα ↦ ?_
  rw [hK, hK, renyiDiv_pi (by linarith)]
  have hne : ∀ i ∈ Finset.univ, renyiDiv α (M i S) (M i S') ≠ ∞ :=
    fun i _ ↦ (h i).renyiDiv_ne_top hS hα
  refine ⟨ENNReal.sum_ne_top.2 hne, ?_⟩
  rw [ENNReal.toReal_sum hne, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ (h i).toReal_renyiDiv_le hS hα

/-- `IsZCDP.pi` for the product kernel `ZCDP.piKernel M`. -/
theorem piKernel {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)] {ξ ρ : ι → ℝ}
    (h : ∀ i, IsZCDP (M i) Adj (ξ i) (ρ i)) :
    IsZCDP (ZCDP.piKernel M) Adj (∑ i, ξ i) (∑ i, ρ i) :=
  pi (fun _ ↦ rfl) h

end IsZCDP

namespace ZCDP

/-- For probability measures and `a > 1`, a finite Rényi divergence and the Hellinger divergence
are related by `exp ((a - 1) Rₐ(μ, ν)) = 1 + (a - 1) Hₐ(μ, ν)`. -/
lemma exp_mul_toReal_renyiDiv {μ ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ} (ha : 1 < a) (h : renyiDiv a μ ν ≠ ∞) :
    exp ((a - 1) * (renyiDiv a μ ν).toReal) = 1 + (a - 1) * (hellingerDiv a μ ν).toReal := by
  have hH : hellingerDiv a μ ν ≠ ∞ :=
    fun hH ↦ h ((renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt ha).2 hH)
  have h1 := mul_hellingerDiv_add_meas_eq_integral (μ := μ) (ν := ν) (by linarith) ha.ne' hH
  have hpos := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top (by linarith) h
  simp only [measure_univ, ENNReal.toReal_one, mul_one] at h1
  rw [toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure (by linarith) ha.ne' h, ← mul_assoc,
    mul_inv_cancel₀ (by linarith : a - 1 ≠ 0), one_mul, exp_log hpos]
  linarith

/-- If `Rₐ(κ y, η y) ≤ r` for every `y`, then the conditional Rényi divergence
`Rₐ(P ⊗ₘ κ, P ⊗ₘ η)` is at most `r`, for a probability measure `P` and `a > 1`. This is the
bound on the conditional term of the chain rule `renyiDiv_compProd_eq_add_condRenyiDiv`; with
it, the chain rule gives the upper bound `Rₐ(μ ⊗ₘ κ, ν ⊗ₘ η) ≤ Rₐ(μ, ν) + sup_y Rₐ(κ y, η y)` of
the composition property in Lemma 2.2 of Bun–Steinke. The proof goes through the Hellinger
divergence, which is an integral over `y` (`condHellingerDiv_eq_lintegral`). -/
lemma condRenyiDiv_le {κ η : Kernel Y Z} [IsMarkovKernel κ] [IsMarkovKernel η]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z] (P : Measure Y) [IsProbabilityMeasure P]
    {a r : ℝ} (ha : 1 < a)
    (h : ∀ y, renyiDiv a (κ y) (η y) ≠ ∞ ∧ (renyiDiv a (κ y) (η y)).toReal ≤ r) :
    condRenyiDiv a κ η P ≠ ∞ ∧ (condRenyiDiv a κ η P).toReal ≤ r := by
  have ha1 : 0 < a - 1 := by linarith
  have hr : 0 ≤ r := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    exact ENNReal.toReal_nonneg.trans (h y).2
  set c := (exp ((a - 1) * r) - 1) / (a - 1) with hc_def
  have hc : 0 ≤ c := div_nonneg (by linarith [one_le_exp (mul_nonneg ha1.le hr)]) ha1.le
  have hH : ∀ y, hellingerDiv a (κ y) (η y) ≤ ENNReal.ofReal c := by
    intro y
    obtain ⟨hR, hRr⟩ := h y
    have hH' : hellingerDiv a (κ y) (η y) ≠ ∞ :=
      fun hH ↦ hR ((renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt ha).2 hH)
    rw [ENNReal.le_ofReal_iff_toReal_le hH' hc, hc_def, le_div_iff₀ ha1]
    have h1 := exp_mul_toReal_renyiDiv ha hR
    have h2 : exp ((a - 1) * (renyiDiv a (κ y) (η y)).toReal) ≤ exp ((a - 1) * r) :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_left hRr ha1.le)
    linarith
  have hcond : hellingerDiv a (P ⊗ₘ κ) (P ⊗ₘ η) ≤ ENNReal.ofReal c := by
    rw [← condHellingerDiv, condHellingerDiv_eq_lintegral]
    calc ∫⁻ y, hellingerDiv a (κ y) (η y) ∂P ≤ ∫⁻ _, ENNReal.ofReal c ∂P := lintegral_mono hH
      _ = ENNReal.ofReal c := by simp
  have hHne : hellingerDiv a (P ⊗ₘ κ) (P ⊗ₘ η) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcond
  have hRne : renyiDiv a (P ⊗ₘ κ) (P ⊗ₘ η) ≠ ∞ :=
    fun hR ↦ hHne ((renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt ha).1 hR)
  refine ⟨hRne, ?_⟩
  have he := exp_mul_toReal_renyiDiv ha hRne
  have hHc := ENNReal.toReal_le_of_le_ofReal hc hcond
  have hle : exp ((a - 1) * (renyiDiv a (P ⊗ₘ κ) (P ⊗ₘ η)).toReal) ≤ exp ((a - 1) * r) := by
    rw [he]
    have : (a - 1) * (hellingerDiv a (P ⊗ₘ κ) (P ⊗ₘ η)).toReal ≤ (a - 1) * c :=
      mul_le_mul_of_nonneg_left hHc ha1.le
    rw [hc_def, mul_div_cancel₀ _ ha1.ne'] at this
    linarith
  exact le_of_mul_le_mul_left (exp_le_exp.1 hle) ha1

end ZCDP

namespace IsZCDP

/-- **Adaptive composition** (Lemma 2.3 of Bun–Steinke, releasing both outputs): let `M` be
`(ξ, ρ)`-zCDP and let `M' : Kernel (𝒟 × Y) Z` be `(ξ', ρ')`-zCDP as a function of its first
argument, for every fixed second argument `y`. Then the mechanism that draws `y ∼ M S` and then
`z ∼ M' (S, y)` and releases `(y, z)` (`M ⊗ₖ M'`) is `(ξ + ξ', ρ + ρ')`-zCDP. The proof uses the
chain rule `renyiDiv_compProd_eq_add_condRenyiDiv`; it assumes `Y` countable or `Z` countably
generated (e.g. standard Borel). -/
theorem compProd [IsMarkovKernel M] {M' : Kernel (𝒟 × Y) Z} [IsMarkovKernel M']
    [MeasurableSpace.CountableOrCountablyGenerated Y Z] (h : IsZCDP M Adj ξ ρ)
    (h' : ∀ y, IsZCDP (M'.sectL y) Adj ξ' ρ') : IsZCDP (M ⊗ₖ M') Adj (ξ + ξ') (ρ + ρ') := by
  refine isZCDP_iff_toReal.2 fun S S' hS α hα ↦ ?_
  rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.compProd_apply_eq_compProd_sectR,
    renyiDiv_compProd_eq_add_condRenyiDiv (by linarith)]
  have hR := h.renyiDiv_ne_top hS hα
  have := isProbabilityMeasure_renyiMeasure_of_renyiDiv_ne_top (by linarith) hR
  obtain ⟨hC, hCr⟩ := ZCDP.condRenyiDiv_le (κ := M'.sectR S) (η := M'.sectR S')
    (renyiMeasure α (M S) (M S')) (r := ξ' + ρ' * α) hα fun y ↦ isZCDP_iff_toReal.1 (h' y) hS α hα
  refine ⟨ENNReal.add_ne_top.2 ⟨hR, hC⟩, ?_⟩
  rw [ENNReal.toReal_add hR hC]
  linarith [h.toReal_renyiDiv_le hS hα]

/-- **Adaptive composition** (Lemma 2.3 of Bun–Steinke, as stated): with `M` and `M'` as in
`IsZCDP.compProd`, the mechanism `S ↦ M' (S, M S)` that releases only the second output
(`(M ⊗ₖ M').snd`) is `(ξ + ξ', ρ + ρ')`-zCDP. -/
theorem snd_compProd [IsMarkovKernel M] {M' : Kernel (𝒟 × Y) Z} [IsMarkovKernel M']
    [MeasurableSpace.CountableOrCountablyGenerated Y Z] (h : IsZCDP M Adj ξ ρ)
    (h' : ∀ y, IsZCDP (M'.sectL y) Adj ξ' ρ') : IsZCDP (M ⊗ₖ M').snd Adj (ξ + ξ') (ρ + ρ') :=
  (h.compProd h').of_renyiDiv_le fun S S' _ α hα ↦ by
    simpa only [Kernel.snd_apply] using
      renyiDiv_map_le (by linarith) ((M ⊗ₖ M') S) ((M ⊗ₖ M') S') measurable_snd

end IsZCDP

/-! ### From zCDP to approximate differential privacy -/

namespace ZCDP

/-- For probability measures, `a > 1` and finite `Rₐ(μ, ν)`, the Hellinger integral is
`∫⁻ (∂μ/∂ν) ^ a ∂ν = exp ((a - 1) Rₐ(μ, ν))`. -/
lemma lintegral_rpow_rnDeriv_eq {μ ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ} (ha : 1 < a) (h : renyiDiv a μ ν ≠ ∞) :
    ∫⁻ x, (∂μ/∂ν) x ^ a ∂ν = ENNReal.ofReal (exp ((a - 1) * (renyiDiv a μ ν).toReal)) := by
  have hint := integrable_rpow_rnDeriv_of_renyiDiv_ne_top (by linarith : (0 : ℝ) ≤ a) h
  have hpos := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top (by linarith) h
  rw [toReal_renyiDiv_of_ne_top_of_isProbabilityMeasure (by linarith) ha.ne' h, ← mul_assoc,
    mul_inv_cancel₀ (by linarith : a - 1 ≠ 0), one_mul, exp_log hpos,
    integral_rpow_rnDeriv_eq_toReal_lintegral (by linarith), ENNReal.ofReal_toReal
      ((integrable_rpow_rnDeriv_iff_lintegral_ne_top (by linarith)).1 hint)]

/-- **Probability preservation** of the Rényi divergence, by Hölder's inequality: for
probability measures, `a > 1`, finite `Rₐ(μ, ν)` and a measurable set `T`,
`μ(T) ^ a ≤ exp ((a - 1) Rₐ(μ, ν)) ν(T) ^ (a - 1)`. -/
lemma measureReal_rpow_le {μ ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ} (ha : 1 < a) (h : renyiDiv a μ ν ≠ ∞) {T : Set Y}
    (hT : MeasurableSet T) :
    μ.real T ^ a ≤ exp ((a - 1) * (renyiDiv a μ ν).toReal) * ν.real T ^ (a - 1) := by
  have hac : μ ≪ ν := absolutelyContinuous_of_renyiDiv_ne_top ha.le h
  have hpq : a.HolderConjugate (a / (a - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent ha).2 rfl
  have ha0 : 0 < a := by linarith
  have hq0 : 0 < a / (a - 1) := div_pos ha0 (by linarith)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun x ↦ (∂μ/∂ν) x)
    (g := T.indicator 1) (Measure.measurable_rnDeriv μ ν).aemeasurable
    ((measurable_one.indicator hT).aemeasurable)
  have h1 : ∫⁻ x, ((fun x ↦ (∂μ/∂ν) x) * T.indicator (1 : Y → ℝ≥0∞)) x ∂ν = μ T := by
    rw [← Measure.setLIntegral_rnDeriv hac T, ← lintegral_indicator hT]
    congr 1 with x
    by_cases hx : x ∈ T <;> simp [hx]
  have h2 : ∫⁻ x, (T.indicator (1 : Y → ℝ≥0∞) x) ^ (a / (a - 1)) ∂ν = ν T := by
    rw [← lintegral_indicator_one hT]
    congr 1 with x
    by_cases hx : x ∈ T <;> simp [hx, hq0]
  rw [h1, h2, lintegral_rpow_rnDeriv_eq ha h] at hH
  have hH' := ENNReal.rpow_le_rpow hH ha0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    one_div_mul_cancel ha0.ne', ENNReal.rpow_one,
    show 1 / (a / (a - 1)) * a = a - 1 by field_simp] at hH'
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _))) hH'
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at this

/-- The numerical step of the conversion: if `p ^ a ≤ exp ((a - 1) r) q ^ (a - 1)` with `a > 1`,
`q ≥ 0` and `δ > 0`, then `p ≤ exp (r + log (1 / δ) / (a - 1)) q + δ`. -/
lemma le_exp_mul_add {a r δ p q : ℝ} (ha : 1 < a) (hδ : 0 < δ) (hq : 0 ≤ q)
    (h : p ^ a ≤ exp ((a - 1) * r) * q ^ (a - 1)) :
    p ≤ exp (r + log (1 / δ) / (a - 1)) * q + δ := by
  set ε := r + log (1 / δ) / (a - 1)
  by_contra hcon
  rw [not_le] at hcon
  have ha1 : 0 < a - 1 := by linarith
  have hlt : q < p * exp (-ε) := by
    have : exp ε * q < p := by nlinarith [(exp_pos ε).le, mul_nonneg (exp_pos ε).le hq]
    rw [exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (exp_pos ε)]
    linarith
  have hpp : 0 < p := by nlinarith [mul_nonneg (exp_pos ε).le hq]
  have h2 : q ^ (a - 1) ≤ (p * exp (-ε)) ^ (a - 1) := rpow_le_rpow hq hlt.le ha1.le
  rw [mul_rpow hpp.le (exp_pos _).le, ← exp_mul] at h2
  have h3 : p ^ a = p * p ^ (a - 1) := by
    rw [rpow_sub hpp, rpow_one]; field_simp
  have h4 : exp ((a - 1) * r) * exp (-ε * (a - 1)) = δ := by
    rw [← exp_add]
    have : (a - 1) * r + -ε * (a - 1) = log δ := by
      simp only [ε, one_div, log_inv]; field_simp; ring
    rw [this, exp_log hδ]
  have h5 : p * p ^ (a - 1) ≤ δ * p ^ (a - 1) := by
    calc p * p ^ (a - 1) = p ^ a := h3.symm
      _ ≤ exp ((a - 1) * r) * q ^ (a - 1) := h
      _ ≤ exp ((a - 1) * r) * (p ^ (a - 1) * exp (-ε * (a - 1))) :=
          mul_le_mul_of_nonneg_left h2 (exp_pos _).le
      _ = δ * p ^ (a - 1) := by rw [← h4]; ring
  have := le_of_mul_le_mul_right h5 (rpow_pos_of_pos hpp _)
  nlinarith [mul_nonneg (exp_pos ε).le hq]

/-- If `Rₐ(μ, ν) ≤ r` for some `a > 1`, then `μ(T) ≤ exp (r + log (1 / δ) / (a - 1)) ν(T) + δ`
for every set `T` and `δ > 0`. -/
lemma measureReal_le_exp_mul_add {μ ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a r δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) (h : renyiDiv a μ ν ≠ ∞)
    (hr : (renyiDiv a μ ν).toReal ≤ r) (T : Set Y) :
    μ.real T ≤ exp (r + log (1 / δ) / (a - 1)) * ν.real T + δ := by
  have hT' : ν.real (toMeasurable ν T) = ν.real T := by
    simp [measureReal_def, measure_toMeasurable]
  rw [← hT']
  refine (measureReal_mono (subset_toMeasurable ν T)).trans (le_exp_mul_add ha hδ
    measureReal_nonneg ((measureReal_rpow_le ha h (measurableSet_toMeasurable ν T)).trans ?_))
  exact mul_le_mul_of_nonneg_right (exp_le_exp.2 (mul_le_mul_of_nonneg_left hr (by linarith)))
    (rpow_nonneg measureReal_nonneg _)

/-- `IsZCDP.isEpsDeltaDP` for `ρ > 0` and `δ < 1`, with the order `α = 1 + √(log (1 / δ) / ρ)`. -/
lemma isEpsDeltaDP_of_pos [IsMarkovKernel M] (h : IsZCDP M Adj ξ ρ) (hρ : 0 < ρ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) : IsEpsDeltaDP M Adj (ξ + ρ + 2 * √(ρ * log (1 / δ))) δ := by
  intro S S' hS E
  have hL : 0 < log (1 / δ) := log_pos (one_lt_one_div hδ hδ1)
  set L := log (1 / δ)
  have hLρ : 0 < L / ρ := div_pos hL hρ
  set s := √(L / ρ) with hs_def
  have hs : 0 < s := sqrt_pos.2 hLρ
  have hs2 : L = ρ * s ^ 2 := by
    rw [hs_def, sq_sqrt hLρ.le]; field_simp
  have hα : 1 < 1 + s := by linarith
  have key := measureReal_le_exp_mul_add (μ := M S) (ν := M S') hα hδ (h.renyiDiv_ne_top hS hα)
    (h.toReal_renyiDiv_le hS hα) E
  have hsq : √(ρ * L) = ρ * s := by
    rw [hs2, show ρ * (ρ * s ^ 2) = (ρ * s) ^ 2 by ring]
    exact sqrt_sq (by positivity)
  have heq : ξ + ρ + 2 * √(ρ * L) = ξ + ρ * (1 + s) + L / (1 + s - 1) := by
    rw [hsq, add_sub_cancel_left, hs2]
    field_simp
    ring
  rwa [heq]

end ZCDP

/-- **Lemma 3.5** of Bun–Steinke (zCDP implies approximate DP): if `M` is `(ξ, ρ)`-zCDP, then it
is `(ξ + ρ + √(4 ρ log (1 / δ)), δ)`-DP for every `δ > 0`; here `√(4 ρ log (1 / δ))` is written
`2 √(ρ log (1 / δ))`. No sign conditions are needed: `ρ < 0` is incompatible with zCDP (for
neighbouring datasets), and for `δ ≥ 1` the claim is trivial. The proof is not the paper's
privacy-loss/Markov argument but the probability-preservation bound
`μ(T) ^ α ≤ exp ((α - 1) D_α(μ ‖ ν)) ν(T) ^ (α - 1)` (Hölder's inequality,
`ZCDP.measureReal_rpow_le`), at the paper's order `α = 1 + √(log (1 / δ) / ρ)`; the case `ρ = 0`,
where that order is undefined, follows by letting `ρ ↓ 0`. -/
theorem IsZCDP.isEpsDeltaDP [IsMarkovKernel M] (h : IsZCDP M Adj ξ ρ) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP M Adj (ξ + ρ + 2 * √(ρ * log (1 / δ))) δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · intro S S' hS E
    exact measureReal_le_one.trans (hδ1.trans
      (le_add_of_nonneg_left (mul_nonneg (exp_pos _).le measureReal_nonneg)))
  rcases lt_trichotomy ρ 0 with hρ | rfl | hρ
  · intro S S' hS E
    exfalso
    have hα : 1 < 2 + |ξ| / -ρ := by
      have : 0 ≤ |ξ| / -ρ := div_nonneg (abs_nonneg ξ) (by linarith)
      linarith
    have h1 := h.toReal_renyiDiv_le hS hα
    have h2 : ρ * (|ξ| / -ρ) = -|ξ| := by
      rw [mul_div_assoc', div_neg, mul_div_cancel_left₀ _ hρ.ne]
    rw [mul_add, h2] at h1
    linarith [ENNReal.toReal_nonneg (a := renyiDiv (2 + |ξ| / -ρ) (M S) (M S')), le_abs_self ξ]
  · intro S S' hS E
    have key : ∀ t : ℝ, 0 < t → (M S).real E ≤
        exp (ξ + t + 2 * √(t * log (1 / δ))) * (M S').real E + δ :=
      fun t ht ↦ ZCDP.isEpsDeltaDP_of_pos (h.mono le_rfl ht.le) ht hδ hδ1 hS E
    have hcont : Filter.Tendsto
        (fun t : ℝ ↦ exp (ξ + t + 2 * √(t * log (1 / δ))) * (M S').real E + δ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (exp (ξ + 0 + 2 * √(0 * log (1 / δ))) * (M S').real E + δ)) :=
      ((by fun_prop : Continuous fun t : ℝ ↦
        exp (ξ + t + 2 * √(t * log (1 / δ))) * (M S').real E + δ).tendsto 0).mono_left
        nhdsWithin_le_nhds
    exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)
  · exact ZCDP.isEpsDeltaDP_of_pos h hρ hδ hδ1

/-- **Proposition 1.3** of Bun–Steinke: if `M` is `ρ`-zCDP, then it is
`(ρ + 2 √(ρ log (1 / δ)), δ)`-DP for every `δ > 0`. -/
theorem IsZCDP.isEpsDeltaDP' [IsMarkovKernel M] (h : IsZCDP M Adj 0 ρ) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP M Adj (ρ + 2 * √(ρ * log (1 / δ))) δ := by
  simpa using h.isEpsDeltaDP hδ

namespace ZCDP

/-- If `μ ≤ e^ε ν` (that is, `D_∞(μ ‖ ν) ≤ ε`), then `D_a(μ ‖ ν) ≤ ε` for every `a > 1`
(monotonicity of the Rényi divergence in the order, used in Lemma 3.2 of Bun–Steinke). -/
lemma renyiDiv_le_of_le_smul {μ ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ε : ℝ}
    (h1 : ∀ E, MeasurableSet E → μ E ≤ ENNReal.ofReal (exp ε) * ν E) {a : ℝ} (ha : 1 < a) :
    renyiDiv a μ ν ≠ ∞ ∧ (renyiDiv a μ ν).toReal ≤ ε := by
  set c := ENNReal.ofReal (exp ε) with hc_def
  have hac : μ ≪ ν := Measure.AbsolutelyContinuous.mk fun s hs hνs ↦
    le_antisymm ((h1 s hs).trans (by simp [hνs])) zero_le
  have hup : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ c :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ ν)
      fun s hs _ ↦ by
        rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
        exact h1 s hs
  have h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν := by
    refine Integrable.of_bound
      ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.pow_const a).aestronglyMeasurable
      (exp ε ^ a) ?_
    filter_upwards [hup] with x hu
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg ENNReal.toReal_nonneg _)]
    exact rpow_le_rpow ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal (exp_pos ε).le hu)
      (by linarith)
  have hR : renyiDiv a μ ν ≠ ∞ := (renyiDiv_ne_top_iff_of_one_lt ha).2 ⟨h_int, hac⟩
  refine ⟨hR, ?_⟩
  have hle : ∫⁻ x, (∂μ/∂ν) x ^ a ∂ν ≤ ∫⁻ x, c ^ (a - 1) * (∂μ/∂ν) x ∂ν := by
    refine lintegral_mono_ae ?_
    filter_upwards [hup] with x hx
    rw [show a = (a - 1) + 1 by ring, ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one,
      ENNReal.rpow_one, add_sub_cancel_right]
    exact mul_le_mul_left (ENNReal.rpow_le_rpow hx (by linarith)) _
  rw [lintegral_const_mul _ (Measure.measurable_rnDeriv μ ν), Measure.lintegral_rnDeriv hac,
    measure_univ, mul_one, lintegral_rpow_rnDeriv_eq ha hR, hc_def,
    ENNReal.ofReal_rpow_of_nonneg (exp_pos ε).le (by linarith), ← exp_mul,
    ENNReal.ofReal_le_ofReal_iff (exp_pos _).le, exp_le_exp] at hle
  nlinarith

/-- **Proposition 3.3** of Bun–Steinke, for measures: if `μ ≤ e^ε ν` and `ν ≤ e^ε μ` (that is,
`D_∞(μ ‖ ν) ≤ ε` and `D_∞(ν ‖ μ) ≤ ε`), then `D_a(μ ‖ ν) ≤ ε² a / 2` for every `a > 1`. The proof
applies Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`) to the privacy loss
`Z = log (dμ/dν) ∈ [-ε, ε]` under `μ` twice: at `t = -1`, where `E_μ[e^{-Z}] = 1` gives
`E_μ[Z] ≤ ε² / 2`, and at `t = a - 1`, where `E_μ[e^{(a-1)Z}] = exp ((a - 1) D_a(μ ‖ ν))`. -/
lemma renyiDiv_le_sq_of_le_smul {μ ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 ≤ ε)
    (h1 : ∀ E, MeasurableSet E → μ E ≤ ENNReal.ofReal (exp ε) * ν E)
    (h2 : ∀ E, MeasurableSet E → ν E ≤ ENNReal.ofReal (exp ε) * μ E) {a : ℝ} (ha : 1 < a) :
    renyiDiv a μ ν ≠ ∞ ∧ (renyiDiv a μ ν).toReal ≤ ε ^ 2 / 2 * a := by
  set c := ENNReal.ofReal (exp ε) with hc_def
  have hc0 : c ≠ 0 := by simp [c, exp_pos]
  have hcinv : c⁻¹ = ENNReal.ofReal (exp (-ε)) := by
    rw [hc_def, exp_neg, ENNReal.ofReal_inv_of_pos (exp_pos ε)]
  have hac : μ ≪ ν := Measure.AbsolutelyContinuous.mk fun s hs hνs ↦
    le_antisymm ((h1 s hs).trans (by simp [hνs])) zero_le
  have hca : ν ≪ μ := Measure.AbsolutelyContinuous.mk fun s hs hμs ↦
    le_antisymm ((h2 s hs).trans (by simp [hμs])) zero_le
  have hup : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ c :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ ν)
      fun s hs _ ↦ by
        rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
        exact h1 s hs
  have hlow : ∀ᵐ x ∂ν, c⁻¹ ≤ μ.rnDeriv ν x :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const fun s hs _ ↦ by
      rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const,
        ENNReal.inv_mul_le_iff hc0 ENNReal.ofReal_ne_top]
      exact h2 s hs
  set Z : Y → ℝ := fun x ↦ log (μ.rnDeriv ν x).toReal with hZ_def
  have hbd : ∀ᵐ x ∂μ, exp (-ε) ≤ (μ.rnDeriv ν x).toReal ∧ (μ.rnDeriv ν x).toReal ≤ exp ε := by
    refine hac.ae_le ?_
    filter_upwards [hup, hlow, Measure.rnDeriv_lt_top μ ν] with x hu hl ht
    refine ⟨?_, ENNReal.toReal_le_of_le_ofReal (exp_pos ε).le hu⟩
    rw [hcinv] at hl
    exact (ENNReal.ofReal_le_iff_le_toReal ht.ne).1 hl
  have hZ : ∀ᵐ x ∂μ, Z x ∈ Set.Icc (-ε) ε := by
    filter_upwards [hbd] with x ⟨hl, hu⟩
    have hpos : 0 < (μ.rnDeriv ν x).toReal := (exp_pos _).trans_le hl
    exact ⟨(le_log_iff_exp_le hpos).2 hl, (log_le_iff_le_exp hpos).2 hu⟩
  have hmeas : AEMeasurable Z μ :=
    ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.log).aemeasurable
  have hsub := hasSubgaussianMGF_of_mem_Icc hmeas hZ
  set m := ∫ x, Z x ∂μ
  have hc2 : (((‖ε - -ε‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = ε ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (by linarith)]
    norm_num
  have hmgf : ∀ t, mgf Z μ t ≤ exp (t * m + ε ^ 2 * t ^ 2 / 2) := by
    intro t
    have h := hsub.mgf_le t
    rw [hc2] at h
    have : mgf (fun x ↦ Z x - m) μ t = mgf Z μ t * exp (-(t * m)) := by
      simp only [sub_eq_add_neg]
      rw [mgf_add_const, mul_neg]
    rw [this, ← le_div_iff₀ (exp_pos _), ← exp_sub] at h
    convert h using 2
    ring
  -- `t = -1`: the mean of the privacy loss is at most `ε ^ 2 / 2`
  have hmgf1 : mgf Z μ (-1) = 1 := by
    have h_ae : (fun x ↦ exp (-1 * Z x)) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x).toReal := by
      filter_upwards [hbd, Measure.inv_rnDeriv hac] with x ⟨hl, _⟩ hinv
      have hpos : 0 < (μ.rnDeriv ν x).toReal := (exp_pos _).trans_le hl
      rw [← hinv, Pi.inv_apply, ENNReal.toReal_inv, neg_one_mul, exp_neg, hZ_def,
        exp_log hpos]
    rw [mgf, integral_congr_ae h_ae, Measure.integral_toReal_rnDeriv hca, probReal_univ]
  have hm : m ≤ ε ^ 2 / 2 := by
    have h := hmgf (-1)
    rw [hmgf1] at h
    have h' : exp 0 ≤ exp (-1 * m + ε ^ 2 * (-1) ^ 2 / 2) := by rwa [exp_zero]
    rw [exp_le_exp] at h'
    nlinarith
  -- `t = a - 1`
  have ha1 : 0 < a - 1 := by linarith
  have hJ : mgf Z μ (a - 1) ≤ exp ((a - 1) * (ε ^ 2 / 2 * a)) := by
    refine (hmgf (a - 1)).trans (exp_le_exp.2 ?_)
    nlinarith [mul_le_mul_of_nonneg_left hm ha1.le]
  have hJpos : 0 < mgf Z μ (a - 1) := mgf_pos (integrable_exp_mul_of_mem_Icc hmeas hZ)
  have hJeq : mgf Z μ (a - 1) = ∫ x, (μ.rnDeriv ν x).toReal ^ (a - 1) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hbd] with x ⟨hl, _⟩
    have hpos : 0 < (μ.rnDeriv ν x).toReal := (exp_pos _).trans_le hl
    rw [rpow_def_of_pos hpos, hZ_def, mul_comm]
  have h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν := by
    refine Integrable.of_bound
      ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.pow_const a).aestronglyMeasurable
      (exp ε ^ a) ?_
    filter_upwards [hup] with x hu
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg ENNReal.toReal_nonneg _)]
    exact rpow_le_rpow ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal (exp_pos ε).le hu)
      (by linarith)
  rw [renyiDiv_eq_log_integral_of_one_lt' ha h_int hac]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal', ← hJeq]
  simp only [measure_univ, ENNReal.toReal_one, log_one, mul_zero, add_zero, sub_zero]
  refine max_le ?_ (by positivity)
  rw [inv_mul_le_iff₀ ha1]
  exact (log_le_iff_le_exp hJpos).2 hJ
end ZCDP

/-- **Lemma 3.2** of Bun–Steinke: a mechanism is `ε`-DP iff it is `(ε, 0)`-zCDP. -/
theorem isZCDP_iff_isEpsDeltaDP [IsMarkovKernel M] {ε : ℝ} :
    IsZCDP M Adj ε 0 ↔ IsEpsDeltaDP M Adj ε 0 := by
  refine ⟨fun h S S' hS E ↦ ?_, fun h ↦ isZCDP_iff_toReal.2 fun S S' hS α hα ↦ ?_⟩
  · refine le_of_forall_sub_le fun δ hδ ↦ ?_
    have := h.isEpsDeltaDP hδ hS E
    simp only [add_zero, zero_mul, sqrt_zero, mul_zero] at this
    linarith
  · simp only [zero_mul, add_zero]
    refine ZCDP.renyiDiv_le_of_le_smul (fun E hE ↦ ?_) hα
    rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (exp_pos ε).le]
    exact ENNReal.ofReal_le_ofReal (by simpa using h hS E)

/-- **Proposition 1.4** of Bun–Steinke (proved as Proposition 3.3): an `ε`-DP mechanism is
`(ε² / 2)`-zCDP, for a symmetric neighbouring relation. The proof uses Hoeffding's lemma rather
than the paper's `sinh` inequality (Lemma B.1); see `ZCDP.renyiDiv_le_sq_of_le_smul`. -/
theorem IsEpsDeltaDP.isZCDP [IsMarkovKernel M] [Std.Symm Adj] {ε : ℝ}
    (h : IsEpsDeltaDP M Adj ε 0) : IsZCDP M Adj 0 (ε ^ 2 / 2) := by
  refine isZCDP_iff_toReal.2 fun S S' hS α hα ↦ ?_
  have hle : ∀ ⦃S S'⦄, Adj S S' → ∀ E, MeasurableSet E →
      M S E ≤ ENNReal.ofReal (exp ε) * M S' E := fun S S' hS E _ ↦ by
    rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (exp_pos ε).le]
    exact ENNReal.ofReal_le_ofReal (by simpa using h hS E)
  have hε : 0 ≤ ε := by
    have := h hS Set.univ
    simp only [probReal_univ, mul_one, add_zero] at this
    exact one_le_exp_iff.1 this
  rw [zero_add]
  exact ZCDP.renyiDiv_le_sq_of_le_smul hε (hle hS) (hle (Std.Symm.symm _ _ hS)) hα

/-- **Composition of pure DP via zCDP** (Proposition 1.4 combined with Lemma 1.7 of Bun–Steinke):
if `M i` is `ε`-DP for each of `k = |ι|` indices, the product mechanism `ZCDP.piKernel M`,
releasing independent outputs of all of them, is `(k ε² / 2)`-zCDP. -/
theorem isZCDP_pi_of_isEpsDeltaDP {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)]
    [Std.Symm Adj] {ε : ℝ} (h : ∀ i, IsEpsDeltaDP (M i) Adj ε 0) :
    IsZCDP (ZCDP.piKernel M) Adj 0 (Fintype.card ι * ε ^ 2 / 2) := by
  have := IsZCDP.piKernel fun i ↦ (h i).isZCDP
  simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  rwa [mul_div_assoc]

/-- **Composition of pure DP, approximate-DP form.** This bound is not stated in the paper; it
follows from Proposition 1.4, Lemma 1.7 and Proposition 1.3 of Bun–Steinke (it is a zCDP form
of the advanced composition theorem discussed in §1.3; it is not comparable with the paper's
Corollary 8.11, whose logarithmic term is `log (√(π / 2) ε √k / δ)`). The product mechanism
`ZCDP.piKernel M` of `k = |ι|` mechanisms, each `ε`-DP with `ε ≥ 0`, is
`(k ε² / 2 + ε √(2 k log (1 / δ)), δ)`-DP for every `δ > 0`. -/
theorem isEpsDeltaDP_pi_of_isEpsDeltaDP {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)]
    [Std.Symm Adj] {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, IsEpsDeltaDP (M i) Adj ε 0) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP (ZCDP.piKernel M) Adj
      (Fintype.card ι * ε ^ 2 / 2 + ε * √(2 * Fintype.card ι * log (1 / δ))) δ := by
  have := (isZCDP_pi_of_isEpsDeltaDP h).isEpsDeltaDP' hδ
  rwa [show (Fintype.card ι : ℝ) * ε ^ 2 / 2 * log (1 / δ)
      = (ε / 2) ^ 2 * (2 * Fintype.card ι * log (1 / δ)) by ring,
    sqrt_mul (sq_nonneg _), sqrt_sq (by linarith),
    show 2 * (ε / 2 * √(2 * Fintype.card ι * log (1 / δ)))
      = ε * √(2 * Fintype.card ι * log (1 / δ)) by ring] at this

/-! ### The Gaussian mechanism -/

namespace ZCDP

/-- The Radon–Nikodym derivative between Gaussians with the same variance `v ≠ 0`:
`dN(μ₁, v)/dN(μ₂, v) (x) = exp ((μ₁ - μ₂) x / v - (μ₁² - μ₂²) / (2 v))`. -/
lemma rnDeriv_gaussianReal_gaussianReal (μ₁ μ₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal μ₁ v).rnDeriv (gaussianReal μ₂ v) =ᵐ[gaussianReal μ₂ v]
      fun x ↦ ENNReal.ofReal (exp ((μ₁ - μ₂) / v * x - (μ₁ ^ 2 - μ₂ ^ 2) / (2 * v))) := by
  have h1 := Measure.rnDeriv_eq_div (μ := gaussianReal μ₁ v) (ν := gaussianReal μ₂ v)
    (gaussianReal_absolutelyContinuous μ₁ hv) (gaussianReal_absolutelyContinuous μ₂ hv)
  filter_upwards [h1, (gaussianReal_absolutelyContinuous μ₂ hv).ae_le (rnDeriv_gaussianReal μ₁ v),
    (gaussianReal_absolutelyContinuous μ₂ hv).ae_le (rnDeriv_gaussianReal μ₂ v)] with x h1 h2 h3
  rw [h1, h2, h3, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_div_of_pos (gaussianPDFReal_pos _ _ _ hv), gaussianPDFReal_def,
    gaussianPDFReal_def]
  congr 1
  have hs : 0 < (√(2 * π * v))⁻¹ := inv_pos.2 (sqrt_pos.2 (by positivity))
  rw [mul_div_mul_left _ _ hs.ne', ← exp_sub]
  congr 1
  have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

/-- **Lemma 2.4** of Bun–Steinke, for orders `a > 1`: the Rényi divergence between Gaussians with
the same variance `v = σ² ≠ 0` is `D_a(N(μ₁, σ²) ‖ N(μ₂, σ²)) = a (μ₁ - μ₂)² / (2 σ²)`. The proof
writes `D_a` as `(a - 1)⁻¹ log E_{N(μ₁, σ²)}[(dN(μ₁, σ²)/dN(μ₂, σ²))^(a - 1)]` and evaluates the
expectation with the Gaussian moment generating function, instead of completing the square. -/
lemma renyiDiv_gaussianReal (μ₁ μ₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {a : ℝ} (ha : 1 < a) :
    renyiDiv a (gaussianReal μ₁ v) (gaussianReal μ₂ v)
      = ENNReal.ofReal (a * (μ₁ - μ₂) ^ 2 / (2 * v)) := by
  set P := gaussianReal μ₁ v
  set Q := gaussianReal μ₂ v
  have hPQ : P ≪ Q := (gaussianReal_absolutelyContinuous μ₁ hv).trans
    (gaussianReal_absolutelyContinuous' μ₂ hv)
  have hrn := rnDeriv_gaussianReal_gaussianReal μ₁ μ₂ hv
  set s := (μ₁ - μ₂) / v
  set c := (μ₁ ^ 2 - μ₂ ^ 2) / (2 * v)
  have h_int : Integrable (fun x ↦ (P.rnDeriv Q x).toReal ^ a) Q := by
    refine ((integrable_exp_mul_gaussianReal (a * s)).mul_const (exp (-(a * c)))).congr ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (exp_pos _).le, ← exp_mul, ← exp_add]
    congr 1
    ring
  have hJ : ∫ x, (P.rnDeriv Q x).toReal ^ (a - 1) ∂P
      = exp (-((a - 1) * c)) * exp (μ₁ * ((a - 1) * s) + v * ((a - 1) * s) ^ 2 / 2) := by
    have hm := congrFun (mgf_fun_id_gaussianReal (μ := μ₁) (v := v)) ((a - 1) * s)
    rw [← hm, mgf, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hPQ.ae_le hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (exp_pos _).le, ← exp_mul, ← exp_add]
    congr 1
    ring
  rw [renyiDiv_eq_log_integral_of_one_lt' ha h_int hPQ, hJ, ← exp_add, log_exp]
  simp only [measure_univ, ENNReal.toReal_one, log_one, mul_zero, add_zero, sub_zero]
  congr 1
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have ha' : a - 1 ≠ 0 := by linarith
  simp only [s, c]
  field_simp
  ring
/-- The Gaussian mechanism `S ↦ N(q S, v)` as a Markov kernel, for a measurable query `q`. -/
noncomputable def gaussianKernel (q : 𝒟 → ℝ) (hq : Measurable q) (v : ℝ≥0) : Kernel 𝒟 ℝ where
  toFun S := gaussianReal (q S) v
  measurable' := measurable_gaussianReal.comp (hq.prodMk measurable_const)

/-- The value of the Gaussian mechanism at a dataset. -/
lemma gaussianKernel_apply (q : 𝒟 → ℝ) (hq : Measurable q) (v : ℝ≥0) (S : 𝒟) :
    gaussianKernel q hq v S = gaussianReal (q S) v := rfl

instance (q : 𝒟 → ℝ) (hq : Measurable q) (v : ℝ≥0) : IsMarkovKernel (gaussianKernel q hq v) :=
  ⟨fun S ↦ by rw [gaussianKernel_apply]; infer_instance⟩

end ZCDP

/-- **Proposition 1.6** of Bun–Steinke (Gaussian mechanism): if the query `q : 𝒟 → ℝ` has
sensitivity `Δ` (`|q S - q S'| ≤ Δ` for neighbours) and `M S = N(q S, σ²)` with variance
`v = σ² ≠ 0`, then `M` is `(Δ² / (2 σ²))`-zCDP. Such a kernel is `ZCDP.gaussianKernel` when `q`
is measurable (`ZCDP.isZCDP_gaussianKernel`). -/
theorem isZCDP_of_gaussianReal {q : 𝒟 → ℝ} {Δ : ℝ} (hq : ∀ ⦃S S'⦄, Adj S S' → |q S - q S'| ≤ Δ)
    {v : ℝ≥0} (hv : v ≠ 0) {M : Kernel 𝒟 ℝ} (hM : ∀ S, M S = gaussianReal (q S) v) :
    IsZCDP M Adj 0 (Δ ^ 2 / (2 * v)) := by
  refine isZCDP_iff_toReal.2 fun S S' hS α hα ↦ ?_
  rw [hM, hM, ZCDP.renyiDiv_gaussianReal _ _ hv hα]
  have hv' : (0 : ℝ) < 2 * v := mul_pos two_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hv'.le),
    zero_add, div_mul_eq_mul_div, mul_comm _ α]
  have : (q S - q S') ^ 2 ≤ Δ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hq hS) 2
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by linarith)) hv'.le

/-- The Gaussian mechanism `ZCDP.gaussianKernel` is `(Δ² / (2 σ²))`-zCDP for a measurable query
of sensitivity `Δ` (Proposition 1.6 of Bun–Steinke). -/
theorem ZCDP.isZCDP_gaussianKernel {q : 𝒟 → ℝ} (hq_meas : Measurable q) {Δ : ℝ}
    (hq : ∀ ⦃S S'⦄, Adj S S' → |q S - q S'| ≤ Δ) {v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP (gaussianKernel q hq_meas v) Adj 0 (Δ ^ 2 / (2 * v)) :=
  isZCDP_of_gaussianReal hq hv fun _ ↦ rfl

end InformationTheory
