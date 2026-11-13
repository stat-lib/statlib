/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Data.EReal.Inv
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Maximal `(α, β)`-leakage

Gilani, Kurri, Kosut and Sankar, *Unifying privacy measures via maximal `(α, β)`-leakage
(MαbeL)*, IEEE Trans. Inf. Theory 70(6), 2024 (arXiv:2304.07456; journal version of *An alphabet
of leakage measures*, ITW 2022, arXiv:2211.15453), introduce a two-parameter family
`L_{α,β}(X → Y)` of leakage measures, defined operationally through an adversary guessing a
randomized function of `X` (their Definition 9). For finite alphabets and
`(α, β) ∈ (1, ∞) × [1, ∞)`, their Theorem 1 gives the closed form (eq. (14))

`L_{α,β}(X → Y) = max_{x'} sup_P α / ((α - 1) β) log ∑_y P(y|x')^(1-β) (∑_x P(x) P(y|x)^α)^(β/α)`,

where `P` ranges over input distributions. Since Definition 9 maximizes over the law of `X`,
the measure depends on the channel `P_{Y|X}` only.

As `maxLeakage` does for Issa, Wagner and Kamath, this file takes the closed form (14) as the
*definition*, for a Markov kernel `κ : Kernel 𝒳 𝒴` between finite alphabets; logarithms are
natural. The leakage is `EReal`-valued (through `ENNReal.log`): by Remark 1, for `β > 1` it is
`+∞` as soon as some row `P_{Y|X=x}` is not absolutely continuous with respect to another row
`P_{Y|X=x'}`, and the `ℝ≥0∞` conventions
`0 ^ (1 - β) = ∞` for `β > 1` and `∞ * 0 = 0` encode exactly this. The operational Definition 9
and the equivalence of Theorem 1 are **not** formalized. Input distributions are `PMF 𝒳`.

## Main definitions

* `alphaBetaTerm κ α β x' p`: the argument of the logarithm in (14).
* `alphaBetaLeakageSum κ α β`: its supremum over `x'` and `p` (multiplicative form).
* `alphaBetaLeakage κ α β`: maximal `(α, β)`-leakage, `α / ((α - 1) β) * log` of the above.
* `localRenyiDP κ β`: local Rényi differential privacy of order `β` (Definition 7, eq. (11)).
* `maxRenyiLeakage κ β`: maximal Rényi leakage of order `β`, in the closed form (15).
* `localDP κ`: local differential privacy (Definition 3, eq. (4)).

## Main statements (paper result → Lean name)

* Theorem 2(1), monotonicity in `β`: `alphaBetaLeakage_mono`.
* Theorem 2(2), data processing (16a): `alphaBetaLeakage_comp_le`; linkage (16b):
  `alphaBetaLeakage_comp_le_right`.
* Theorem 2(3), non-negativity and its equality case: `alphaBetaLeakage_nonneg`,
  `alphaBetaLeakage_eq_zero_iff`.
* Theorem 2(4), additivity (case `n = 2`, from which (18) follows by induction):
  `alphaBetaLeakage_parallelComp`.
* Theorem 1, eq. (15), the limit `α → ∞`: `tendsto_alphaBetaLeakage_atTop`.
* Proposition 1(1)–(2), `α ≤ β` gives scaled local Rényi DP: `alphaBetaLeakage_eq_mul_localRenyiDP`,
  `alphaBetaLeakage_self`.
* Proposition 1(3), local DP at `(∞, ∞)`: `tendsto_maxRenyiLeakage_atTop`,
  `tendsto_limUnder_alphaBetaLeakage_atTop`.
* Remark after Definition 9, maximal `α`-leakage at `β = 1`: `alphaBetaLeakage_one_right`;
  maximal leakage at `(∞, 1)`: `maxRenyiLeakage_one`, `tendsto_alphaBetaLeakage_one_atTop`.

## Not formalized

The operational definition and Theorem 1 itself, conditional and vector MαbeL (Definitions 10–11,
Theorems 3–5, Propositions 2–3), the `(α, τ)` reparametrization (Section V) and continuous
alphabets (Section VI).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-! ### Auxiliary inequalities in `ℝ≥0∞`

These lemmas are not specific to leakage and are candidates for Mathlib. -/

namespace ENNReal

variable {α β : ℝ}

/-- `a ^ (1 - β) * a ^ β = a` for a finite `a` and `β > 0`. -/
lemma rpow_one_sub_mul_rpow_self {a : ℝ≥0∞} (ha : a ≠ ∞) (hβ : 0 < β) :
    a ^ (1 - β) * a ^ β = a := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp [ENNReal.zero_rpow_of_pos hβ]
  · rw [← ENNReal.rpow_add _ _ ha₀ ha]
    simp

/-- `w ^ (1 - β) * g ^ β = w * (g / w) ^ β` for `0 < β` and a finite `w`, provided `g = 0`
whenever `w = 0`. -/
lemma rpow_one_sub_mul_rpow_eq_mul_div_rpow {w g : ℝ≥0∞} (hw : w ≠ ∞) (hwg : w = 0 → g = 0)
    (hβ : 0 < β) : w ^ (1 - β) * g ^ β = w * (g / w) ^ β := by
  rcases eq_or_ne w 0 with h0 | h0
  · simp [h0, hwg h0, ENNReal.zero_rpow_of_pos hβ]
  · rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hβ.le, ENNReal.inv_rpow,
      sub_eq_add_neg, ENNReal.rpow_add _ _ h0 hw, ENNReal.rpow_neg, ENNReal.rpow_one]
    ring

lemma rpow_one_div_mul_rpow {a b : ℝ≥0∞} (hα : 0 < α) :
    (a ^ (1 / α) * b) ^ α = a * b ^ α := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le, ← ENNReal.rpow_mul, one_div_mul_cancel hα.ne',
    ENNReal.rpow_one]

/-- The `L^β(w)`-type mean `(∑ᵢ wᵢ^(1 - β) gᵢ^β)^(1/β)` is non-decreasing in `β ≥ 1` for a
probability vector `w`. This is the inequality behind Theorem 2(1). -/
lemma rpow_sum_rpow_one_sub_mul_rpow_le {ι : Type*} (s : Finset ι) {w g : ι → ℝ≥0∞}
    (hw : ∑ i ∈ s, w i = 1) {β₁ β₂ : ℝ} (h₁ : 1 ≤ β₁) (h₁₂ : β₁ ≤ β₂) :
    (∑ i ∈ s, w i ^ (1 - β₁) * g i ^ β₁) ^ β₁⁻¹ ≤
      (∑ i ∈ s, w i ^ (1 - β₂) * g i ^ β₂) ^ β₂⁻¹ := by
  have h₂ : 0 < β₂ := by linarith
  by_cases hA : ∃ i ∈ s, w i = 0 ∧ g i ≠ 0 ∧ 1 < β₂
  · obtain ⟨i, hi, hwi, hgi, hβ₂⟩ := hA
    have : ∑ i ∈ s, w i ^ (1 - β₂) * g i ^ β₂ = ∞ := by
      refine top_unique (le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun i ↦ w i ^ (1 - β₂) * g i ^ β₂) (fun _ _ ↦ zero_le) hi))
      rw [hwi, ENNReal.zero_rpow_of_neg (by linarith), ENNReal.top_mul]
      exact (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hgi) h₂.le).ne'
    rw [this, ENNReal.top_rpow_of_pos (inv_pos.2 h₂)]
    exact le_top
  push Not at hA
  rcases h₁₂.eq_or_lt with rfl | h₁₂'
  · exact le_rfl
  have hβ₂ : 1 < β₂ := h₁.trans_lt h₁₂'
  have hw_ne_top : ∀ i ∈ s, w i ≠ ∞ := fun i hi ↦
    ne_top_of_le_ne_top ENNReal.one_ne_top (hw ▸ Finset.single_le_sum (fun _ _ ↦ zero_le) hi)
  -- rewrite each term as `w i * (g i / w i) ^ β`
  have key (β : ℝ) (hβ : 0 < β) :
      ∑ i ∈ s, w i ^ (1 - β) * g i ^ β = ∑ i ∈ s, w i * (g i / w i) ^ β := by
    refine Finset.sum_congr rfl fun i hi ↦ rpow_one_sub_mul_rpow_eq_mul_div_rpow (hw_ne_top i hi)
      (fun h0 ↦ ?_) hβ
    by_contra hg
    exact (hA i hi h0 hg).not_gt hβ₂
  rw [key β₁ (by linarith), key β₂ h₂]
  have hr : 1 ≤ β₂ / β₁ := (one_le_div (by linarith)).2 h₁₂
  calc (∑ i ∈ s, w i * (g i / w i) ^ β₁) ^ β₁⁻¹
      = ((∑ i ∈ s, w i * (g i / w i) ^ β₁) ^ (β₂ / β₁)) ^ β₂⁻¹ := by
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp
    _ ≤ (∑ i ∈ s, w i * ((g i / w i) ^ β₁) ^ (β₂ / β₁)) ^ β₂⁻¹ := by
        gcongr
        exact ENNReal.rpow_arith_mean_le_arith_mean_rpow _ _ _ hw hr
    _ = (∑ i ∈ s, w i * (g i / w i) ^ β₂) ^ β₂⁻¹ := by
        simp_rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ (show β₁ ≠ 0 by linarith)]

/-- A finite Jensen inequality for the jointly convex, positively homogeneous function
`(a, b) ↦ a ^ (1 - β) * b ^ β` (`β ≥ 1`), deduced from Hölder's inequality. It drives both data
processing inequalities of Theorem 2(2). -/
lemma rpow_sum_mul_rpow_sum_le {ι : Type*} (s : Finset ι) {c w g : ι → ℝ≥0∞}
    (hc : ∀ i ∈ s, c i ≠ ∞) (hw : ∀ i ∈ s, w i ≠ ∞) (hβ : 1 ≤ β) :
    (∑ i ∈ s, c i * w i) ^ (1 - β) * (∑ i ∈ s, c i * g i) ^ β ≤
      ∑ i ∈ s, c i * (w i ^ (1 - β) * g i ^ β) := by
  rcases hβ.eq_or_lt with rfl | hβ
  · simp
  by_cases hA : ∃ i ∈ s, c i ≠ 0 ∧ w i = 0 ∧ g i ≠ 0
  · obtain ⟨i, hi, hci, hwi, hgi⟩ := hA
    have : ∑ i ∈ s, c i * (w i ^ (1 - β) * g i ^ β) = ∞ := by
      refine top_unique (le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun i ↦ c i * (w i ^ (1 - β) * g i ^ β)) (fun _ _ ↦ zero_le) hi))
      rw [hwi, ENNReal.zero_rpow_of_neg (by linarith), ENNReal.top_mul
        (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hgi) (by linarith)).ne',
        ENNReal.mul_top hci]
    rw [this]
    exact le_top
  push Not at hA
  set A := ∑ i ∈ s, c i * w i with hA_def
  have hB : ∑ i ∈ s, c i * g i = ∑ i ∈ s, c i * w i * (g i / w i) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rcases eq_or_ne (c i) 0 with hc0 | hc0
    · simp [hc0]
    rw [mul_assoc, ENNReal.mul_div_cancel' (hA i hi hc0) (fun h ↦ (hw i hi h).elim)]
  have hR : ∑ i ∈ s, c i * (w i ^ (1 - β) * g i ^ β) =
      ∑ i ∈ s, c i * w i * (g i / w i) ^ β := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rcases eq_or_ne (c i) 0 with hc0 | hc0
    · simp [hc0]
    rw [mul_assoc, rpow_one_sub_mul_rpow_eq_mul_div_rpow (hw i hi) (hA i hi hc0) (by linarith)]
  rw [hB, hR]
  rcases eq_or_ne A 0 with hA0 | hA0
  · have : ∑ i ∈ s, c i * w i * (g i / w i) = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [Finset.sum_eq_zero_iff] at hA0
      rw [hA0 i hi, zero_mul]
    rw [this, ENNReal.zero_rpow_of_pos (by linarith), mul_zero]
    exact zero_le
  have hAt : A ≠ ∞ := ENNReal.sum_ne_top.2 fun i hi ↦ ENNReal.mul_ne_top (hc i hi) (hw i hi)
  have hH := ENNReal.inner_le_weight_mul_Lp_of_nonneg s hβ.le (fun i ↦ c i * w i)
    (fun i ↦ g i / w i)
  rw [← hA_def] at hH
  calc A ^ (1 - β) * (∑ i ∈ s, c i * w i * (g i / w i)) ^ β
      ≤ A ^ (1 - β) * (A ^ (1 - β⁻¹) * (∑ i ∈ s, c i * w i * (g i / w i) ^ β) ^ β⁻¹) ^ β := by
        gcongr
    _ = A ^ ((1 - β) + (1 - β⁻¹) * β) * ∑ i ∈ s, c i * w i * (g i / w i) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          inv_mul_cancel₀ (by linarith), ENNReal.rpow_one, ← mul_assoc,
          ← ENNReal.rpow_add _ _ hA0 hAt]
    _ = ∑ i ∈ s, c i * w i * (g i / w i) ^ β := by
        rw [show (1 - β) + (1 - β⁻¹) * β = 0 by field_simp; ring, ENNReal.rpow_zero, one_mul]

/-- **Minkowski's inequality** for a finite family of vectors, `ℝ≥0∞`-valued:
`‖∑ⱼ Fⱼ‖_α ≤ ∑ⱼ ‖Fⱼ‖_α`. -/
lemma rpow_sum_sum_rpow_le {ι ι' : Type*} (s : Finset ι) (t : Finset ι') (F : ι → ι' → ℝ≥0∞)
    (hα : 1 ≤ α) :
    (∑ i ∈ s, (∑ j ∈ t, F i j) ^ α) ^ (1 / α) ≤ ∑ j ∈ t, (∑ i ∈ s, F i j ^ α) ^ (1 / α) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hα₀ : 0 < α := by linarith
    simp [ENNReal.zero_rpow_of_pos hα₀, hα₀]
  | insert j t hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact (ENNReal.Lp_add_le s _ _ hα).trans (add_le_add_right ih _)

/-- Strict convexity of `t ↦ t ^ α` (`α > 1`) at the midpoint of two distinct finite points of
`ℝ≥0∞`. -/
lemma inv_two_mul_add_rpow_lt {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) (hab : a ≠ b)
    (hα : 1 < α) : (2⁻¹ * a + 2⁻¹ * b) ^ α < 2⁻¹ * a ^ α + 2⁻¹ * b ^ α := by
  have hα₀ : 0 ≤ α := by linarith
  have hl : (2⁻¹ * a + 2⁻¹ * b) ^ α ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hα₀ (by finiteness)
  have hr : 2⁻¹ * a ^ α + 2⁻¹ * b ^ α ≠ ∞ := by
    have := ENNReal.rpow_ne_top_of_nonneg hα₀ ha
    have := ENNReal.rpow_ne_top_of_nonneg hα₀ hb
    finiteness
  rw [← ENNReal.toReal_lt_toReal hl hr, ← ENNReal.toReal_rpow,
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (ENNReal.mul_ne_top (by simp)
      (ENNReal.rpow_ne_top_of_nonneg hα₀ hb))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow]
  have := (strictConvexOn_rpow hα).2 (Set.mem_Ici.2 ENNReal.toReal_nonneg)
    (Set.mem_Ici.2 ENNReal.toReal_nonneg) (by rwa [Ne, ENNReal.toReal_eq_toReal_iff' ha hb])
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
  simpa [smul_eq_mul] using this

lemma tendsto_rpow_inv_atTop {w : ℝ≥0∞} (h₀ : w ≠ 0) (h : w ≠ ∞) :
    Tendsto (fun β : ℝ ↦ w ^ β⁻¹) atTop (𝓝 1) := by
  have ht : 0 < w.toReal := ENNReal.toReal_pos h₀ h
  have := ENNReal.tendsto_ofReal
    ((Real.continuousAt_const_rpow ht.ne').tendsto.comp tendsto_inv_atTop_zero)
  rw [Real.rpow_zero, ENNReal.ofReal_one] at this
  refine this.congr fun β ↦ ?_
  rw [Function.comp_apply, ← ENNReal.ofReal_rpow_of_pos ht, ENNReal.ofReal_toReal h]

end ENNReal

namespace InformationTheory

variable {𝒳 𝒴 𝒵 : Type*} [Fintype 𝒳] [Fintype 𝒴] {m𝒳 : MeasurableSpace 𝒳}
  {m𝒴 : MeasurableSpace 𝒴} {κ : Kernel 𝒳 𝒴} {α β : ℝ}

/-! ### Definitions -/

/-- The argument of the logarithm in the closed form (14) of maximal `(α, β)`-leakage, for a
reference input `x'` and an input distribution `p`:
`∑_y P(y|x')^(1 - β) (∑_x p(x) P(y|x)^α)^(β/α)`. -/
noncomputable def alphaBetaTerm (κ : Kernel 𝒳 𝒴) (α β : ℝ) (x' : 𝒳) (p : PMF 𝒳) : ℝ≥0∞ :=
  ∑ y, κ x' {y} ^ (1 - β) * (∑ x, p x * κ x {y} ^ α) ^ (β / α)

/-- The multiplicative form of maximal `(α, β)`-leakage: `alphaBetaTerm` maximized over the
reference input `x'` and over all input distributions `p`. -/
noncomputable def alphaBetaLeakageSum (κ : Kernel 𝒳 𝒴) (α β : ℝ) : ℝ≥0∞ :=
  ⨆ (x' : 𝒳) (p : PMF 𝒳), alphaBetaTerm κ α β x' p

/-- **Maximal `(α, β)`-leakage** (MαbeL) of the channel `κ`, in nats, in the closed form of
Theorem 1, eq. (14):
`L_{α,β}(X → Y) = max_{x'} sup_p α / ((α - 1) β) log ∑_y P(y|x')^(1-β) (∑_x p(x) P(y|x)^α)^(β/α)`.
It is meaningful for `(α, β) ∈ (1, ∞) × [1, ∞)`; the supremum is taken inside the (order
isomorphism) `ENNReal.log`. -/
noncomputable def alphaBetaLeakage (κ : Kernel 𝒳 𝒴) (α β : ℝ) : EReal :=
  ((α / ((α - 1) * β) : ℝ) : EReal) * ENNReal.log (alphaBetaLeakageSum κ α β)

/-- The argument of the logarithm in local Rényi differential privacy:
`max_{x, x'} ∑_y P(y|x')^(1 - β) P(y|x)^β`. -/
noncomputable def localRenyiDPSum (κ : Kernel 𝒳 𝒴) (β : ℝ) : ℝ≥0∞ :=
  ⨆ (x : 𝒳) (x' : 𝒳), ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β

/-- **Local Rényi differential privacy** of order `β > 1` (Definition 7, eq. (11)):
`max_{x, x'} D_β(P_{Y|X=x} ‖ P_{Y|X=x'}) = max_{x, x'} 1/(β - 1) log ∑_y P(y|x')^(1-β) P(y|x)^β`.
-/
noncomputable def localRenyiDP (κ : Kernel 𝒳 𝒴) (β : ℝ) : EReal :=
  (((β - 1)⁻¹ : ℝ) : EReal) * ENNReal.log (localRenyiDPSum κ β)

/-- The argument of the logarithm in maximal Rényi leakage:
`max_{x'} ∑_y P(y|x')^(1 - β) (max_x P(y|x))^β`. -/
noncomputable def maxRenyiLeakageSum (κ : Kernel 𝒳 𝒴) (β : ℝ) : ℝ≥0∞ :=
  ⨆ x' : 𝒳, ∑ y, κ x' {y} ^ (1 - β) * (⨆ x : 𝒳, κ x {y}) ^ β

/-- **Maximal Rényi leakage** of order `β` (Definition 8), in the closed form (15):
`(1/β) log max_{x'} ∑_y P(y|x')^(1 - β) max_x P(y|x)^β`. That this is the limit `α → ∞` of
maximal `(α, β)`-leakage is `tendsto_alphaBetaLeakage_atTop`. -/
noncomputable def maxRenyiLeakage (κ : Kernel 𝒳 𝒴) (β : ℝ) : EReal :=
  ((β⁻¹ : ℝ) : EReal) * ENNReal.log (maxRenyiLeakageSum κ β)

/-- **Local differential privacy** (Definition 3, eq. (4)): `max_{x, x', y} log P(y|x)/P(y|x')`.
In `ℝ≥0∞`, a ratio `a / 0` with `a ≠ 0` is `∞` and `0 / 0 = 0`, so pairs with
`P(y|x) = P(y|x') = 0` do not contribute. -/
noncomputable def localDP (κ : Kernel 𝒳 𝒴) : EReal :=
  ENNReal.log (⨆ (x : 𝒳) (x' : 𝒳) (y : 𝒴), κ x {y} / κ x' {y})

/-! ### Basic lemmas -/

omit [Fintype 𝒴] in
private lemma sum_pmf_eq_one (p : PMF 𝒳) : ∑ x, p x = 1 :=
  (tsum_fintype (L := .unconditional _) _).symm.trans p.tsum_coe

omit [Fintype 𝒴] in
lemma sum_inv_card_eq_one [Nonempty 𝒳] : ∑ _x : 𝒳, (Fintype.card 𝒳 : ℝ≥0∞)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by simp) (by simp)]

/-- At a point mass `p = δ_x`, the term of (14) is the local Rényi DP term of the pair
`(x, x')`. -/
lemma alphaBetaTerm_pure (hα : α ≠ 0) (x' x : 𝒳) :
    alphaBetaTerm κ α β x' (PMF.pure x) = ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β := by
  classical
  simp only [alphaBetaTerm, PMF.pure_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, ← ENNReal.rpow_mul, mul_div_cancel₀ _ hα]

lemma alphaBetaTerm_eq (x' : 𝒳) (p : PMF 𝒳) :
    alphaBetaTerm κ α β x' p =
      ∑ y, κ x' {y} ^ (1 - β) * ((∑ x, p x * κ x {y} ^ α) ^ (1 / α)) ^ β := by
  simp_rw [alphaBetaTerm, ← ENNReal.rpow_mul, one_div_mul_eq_div]

/-- `maximal (α, β)-leakage = (α / (α - 1)) log (alphaBetaLeakageSum ^ (1/β))`. -/
lemma alphaBetaLeakage_eq_mul_log_rpow (κ : Kernel 𝒳 𝒴) (α β : ℝ) :
    alphaBetaLeakage κ α β =
      ((α / (α - 1) : ℝ) : EReal) * ENNReal.log (alphaBetaLeakageSum κ α β ^ β⁻¹) := by
  rw [alphaBetaLeakage, ENNReal.log_rpow, ← mul_assoc, ← EReal.coe_mul, div_mul_eq_div_div,
    div_eq_mul_inv (α / (α - 1))]

variable [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ]

omit [Fintype 𝒳] in
lemma sum_rpow_one_sub_mul_rpow_self (hβ : 0 < β) (x : 𝒳) :
    ∑ y, κ x {y} ^ (1 - β) * κ x {y} ^ β = 1 := by
  simp_rw [ENNReal.rpow_one_sub_mul_rpow_self (measure_ne_top _ _) hβ]
  simp [sum_measure_singleton]

lemma one_le_alphaBetaLeakageSum [Nonempty 𝒳] (hα : α ≠ 0) (hβ : 0 < β) :
    1 ≤ alphaBetaLeakageSum κ α β := by
  obtain ⟨x⟩ := ‹Nonempty 𝒳›
  calc (1 : ℝ≥0∞) = alphaBetaTerm κ α β x (PMF.pure x) := by
        rw [alphaBetaTerm_pure hα, sum_rpow_one_sub_mul_rpow_self hβ]
    _ ≤ _ := le_iSup₂ (f := fun x' p ↦ alphaBetaTerm κ α β x' p) x (PMF.pure x)

/-! ### Non-negativity (Theorem 2(3)) -/

/-- **Non-negativity** of maximal `(α, β)`-leakage (Theorem 2(3), eq. (17)). -/
theorem alphaBetaLeakage_nonneg [Nonempty 𝒳] (hα : 1 < α) (hβ : 1 ≤ β) :
    0 ≤ alphaBetaLeakage κ α β := by
  refine EReal.mul_nonneg (EReal.coe_nonneg.2 (by positivity)) ?_
  exact ENNReal.zero_le_log_iff.2 (one_le_alphaBetaLeakageSum (by positivity) (by positivity))

/-- If all rows of the channel coincide, i.e. `X` and `Y` are independent for every input law,
then the multiplicative form of maximal `(α, β)`-leakage is `1`. -/
lemma alphaBetaLeakageSum_eq_one_of_forall_eq [Nonempty 𝒳] (hα : α ≠ 0) (hβ : 0 < β)
    (h : ∀ x x', κ x = κ x') : alphaBetaLeakageSum κ α β = 1 := by
  refine le_antisymm (iSup₂_le fun x' p ↦ le_of_eq ?_) (one_le_alphaBetaLeakageSum hα hβ)
  simp_rw [alphaBetaTerm, h _ x', ← Finset.sum_mul, sum_pmf_eq_one, one_mul,
    ← ENNReal.rpow_mul, mul_div_cancel₀ _ hα]
  exact sum_rpow_one_sub_mul_rpow_self hβ x'

/-- Maximal `(α, β)`-leakage vanishes when all rows of the channel coincide, i.e. when `X` and
`Y` are independent for every input law (the "if" direction of the equality case in
Theorem 2(3)). -/
theorem alphaBetaLeakage_eq_zero_of_forall_eq [Nonempty 𝒳] (hα : α ≠ 0) (hβ : 0 < β)
    (h : ∀ x x', κ x = κ x') : alphaBetaLeakage κ α β = 0 := by
  simp [alphaBetaLeakage, alphaBetaLeakageSum_eq_one_of_forall_eq hα hβ h]

/-! ### Special cases: local Rényi DP and maximal `α`-leakage (Proposition 1) -/

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- For `α ≤ β`, the supremum over the input distribution in (14) is attained at a point
mass: this is the key step of Proposition 1. -/
lemma alphaBetaTerm_le_iSup (hα : 0 < α) (hαβ : α ≤ β) (x' : 𝒳) (p : PMF 𝒳) :
    alphaBetaTerm κ α β x' p ≤ ⨆ x, ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β := by
  have hβα : 1 ≤ β / α := (one_le_div hα).2 hαβ
  calc alphaBetaTerm κ α β x' p
      ≤ ∑ y, κ x' {y} ^ (1 - β) * ∑ x, p x * (κ x {y} ^ α) ^ (β / α) := by
        unfold alphaBetaTerm
        gcongr with y
        exact ENNReal.rpow_arith_mean_le_arith_mean_rpow _ _ _ (sum_pmf_eq_one p) hβα
    _ = ∑ x, p x * ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β := by
        simp_rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hα.ne', Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [mul_left_comm]
    _ ≤ ∑ x, p x * ⨆ x, ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β := by
        gcongr with x
        exact le_iSup (fun x ↦ ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β) x
    _ = ⨆ x, ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β := by
        rw [← Finset.sum_mul, sum_pmf_eq_one, one_mul]

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- Multiplicative form of Proposition 1: for `α ≤ β` the supremum over input distributions in
(14) is attained at point masses, so that `alphaBetaLeakageSum` is the local Rényi DP sum. -/
theorem alphaBetaLeakageSum_eq_localRenyiDPSum (hα : 0 < α) (hαβ : α ≤ β) :
    alphaBetaLeakageSum κ α β = localRenyiDPSum κ β := by
  refine le_antisymm (iSup₂_le fun x' p ↦ (alphaBetaTerm_le_iSup hα hαβ x' p).trans ?_)
    (iSup₂_le fun x x' ↦ ?_)
  · exact iSup_le fun x ↦
      le_iSup₂ (f := fun x x' : 𝒳 ↦ ∑ y, κ x' {y} ^ (1 - β) * κ x {y} ^ β) x x'
  · rw [← alphaBetaTerm_pure hα.ne']
    exact le_iSup₂ (f := fun x' p ↦ alphaBetaTerm κ α β x' p) x' (PMF.pure x)

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- **Proposition 1** (first item): for `1 < α ≤ β`, maximal `(α, β)`-leakage is a scaled local
Rényi differential privacy of order `β`. -/
theorem alphaBetaLeakage_eq_mul_localRenyiDP (hα : 1 < α) (hαβ : α ≤ β) :
    alphaBetaLeakage κ α β =
      ((α * (β - 1) / ((α - 1) * β) : ℝ) : EReal) * localRenyiDP κ β := by
  rw [alphaBetaLeakage, localRenyiDP, alphaBetaLeakageSum_eq_localRenyiDPSum (by linarith) hαβ,
    ← mul_assoc, ← EReal.coe_mul]
  have : β - 1 ≠ 0 := by linarith
  rw [show α * (β - 1) / ((α - 1) * β) * (β - 1)⁻¹ = α / ((α - 1) * β) by field_simp]

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- **Proposition 1** (second item): maximal `(β, β)`-leakage is local Rényi differential privacy
of order `β`, for `β > 1`. -/
theorem alphaBetaLeakage_self (hβ : 1 < β) : alphaBetaLeakage κ β β = localRenyiDP κ β := by
  rw [alphaBetaLeakage_eq_mul_localRenyiDP hβ le_rfl, mul_comm β, div_self, EReal.coe_one,
    one_mul]
  have : β - 1 ≠ 0 := by linarith
  positivity

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- For `β = 1`, maximal `(α, β)`-leakage is **maximal `α`-leakage** (remark after Definition 9,
Proposition 1 and Figure 1a), in the closed form `sup_p I_α^S(p, P_{Y|X})` of Liao et al.
(eq. (3)), for an input distribution of full support:
`L_{α,1}(X → Y) = α / (α - 1) log sup_p ∑_y (∑_x p(x) P(y|x)^α)^(1/α)`. -/
theorem alphaBetaLeakage_one_right [Nonempty 𝒳] :
    alphaBetaLeakage κ α 1 = ((α / (α - 1) : ℝ) : EReal) *
      ENNReal.log (⨆ p : PMF 𝒳, ∑ y, (∑ x, p x * κ x {y} ^ α) ^ (1 / α)) := by
  simp [alphaBetaLeakage, alphaBetaLeakageSum, alphaBetaTerm]

omit [Fintype 𝒳] in
/-- Maximal Rényi leakage of order `1` is maximal leakage, for any input distribution `μ` of full
support (eq. (15) at `β = 1`, see Figure 1a). -/
theorem maxRenyiLeakage_one [Nonempty 𝒳] {μ : Measure 𝒳} (hμ : ∀ x, μ {x} ≠ 0) :
    maxRenyiLeakage κ 1 = maxLeakage μ κ := by
  obtain ⟨x⟩ := ‹Nonempty 𝒳›
  have h : maxRenyiLeakageSum κ 1 = maxLeakageSum μ κ := by
    simp [maxRenyiLeakageSum, maxLeakageSum, hμ]
  rw [maxRenyiLeakage, h, inv_one, EReal.coe_one, one_mul, maxLeakage,
    ENNReal.log_pos_real (zero_lt_one.trans_le (one_le_maxLeakageSum (hμ x))).ne'
      maxLeakageSum_ne_top]

/-! ### Monotonicity in `β` (Theorem 2(1)) -/

/-- **Monotonicity in `β`** (Theorem 2(1)): for a fixed `α > 1`, maximal `(α, β)`-leakage is
non-decreasing in `β ∈ [1, ∞)`. -/
theorem alphaBetaLeakage_mono (hα : 1 < α) {β₁ β₂ : ℝ} (h₁ : 1 ≤ β₁) (h₁₂ : β₁ ≤ β₂) :
    alphaBetaLeakage κ α β₁ ≤ alphaBetaLeakage κ α β₂ := by
  simp_rw [alphaBetaLeakage_eq_mul_log_rpow]
  refine mul_le_mul_of_nonneg_left (ENNReal.log_le_log ?_) (EReal.coe_nonneg.2 (by positivity))
  simp_rw [alphaBetaLeakageSum, ENNReal.iSup_rpow_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < β₁)),
    ENNReal.iSup_rpow_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < β₂))]
  refine iSup₂_mono fun x' p ↦ ?_
  have h (β : ℝ) : alphaBetaTerm κ α β x' p =
      ∑ y, κ x' {y} ^ (1 - β) * ((∑ x, p x * κ x {y} ^ α) ^ α⁻¹) ^ β := by
    simp_rw [alphaBetaTerm, ← ENNReal.rpow_mul, inv_mul_eq_div]
  rw [h, h]
  exact ENNReal.rpow_sum_rpow_one_sub_mul_rpow_le _ (by simp [sum_measure_singleton]) h₁ h₁₂

/-! ### The equality case of non-negativity (Theorem 2(3)) -/

/-- If two rows of the channel differ, the multiplicative form of maximal `(α, β)`-leakage
exceeds `1`: the half-half mixture of the two rows already leaks. -/
lemma one_lt_alphaBetaLeakageSum (hα : 1 < α) (hβ : 1 ≤ β) {x₀ x₁ : 𝒳} (h : κ x₀ ≠ κ x₁) :
    1 < alphaBetaLeakageSum κ α β := by
  classical
  have hα₀ : 0 < α := by linarith
  have hne : x₀ ≠ x₁ := fun h' ↦ h (h' ▸ rfl)
  obtain ⟨y₀, hy₀⟩ : ∃ y, κ x₀ {y} ≠ κ x₁ {y} := by
    by_contra! H
    exact h (Measure.ext_of_singleton H)
  set f : 𝒳 → ℝ≥0∞ := fun x ↦ (if x = x₀ then 2⁻¹ else 0) + (if x = x₁ then 2⁻¹ else 0)
  have hf : ∑ x, f x = 1 := by
    simp [f, Finset.sum_add_distrib, ENNReal.inv_two_add_inv_two]
  set p := PMF.ofFintype f hf
  have hp (g : 𝒳 → ℝ≥0∞) : ∑ x, p x * g x = 2⁻¹ * g x₀ + 2⁻¹ * g x₁ := by
    simp [p, f, PMF.ofFintype_apply, add_mul, Finset.sum_add_distrib]
  set g : 𝒴 → ℝ≥0∞ := fun y ↦ (∑ x, p x * κ x {y} ^ α) ^ (1 / α)
  have hlow : 1 < ∑ y, g y := by
    calc (1 : ℝ≥0∞) = ∑ y, (2⁻¹ * κ x₀ {y} + 2⁻¹ * κ x₁ {y}) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_measure_singleton,
            sum_measure_singleton, Finset.coe_univ, measure_univ, measure_univ, mul_one,
            ENNReal.inv_two_add_inv_two]
      _ < ∑ y, g y := by
          have hle (y : 𝒴) : 2⁻¹ * κ x₀ {y} + 2⁻¹ * κ x₁ {y} ≤ g y := by
            simp only [g, hp, one_div]
            exact (ENNReal.le_rpow_inv_iff hα₀).2 (ENNReal.rpow_arith_mean_le_arith_mean2_rpow
              _ _ _ _ ENNReal.inv_two_add_inv_two hα.le)
          have hlt : 2⁻¹ * κ x₀ {y₀} + 2⁻¹ * κ x₁ {y₀} < g y₀ := by
            simp only [g, hp, one_div]
            exact (ENNReal.lt_rpow_inv_iff hα₀).2 (ENNReal.inv_two_mul_add_rpow_lt
              (measure_ne_top _ _) (measure_ne_top _ _) hy₀ hα)
          rw [← Finset.add_sum_erase Finset.univ g (Finset.mem_univ y₀),
            ← Finset.add_sum_erase Finset.univ (fun y ↦ 2⁻¹ * κ x₀ {y} + 2⁻¹ * κ x₁ {y})
              (Finset.mem_univ y₀)]
          refine ENNReal.add_lt_add_of_lt_of_le (ENNReal.sum_ne_top.2 fun y _ ↦ ?_) hlt
            (Finset.sum_le_sum fun y _ ↦ hle y)
          exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (measure_ne_top _ _),
            ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)⟩
  have hmono : ∑ y, g y ≤ alphaBetaTerm κ α β x₀ p ^ β⁻¹ := by
    have := ENNReal.rpow_sum_rpow_one_sub_mul_rpow_le Finset.univ (w := fun y ↦ κ x₀ {y}) (g := g)
      (by simp [sum_measure_singleton]) le_rfl hβ
    simp only [sub_self, ENNReal.rpow_zero, one_mul, ENNReal.rpow_one, inv_one] at this
    rw [alphaBetaTerm_eq]
    exact this
  have h1 : 1 < alphaBetaTerm κ α β x₀ p := by
    by_contra! hT
    exact (hlow.trans_le hmono).not_ge (ENNReal.rpow_le_one hT (inv_nonneg.2 (by linarith)))
  exact h1.trans_le (le_iSup₂ (f := fun x' p ↦ alphaBetaTerm κ α β x' p) x₀ p)

/-- **Non-negativity with its equality case** (Theorem 2(3)): maximal `(α, β)`-leakage vanishes
if and only if all rows of the channel coincide, i.e. iff `X` and `Y` are independent (for any
input distribution of full support). -/
theorem alphaBetaLeakage_eq_zero_iff [Nonempty 𝒳] (hα : 1 < α) (hβ : 1 ≤ β) :
    alphaBetaLeakage κ α β = 0 ↔ ∀ x x', κ x = κ x' := by
  refine ⟨fun h x x' ↦ ?_, alphaBetaLeakage_eq_zero_of_forall_eq (by positivity) (by positivity)⟩
  by_contra hne
  have hpos : 0 < alphaBetaLeakage κ α β :=
    EReal.mul_pos (EReal.coe_pos.2 (by positivity))
      (ENNReal.zero_lt_log_iff.2 (one_lt_alphaBetaLeakageSum hα hβ hne))
  exact hpos.ne' h

/-! ### The limit `α → ∞`: maximal Rényi leakage -/

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- Each term of (14) is at most the corresponding term of (15). -/
lemma alphaBetaTerm_le_sum_iSup (hα : 0 < α) (hβ : 0 ≤ β) (x' : 𝒳) (p : PMF 𝒳) :
    alphaBetaTerm κ α β x' p ≤ ∑ y, κ x' {y} ^ (1 - β) * (⨆ x, κ x {y}) ^ β := by
  unfold alphaBetaTerm
  gcongr with y
  calc (∑ x, p x * κ x {y} ^ α) ^ (β / α)
      ≤ (∑ x, p x * (⨆ x, κ x {y}) ^ α) ^ (β / α) := by
        refine ENNReal.rpow_le_rpow ?_ (div_nonneg hβ hα.le)
        gcongr with x
        exact le_iSup (fun x ↦ κ x {y}) x
    _ = (⨆ x, κ x {y}) ^ β := by
        rw [← Finset.sum_mul, sum_pmf_eq_one, one_mul, ← ENNReal.rpow_mul,
          mul_div_cancel₀ _ hα.ne']

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
lemma alphaBetaLeakageSum_le_maxRenyiLeakageSum (hα : 0 < α) (hβ : 0 ≤ β) :
    alphaBetaLeakageSum κ α β ≤ maxRenyiLeakageSum κ β :=
  iSup₂_le fun x' p ↦ (alphaBetaTerm_le_sum_iSup hα hβ x' p).trans <|
    le_iSup (fun x' ↦ ∑ y, κ x' {y} ^ (1 - β) * (⨆ x, κ x {y}) ^ β) x'

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- The uniform input distribution achieves (15) up to the factor `|𝒳|^(-β/α)`. -/
lemma card_rpow_mul_le_alphaBetaTerm [Nonempty 𝒳] (hα : 0 < α) (hβ : 0 ≤ β) (x' : 𝒳) :
    (Fintype.card 𝒳 : ℝ≥0∞) ^ (-(β / α)) *
        ∑ y, κ x' {y} ^ (1 - β) * (⨆ x, κ x {y}) ^ β ≤
      alphaBetaTerm κ α β x' (PMF.ofFintype _ sum_inv_card_eq_one) := by
  set n := (Fintype.card 𝒳 : ℝ≥0∞)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  rw [mul_left_comm]
  gcongr
  calc n ^ (-(β / α)) * (⨆ x, κ x {y}) ^ β
      = (n⁻¹ * (⨆ x, κ x {y}) ^ α) ^ (β / α) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg hβ hα.le), ← ENNReal.rpow_mul,
          mul_div_cancel₀ _ hα.ne', ENNReal.rpow_neg, ENNReal.inv_rpow]
    _ ≤ (∑ x, PMF.ofFintype _ sum_inv_card_eq_one x * κ x {y} ^ α) ^ (β / α) := by
        refine ENNReal.rpow_le_rpow ?_ (div_nonneg hβ hα.le)
        rw [ENNReal.iSup_rpow_of_pos hα, ENNReal.mul_iSup]
        exact iSup_le fun x ↦ Finset.single_le_sum (f := fun x ↦ n⁻¹ * κ x {y} ^ α)
          (fun _ _ ↦ zero_le) (Finset.mem_univ x)

omit [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
lemma card_rpow_mul_le_alphaBetaLeakageSum [Nonempty 𝒳] (hα : 0 < α) (hβ : 0 ≤ β) :
    (Fintype.card 𝒳 : ℝ≥0∞) ^ (-(β / α)) * maxRenyiLeakageSum κ β ≤
      alphaBetaLeakageSum κ α β := by
  rw [maxRenyiLeakageSum, ENNReal.mul_iSup]
  exact iSup_le fun x' ↦ (card_rpow_mul_le_alphaBetaTerm hα hβ x').trans <|
    le_iSup₂ (f := fun x' p ↦ alphaBetaTerm κ α β x' p) x' _

omit [Fintype 𝒳] in
lemma one_le_maxRenyiLeakageSum [Finite 𝒳] [Nonempty 𝒳] (hβ : 0 < β) :
    1 ≤ maxRenyiLeakageSum κ β :=
  have := Fintype.ofFinite 𝒳
  (one_le_alphaBetaLeakageSum one_ne_zero hβ).trans
    (alphaBetaLeakageSum_le_maxRenyiLeakageSum one_pos hβ.le)

private lemma tendsto_coeff_atTop (hβ : β ≠ 0) :
    Tendsto (fun α : ℝ ↦ α / ((α - 1) * β)) atTop (𝓝 β⁻¹) := by
  have h : Tendsto (fun α : ℝ ↦ ((1 - α⁻¹) * β)⁻¹) atTop (𝓝 ((1 - 0) * β)⁻¹) :=
    ((tendsto_const_nhds.sub tendsto_inv_atTop_zero).mul_const β).inv₀ (by simpa using hβ)
  rw [sub_zero, one_mul] at h
  refine h.congr' ((eventually_gt_atTop 1).mono fun α hα ↦ ?_)
  have : α - 1 ≠ 0 := by linarith
  have : α ≠ 0 := by linarith
  field_simp

/-- **Theorem 1, eq. (15)**: as `α → ∞`, maximal `(α, β)`-leakage converges to maximal Rényi
leakage of order `β`, `(1/β) log max_{x'} ∑_y P(y | x')^(1 - β) max_x P(y | x)^β`. -/
theorem tendsto_alphaBetaLeakage_atTop [Nonempty 𝒳] (hβ : 1 ≤ β) :
    Tendsto (fun α ↦ alphaBetaLeakage κ α β) atTop (𝓝 (maxRenyiLeakage κ β)) := by
  have hβ₀ : 0 < β := by linarith
  set M := maxRenyiLeakageSum κ β with hM
  set n := (Fintype.card 𝒳 : ℝ≥0∞)
  have hn₀ : n ≠ 0 := by simp [n]
  have hn : n ≠ ∞ := by simp [n]
  have hM₁ : 1 ≤ M := one_le_maxRenyiLeakageSum hβ₀
  rcases eq_or_ne M ∞ with hMt | hMt
  · -- infinite leakage
    have h : ∀ α : ℝ, 1 < α → alphaBetaLeakage κ α β = ⊤ := fun α hα ↦ by
      have hS : alphaBetaLeakageSum κ α β = ∞ := by
        refine top_unique ((le_of_eq ?_).trans
          (card_rpow_mul_le_alphaBetaLeakageSum (by linarith) hβ₀.le))
        rw [← hM, hMt, ENNReal.mul_top]
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hn₀) hn).ne'
      rw [alphaBetaLeakage, hS, ENNReal.log_top, EReal.coe_mul_top_of_pos]
      exact div_pos (by linarith) (mul_pos (by linarith) hβ₀)
    rw [maxRenyiLeakage, ← hM, hMt, ENNReal.log_top, EReal.coe_mul_top_of_pos (inv_pos.2 hβ₀)]
    exact tendsto_const_nhds.congr' ((eventually_gt_atTop 1).mono fun α hα ↦ (h α hα).symm)
  · -- finite leakage: squeeze in `ℝ`
    set m := Real.log M.toReal
    have hM₀ : M ≠ 0 := (zero_lt_one.trans_le hM₁).ne'
    have hlogM : ENNReal.log M = m := ENNReal.log_pos_real hM₀ hMt
    have hS (α : ℝ) (hα : 1 < α) : alphaBetaLeakage κ α β =
        ((α / ((α - 1) * β) * Real.log (alphaBetaLeakageSum κ α β).toReal : ℝ) : EReal) := by
      have h₁ : 1 ≤ alphaBetaLeakageSum κ α β :=
        one_le_alphaBetaLeakageSum (by linarith) hβ₀
      have h₂ : alphaBetaLeakageSum κ α β ≠ ∞ :=
        ne_top_of_le_ne_top hMt (alphaBetaLeakageSum_le_maxRenyiLeakageSum (by linarith) hβ₀.le)
      rw [alphaBetaLeakage, ENNReal.log_pos_real (zero_lt_one.trans_le h₁).ne' h₂,
        EReal.coe_mul]
    rw [maxRenyiLeakage, ← hM, hlogM, ← EReal.coe_mul]
    refine (EReal.tendsto_coe.2 ?_).congr' ((eventually_gt_atTop 1).mono fun α hα ↦
      (hS α hα).symm)
    have hc := tendsto_coeff_atTop hβ₀.ne'
    have hlow : Tendsto (fun α : ℝ ↦ α / ((α - 1) * β) *
        (-(β / α) * Real.log n.toReal + m)) atTop (𝓝 (β⁻¹ * (-0 * Real.log n.toReal + m))) :=
      hc.mul (((tendsto_const_nhds.div_atTop tendsto_id).neg.mul_const _).add_const _)
    rw [neg_zero, zero_mul, zero_add] at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow (hc.mul_const m) ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with α hα
      have hcα : 0 < α / ((α - 1) * β) := div_pos (by linarith) (mul_pos (by linarith) hβ₀)
      refine mul_le_mul_of_nonneg_left ?_ hcα.le
      have hlow := card_rpow_mul_le_alphaBetaLeakageSum (κ := κ) (by linarith : 0 < α) hβ₀.le
      have hpos : 0 < (n ^ (-(β / α)) * M).toReal :=
        ENNReal.toReal_pos (mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 hn₀) hn).ne' hM₀)
          (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hn₀ hn) hMt)
      calc -(β / α) * Real.log n.toReal + m = Real.log (n ^ (-(β / α)) * M).toReal := by
            rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
              Real.log_mul (Real.rpow_pos_of_pos (ENNReal.toReal_pos hn₀ hn) _).ne'
                (ENNReal.toReal_pos hM₀ hMt).ne', Real.log_rpow (ENNReal.toReal_pos hn₀ hn)]
        _ ≤ Real.log (alphaBetaLeakageSum κ α β).toReal :=
            Real.log_le_log hpos <| ENNReal.toReal_mono (ne_top_of_le_ne_top hMt
              (alphaBetaLeakageSum_le_maxRenyiLeakageSum (by linarith) hβ₀.le)) hlow
    · filter_upwards [eventually_gt_atTop 1] with α hα
      have hcα : 0 < α / ((α - 1) * β) := div_pos (by linarith) (mul_pos (by linarith) hβ₀)
      refine mul_le_mul_of_nonneg_left ?_ hcα.le
      have h₁ : 1 ≤ alphaBetaLeakageSum κ α β := one_le_alphaBetaLeakageSum (by linarith) hβ₀
      exact Real.log_le_log (ENNReal.toReal_pos (zero_lt_one.trans_le h₁).ne'
          (ne_top_of_le_ne_top hMt (alphaBetaLeakageSum_le_maxRenyiLeakageSum (by linarith)
            hβ₀.le)))
        (ENNReal.toReal_mono hMt (alphaBetaLeakageSum_le_maxRenyiLeakageSum (by linarith) hβ₀.le))

/-! ### The limit `β → ∞`: local differential privacy -/

omit [Fintype 𝒳] in
/-- The upper bound in the proof of Proposition 1(3):
`M_β^(1/β) ≤ max_{x, x', y} P(y|x)/P(y|x')`. -/
lemma maxRenyiLeakageSum_rpow_inv_le (hβ : 0 < β) :
    maxRenyiLeakageSum κ β ^ β⁻¹ ≤ ⨆ (x : 𝒳) (x' : 𝒳) (y : 𝒴), κ x {y} / κ x' {y} := by
  set D := ⨆ (x : 𝒳) (x' : 𝒳) (y : 𝒴), κ x {y} / κ x' {y}
  rcases eq_or_ne D ∞ with hD | hD
  · exact hD ▸ le_top
  refine ENNReal.rpow_inv_le_iff hβ |>.2 <| iSup_le fun x' ↦ ?_
  have hm (y : 𝒴) : (⨆ x, κ x {y}) ≤ D * κ x' {y} := iSup_le fun x ↦
    (ENNReal.div_le_iff_le_mul (Or.inr hD) (Or.inl (measure_ne_top _ _))).1 <|
      le_iSup_of_le x <| le_iSup_of_le x' <| le_iSup (fun y ↦ κ x {y} / κ x' {y}) y
  calc ∑ y, κ x' {y} ^ (1 - β) * (⨆ x, κ x {y}) ^ β
      ≤ ∑ y, κ x' {y} ^ (1 - β) * (D * κ x' {y}) ^ β := by
        gcongr with y
        exact hm y
    _ = D ^ β * ∑ y, κ x' {y} ^ (1 - β) * κ x' {y} ^ β := by
        rw [Finset.mul_sum]
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hβ.le]
        exact Finset.sum_congr rfl fun y _ ↦ by ring
    _ = D ^ β := by rw [sum_rpow_one_sub_mul_rpow_self hβ, mul_one]

omit [Fintype 𝒳] [MeasurableSingletonClass 𝒴] [IsMarkovKernel κ] in
/-- The lower bound in the proof of Proposition 1(3). -/
lemma eventually_lt_maxRenyiLeakageSum_rpow_inv {a : ℝ≥0∞} (x x' : 𝒳) (y : 𝒴)
    (ha : a < κ x {y} / κ x' {y}) (hfin : ∀ x y, κ x {y} ≠ ∞) :
    ∀ᶠ β in atTop, a < maxRenyiLeakageSum κ β ^ β⁻¹ := by
  have hk : κ x {y} ≠ 0 := by
    rintro h
    simp [h] at ha
  have hle (β : ℝ) (hβ : 0 ≤ β) :
      κ x' {y} ^ (1 - β) * κ x {y} ^ β ≤ maxRenyiLeakageSum κ β := by
    refine le_iSup_of_le x' <| le_trans ?_ <| Finset.single_le_sum
      (f := fun y ↦ κ x' {y} ^ (1 - β) * (⨆ x, κ x {y}) ^ β) (fun _ _ ↦ zero_le)
      (Finset.mem_univ y)
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (le_iSup (fun x ↦ κ x {y}) x) hβ) _
  rcases eq_or_ne (κ x' {y}) 0 with hw | hw
  · filter_upwards [eventually_gt_atTop 1] with β hβ
    have : maxRenyiLeakageSum κ β = ∞ := by
      refine top_unique <| le_trans (le_of_eq ?_) (hle β (by linarith))
      rw [hw, ENNReal.zero_rpow_of_neg (by linarith), ENNReal.top_mul]
      exact (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hk) (by linarith)).ne'
    rw [this, ENNReal.top_rpow_of_pos (by positivity)]
    exact ha.trans_le le_top
  · have hw' : κ x' {y} ≠ ∞ := hfin x' y
    have hr : κ x {y} / κ x' {y} ≠ ∞ := ENNReal.div_ne_top (hfin x y) hw
    have hlim := ENNReal.Tendsto.mul_const (ENNReal.tendsto_rpow_inv_atTop hw hw') (Or.inr hr)
    rw [one_mul] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds ha), eventually_gt_atTop 0] with β hβ hβ₀
    refine hβ.trans_le ?_
    have hexp : (1 - β) * β⁻¹ = β⁻¹ + -1 := by field_simp; ring
    calc κ x' {y} ^ β⁻¹ * (κ x {y} / κ x' {y})
        = κ x' {y} ^ (β⁻¹ + -1) * κ x {y} := by
          rw [ENNReal.rpow_add _ _ hw hw', ENNReal.rpow_neg_one, div_eq_mul_inv]
          ring
      _ = (κ x' {y} ^ (1 - β) * κ x {y} ^ β) ^ β⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hβ₀.le), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_inv_cancel₀ hβ₀.ne', ENNReal.rpow_one, hexp]
      _ ≤ maxRenyiLeakageSum κ β ^ β⁻¹ :=
          ENNReal.rpow_le_rpow (hle β hβ₀.le) (inv_nonneg.2 hβ₀.le)

omit [Fintype 𝒳] in
/-- **Proposition 1** (third item, inner limit taken in `tendsto_alphaBetaLeakage_atTop`):
as `β → ∞`, maximal Rényi leakage of order `β` converges to local differential privacy. -/
theorem tendsto_maxRenyiLeakage_atTop :
    Tendsto (fun β ↦ maxRenyiLeakage κ β) atTop (𝓝 (localDP κ)) := by
  have h : ∀ β, maxRenyiLeakage κ β = ENNReal.log (maxRenyiLeakageSum κ β ^ β⁻¹) := fun β ↦ by
    rw [maxRenyiLeakage, ENNReal.log_rpow]
  simp_rw [h, localDP]
  refine (ENNReal.continuous_log.tendsto _).comp (tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩)
  · obtain ⟨x, ha⟩ := lt_iSup_iff.1 ha
    obtain ⟨x', ha⟩ := lt_iSup_iff.1 ha
    obtain ⟨y, ha⟩ := lt_iSup_iff.1 ha
    exact eventually_lt_maxRenyiLeakageSum_rpow_inv x x' y ha fun _ _ ↦ measure_ne_top _ _
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    exact (maxRenyiLeakageSum_rpow_inv_le hβ).trans_lt ha

/-- MαbeL recovers **maximal leakage** at `(α, β) = (∞, 1)` (Proposition 1 and Figure 1a):
`L_{α,1}(X → Y) → L(X → Y)` as `α → ∞`, for any input distribution of full support. -/
theorem tendsto_alphaBetaLeakage_one_atTop [Nonempty 𝒳] {μ : Measure 𝒳}
    (hμ : ∀ x, μ {x} ≠ 0) :
    Tendsto (fun α ↦ alphaBetaLeakage κ α 1) atTop (𝓝 (maxLeakage μ κ : EReal)) := by
  rw [← maxRenyiLeakage_one hμ]
  exact tendsto_alphaBetaLeakage_atTop le_rfl

/-- **Proposition 1** (third item): MαbeL recovers **local differential privacy** at
`(α, β) = (∞, ∞)`, defined as the iterated limit `lim_{β → ∞} lim_{α → ∞} L_{α,β}(X → Y)`. -/
theorem tendsto_limUnder_alphaBetaLeakage_atTop [Nonempty 𝒳] :
    Tendsto (fun β ↦ limUnder atTop fun α ↦ alphaBetaLeakage κ α β) atTop
      (𝓝 (localDP κ)) := by
  refine tendsto_maxRenyiLeakage_atTop.congr' ((eventually_ge_atTop 1).mono fun β hβ ↦ ?_)
  exact (tendsto_alphaBetaLeakage_atTop hβ).limUnder_eq.symm

/-! ### Data processing inequalities -/

section DataProcessing

variable {m𝒵 : MeasurableSpace 𝒵} [Fintype 𝒵] [MeasurableSingletonClass 𝒵]

omit [Fintype 𝒳] [IsMarkovKernel κ] [Fintype 𝒵] in
private lemma comp_apply_singleton_eq_sum (η : Kernel 𝒴 𝒵) (κ : Kernel 𝒳 𝒴) (x : 𝒳) (z : 𝒵) :
    (η ∘ₖ κ) x {z} = ∑ y, η y {z} * κ x {y} := by
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton z), lintegral_fintype]

/-- Post-processing inequality for a fixed reference input and input distribution. -/
lemma alphaBetaTerm_comp_le (hα : 1 ≤ α) (hβ : 1 ≤ β) (η : Kernel 𝒴 𝒵) [IsMarkovKernel η]
    (x' : 𝒳) (p : PMF 𝒳) :
    alphaBetaTerm (η ∘ₖ κ) α β x' p ≤ alphaBetaTerm κ α β x' p := by
  have hα₀ : 0 < α := by linarith
  set g : 𝒴 → ℝ≥0∞ := fun y ↦ (∑ x, p x * κ x {y} ^ α) ^ (1 / α)
  have hmink (z : 𝒵) :
      (∑ x, p x * ((η ∘ₖ κ) x {z}) ^ α) ^ (1 / α) ≤ ∑ y, η y {z} * g y := by
    have h := ENNReal.rpow_sum_sum_rpow_le Finset.univ Finset.univ
      (fun x y ↦ p x ^ (1 / α) * (η y {z} * κ x {y})) hα
    simp_rw [← Finset.mul_sum, ENNReal.rpow_one_div_mul_rpow hα₀,
      ← comp_apply_singleton_eq_sum] at h
    refine h.trans_eq (Finset.sum_congr rfl fun y _ ↦ ?_)
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hα₀.le, mul_left_comm (p _), ← Finset.mul_sum]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
      mul_one_div_cancel hα₀.ne', ENNReal.rpow_one]
  rw [alphaBetaTerm_eq, alphaBetaTerm_eq]
  calc ∑ z, (η ∘ₖ κ) x' {z} ^ (1 - β) * ((∑ x, p x * (η ∘ₖ κ) x {z} ^ α) ^ (1 / α)) ^ β
      ≤ ∑ z, (η ∘ₖ κ) x' {z} ^ (1 - β) * (∑ y, η y {z} * g y) ^ β :=
        Finset.sum_le_sum fun z _ ↦
          mul_le_mul_right (ENNReal.rpow_le_rpow (hmink z) (by linarith)) _
    _ ≤ ∑ z, ∑ y, η y {z} * (κ x' {y} ^ (1 - β) * g y ^ β) := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        rw [comp_apply_singleton_eq_sum]
        exact ENNReal.rpow_sum_mul_rpow_sum_le _ (fun _ _ ↦ measure_ne_top _ _)
          (fun _ _ ↦ measure_ne_top _ _) hβ
    _ = ∑ y, κ x' {y} ^ (1 - β) * g y ^ β := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]

/-- **Data processing inequality** (Theorem 2(2), eq. (16a)), multiplicative form: for a
Markov chain `X - Y - Z` obtained by post-processing `Y` with `η`, the multiplicative form of
maximal `(α, β)`-leakage does not increase. -/
lemma alphaBetaLeakageSum_comp_le (hα : 1 ≤ α) (hβ : 1 ≤ β) (η : Kernel 𝒴 𝒵)
    [IsMarkovKernel η] :
    alphaBetaLeakageSum (η ∘ₖ κ) α β ≤ alphaBetaLeakageSum κ α β :=
  iSup₂_mono fun x' p ↦ alphaBetaTerm_comp_le hα hβ η x' p

/-- **Data processing inequality** (Theorem 2(2), eq. (16a)): for a Markov chain `X - Y - Z`
obtained by post-processing `Y` with `η`, `L_{α,β}(X → Z) ≤ L_{α,β}(X → Y)`. -/
theorem alphaBetaLeakage_comp_le (hα : 1 < α) (hβ : 1 ≤ β) (η : Kernel 𝒴 𝒵)
    [IsMarkovKernel η] :
    alphaBetaLeakage (η ∘ₖ κ) α β ≤ alphaBetaLeakage κ α β := by
  refine mul_le_mul_of_nonneg_left (ENNReal.log_le_log ?_) (EReal.coe_nonneg.2 (by positivity))
  exact alphaBetaLeakageSum_comp_le hα.le hβ η

omit [Fintype 𝒳] in
private lemma sum_sum_mul_kernel_apply_singleton (p : PMF 𝒳) [Fintype 𝒳] :
    ∑ y, ∑ x, p x * κ x {y} = 1 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
  exact sum_pmf_eq_one p

/-- Pre-processing inequality for a fixed reference input and input distribution: the term of
the composite channel is dominated through the output law `q = ∑_x p(x) κ(· | x)`. -/
lemma alphaBetaTerm_comp_le_alphaBetaLeakageSum (hα : 1 ≤ α) (hβ : 1 ≤ β) (η : Kernel 𝒴 𝒵)
    [IsMarkovKernel η] (x' : 𝒳) (p : PMF 𝒳) :
    alphaBetaTerm (η ∘ₖ κ) α β x' p ≤ alphaBetaLeakageSum η α β := by
  set q := PMF.ofFintype (fun y ↦ ∑ x, p x * κ x {y}) (sum_sum_mul_kernel_apply_singleton p)
  have hκ (x : 𝒳) : ∑ y, κ x {y} = 1 := by
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
  have h1 (z : 𝒵) : (η ∘ₖ κ) x' {z} ^ (1 - β) ≤ ∑ y, κ x' {y} * η y {z} ^ (1 - β) := by
    have := ENNReal.rpow_sum_mul_rpow_sum_le Finset.univ (c := fun y ↦ κ x' {y})
      (w := fun y ↦ η y {z}) (g := fun _ ↦ 1) (fun _ _ ↦ measure_ne_top _ _)
      (fun _ _ ↦ measure_ne_top _ _) hβ
    simp only [mul_one, ENNReal.one_rpow, hκ] at this
    rw [comp_apply_singleton_eq_sum]
    simpa only [mul_comm (η _ _)] using this
  have h2 (z : 𝒵) : ∑ x, p x * (η ∘ₖ κ) x {z} ^ α ≤ ∑ y, q y * η y {z} ^ α := by
    calc ∑ x, p x * (η ∘ₖ κ) x {z} ^ α ≤ ∑ x, p x * ∑ y, κ x {y} * η y {z} ^ α := by
          gcongr with x
          rw [comp_apply_singleton_eq_sum]
          simp_rw [mul_comm (η _ _)]
          exact ENNReal.rpow_arith_mean_le_arith_mean_rpow _ _ _ (hκ x) hα
      _ = ∑ y, q y * η y {z} ^ α := by
          simp_rw [Finset.mul_sum, q, PMF.ofFintype_apply, Finset.sum_mul]
          rw [Finset.sum_comm]
          simp_rw [mul_assoc]
  calc alphaBetaTerm (η ∘ₖ κ) α β x' p
      ≤ ∑ z, (∑ y, κ x' {y} * η y {z} ^ (1 - β)) * (∑ y, q y * η y {z} ^ α) ^ (β / α) :=
        Finset.sum_le_sum fun z _ ↦
          mul_le_mul' (h1 z) (ENNReal.rpow_le_rpow (h2 z) (div_nonneg (by linarith) (by linarith)))
    _ = ∑ y, κ x' {y} * alphaBetaTerm η α β y q := by
        simp_rw [alphaBetaTerm, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc]
    _ ≤ ∑ y, κ x' {y} * alphaBetaLeakageSum η α β := by
        gcongr with y
        exact le_iSup₂ (f := fun y q ↦ alphaBetaTerm η α β y q) y q
    _ = alphaBetaLeakageSum η α β := by rw [← Finset.sum_mul, hκ, one_mul]

/-- **Data processing inequality** (Theorem 2(2), eq. (16b), the linkage inequality),
multiplicative form: for a Markov chain `X - Y - Z`, the leakage from `X` to `Z` is at most the
leakage from `Y` to `Z`. -/
lemma alphaBetaLeakageSum_comp_le_right (hα : 1 ≤ α) (hβ : 1 ≤ β) (η : Kernel 𝒴 𝒵)
    [IsMarkovKernel η] :
    alphaBetaLeakageSum (η ∘ₖ κ) α β ≤ alphaBetaLeakageSum η α β :=
  iSup₂_le fun x' p ↦ alphaBetaTerm_comp_le_alphaBetaLeakageSum hα hβ η x' p

/-- **Data processing inequality** (Theorem 2(2), eq. (16b), the linkage inequality): for a
Markov chain `X - Y - Z`, `L_{α,β}(X → Z) ≤ L_{α,β}(Y → Z)`. -/
theorem alphaBetaLeakage_comp_le_right (hα : 1 < α) (hβ : 1 ≤ β) (η : Kernel 𝒴 𝒵)
    [IsMarkovKernel η] :
    alphaBetaLeakage (η ∘ₖ κ) α β ≤ alphaBetaLeakage η α β := by
  refine mul_le_mul_of_nonneg_left (ENNReal.log_le_log ?_) (EReal.coe_nonneg.2 (by positivity))
  exact alphaBetaLeakageSum_comp_le_right hα.le hβ η

end DataProcessing

/-! ### Additivity over independent releases -/

section Additivity

variable {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : Type*} [Fintype 𝒳₁] [Fintype 𝒳₂] [Fintype 𝒴₁] [Fintype 𝒴₂]
  {m𝒳₁ : MeasurableSpace 𝒳₁} {m𝒳₂ : MeasurableSpace 𝒳₂} {m𝒴₁ : MeasurableSpace 𝒴₁}
  {m𝒴₂ : MeasurableSpace 𝒴₂} [MeasurableSingletonClass 𝒴₁] [MeasurableSingletonClass 𝒴₂]
  {κ₁ : Kernel 𝒳₁ 𝒴₁} {κ₂ : Kernel 𝒳₂ 𝒴₂} [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]

omit [Fintype 𝒳₁] [Fintype 𝒳₂] [Fintype 𝒴₁] [Fintype 𝒴₂] [MeasurableSingletonClass 𝒴₁]
  [MeasurableSingletonClass 𝒴₂] in
private lemma parallelComp_apply_singleton (x₁ : 𝒳₁) (x₂ : 𝒳₂) (y₁ : 𝒴₁) (y₂ : 𝒴₂) :
    (κ₁ ∥ₖ κ₂) (x₁, x₂) {(y₁, y₂)} = κ₁ x₁ {y₁} * κ₂ x₂ {y₂} := by
  rw [← Set.singleton_prod_singleton, Kernel.parallelComp_apply_prod]

omit [MeasurableSingletonClass 𝒴₁] [MeasurableSingletonClass 𝒴₂] in
/-- Product inputs and product reference points give the lower bound in Theorem 2(4). -/
lemma mul_le_alphaBetaLeakageSum_parallelComp (hα : 0 < α) (hβ : 0 ≤ β) :
    alphaBetaLeakageSum κ₁ α β * alphaBetaLeakageSum κ₂ α β ≤
      alphaBetaLeakageSum (κ₁ ∥ₖ κ₂) α β := by
  simp_rw [alphaBetaLeakageSum, ENNReal.iSup_mul, ENNReal.mul_iSup]
  refine iSup₂_le fun x₁ p₁ ↦ iSup₂_le fun x₂ p₂ ↦ ?_
  have hp : ∑ x : 𝒳₁ × 𝒳₂, p₁ x.1 * p₂ x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, sum_pmf_eq_one, mul_one]
    exact sum_pmf_eq_one p₁
  refine le_iSup₂_of_le (f := fun x' p ↦ alphaBetaTerm (κ₁ ∥ₖ κ₂) α β x' p) (x₁, x₂)
    (PMF.ofFintype _ hp) (le_of_eq ?_)
  simp only [alphaBetaTerm, Fintype.sum_prod_type, parallelComp_apply_singleton,
    PMF.ofFintype_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y₁ _ ↦ Finset.sum_congr rfl fun y₂ _ ↦ ?_
  have h : ∑ x₁, ∑ x₂, p₁ x₁ * p₂ x₂ * (κ₁ x₁ {y₁} * κ₂ x₂ {y₂}) ^ α =
      (∑ x₁, p₁ x₁ * κ₁ x₁ {y₁} ^ α) * ∑ x₂, p₂ x₂ * κ₂ x₂ {y₂} ^ α := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x₁ _ ↦ Finset.sum_congr rfl fun x₂ _ ↦ ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le]
    ring
  rw [h, ENNReal.mul_rpow_of_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg hβ hα.le)]
  ring

omit [MeasurableSingletonClass 𝒴₁] [MeasurableSingletonClass 𝒴₂] in
/-- The upper bound in Theorem 2(4), for a fixed reference input and a fixed (possibly
correlated) joint input distribution; this is the argument of eqs. (117)–(123). -/
lemma alphaBetaTerm_parallelComp_le (hα : 0 < α) (hβ : 0 < β) (x₁' : 𝒳₁) (x₂' : 𝒳₂)
    (p : PMF (𝒳₁ × 𝒳₂)) :
    alphaBetaTerm (κ₁ ∥ₖ κ₂) α β (x₁', x₂') p ≤
      alphaBetaLeakageSum κ₁ α β * alphaBetaLeakageSum κ₂ α β := by
  have hβα : 0 < β / α := div_pos hβ hα
  have hp₁ : ∑ x₁, ∑ x₂, p (x₁, x₂) = 1 := by
    rw [← Fintype.sum_prod_type']
    exact sum_pmf_eq_one p
  set p₁ := PMF.ofFintype (fun x₁ ↦ ∑ x₂, p (x₁, x₂)) hp₁
  set k : 𝒴₁ → ℝ≥0∞ := fun y₁ ↦ ∑ x₁, p₁ x₁ * κ₁ x₁ {y₁} ^ α with hk_def
  set r : 𝒴₁ → 𝒳₂ → ℝ≥0∞ := fun y₁ x₂ ↦ ∑ x₁, p (x₁, x₂) * κ₁ x₁ {y₁} ^ α with hr_def
  have hrk (y₁ : 𝒴₁) : ∑ x₂, r y₁ x₂ = k y₁ := by
    simp only [r, k, p₁, PMF.ofFintype_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hk_top (y₁ : 𝒴₁) : k y₁ ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc k y₁ ≤ ∑ x₁, p₁ x₁ * 1 := by
          simp only [k]
          gcongr with x₁
          exact ENNReal.rpow_le_one prob_le_one hα.le
      _ = 1 := by simp_rw [mul_one]; exact sum_pmf_eq_one p₁
  have hinner (y₁ : 𝒴₁) (y₂ : 𝒴₂) :
      ∑ x : 𝒳₁ × 𝒳₂, p x * (κ₁ ∥ₖ κ₂) x {(y₁, y₂)} ^ α = ∑ x₂, r y₁ x₂ * κ₂ x₂ {y₂} ^ α := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x₂ _ ↦ ?_
    simp_rw [r, Finset.sum_mul, parallelComp_apply_singleton,
      ENNReal.mul_rpow_of_nonneg _ _ hα.le, mul_assoc]
  have hstep (y₁ : 𝒴₁) :
      ∑ y₂, κ₂ x₂' {y₂} ^ (1 - β) * (∑ x₂, r y₁ x₂ * κ₂ x₂ {y₂} ^ α) ^ (β / α) ≤
        k y₁ ^ (β / α) * alphaBetaLeakageSum κ₂ α β := by
    rcases eq_or_ne (k y₁) 0 with hk | hk
    · have h0 : ∀ x₂, r y₁ x₂ = 0 := fun x₂ ↦ by
        rw [← hrk, Finset.sum_eq_zero_iff] at hk
        exact hk x₂ (Finset.mem_univ _)
      simp [h0, ENNReal.zero_rpow_of_pos hβα]
    · have hq : ∑ x₂, r y₁ x₂ / k y₁ = 1 := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, hrk, ENNReal.mul_inv_cancel hk (hk_top y₁)]
      calc ∑ y₂, κ₂ x₂' {y₂} ^ (1 - β) * (∑ x₂, r y₁ x₂ * κ₂ x₂ {y₂} ^ α) ^ (β / α)
          = k y₁ ^ (β / α) * alphaBetaTerm κ₂ α β x₂' (PMF.ofFintype _ hq) := by
            rw [alphaBetaTerm, Finset.mul_sum]
            refine Finset.sum_congr rfl fun y₂ _ ↦ ?_
            have : ∑ x₂, r y₁ x₂ * κ₂ x₂ {y₂} ^ α =
                k y₁ * ∑ x₂, PMF.ofFintype _ hq x₂ * κ₂ x₂ {y₂} ^ α := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x₂ _ ↦ ?_
              rw [PMF.ofFintype_apply, ← mul_assoc, ENNReal.mul_div_cancel hk (hk_top y₁)]
            rw [this, ENNReal.mul_rpow_of_nonneg _ _ hβα.le]
            ring
        _ ≤ k y₁ ^ (β / α) * alphaBetaLeakageSum κ₂ α β := by
            gcongr
            exact le_iSup₂ (f := fun x' p ↦ alphaBetaTerm κ₂ α β x' p) x₂' _
  calc alphaBetaTerm (κ₁ ∥ₖ κ₂) α β (x₁', x₂') p
      = ∑ y₁, κ₁ x₁' {y₁} ^ (1 - β) *
          ∑ y₂, κ₂ x₂' {y₂} ^ (1 - β) * (∑ x₂, r y₁ x₂ * κ₂ x₂ {y₂} ^ α) ^ (β / α) := by
        rw [alphaBetaTerm, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun y₁ _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y₂ _ ↦ ?_
        rw [parallelComp_apply_singleton, hinner,
          ENNReal.mul_rpow_of_ne_top (measure_ne_top _ _) (measure_ne_top _ _), mul_assoc]
    _ ≤ ∑ y₁, κ₁ x₁' {y₁} ^ (1 - β) * (k y₁ ^ (β / α) * alphaBetaLeakageSum κ₂ α β) := by
        gcongr with y₁
        exact hstep y₁
    _ = alphaBetaTerm κ₁ α β x₁' p₁ * alphaBetaLeakageSum κ₂ α β := by
        rw [alphaBetaTerm, Finset.sum_mul]
        simp_rw [mul_assoc, k]
    _ ≤ alphaBetaLeakageSum κ₁ α β * alphaBetaLeakageSum κ₂ α β := by
        gcongr
        exact le_iSup₂ (f := fun x' p ↦ alphaBetaTerm κ₁ α β x' p) x₁' p₁

omit [MeasurableSingletonClass 𝒴₁] [MeasurableSingletonClass 𝒴₂] in
/-- **Additivity** (Theorem 2(4), case `n = 2`), multiplicative form: for independent pairs
`(X₁, Y₁)` and `(X₂, Y₂)`, released through the parallel channel `κ₁ ∥ₖ κ₂`, the multiplicative
form of maximal `(α, β)`-leakage is multiplicative. -/
theorem alphaBetaLeakageSum_parallelComp (hα : 0 < α) (hβ : 0 < β) :
    alphaBetaLeakageSum (κ₁ ∥ₖ κ₂) α β =
      alphaBetaLeakageSum κ₁ α β * alphaBetaLeakageSum κ₂ α β :=
  le_antisymm (iSup₂_le fun x' p ↦ alphaBetaTerm_parallelComp_le hα hβ x'.1 x'.2 p)
    (mul_le_alphaBetaLeakageSum_parallelComp hα hβ.le)

/-- **Additivity** (Theorem 2(4), case `n = 2`, from which eq. (18) follows by induction): for
independent pairs `(X₁, Y₁)` and `(X₂, Y₂)`,
`L_{α,β}((X₁, X₂) → (Y₁, Y₂)) = L_{α,β}(X₁ → Y₁) + L_{α,β}(X₂ → Y₂)`. -/
theorem alphaBetaLeakage_parallelComp [Nonempty 𝒳₁] [Nonempty 𝒳₂] (hα : 0 < α) (hβ : 0 < β) :
    alphaBetaLeakage (κ₁ ∥ₖ κ₂) α β = alphaBetaLeakage κ₁ α β + alphaBetaLeakage κ₂ α β := by
  rw [alphaBetaLeakage, alphaBetaLeakageSum_parallelComp hα hβ, ENNReal.log_mul_add,
    EReal.left_distrib_of_nonneg
      (ENNReal.zero_le_log_iff.2 (one_le_alphaBetaLeakageSum hα.ne' hβ))
      (ENNReal.zero_le_log_iff.2 (one_le_alphaBetaLeakageSum hα.ne' hβ)),
    alphaBetaLeakage, alphaBetaLeakage]

end Additivity

end InformationTheory
