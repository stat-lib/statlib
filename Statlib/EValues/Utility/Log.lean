/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Statlib.EValues.Utility.Basic

/-!
# Logarithmic utility

## Main definitions

* `logUtility`: The logarithmic utility function.
* `harmonicTrunc`: The harmonic truncation `harmonicTrunc n x = n x / (n + x)`.
* `boundedLogUtility`: Bounded approximations `x ↦ log (N x / (N + x))` of the logarithmic
  utility function, and `harmonicDeriv`, their derivative in `ℝ≥0∞` form.

## Main statements

* `deriv_logUtility`: The derivative of the logarithmic utility function.
* `deriv_boundedLogUtility`: The derivative of `boundedLogUtility`, in `ℝ≥0∞` form.

-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {U : ℝ≥0∞ → EReal}

section Log

/-- The logarithmic utility function. -/
noncomputable def logUtility : Utility where
  toFun := ENNReal.log
  eq_coe' := by
    intros x hx0 hx_top
    simp [ENNReal.log_eq_bot_iff, ENNReal.log_eq_top_iff, hx0, hx_top]
  monotone' := ENNReal.log_monotone
  continuous' := ENNReal.continuous_log
  concave' := ConcaveOn_log
  differentiable' := by
    have h_eq x (hx : 0 < x) : (ENNReal.log (ENNReal.ofReal x)).toReal = Real.log x := by
      simp [ENNReal.log_ofReal, not_le.mpr hx]
    have h_diff : ContDiffOn ℝ 1 Real.log (Set.Ioi 0) :=
      analyticOn_log.contDiffOn (uniqueDiffOn_Ioi 0)
    exact ContDiffOn.congr h_diff h_eq

@[simp]
lemma logUtility_zero : logUtility 0 = ⊥ := by simp [logUtility]

@[simp]
lemma logUtility_top : logUtility ∞ = ⊤ := by simp [logUtility]

@[simp]
lemma real_logUtility {x : ℝ} (hx : 0 < x) :
    logUtility.real x = Real.log x := by
  simp [logUtility, Utility.real, ENNReal.log_ofReal, not_le.mpr hx]

lemma deriv_real_logUtility {x : ℝ} (hx : 0 < x) :
    deriv logUtility.real x = x⁻¹ := by
  rw [← Real.deriv_log]
  refine EventuallyEq.deriv_eq ?_
  have h_ev_pos : ∀ᶠ y in 𝓝 x, 0 < y := eventually_gt_nhds hx
  filter_upwards [h_ev_pos] with y hy using real_logUtility hy

lemma deriv_logUtility (x : ℝ≥0∞) :
    logUtility.deriv x = if x = 0 then ⊤ else 1 / x := by
  by_cases hx0 : x = 0
  · simp only [hx0, ↓reduceIte, EReal.coe_ennreal_top]
    simp only [Utility.deriv, ↓reduceIte]
    refine Tendsto.limsup_eq ?_
    simp only [EReal.tendsto_coe_nhds_top_iff]
    have h_toReal_pos : ∀ᶠ (x : ℝ≥0∞) in 𝓝[>] 0, 0 < x.toReal := by
      have h_ne_top : ∀ᶠ x in 𝓝[>] 0, x ≠ ∞ := eventually_ne_nhdsWithin (by simp)
      have h_pos : ∀ᶠ x in 𝓝[>] (0 : ℝ≥0∞), 0 < x := eventually_nhdsWithin_of_forall fun x hx ↦ hx
      filter_upwards [h_ne_top, h_pos] with x hx_ne_top hx_pos
      simp [ENNReal.toReal_pos_iff, hx_pos, hx_ne_top.lt_top]
    suffices Tendsto (fun x : ℝ≥0∞ ↦ x.toReal⁻¹) (𝓝[>] 0) atTop by
      refine this.congr' ?_
      filter_upwards [h_toReal_pos] with x hx_pos
      simp [deriv_real_logUtility hx_pos]
    refine tendsto_inv_nhdsGT_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]
    constructor
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      refine ContinuousAt.tendsto ?_
      exact ENNReal.continuousAt_toReal (by simp)
    · simpa
  by_cases hx_top : x = ∞
  · simp only [hx_top, ENNReal.top_ne_zero, ↓reduceIte, one_div, ENNReal.inv_top,
      EReal.coe_ennreal_zero]
    simp only [Utility.deriv, ENNReal.top_ne_zero, ↓reduceIte]
    refine Tendsto.limsup_eq ?_
    have : (0 : EReal) = (0 : ℝ) := rfl
    rw [this]
    rw [EReal.tendsto_coe]
    have h_toReal_pos : ∀ᶠ (x : ℝ≥0∞) in 𝓝[<] ∞, 0 < x.toReal := by
      have h_ne_top : ∀ᶠ x in 𝓝[<] ∞, x ≠ ∞ := eventually_nhdsWithin_of_forall fun x hx ↦ by
        simp only [Set.mem_Iio] at hx; exact hx.ne
      have h_pos : ∀ᶠ x in 𝓝[<] ∞, 0 < x := by
        simp only [pos_iff_ne_zero, ne_eq]
        exact eventually_ne_nhdsWithin (by simp)
      filter_upwards [h_ne_top, h_pos] with x hx_ne_top hx_pos
      simp [ENNReal.toReal_pos_iff, hx_pos, hx_ne_top.lt_top]
    suffices Tendsto (fun x : ℝ≥0∞ ↦ x.toReal⁻¹) (𝓝[<] ∞) (𝓝 0) by
      refine this.congr' ?_
      filter_upwards [h_toReal_pos] with x hx_pos
      simp [deriv_real_logUtility hx_pos]
    suffices h_tendsto_toReal : Tendsto (fun x : ℝ≥0∞ ↦ x.toReal) (𝓝[<] ∞) atTop from
      tendsto_inv_atTop_zero.comp h_tendsto_toReal
    exact ENNReal.tendsto_toReal_atTop
  simp only [Utility.deriv, hx0, ↓reduceIte, hx_top, one_div]
  have hx_pos : 0 < x.toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨Ne.bot_lt hx0, Ne.lt_top hx_top⟩
  suffices deriv logUtility.real x.toReal = 1 / x.toReal by
    simp only [this, one_div]
    rw [← ENNReal.toReal_inv, EReal.coe_ennreal_toReal]
    simpa
  simp [deriv_real_logUtility hx_pos]

lemma deriv_logUtility_eq_ennreal (x : ℝ≥0∞) :
    logUtility.deriv x = (1 / x : ℝ≥0∞) := by
  by_cases hx0 : x = 0 <;> simp [deriv_logUtility, hx0]

end Log

section BoundedLog

/-! ### Bounded approximations of the logarithmic utility

We introduce the bounded approximations `x ↦ log (n x / (n + x))` of the logarithm, obtained by
composing the logarithm with the *harmonic truncation* `harmonicTrunc n x = (x⁻¹ + n⁻¹)⁻¹`. -/

/-- The harmonic truncation `harmonicTrunc n x = n x / (n + x)`, written in a form that behaves
well at `0` and `∞`. It is concave, increasing, bounded above by `n`, and converges to `x` as
`n → ∞`. -/
noncomputable def harmonicTrunc (n x : ℝ≥0∞) : ℝ≥0∞ := (x⁻¹ + n⁻¹)⁻¹

@[simp]
lemma harmonicTrunc_zero (n : ℝ≥0∞) : harmonicTrunc n 0 = 0 := by simp [harmonicTrunc]

@[simp]
lemma harmonicTrunc_top (n : ℝ≥0∞) : harmonicTrunc n ∞ = n := by
  simp [harmonicTrunc]

lemma harmonicTrunc_le_left (n x : ℝ≥0∞) : harmonicTrunc n x ≤ x := by
  conv_rhs => rw [← inv_inv x]
  exact ENNReal.inv_le_inv.mpr le_self_add

lemma harmonicTrunc_le_right (n x : ℝ≥0∞) : harmonicTrunc n x ≤ n := by
  conv_rhs => rw [← inv_inv n]
  exact ENNReal.inv_le_inv.mpr le_add_self

lemma harmonicTrunc_ne_zero {n x : ℝ≥0∞} (hn0 : n ≠ 0) (hx0 : x ≠ 0) : harmonicTrunc n x ≠ 0 := by
  simp only [harmonicTrunc, ne_eq, ENNReal.inv_eq_zero, ENNReal.add_eq_top, ENNReal.inv_eq_top,
    not_or]
  exact ⟨hx0, hn0⟩

lemma harmonicTrunc_ne_top {n : ℝ≥0∞} (hn_top : n ≠ ∞) (x : ℝ≥0∞) : harmonicTrunc n x ≠ ∞ :=
  fun h ↦ (harmonicTrunc_le_right n x).trans_lt (Ne.lt_top hn_top) |>.ne h

lemma monotone_harmonicTrunc (n : ℝ≥0∞) : Monotone (harmonicTrunc n) := by
  intro x y hxy
  simp only [harmonicTrunc]
  gcongr

@[fun_prop]
lemma continuous_harmonicTrunc (n : ℝ≥0∞) : Continuous (harmonicTrunc n) := by
  unfold harmonicTrunc
  fun_prop

/-- The harmonic truncation of a real number, computed in `ℝ`. -/
lemma harmonicTrunc_ofReal {N x : ℝ} (hN : 0 < N) (hx : 0 < x) :
    harmonicTrunc (.ofReal N) (.ofReal x) = .ofReal ((x⁻¹ + N⁻¹)⁻¹) := by
  rw [harmonicTrunc, ← ENNReal.ofReal_inv_of_pos hx, ← ENNReal.ofReal_inv_of_pos hN,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_inv_of_pos (by positivity)]

lemma toReal_harmonicTrunc {n x : ℝ≥0∞} (hn0 : n ≠ 0) (hx0 : x ≠ 0) :
    (harmonicTrunc n x).toReal = (x.toReal⁻¹ + n.toReal⁻¹)⁻¹ := by
  rw [harmonicTrunc, ENNReal.toReal_inv, ENNReal.toReal_add (by simp [hx0]) (by simp [hn0]),
    ENNReal.toReal_inv, ENNReal.toReal_inv]

/-- `harmonicTrunc n` is the pointwise infimum of the affine maps `w ↦ s ^ 2 * w + t ^ 2 * n`
over `s + t = 1`: this is one half of that statement. -/
lemma harmonicTrunc_le_sq_add {n : ℝ≥0∞} (hn0 : n ≠ 0) (hn_top : n ≠ ∞) (w : ℝ≥0∞)
    {s t : ℝ≥0∞} (hst : s + t = 1) :
    harmonicTrunc n w ≤ s ^ 2 * w + t ^ 2 * n := by
  have hs_top : s ≠ ∞ := fun h ↦ by simp [h] at hst
  have ht_top : t ≠ ∞ := fun h ↦ by simp [h] at hst
  by_cases hw0 : w = 0
  · simp [hw0]
  by_cases hw_top : w = ∞
  · subst hw_top
    rw [harmonicTrunc_top]
    by_cases hs0 : s = 0
    · rw [hs0] at hst ⊢
      rw [zero_add] at hst
      simp [hst]
    · rw [ENNReal.mul_top (by simp [hs0])]
      simp
  have hsum_ne_top : s ^ 2 * w + t ^ 2 * n ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp [hs_top]) hw_top,
      ENNReal.mul_ne_top (by simp [ht_top]) hn_top⟩
  refine (ENNReal.toReal_le_toReal (harmonicTrunc_ne_top hn_top w) hsum_ne_top).mp ?_
  have hw_pos : 0 < w.toReal := ENNReal.toReal_pos hw0 hw_top
  have hn_pos : 0 < n.toReal := ENNReal.toReal_pos hn0 hn_top
  have hst' : s.toReal + t.toReal = 1 := by
    rw [← ENNReal.toReal_add hs_top ht_top, hst, ENNReal.toReal_one]
  rw [toReal_harmonicTrunc hn0 hw0, ENNReal.toReal_add
      (ENNReal.mul_ne_top (by simp [hs_top]) hw_top) (ENNReal.mul_ne_top (by simp [ht_top]) hn_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
  have h_eq : (w.toReal⁻¹ + n.toReal⁻¹)⁻¹ = w.toReal * n.toReal / (w.toReal + n.toReal) := by
    field_simp
    ring
  rw [h_eq, div_le_iff₀ (by positivity)]
  have ht_eq : t.toReal = 1 - s.toReal := by linarith
  have key : (s.toReal ^ 2 * w.toReal + t.toReal ^ 2 * n.toReal) * (w.toReal + n.toReal)
      - w.toReal * n.toReal = (s.toReal * w.toReal - t.toReal * n.toReal) ^ 2 := by
    rw [ht_eq]; ring
  linarith [sq_nonneg (s.toReal * w.toReal - t.toReal * n.toReal), key]

/-- The infimum in `harmonicTrunc_le_sq_add` is attained. -/
lemma exists_sq_add_le_harmonicTrunc {n : ℝ≥0∞} (hn0 : n ≠ 0) (hn_top : n ≠ ∞) (z : ℝ≥0∞) :
    ∃ s t : ℝ≥0∞, s + t = 1 ∧ s ^ 2 * z + t ^ 2 * n ≤ harmonicTrunc n z := by
  by_cases hz0 : z = 0
  · exact ⟨1, 0, by simp, by simp [hz0]⟩
  by_cases hz_top : z = ∞
  · exact ⟨0, 1, by simp, by simp [hz_top]⟩
  have hzn : z + n ≠ 0 := by simp [hz0]
  have hzn_top : z + n ≠ ∞ := by simp [hz_top, hn_top]
  refine ⟨n / (z + n), z / (z + n), ?_, ?_⟩
  · rw [ENNReal.div_add_div_same, add_comm n z, ENNReal.div_self hzn hzn_top]
  refine (ENNReal.toReal_le_toReal ?_ (harmonicTrunc_ne_top hn_top z)).mp ?_
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp [ENNReal.div_eq_top, hzn, hn_top]) hz_top,
        ENNReal.mul_ne_top (by simp [ENNReal.div_eq_top, hzn, hz_top]) hn_top⟩
  have hz_pos : 0 < z.toReal := ENNReal.toReal_pos hz0 hz_top
  have hn_pos : 0 < n.toReal := ENNReal.toReal_pos hn0 hn_top
  have hzn_pos : 0 < z.toReal + n.toReal := by positivity
  rw [toReal_harmonicTrunc hn0 hz0, ENNReal.toReal_add
      (ENNReal.mul_ne_top (by simp [ENNReal.div_eq_top, hzn, hn_top]) hz_top)
      (ENNReal.mul_ne_top (by simp [ENNReal.div_eq_top, hzn, hz_top]) hn_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_add hz_top hn_top]
  have h_eq : (z.toReal⁻¹ + n.toReal⁻¹)⁻¹ = z.toReal * n.toReal / (z.toReal + n.toReal) := by
    field_simp
    ring
  rw [h_eq]
  refine le_of_eq ?_
  field_simp
  ring

lemma concaveOn_harmonicTrunc {n : ℝ≥0∞} (hn0 : n ≠ 0) (hn_top : n ≠ ∞) :
    ConcaveOn ℝ≥0∞ Set.univ (harmonicTrunc n) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  obtain ⟨s, t, hst, hle⟩ := exists_sq_add_le_harmonicTrunc hn0 hn_top (a • x + b • y)
  refine le_trans ?_ hle
  simp only [smul_eq_mul]
  calc a * harmonicTrunc n x + b * harmonicTrunc n y
  _ ≤ a * (s ^ 2 * x + t ^ 2 * n) + b * (s ^ 2 * y + t ^ 2 * n) := by
    gcongr <;> exact harmonicTrunc_le_sq_add hn0 hn_top _ hst
  _ = s ^ 2 * (a * x + b * y) + (a + b) * (t ^ 2 * n) := by ring
  _ = s ^ 2 * (a * x + b * y) + t ^ 2 * n := by rw [hab, one_mul]

lemma concaveOn_log_harmonicTrunc' {n : ℝ≥0∞} (hn0 : n ≠ 0) (hn_top : n ≠ ∞) :
    ConcaveOn ℝ≥0∞ Set.univ (fun x ↦ ENNReal.log (harmonicTrunc n x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  calc a • ENNReal.log (harmonicTrunc n x) + b • ENNReal.log (harmonicTrunc n y)
  _ ≤ ENNReal.log (a • harmonicTrunc n x + b • harmonicTrunc n y) :=
    ConcaveOn_log'.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  _ ≤ ENNReal.log (harmonicTrunc n (a • x + b • y)) :=
    ENNReal.log_monotone ((concaveOn_harmonicTrunc hn0 hn_top).2
      (Set.mem_univ _) (Set.mem_univ _) ha hb hab)

lemma concaveOn_log_harmonicTrunc {n : ℝ≥0∞} (hn0 : n ≠ 0) (hn_top : n ≠ ∞) :
    ConcaveOn ℝ≥0 Set.univ (fun x ↦ ENNReal.log (harmonicTrunc n x)) := by
  refine ⟨convex_univ, fun x hx y hy a b ha hb hab ↦ ?_⟩
  obtain ⟨-, conv⟩ := concaveOn_log_harmonicTrunc' hn0 hn_top
  exact conv hx hy zero_le zero_le <| (ENNReal.toNNReal_eq_one_iff _).mp hab

/-- Bounded approximation of the logarithmic utility at level `N`:
`boundedLogUtility hN x = log (N x / (N + x))`. -/
noncomputable def boundedLogUtility {N : ℝ} (hN : 0 < N) : Utility where
  toFun x := ENNReal.log (harmonicTrunc (ENNReal.ofReal N) x)
  eq_coe' x hx0 _ := by
    refine ⟨?_, ?_⟩
    · simp only [ne_eq, ENNReal.log_eq_bot_iff]
      exact harmonicTrunc_ne_zero (by simp [hN]) hx0
    · simp only [ne_eq, ENNReal.log_eq_top_iff]
      exact harmonicTrunc_ne_top (by simp) x
  monotone' := ENNReal.log_monotone.comp (monotone_harmonicTrunc _)
  continuous' := ENNReal.continuous_log.comp (continuous_harmonicTrunc _)
  concave' := concaveOn_log_harmonicTrunc (by simp [hN]) (by simp)
  differentiable' := by
    have h_eq : ∀ x ∈ Set.Ioi (0 : ℝ),
        (ENNReal.log (harmonicTrunc (ENNReal.ofReal N) (ENNReal.ofReal x))).toReal
          = Real.log x + Real.log N - Real.log (x + N) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      rw [harmonicTrunc_ofReal hN hx, ENNReal.log_ofReal_of_pos (by positivity)]
      simp only [EReal.toReal_coe]
      rw [show (x⁻¹ + N⁻¹)⁻¹ = x * N / (x + N) by field_simp; ring,
        Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    refine ContDiffOn.congr ?_ h_eq
    intro x hx
    simp only [Set.mem_Ioi] at hx
    refine ContDiffAt.contDiffWithinAt (ContDiffAt.sub (ContDiffAt.add ?_ contDiffAt_const) ?_)
    · exact Real.contDiffAt_log.mpr hx.ne'
    · exact (Real.contDiffAt_log.mpr (by positivity)).comp x (contDiffAt_id.add contDiffAt_const)

lemma boundedLogUtility_apply {N : ℝ} (hN : 0 < N) (x : ℝ≥0∞) :
    boundedLogUtility hN x = ENNReal.log (harmonicTrunc (ENNReal.ofReal N) x) := rfl

lemma boundedLogUtility_le {N : ℝ} (hN : 0 < N) (x : ℝ≥0∞) :
    boundedLogUtility hN x ≤ (Real.log N : EReal) := by
  rw [boundedLogUtility_apply, ← ENNReal.log_ofReal_of_pos hN]
  exact ENNReal.log_monotone (harmonicTrunc_le_right _ x)

lemma boundedLogUtility_real {N : ℝ} (hN : 0 < N) {x : ℝ} (hx : 0 < x) :
    (boundedLogUtility hN).real x = Real.log x + Real.log N - Real.log (x + N) := by
  rw [Utility.real, boundedLogUtility_apply, harmonicTrunc_ofReal hN hx,
    ENNReal.log_ofReal_of_pos (by positivity)]
  simp only [EReal.toReal_coe]
  rw [show (x⁻¹ + N⁻¹)⁻¹ = x * N / (x + N) by field_simp; ring,
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]

lemma deriv_boundedLogUtility_real {N : ℝ} (hN : 0 < N) {x : ℝ} (hx : 0 < x) :
    deriv (boundedLogUtility hN).real x = x⁻¹ - (x + N)⁻¹ := by
  have h_ev : (boundedLogUtility hN).real
      =ᶠ[𝓝 x] fun y ↦ Real.log y + Real.log N - Real.log (y + N) := by
    filter_upwards [eventually_gt_nhds hx] with y hy using boundedLogUtility_real hN hy
  have hlog2 : HasDerivAt (fun y : ℝ ↦ Real.log (y + N)) ((x + N)⁻¹) x := by
    have h := (Real.hasDerivAt_log (x := x + N) (by positivity)).comp x
      ((hasDerivAt_id x).add_const N)
    simp at h
    simpa
  have h1 : HasDerivAt (fun y : ℝ ↦ Real.log y + Real.log N - Real.log (y + N))
      (x⁻¹ - (x + N)⁻¹) x := ((Real.hasDerivAt_log hx.ne').add_const (Real.log N)).sub hlog2
  rw [h_ev.deriv_eq, h1.deriv]

/-- The derivative of `boundedLogUtility hN`, as an `ℝ≥0∞`-valued function. -/
noncomputable def harmonicDeriv (N : ℝ) (y : ℝ≥0∞) : ℝ≥0∞ := y⁻¹ - (y + ENNReal.ofReal N)⁻¹

lemma harmonicDeriv_add_inv (N : ℝ) (y : ℝ≥0∞) :
    harmonicDeriv N y + (y + ENNReal.ofReal N)⁻¹ = y⁻¹ :=
  tsub_add_cancel_of_le (ENNReal.inv_le_inv.mpr le_self_add)

lemma inv_le_harmonicDeriv_add (N : ℝ) (y : ℝ≥0∞) :
    y⁻¹ ≤ harmonicDeriv N y + (ENNReal.ofReal N)⁻¹ := by
  rw [← harmonicDeriv_add_inv N y]
  gcongr
  exact le_add_self

@[simp]
lemma harmonicDeriv_top (N : ℝ) : harmonicDeriv N ∞ = 0 := by simp [harmonicDeriv]

lemma harmonicDeriv_le_inv (N : ℝ) (y : ℝ≥0∞) : harmonicDeriv N y ≤ y⁻¹ := tsub_le_self

lemma harmonicDeriv_mul_le_one (N : ℝ) (y : ℝ≥0∞) : harmonicDeriv N y * y ≤ 1 := by
  have h : harmonicDeriv N y * y ≤ y⁻¹ * y := by
    gcongr
    exact harmonicDeriv_le_inv N y
  refine h.trans ?_
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  rcases eq_or_ne y ∞ with rfl | hy_top
  · simp
  rw [ENNReal.inv_mul_cancel hy0 hy_top]

lemma harmonicDeriv_eq_top_iff {N : ℝ} (hN : 0 < N) {y : ℝ≥0∞} :
    harmonicDeriv N y = ∞ ↔ y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · rw [harmonicDeriv, h, ENNReal.inv_zero, ENNReal.sub_eq_top_iff]
    exact ⟨rfl, by simp [hN]⟩
  by_contra hy0
  rw [harmonicDeriv, ENNReal.sub_eq_top_iff] at h
  exact (ENNReal.inv_ne_top.mpr hy0) h.1

@[fun_prop]
lemma measurable_harmonicDeriv (N : ℝ) : Measurable (harmonicDeriv N) := by
  unfold harmonicDeriv
  fun_prop

lemma toReal_harmonicDeriv {N : ℝ} (hN : 0 < N) {y : ℝ≥0∞} (hy0 : y ≠ 0) (hy_top : y ≠ ∞) :
    (harmonicDeriv N y).toReal = y.toReal⁻¹ - (y.toReal + N)⁻¹ := by
  have h1 : (y + ENNReal.ofReal N)⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, add_eq_zero, not_and]
    exact fun h ↦ absurd h hy0
  rw [harmonicDeriv, ENNReal.toReal_sub_of_le (a := y⁻¹) (b := (y + ENNReal.ofReal N)⁻¹)
      (ENNReal.inv_le_inv.mpr le_self_add) (by simp [hy0]),
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_add hy_top (by simp),
    ENNReal.toReal_ofReal hN.le]

lemma deriv_boundedLogUtility_zero {N : ℝ} (hN : 0 < N) :
    (boundedLogUtility hN).deriv 0 = ⊤ := by
  rw [Utility.deriv_zero_eq]
  refine Tendsto.limsup_eq ?_
  simp only [EReal.tendsto_coe_nhds_top_iff]
  have h_inv : Tendsto (fun y : ℝ≥0∞ ↦ y.toReal⁻¹) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds
      (ENNReal.continuousAt_toReal (by simp)).tendsto, ?_⟩
    simpa using ENNReal.eventually_toReal_pos_nhdsGT_zero
  refine tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_right (𝓝[>] (0 : ℝ≥0∞)) (-N⁻¹) h_inv)
  filter_upwards [ENNReal.eventually_toReal_pos_nhdsGT_zero] with y hy
  rw [deriv_boundedLogUtility_real hN hy]
  have h2 : (y.toReal + N)⁻¹ ≤ N⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hN]
    linarith
  simp only [← sub_eq_add_neg]
  linarith

/-- The derivative of the bounded logarithmic utility, in `ℝ≥0∞` form. -/
lemma deriv_boundedLogUtility {N : ℝ} (hN : 0 < N) (y : ℝ≥0∞) :
    (boundedLogUtility hN).deriv y = ((harmonicDeriv N y : ℝ≥0∞) : EReal) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [deriv_boundedLogUtility_zero hN, (harmonicDeriv_eq_top_iff hN).mpr rfl]
    simp
  rcases eq_or_ne y ∞ with rfl | hy_top
  · rw [(boundedLogUtility hN).deriv_top_eq_zero (boundedLogUtility_le hN), harmonicDeriv_top]
    simp
  rw [Utility.deriv_eq_coe _ hy0 hy_top, deriv_boundedLogUtility_real hN
    (ENNReal.toReal_pos hy0 hy_top), ← toReal_harmonicDeriv hN hy0 hy_top,
    EReal.coe_ennreal_toReal (by simp [harmonicDeriv_eq_top_iff hN, hy0])]

lemma harmonicDeriv_ne_zero {N : ℝ} (hN : 0 < N) {y : ℝ≥0∞} (hy : y ≠ ∞) :
    harmonicDeriv N y ≠ 0 := by
  simp only [harmonicDeriv, ne_eq, tsub_eq_zero_iff_le, ENNReal.inv_le_inv, not_le]
  refine ENNReal.lt_add_right hy ?_
  simp [hN]

end BoundedLog

end ProbabilityTheory
