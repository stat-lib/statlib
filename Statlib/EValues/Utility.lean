/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Order.CompletePartialOrder
public import Statlib.ForMathlib.EIntegral
public import Statlib.ForMathlib.ENNReal
public import Statlib.ForMathlib.Convex

/-!
# Utility Functions

This file defines utility functions for use in probability theory and e-value theory.

## Main definitions

* `Utility`: A structure representing a concave, monotone, and differentiable function from
  `ℝ≥0∞` to `EReal`, which is finite on `(0, ∞)`.
* `Utility.deriv`: The derivative of a utility function.
* `logUtility`: The logarithmic utility function.
* `harmonicTrunc`: The harmonic truncation `harmonicTrunc n x = n x / (n + x)`.
* `boundedLogUtility`: Bounded approximations `x ↦ log (N x / (N + x))` of the logarithmic
  utility function, and `harmonicDeriv`, their derivative in `ℝ≥0∞` form.

## Main statements

* `Utility.eintegral_le_map`: Jensen's inequality for utility functions.
* `Utility.le_add_deriv_mul`: The utility function is upper-bounded by its first-order
  Taylor approximation (a consequence of concavity).
* `Utility.antitone_deriv`, `Utility.continuous_deriv`: the derivative of a utility function is
  antitone and continuous on all of `ℝ≥0∞`, including at `0` and at `∞`.
* `Utility.deriv_mul_sub_le_liminf`: the difference quotients of a utility function along a
  segment are eventually at least the directional derivative.
* `deriv_logUtility`: The derivative of the logarithmic utility function.
* `deriv_boundedLogUtility`: The derivative of `boundedLogUtility`, in `ℝ≥0∞` form.

-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {U : ℝ≥0∞ → EReal}

/-- A utility function is a concave, monotone and differentiable function from `ℝ≥0∞` to `EReal`,
which is finite on `(0, ∞)`. -/
structure Utility where
  /-- The function itself. -/
  toFun : ℝ≥0∞ → EReal
  eq_coe' : ∀ x, x ≠ 0 → x ≠ ∞ → toFun x ≠ ⊥ ∧ toFun x ≠ ⊤
  monotone' : Monotone toFun
  continuous' : Continuous toFun
  concave' : ConcaveOn ℝ≥0 Set.univ toFun
  differentiable' : ContDiffOn ℝ 1 (fun x ↦ (toFun (ENNReal.ofReal x)).toReal) (Set.Ioi 0)

-- instance : Coe (Utility) (ℝ≥0∞ → EReal) := ⟨Utility.toFun⟩
instance : CoeFun (Utility) (fun _ ↦ ℝ≥0∞ → EReal) := ⟨Utility.toFun⟩

lemma Utility.eq_coe (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx_top : x ≠ ∞) :
    U x ≠ ⊥ ∧ U x ≠ ⊤ := U.eq_coe' x hx0 hx_top

lemma Utility.monotone (U : Utility) : Monotone U := U.monotone'

lemma Utility.continuous (U : Utility) : Continuous U := U.continuous'

@[fun_prop]
lemma Utility.measurable (U : Utility) : Measurable U := U.continuous.measurable

lemma Utility.aemeasurable {μ : Measure ℝ≥0∞} (U : Utility) :
    AEMeasurable U μ := U.measurable.aemeasurable

lemma Utility.concave (U : Utility) : ConcaveOn ℝ≥0 Set.univ U := U.concave'

lemma Utility.ne_top (U : Utility) {x : ℝ≥0∞} (hx_top : x ≠ ∞) : U x ≠ ⊤ := by
  by_cases hx0 : x = 0
  · simp only [hx0, ne_eq]
    refine ne_top_of_le_ne_top (b := U 1) ?_ ?_
    · exact (U.eq_coe (by simp) (by simp)).2
    · exact U.monotone (by simp)
  · exact (U.eq_coe hx0 hx_top).2

lemma Utility.ne_bot (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) : U x ≠ ⊥ := by
  by_cases hx_top : x = ∞
  · simp only [hx_top, ne_eq]
    refine ne_bot_of_le_ne_bot (b := U 1) ?_ ?_
    · exact (U.eq_coe (by simp) (by simp)).1
    · exact U.monotone (by simp)
  · exact (U.eq_coe hx0 hx_top).1

/-- The real-valued representation of a utility function. -/
def Utility.real (U : Utility) : ℝ → ℝ := fun x ↦ (U (ENNReal.ofReal x)).toReal

lemma Utility.real_toReal (U : Utility) {x : ℝ≥0∞} (hx_top : x ≠ ∞) :
    U.real x.toReal = (U x).toReal := by
  simp only [real]
  rw [ENNReal.ofReal_toReal hx_top]

lemma Utility.coe_real_toReal' (U : Utility) {x : ℝ≥0∞} (hx0 : U x ≠ ⊥) (hx_top : x ≠ ∞) :
    (U.real x.toReal : EReal) = U x := by
  rw [U.real_toReal hx_top, EReal.coe_toReal]
  · exact U.ne_top hx_top
  · exact hx0

lemma Utility.coe_real_toReal (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx_top : x ≠ ∞) :
    (U.real x.toReal : EReal) = U x :=
  coe_real_toReal' U (U.ne_bot hx0) hx_top

lemma Utility.contDiffOn (U : Utility) : ContDiffOn ℝ 1 U.real (Set.Ioi 0) := U.differentiable'

lemma Utility.differentiableOn (U : Utility) : DifferentiableOn ℝ U.real (Set.Ioi 0) :=
  U.contDiffOn.differentiableOn (by simp)

lemma Utility.monotoneOn_Ioi_real (U : Utility) : MonotoneOn U.real (Set.Ioi 0) := by
  intro x hx y hy hxy
  refine EReal.toReal_le_toReal ?_ ?_ ?_
  · exact U.monotone (ENNReal.ofReal_le_ofReal hxy)
  · exact U.ne_bot (by simpa)
  · exact U.ne_top (by simp)

lemma Utility.monotoneOn_Ici_real (U : Utility) (hU0 : U 0 ≠ ⊥) :
    MonotoneOn U.real (Set.Ici 0) := by
  intro x hx y hy hxy
  refine EReal.toReal_le_toReal ?_ ?_ ?_
  · exact U.monotone (ENNReal.ofReal_le_ofReal hxy)
  · by_cases hx0 : x = 0
    · simpa [hx0]
    · exact U.ne_bot (by simp [lt_of_le_of_ne (Set.mem_Ici.mp hx) (Ne.symm hx0)])
  · exact U.ne_top (by simp)

/-- The utility function is concave on `(0, ∞)` when viewed as a real-valued function. -/
lemma Utility.concaveOn_Ioi_real (U : Utility) : ConcaveOn ℝ (Set.Ioi 0) U.real := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_pos : 0 < x := Set.mem_Ioi.mp hx
  have hy_pos : 0 < y := Set.mem_Ioi.mp hy
  simp only [smul_eq_mul]
  have h_ccv := U.concave.2 (Set.mem_univ (ENNReal.ofReal x)) (Set.mem_univ (ENNReal.ofReal y))
    (by simp : 0 ≤ (⟨a, ha⟩ : ℝ≥0)) (by simp : 0 ≤ (⟨b, hb⟩ : ℝ≥0)) (by ext; exact hab)
  simp only [EReal.smul_nnreal_eq_mul, ENNReal.smul_def, smul_eq_mul] at h_ccv
  have h_mul (x a : ℝ) (ha : 0 ≤ a) :
      (ENNReal.ofNNReal (⟨a, ha⟩ : ℝ≥0)) * ENNReal.ofReal x = ENNReal.ofReal (a * x) := by
    rw [ENNReal.ofReal_mul ha]
    congr
    simp [ha]
  rw [h_mul, h_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)] at h_ccv
  rw [← U.coe_real_toReal' (U.ne_bot (by simpa)) (by simp),
    ← U.coe_real_toReal' (U.ne_bot (by simpa)) (by simp),
    ← U.coe_real_toReal' (U.ne_bot ?_) (by simp)] at h_ccv
  swap
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    by_cases ha_zero : a = 0
    · suffices hb_pos : 0 < b by simpa [ha_zero, hb_pos] using hy
      by_contra hb_nonpos
      linarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
      positivity
  norm_cast at h_ccv
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at h_ccv

/-- The utility function is concave on `[0, ∞)` when viewed as a real-valued function. -/
lemma Utility.concaveOn_Ici_real (U : Utility) (h0 : U 0 ≠ ⊥) : ConcaveOn ℝ (Set.Ici 0) U.real := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_nonneg : 0 ≤ x := Set.mem_Ici.mp hx
  have hy_nonneg : 0 ≤ y := Set.mem_Ici.mp hy
  have hU_ne_bot x : U x ≠ ⊥ := ne_bot_of_le_ne_bot (b := U 0) h0 (U.monotone zero_le)
  simp only [smul_eq_mul]
  have h_ccv := U.concave.2 (Set.mem_univ (ENNReal.ofReal x)) (Set.mem_univ (ENNReal.ofReal y))
    (by simp : 0 ≤ (⟨a, ha⟩ : ℝ≥0)) (by simp : 0 ≤ (⟨b, hb⟩ : ℝ≥0)) (by ext; exact hab)
  simp only [EReal.smul_nnreal_eq_mul, ENNReal.smul_def, smul_eq_mul] at h_ccv
  have h_mul (x a : ℝ) (ha : 0 ≤ a) :
      (ENNReal.ofNNReal (⟨a, ha⟩ : ℝ≥0)) * ENNReal.ofReal x = ENNReal.ofReal (a * x) := by
    rw [ENNReal.ofReal_mul ha]
    congr
    simp [ha]
  rw [h_mul, h_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)] at h_ccv
  rw [← U.coe_real_toReal' (hU_ne_bot _) (by simp),
    ← U.coe_real_toReal' (hU_ne_bot _) (by simp),
    ← U.coe_real_toReal' (hU_ne_bot _) (by simp)] at h_ccv
  norm_cast at h_ccv
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at h_ccv

/-- The derivative of a utility function.
At `x ∈ (0, ∞)`, this is the derivative of the real-valued representation.
At `0` or `∞`, this is defined as a limit. -/
protected noncomputable
def Utility.deriv (U : Utility) (x : ℝ≥0∞) : EReal :=
  if x = 0 then
    limsup (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[>] 0)
  else if x = ∞ then
    limsup (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[<] ∞)
  else
    ((deriv U.real x.toReal : ℝ) : EReal)

lemma Utility.differentiableAt_real (U : Utility) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ U.real x :=
  U.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds hx)

lemma Utility.deriv_real_nonneg (U : Utility) {x : ℝ} (hx : 0 < x) : 0 ≤ deriv U.real x := by
  refine (U.monotoneOn_Ioi_real.derivWithin_nonneg (x := x)).trans_eq ?_
  exact derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hx)

lemma Utility.antitoneOn_deriv_real (U : Utility) : AntitoneOn (deriv U.real) (Set.Ioi 0) :=
  U.concaveOn_Ioi_real.antitoneOn_deriv fun _ hx ↦ U.differentiableAt_real hx

lemma Utility.continuousOn_deriv_real (U : Utility) : ContinuousOn (deriv U.real) (Set.Ioi 0) :=
  U.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl

lemma Utility.deriv_eq_coe (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx_top : x ≠ ∞) :
    U.deriv x = ((deriv U.real x.toReal : ℝ) : EReal) := by
  simp [Utility.deriv, hx0, hx_top]

lemma Utility.deriv_zero_eq (U : Utility) :
    U.deriv 0 = limsup (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[>] 0) := by
  simp [Utility.deriv]

lemma Utility.deriv_top_eq (U : Utility) :
    U.deriv ∞ = limsup (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[<] ∞) := by
  simp [Utility.deriv]

lemma Utility.deriv_nonneg (U : Utility) (x : ℝ≥0∞) : 0 ≤ U.deriv x := by
  by_cases! hx0 : x = 0
  · simp only [hx0, Utility.deriv, ↓reduceIte]
    refine le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
    filter_upwards [ENNReal.eventually_toReal_pos_nhdsGT_zero] with y hy
    exact_mod_cast U.deriv_real_nonneg hy
  by_cases! hx_top : x = ∞
  · simp only [hx_top, Utility.deriv, ENNReal.top_ne_zero, ↓reduceIte]
    refine le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
    filter_upwards [ENNReal.eventually_toReal_pos_nhdsLT_top] with y hy
    exact_mod_cast U.deriv_real_nonneg hy
  simp only [Utility.deriv, hx0, ↓reduceIte, hx_top, EReal.coe_nonneg]
  have h_nonneg := U.monotoneOn_Ioi_real.derivWithin_nonneg (x := x.toReal)
  refine h_nonneg.trans_eq ?_
  refine derivWithin_of_mem_nhds ?_
  refine isOpen_Ioi.mem_nhds ?_
  simp only [Set.mem_Ioi, ENNReal.toReal_pos_iff]
  exact ⟨hx0.bot_lt, hx_top.lt_top⟩

lemma Utility.le_add_deriv_mul (U : Utility) {x y : ℝ≥0∞} (hx_top : x ≠ ∞)
    (hy_zero : y ≠ 0) (hy_top : y ≠ ∞) :
    U x ≤ U y + U.deriv y * (x - y) := by
  by_cases h_bot : U x = ⊥
  · simp [h_bot]
  have hUx_top : U x ≠ ⊤ := U.ne_top hx_top
  by_cases hU0 : U 0 = ⊥
  · by_cases hx0 : x = 0
    · simp [hx0, hU0]
    have h_ccv := ConcaveOn.le_add_deriv_mul U.concaveOn_Ioi_real (x := x.toReal) (y := y.toReal)
      ?_ ?_ ?_
    rotate_left
    · simpa [ENNReal.toReal_pos_iff] using ⟨Ne.bot_lt hx0, Ne.lt_top hx_top⟩
    · simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
    · refine U.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds ?_)
      simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
    rw [← U.coe_real_toReal hx0 hx_top, ← U.coe_real_toReal hy_zero hy_top, Utility.deriv]
    simp only [hy_zero, ↓reduceIte, hy_top, ge_iff_le]
    nth_rw 2 [← ENNReal.ofReal_toReal hx_top]
    nth_rw 3 [← ENNReal.ofReal_toReal hy_top]
    simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
    norm_cast
  · have h_ccv := ConcaveOn.le_add_deriv_mul (U.concaveOn_Ici_real hU0)
      (x := x.toReal) (y := y.toReal) (by simp) (by simp) ?_
    swap
    · refine U.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds ?_)
      simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
    rw [← U.coe_real_toReal' h_bot hx_top, ← U.coe_real_toReal hy_zero hy_top, Utility.deriv]
    simp only [hy_zero, ↓reduceIte, hy_top, ge_iff_le]
    nth_rw 2 [← ENNReal.ofReal_toReal hx_top]
    nth_rw 3 [← ENNReal.ofReal_toReal hy_top]
    simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
    norm_cast

lemma Utility.deriv_top_le (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) :
    U.deriv ∞ ≤ U.deriv x := by
  by_cases! hx_top : x = ∞
  · simp [hx_top]
  rw [U.deriv_eq_coe hx0 hx_top]
  simp only [Utility.deriv, ENNReal.top_ne_zero, ↓reduceIte]
  refine limsup_le_of_le (h := ?_)
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx0 hx_top
  have h_gt : ∀ᶠ y in 𝓝[<] (∞ : ℝ≥0∞), x < y :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hx_top.lt_top)
  filter_upwards [ENNReal.eventually_toReal_pos_nhdsLT_top, h_gt] with y hy hxy
  have hy_top : y ≠ ∞ := by rintro rfl; simp at hy
  exact_mod_cast U.antitoneOn_deriv_real hx_pos hy (ENNReal.toReal_mono hy_top hxy.le)

lemma Utility.deriv_le_deriv_zero (U : Utility) (x : ℝ≥0∞) : U.deriv x ≤ U.deriv 0 := by
  have key {y : ℝ≥0∞} (hy0 : y ≠ 0) (hy_top : y ≠ ∞) : U.deriv y ≤ U.deriv 0 := by
    rw [U.deriv_eq_coe hy0 hy_top]
    simp only [Utility.deriv, ↓reduceIte]
    refine le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
    have h_lt : ∀ᶠ z in 𝓝[>] (0 : ℝ≥0∞), z < y :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hy0.bot_lt)
    filter_upwards [ENNReal.eventually_toReal_pos_nhdsGT_zero, h_lt] with z hz hzy
    exact_mod_cast U.antitoneOn_deriv_real hz (ENNReal.toReal_pos hy0 hy_top)
      (ENNReal.toReal_mono hy_top hzy.le)
  rcases eq_or_ne x 0 with rfl | hx0
  · exact le_rfl
  rcases eq_or_ne x ∞ with rfl | hx_top
  · exact (U.deriv_top_le one_ne_zero).trans (key one_ne_zero (by simp))
  · exact key hx0 hx_top

/-- The derivative of a utility function is antitone on all of `ℝ≥0∞`, including at `0` and
at `∞`. -/
lemma Utility.antitone_deriv (U : Utility) : Antitone U.deriv := by
  intro x y hxy
  rcases eq_or_ne x 0 with rfl | hx0
  · exact U.deriv_le_deriv_zero y
  rcases eq_or_ne x ∞ with rfl | hx_top
  · rw [top_le_iff.mp hxy]
  rcases eq_or_ne y ∞ with rfl | hy_top
  · exact U.deriv_top_le hx0
  have hy0 : y ≠ 0 := fun h ↦ hx0 (nonpos_iff_eq_zero.mp (h ▸ hxy))
  rw [U.deriv_eq_coe hx0 hx_top, U.deriv_eq_coe hy0 hy_top]
  exact_mod_cast U.antitoneOn_deriv_real (ENNReal.toReal_pos hx0 hx_top)
    (ENNReal.toReal_pos hy0 hy_top) (ENNReal.toReal_mono hy_top hxy)

lemma Utility.tendsto_deriv_real_atTop (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) :
    Tendsto (deriv U.real) atTop (𝓝 0) := by
  have hb (y : ℝ) (hy : 0 < y) : U.real y ≤ b := by
    have : ((b : EReal)).toReal = b := EReal.toReal_coe b
    rw [Utility.real, ← this]
    exact EReal.toReal_le_toReal (hU_le _) (U.ne_bot (by simp [hy])) (by simp)
  refine squeeze_zero' (g := fun y ↦ (b - U.real 1) / (y - 1)) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy using U.deriv_real_nonneg hy
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    have h := U.concaveOn_Ioi_real.le_add_deriv_mul (x := 1) (y := y) (by simp)
      (by simp only [Set.mem_Ioi]; positivity) (U.differentiableAt_real (by positivity))
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hb y (by positivity)]
  · exact Filter.Tendsto.const_div_atTop
      (by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id) _

/-- The derivative of a utility function is continuous at every `α ≠ ∞`: this is a continuity
statement on `(0, ∞)` and a monotone limit statement at `0`. See `Utility.tendsto_deriv_top` for
the case `α = ∞` and `Utility.continuous_deriv` for the combination of the two. -/
lemma Utility.tendsto_deriv (U : Utility) {α : ℝ≥0∞} (hα_top : α ≠ ∞) {ι : Type*} {l : Filter ι}
    {z : ι → ℝ≥0∞} (hz : Tendsto z l (𝓝 α)) :
    Tendsto (fun n ↦ U.deriv (z n)) l (𝓝 (U.deriv α)) := by
  by_cases hα0 : α = 0
  · subst hα0
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · rw [U.deriv_zero_eq]
      refine limsup_le_of_le (h := ?_)
      filter_upwards [ENNReal.eventually_toReal_pos_nhdsGT_zero] with y hy
      refine le_liminf_of_le (h := ?_)
      have hy0 : (0 : ℝ≥0∞) < y := by
        rw [pos_iff_ne_zero]
        rintro rfl
        simp at hy
      have hy_top : y ≠ ∞ := by rintro rfl; simp at hy
      filter_upwards [hz.eventually (eventually_lt_nhds hy0)] with n hn
      rw [← U.deriv_eq_coe hy0.ne' hy_top]
      exact U.antitone_deriv hn.le
    · exact limsup_le_of_le (h := .of_forall fun n ↦ U.deriv_le_deriv_zero (z n))
  · -- for `α ≠ 0`, the terms `z n` are eventually finite and nonzero
    have hα_pos : 0 < α.toReal := ENNReal.toReal_pos hα0 hα_top
    have h_ev : ∀ᶠ n in l, z n ≠ 0 ∧ z n ≠ ∞ := by
      filter_upwards [hz.eventually (eventually_gt_nhds (Ne.bot_lt hα0)),
        hz.eventually (eventually_lt_nhds hα_top.lt_top)] with n h1 h2
      exact ⟨h1.ne', h2.ne⟩
    rw [U.deriv_eq_coe hα0 hα_top]
    refine Tendsto.congr' (f₁ := fun n ↦ ((deriv U.real (z n).toReal : ℝ) : EReal)) ?_ ?_
    · filter_upwards [h_ev] with n hn
      exact (U.deriv_eq_coe hn.1 hn.2).symm
    rw [EReal.tendsto_coe]
    refine (U.continuousOn_deriv_real α.toReal hα_pos).tendsto.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(ENNReal.tendsto_toReal hα_top).comp hz, ?_⟩
    filter_upwards [h_ev] with n hn
    exact ENNReal.toReal_pos hn.1 hn.2

/-- The derivative of a utility function is continuous at `∞`. -/
lemma Utility.tendsto_deriv_top (U : Utility) {ι : Type*} {l : Filter ι} {z : ι → ℝ≥0∞}
    (hz : Tendsto z l (𝓝 ∞)) :
    Tendsto (fun n ↦ U.deriv (z n)) l (𝓝 (U.deriv ∞)) := by
  refine tendsto_of_le_liminf_of_limsup_le
    (le_liminf_of_le (h := .of_forall fun n ↦ U.antitone_deriv le_top)) ?_
  calc limsup (fun n ↦ U.deriv (z n)) l
  _ ≤ liminf (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[<] ∞) := by
    refine le_liminf_of_le (h := ?_)
    filter_upwards [ENNReal.eventually_toReal_pos_nhdsLT_top] with y hy
    have hy0 : (0 : ℝ≥0∞) < y := by
      rw [pos_iff_ne_zero]
      rintro rfl
      simp at hy
    have hy_top : y ≠ ∞ := by rintro rfl; simp at hy
    rw [← U.deriv_eq_coe hy0.ne' hy_top]
    refine limsup_le_of_le (h := ?_)
    filter_upwards [hz.eventually (eventually_gt_nhds hy_top.lt_top)] with n hn
    exact U.antitone_deriv hn.le
  _ ≤ limsup (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[<] ∞) := liminf_le_limsup
  _ = U.deriv ∞ := U.deriv_top_eq.symm

/-- The derivative of a utility function is continuous on `ℝ≥0∞`, including at `0` and at `∞`. -/
@[fun_prop]
lemma Utility.continuous_deriv (U : Utility) : Continuous U.deriv := by
  rw [continuous_iff_continuousAt]
  intro α
  rcases eq_or_ne α ∞ with rfl | hα_top
  · exact U.tendsto_deriv_top tendsto_id
  · exact U.tendsto_deriv hα_top tendsto_id

@[fun_prop]
lemma Utility.measurable_deriv (U : Utility) : Measurable U.deriv := U.continuous_deriv.measurable

lemma Utility.deriv_top_eq_zero (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) :
    U.deriv ∞ = 0 := by
  simp only [Utility.deriv, ENNReal.top_ne_zero, ↓reduceIte]
  refine Tendsto.limsup_eq ?_
  have h0 : (0 : EReal) = ((0 : ℝ) : EReal) := rfl
  rw [h0, EReal.tendsto_coe]
  exact (U.tendsto_deriv_real_atTop hU_le).comp ENNReal.tendsto_toReal_atTop

/-- The first-order Taylor inequality, in the form of a lower bound on the increment of `U`. -/
lemma Utility.deriv_mul_sub_le (U : Utility) {α Z : ℝ≥0∞} (hα_top : α ≠ ∞)
    (hZ0 : Z ≠ 0) (hZ_top : Z ≠ ∞) :
    U.deriv Z * ((Z : EReal) - α) ≤ U Z - U α := by
  by_cases hUα : U α = ⊥
  · rw [hUα, EReal.sub_bot (U.ne_bot hZ0)]
    exact le_top
  have h := U.le_add_deriv_mul hα_top hZ0 hZ_top
  rw [U.deriv_eq_coe hZ0 hZ_top, ← U.coe_real_toReal' (U.ne_bot hZ0) hZ_top,
    ← U.coe_real_toReal' hUα hα_top, ← EReal.coe_ennreal_toReal hZ_top,
    ← EReal.coe_ennreal_toReal hα_top] at h ⊢
  norm_cast at h ⊢
  nlinarith [h]

/-- A convex combination inequality: the difference quotient of `U` along the segment from `α`
to `β` is bounded below by `U β - U α`. -/
lemma Utility.sub_le_inv_mul_sub (U : Utility) {α β : ℝ≥0∞} (hβ0 : β ≠ 0) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    U β - U α ≤ (t : EReal)⁻¹ *
      (U (ENNReal.ofReal t * β + ENNReal.ofReal (1 - t) * α) - U α) := by
  set W := ENNReal.ofReal t * β + ENNReal.ofReal (1 - t) * α with hW_def
  have ht_inv_pos : (0 : EReal) < (t : EReal)⁻¹ := by
    rw [← EReal.coe_inv]
    exact_mod_cast inv_pos.mpr ht0
  have hW0 : W ≠ 0 := by
    simp only [hW_def, ne_eq, add_eq_zero, mul_eq_zero, not_and, not_or]
    simp [ENNReal.ofReal_eq_zero, not_le.mpr ht0, hβ0]
  have hUW_bot : U W ≠ ⊥ := U.ne_bot hW0
  by_cases hUα : U α = ⊥
  · rw [hUα, EReal.sub_bot hUW_bot, EReal.mul_top_of_pos ht_inv_pos]
    exact le_top
  by_cases hUα_top : U α = ⊤
  · rw [hUα_top, EReal.sub_top]
    exact bot_le
  by_cases hUW : U W = ⊤
  · rw [hUW, EReal.top_sub hUα_top, EReal.mul_top_of_pos ht_inv_pos]
    exact le_top
  -- now all values are finite
  have hUβ_bot : U β ≠ ⊥ := U.ne_bot hβ0
  have hUβ_top : U β ≠ ⊤ := by
    intro h_top
    refine hUW ?_
    have hβ_top : β = ∞ := by
      by_contra h
      exact U.ne_top h h_top
    have : W = ∞ := by
      simp [hW_def, hβ_top, ENNReal.ofReal_eq_zero, not_le.mpr ht0]
    rw [this, ← hβ_top]
    exact h_top
  have h_ccv := U.concave.2 (Set.mem_univ β) (Set.mem_univ α)
    (zero_le (a := t.toNNReal)) (zero_le (a := (1 - t).toNNReal)) ?_
  swap
  · rw [← Real.toNNReal_add ht0.le (by positivity)]
    simp
  simp only [EReal.smul_nnreal_eq_mul, ENNReal.smul_def, smul_eq_mul] at h_ccv
  rw [Real.coe_toNNReal _ ht0.le, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 1 - t)] at h_ccv
  have hW_eq : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) * β + (((1 - t).toNNReal : ℝ≥0) : ℝ≥0∞) * α = W := rfl
  rw [hW_eq] at h_ccv
  obtain ⟨p, hp⟩ : ∃ p : ℝ, U α = p := ⟨(U α).toReal, (EReal.coe_toReal hUα_top hUα).symm⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, U β = q := ⟨(U β).toReal, (EReal.coe_toReal hUβ_top hUβ_bot).symm⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, U W = r := ⟨(U W).toReal, (EReal.coe_toReal hUW hUW_bot).symm⟩
  rw [hp, hq, hr] at h_ccv ⊢
  rw [← EReal.coe_inv]
  norm_cast at h_ccv ⊢
  rw [inv_mul_eq_div, le_div_iff₀ ht0]
  nlinarith [h_ccv]

/-- The increment of `U` is dominated by its first order Taylor approximation. -/
lemma Utility.sub_le_deriv_mul_sub (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    {α β : ℝ≥0∞} (hα0 : α ≠ 0) (hαβ : α ≠ ∞ → β ≠ ∞) :
    U β - U α ≤ U.deriv α * ((β : EReal) - α) := by
  by_cases hα_top : α = ∞
  · subst hα_top
    rw [U.deriv_top_eq_zero hU_le, zero_mul, EReal.sub_nonpos]
    exact U.monotone le_top
  have hβ_top : β ≠ ∞ := hαβ hα_top
  have hUα_bot : U α ≠ ⊥ := U.ne_bot hα0
  by_cases hUβ : U β = ⊥
  · rw [hUβ, EReal.bot_sub]
    exact bot_le
  have h := U.le_add_deriv_mul hβ_top hα0 hα_top
  rw [U.deriv_eq_coe hα0 hα_top, ← U.coe_real_toReal' hUβ hβ_top,
    ← U.coe_real_toReal' hUα_bot hα_top, ← EReal.coe_ennreal_toReal hβ_top,
    ← EReal.coe_ennreal_toReal hα_top] at h ⊢
  norm_cast at h ⊢
  linarith

/-- The map `y ↦ U.deriv α * (y - α)` is affine: it turns a convex combination of `1` and `β`
into the corresponding convex combination of its values. -/
lemma Utility.deriv_mul_sub_convex (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    {α β : ℝ≥0∞} (hαβ : α ≠ ∞ → β ≠ ∞) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    U.deriv α * (((ENNReal.ofReal δ * 1 + ENNReal.ofReal (1 - δ) * β : ℝ≥0∞) : EReal) - α)
      = ((1 - δ : ℝ) : EReal) * (U.deriv α * ((β : EReal) - α))
        + (δ : EReal) * (U.deriv α * ((1 : EReal) - α)) := by
  by_cases hα_top : α = ∞
  · subst hα_top
    rw [U.deriv_top_eq_zero hU_le]
    simp
  have hβ_top : β ≠ ∞ := hαβ hα_top
  have hδ0' : (0 : ℝ) < 1 - δ := by positivity
  have hw : (ENNReal.ofReal δ * 1 + ENNReal.ofReal (1 - δ) * β : ℝ≥0∞)
      = ENNReal.ofReal (δ + (1 - δ) * β.toReal) := by
    rw [mul_one]
    conv_lhs => rw [← ENNReal.ofReal_toReal hβ_top]
    rw [← ENNReal.ofReal_mul hδ0'.le,
      ← ENNReal.ofReal_add hδ0.le (mul_nonneg hδ0'.le ENNReal.toReal_nonneg)]
  have hw_pos : (0 : ℝ) < δ + (1 - δ) * β.toReal :=
    lt_of_lt_of_le hδ0 (le_add_of_nonneg_right (mul_nonneg hδ0'.le ENNReal.toReal_nonneg))
  rw [hw]
  by_cases hd_top : U.deriv α = ⊤
  · have hα0 : α = 0 := by
      by_contra h
      rw [U.deriv_eq_coe h hα_top] at hd_top
      simp at hd_top
    subst hα0
    rw [hd_top]
    simp only [EReal.coe_ennreal_zero, sub_zero, mul_one]
    rw [EReal.top_mul_of_pos (by
      simpa [EReal.coe_ennreal_pos] using (ENNReal.ofReal_pos.mpr hw_pos)),
      EReal.coe_mul_top_of_pos hδ0,
      EReal.add_top_of_ne_bot (EReal.ne_bot_of_nonneg
        (mul_nonneg (by positivity) (mul_nonneg le_top (EReal.coe_ennreal_nonneg β))))]
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, U.deriv α = (r : EReal) :=
      ⟨(U.deriv α).toReal,
        (EReal.coe_toReal hd_top (EReal.ne_bot_of_nonneg (U.deriv_nonneg α))).symm⟩
    have hcoe : ((ENNReal.ofReal (δ + (1 - δ) * β.toReal) : ℝ≥0∞) : EReal)
        = ((δ + (1 - δ) * β.toReal : ℝ) : EReal) := by
      simp only [EReal.coe_ennreal_ofReal]
      exact_mod_cast sup_of_le_left hw_pos.le
    rw [hr, hcoe, ← EReal.coe_ennreal_toReal hα_top, ← EReal.coe_ennreal_toReal hβ_top]
    norm_cast
    ring

/-- The key pointwise estimate for the first order optimality condition: along a sequence
`t n → 0`, the difference quotients of `U` between `α` and `β` are eventually at least the
directional derivative `U.deriv α * (β - α)`. -/
lemma Utility.deriv_mul_sub_le_liminf (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    {α β : ℝ≥0∞} (hβ0 : β ≠ 0) (hαβ : α ≠ ∞ → β ≠ ∞)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n) (ht1 : ∀ n, t n < 1) (ht : Tendsto t atTop (𝓝 0)) :
    U.deriv α * ((β : EReal) - α)
      ≤ liminf (fun n ↦ ((t n : ℝ) : EReal)⁻¹ *
          (U (ENNReal.ofReal (t n) * β + ENNReal.ofReal (1 - t n) * α) - U α)) atTop := by
  by_cases hα_top : α = ∞
  · subst hα_top
    have hU_bot : U (∞ : ℝ≥0∞) ≠ ⊥ := U.ne_bot (by simp)
    have hU_top : U (∞ : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp : (b : EReal) ≠ ⊤) (hU_le _)
    have h_eq (n : ℕ) : ENNReal.ofReal (t n) * β + ENNReal.ofReal (1 - t n) * (∞ : ℝ≥0∞) = ∞ := by
      rw [ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith [ht1 n])]
      simp
    simp only [h_eq, EReal.sub_self hU_top hU_bot, mul_zero]
    rw [U.deriv_top_eq_zero hU_le, zero_mul]
    simp
  have hβ_top : β ≠ ∞ := hαβ hα_top
  have hbb_pos : 0 < β.toReal := ENNReal.toReal_pos hβ0 hβ_top
  have ha0 : (0 : ℝ) ≤ α.toReal := ENNReal.toReal_nonneg
  have hz_pos (n : ℕ) : 0 < t n * β.toReal + (1 - t n) * α.toReal := by
    have h1 : 0 < t n * β.toReal := mul_pos (ht0 n) hbb_pos
    have h2 : 0 ≤ (1 - t n) * α.toReal := mul_nonneg (by linarith [ht1 n]) ha0
    positivity
  have hZ_eq (n : ℕ) : ENNReal.ofReal (t n) * β + ENNReal.ofReal (1 - t n) * α
      = ENNReal.ofReal (t n * β.toReal + (1 - t n) * α.toReal) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hβ_top, ← ENNReal.ofReal_toReal hα_top]
    rw [← ENNReal.ofReal_mul (ht0 n).le, ← ENNReal.ofReal_mul (by linarith [ht1 n]),
      ← ENNReal.ofReal_add (mul_nonneg (ht0 n).le ENNReal.toReal_nonneg)
        (mul_nonneg (by linarith [ht1 n]) ENNReal.toReal_nonneg)]
  simp only [hZ_eq]
  set Z : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (t n * β.toReal + (1 - t n) * α.toReal) with hZ_def
  have hZ0 (n : ℕ) : Z n ≠ 0 := by
    simp only [hZ_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hz_pos n
  have hZ_top (n : ℕ) : Z n ≠ ∞ := by simp [hZ_def]
  have h_cancel (n : ℕ) : ((t n : ℝ) : EReal)⁻¹ * ((t n : ℝ) : EReal) = 1 := by
    rw [← EReal.coe_inv, ← EReal.coe_mul, inv_mul_cancel₀ (ht0 n).ne']
    rfl
  have h_step (n : ℕ) : U.deriv (Z n) * ((β : EReal) - α)
      ≤ ((t n : ℝ) : EReal)⁻¹ * (U (Z n) - U α) := by
    have h := U.deriv_mul_sub_le (α := α) (Z := Z n) hα_top (hZ0 n) (hZ_top n)
    have hZ_coe : ((Z n : ℝ≥0∞) : EReal)
        = ((t n * β.toReal + (1 - t n) * α.toReal : ℝ) : EReal) := by
      rw [hZ_def]
      simp only [EReal.coe_ennreal_ofReal]
      exact_mod_cast sup_of_le_left (hz_pos n).le
    have h_sub : ((Z n : ℝ≥0∞) : EReal) - (α : EReal)
        = ((t n : ℝ) : EReal) * ((β : EReal) - (α : EReal)) := by
      rw [hZ_coe, ← EReal.coe_ennreal_toReal hα_top, ← EReal.coe_ennreal_toReal hβ_top]
      norm_cast
      ring
    rw [h_sub] at h
    calc U.deriv (Z n) * ((β : EReal) - α)
    _ = ((t n : ℝ) : EReal)⁻¹
        * (U.deriv (Z n) * (((t n : ℝ) : EReal) * ((β : EReal) - α))) := by
      rw [mul_left_comm (U.deriv (Z n)), ← mul_assoc, h_cancel n, one_mul]
    _ ≤ ((t n : ℝ) : EReal)⁻¹ * (U (Z n) - U α) := by
      gcongr
      rw [← EReal.coe_inv]
      exact_mod_cast (inv_pos.mpr (ht0 n)).le
  refine le_trans ?_ (liminf_le_liminf (.of_forall h_step))
  have hZ_tendsto : Tendsto Z atTop (𝓝 α) := by
    have h : Tendsto (fun n ↦ t n * β.toReal + (1 - t n) * α.toReal) atTop (𝓝 α.toReal) := by
      have := ((ht.mul_const β.toReal).add (((tendsto_const_nhds (x := (1 : ℝ))).sub
        ht).mul_const α.toReal))
      simpa using this
    have := ENNReal.tendsto_ofReal h
    rwa [ENNReal.ofReal_toReal hα_top] at this
  have h_deriv_tendsto : Tendsto (fun n ↦ U.deriv (Z n)) atTop (𝓝 (U.deriv α)) :=
    U.tendsto_deriv hα_top hZ_tendsto
  have hb_eq : ((β : EReal) - α) = ((β.toReal - α.toReal : ℝ) : EReal) := by
    rw [EReal.coe_sub, EReal.coe_ennreal_toReal hα_top, EReal.coe_ennreal_toReal hβ_top]
  have hb_ne_bot : ((β : EReal) - α) ≠ ⊥ := by rw [hb_eq]; exact EReal.coe_ne_bot _
  have hb_ne_top : ((β : EReal) - α) ≠ ⊤ := by rw [hb_eq]; exact EReal.coe_ne_top _
  have h4 : U.deriv α ≠ ⊤ ∨ ((β : EReal) - α) ≠ 0 := by
    by_cases hα0 : α = 0
    · refine Or.inr ?_
      simp [hα0, hβ0]
    · exact Or.inl (by rw [U.deriv_eq_coe hα0 hα_top]; simp)
  have h_mul_tendsto : Tendsto (fun n ↦ U.deriv (Z n) * ((β : EReal) - α)) atTop
      (𝓝 (U.deriv α * ((β : EReal) - α))) :=
    EReal.Tendsto.mul h_deriv_tendsto tendsto_const_nhds (Or.inr hb_ne_bot) (Or.inr hb_ne_top)
      (Or.inl (EReal.ne_bot_of_nonneg (U.deriv_nonneg α))) h4
  exact h_mul_tendsto.liminf_eq.ge

/-- Jensen's inequality. -/
theorem Utility.eintegral_le_map {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [IsProbabilityMeasure μ]
    (U : Utility) {X : α → ℝ≥0∞} (hX_meas : AEMeasurable X μ) :
    ∫ᵉ x, U (X x) ∂μ ≤ U (∫⁻ x, X x ∂μ) := by
  by_cases h : ∫ᵉ x, U (X x) ∂μ = ⊥
  · simp [h]
  have h_ne_bot : ∀ᵐ ω ∂μ, U (X ω) ≠ ⊥ := ae_ne_bot_of_eintegral_ne_bot (by fun_prop) h
  by_cases hX_int_top : ∫⁻ x, X x ∂μ = ∞
  · rw [hX_int_top]
    calc ∫ᵉ x, U (X x) ∂μ
    _ ≤ ∫ᵉ x, U ∞ ∂μ := eintegral_mono (fun _ ↦ U.monotone (by simp))
    _ = U ∞ := by simp
  by_cases hX_int_zero : ∫⁻ x, X x ∂μ = 0
  · rw [hX_int_zero]
    rw [lintegral_eq_zero_iff' hX_meas] at hX_int_zero
    have : ∀ᵐ x ∂μ, U (X x) = U 0 := by
      filter_upwards [hX_int_zero] with x hx
      simp [hx]
    rw [eintegral_congr_ae this]
    simp
  have hX_top : ∀ᵐ ω ∂μ, X ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (by fun_prop) hX_int_top] with x hx using hx.ne
  have h_ne_top : ∀ᵐ ω ∂μ, U (X ω) ≠ ⊤ := by
    filter_upwards [hX_top] with x hx using U.ne_top hx
  have h_ccv : ∀ᵐ x ∂μ, U (X x)
      ≤ U (∫⁻ y, X y ∂μ) + (U.deriv (∫⁻ y, X y ∂μ)) * (X x - ∫⁻ y, X y ∂μ) := by
    filter_upwards [h_ne_bot, h_ne_top, hX_top] with x hx_bot hx_top hx_top'
    exact U.le_add_deriv_mul hx_top' hX_int_zero hX_int_top
  calc ∫ᵉ x, U (X x) ∂μ
  _ ≤ ∫ᵉ x, U (∫⁻ y, X y ∂μ) + (U.deriv (∫⁻ y, X y ∂μ)) * (X x - ∫⁻ y, X y ∂μ) ∂μ :=
    eintegral_mono_ae h_ccv
  _ = U (∫⁻ y, X y ∂μ) := by
    have h_int_eq : ∫ᵉ x, U.deriv (∫⁻ y, X y ∂μ) * (X x - ∫⁻ y, X y ∂μ) ∂μ = 0 := by
      rw [eintegral_mul_const, eintegral_sub']
      rotate_left
      · fun_prop
      · fun_prop
      · simpa
      · exact EReal.ne_bot_of_nonneg (eintegral_nonneg (fun _ ↦ by positivity))
      · simp [Utility.deriv, hX_int_zero, hX_int_top]
      · simp [Utility.deriv, hX_int_zero, hX_int_top]
      · refine eintegrable_of_eintegral_ne_bot ?_
        rw [eintegral_sub']
        · simp [sub_eq_add_neg, EReal.add_eq_bot_iff, hX_int_top, eintegral_eq_lintegral]
        · fun_prop
        · fun_prop
        · simp [hX_int_top]
        · simp
      simp only [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one, mul_eq_zero]
      rw [eintegral_eq_lintegral, EReal.sub_self (by simpa) (by simp)]
      simp
    rw [eintegral_add', h_int_eq]
    rotate_left
    · fun_prop
    · fun_prop
    · simp [h_int_eq]
    · simp [h_int_eq]
    simp

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
    simpa using (Real.hasDerivAt_log (x := x + N) (by positivity)).comp x
      ((hasDerivAt_id x).add_const N)
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
