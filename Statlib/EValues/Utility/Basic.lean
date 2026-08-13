/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Statlib.ForMathlib.Convex
public import Statlib.ForMathlib.ENNReal
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral

/-!
# Utility Functions

This file defines utility functions for use in probability theory and e-value theory.

## Main definitions

* `Utility`: A structure representing a concave, monotone, and differentiable function from
  `ℝ≥0∞` to `EReal`, which is finite on `(0, ∞)`.
* `Utility.deriv`: The derivative of a utility function.

## Main statements

* `Utility.eintegral_le_map`: Jensen's inequality for utility functions.
* `Utility.le_add_deriv_mul`: The utility function is upper-bounded by its first-order
  Taylor approximation (a consequence of concavity).
* `Utility.antitone_deriv`, `Utility.continuous_deriv`: the derivative of a utility function is
  antitone and continuous on all of `ℝ≥0∞`, including at `0` and at `∞`.
* `Utility.deriv_mul_sub_le_liminf`: the difference quotients of a utility function along a
  segment are eventually at least the directional derivative.

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

set_option backward.isDefEq.respectTransparency false in
/-- The utility function is concave on `(0, ∞)` when viewed as a real-valued function. -/
lemma Utility.concaveOn_Ioi_real (U : Utility) : ConcaveOn ℝ (Set.Ioi 0) U.real := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_pos : 0 < x := Set.mem_Ioi.mp hx
  have hy_pos : 0 < y := Set.mem_Ioi.mp hy
  simp only [smul_eq_mul]
  have h_ccv := U.concave.2 (Set.mem_univ (ENNReal.ofReal x)) (Set.mem_univ (ENNReal.ofReal y))
    (by simp : 0 ≤ (⟨a, ha⟩ : ℝ≥0)) (by simp : 0 ≤ (⟨b, hb⟩ : ℝ≥0)) (by ext; exact hab)
  rw [EReal.smul_nnreal_eq_mul] at h_ccv
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

set_option backward.isDefEq.respectTransparency false in
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

/-- Jensen's inequality for a utility function. -/
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
      rw [eintegral_const_mul, eintegral_sub']
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

end ProbabilityTheory
