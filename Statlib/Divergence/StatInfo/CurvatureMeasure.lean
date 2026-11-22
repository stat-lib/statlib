/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.DivFunction.CurvatureMeasure
public import Statlib.Divergence.StatInfo.StatInfoDivFun

/-!
# Curvature measure of the statistical information divergence functions

For `0 < β` and `0 < γ`, the hockey-stick function `statInfoFun β γ` is piecewise linear on
`[0, ∞)`, with a single kink at `γ / β` where its slope increases by `β`. Its curvature measure is
therefore `β • dirac (γ / β)`, plus an infinite atom at `0`: by convention, the right derivative
`rightDerivStieltjes` of a divergence function is `⊥` below the lower end `xmin` of its effective
domain (here `0`), and its right derivative at `0` is finite.

## Main statements

* `measure_rightDerivStieltjes_statInfoDivFun`: the Stieltjes measure of the right derivative of
  `statInfoDivFun β γ` is `∞ • dirac 0 + β • dirac (γ / β)`.
* `curvatureMeasure_statInfoDivFun`, `curvatureMeasureReal_statInfoDivFun`: the curvature measure
  of `statInfoDivFun β γ`, as a measure on `ℝ≥0∞` and on `ℝ`.
* `curvatureMeasureReal_statInfoDivFun_restrict_Ioi`: on `(0, ∞)`, the curvature measure of
  `statInfoDivFun β γ` is `β • dirac (γ / β)`.
-/

@[expose] public section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {β γ : ℝ}

section RightDeriv

/-- The right derivative of `statInfoDivFun β γ` at `0 ≤ x`, for `0 ≤ β`: it is `-β` (if `γ ≤ β`)
or `0` (if `β < γ`) before the kink `γ / β`, and it increases by `β` at the kink. -/
lemma rightDerivStieltjes_statInfoDivFun_of_nonneg (hβ : 0 ≤ β) {x : ℝ} (hx : 0 ≤ x) :
    (statInfoDivFun β γ).rightDerivStieltjes x
      = (((if γ ≤ β then -β else 0) + if γ / β ≤ x then β else 0 : ℝ) : EReal) := by
  have h_pos {x : ℝ} (hx : 0 < x) : (statInfoDivFun β γ).rightDerivStieltjes x
      = (((if γ ≤ β then -β else 0) + if γ / β ≤ x then β else 0 : ℝ) : EReal) := by
    rw [DivFunction.rightDerivStieltjes_of_mem_interior (by simpa using hx) (by simp)]
    congr 1
    refine HasDerivWithinAt.derivWithin ?_ (uniqueDiffWithinAt_Ioi x)
    refine (hasDerivWithinAt_statInfoFun_Ioi hβ x).congr_of_eventuallyEq ?_
      (realFun_statInfoDivFun_of_nonneg hx.le)
    filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
    exact realFun_statInfoDivFun_of_nonneg (hx.trans hy).le
  rcases hx.lt_or_eq with hx | rfl
  · exact h_pos hx
  -- at `0`, the right derivative is the infimum of its values on `(0, ∞)`
  rw [← ERealStieltjes.iInf_Ioi_eq]
  refine le_antisymm ?_ (le_iInf fun r ↦ ?_)
  · by_cases hc : γ / β ≤ 0
    · refine (iInf_le _ ⟨1, zero_lt_one⟩).trans_eq ?_
      simp [h_pos zero_lt_one, hc, hc.trans zero_le_one]
    · have h_half : 0 < γ / β / 2 := by linarith
      refine (iInf_le _ ⟨γ / β / 2, h_half⟩).trans_eq ?_
      simp [h_pos h_half, hc, show ¬ γ / β ≤ γ / β / 2 by linarith]
  · rw [h_pos r.property]
    exact EReal.coe_le_coe_iff.mpr (by split_ifs <;> linarith [mem_Ioi.mp r.property])

end RightDeriv

section CurvatureMeasure

/-- The Stieltjes measure of the right derivative of `statInfoDivFun β γ` has an atom of mass `β`
at the kink `γ / β`, and an infinite atom at `0`, where the right derivative jumps from `⊥` to a
finite value. -/
lemma measure_rightDerivStieltjes_statInfoDivFun (hβ : 0 < β) (hγ : 0 < γ) :
    (statInfoDivFun β γ).rightDerivStieltjes.measure
      = ∞ • Measure.dirac 0 + ENNReal.ofReal β • Measure.dirac (γ / β) := by
  set g := (statInfoDivFun β γ).rightDerivStieltjes
  set a : ℝ := if γ ≤ β then -β else 0
  have hc : 0 < γ / β := div_pos hγ hβ
  have hg_pos (x : ℝ) (hx : 0 ≤ x) : g x = ((a + if γ / β ≤ x then β else 0 : ℝ) : EReal) :=
    rightDerivStieltjes_statInfoDivFun_of_nonneg hβ.le hx
  have hg0 : g 0 = a := by simpa [hc.not_ge] using hg_pos 0 le_rfl
  have hg_neg (x : ℝ) (hx : x < 0) : g x = ⊥ := DivFunction.rightDerivStieltjes_of_neg hx
  -- the part of the measure on `Iic 0` is an infinite atom at `0`
  have h_Iic : g.measure.restrict (Iic 0) = ∞ • Measure.dirac 0 := by
    ext s hs
    rw [Measure.restrict_apply hs, smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    by_cases h0 : (0 : ℝ) ∈ s
    · rw [indicator_of_mem h0, Pi.one_apply, mul_one]
      refine top_le_iff.mp ?_
      calc ∞ = g.measure {0} := (g.measure_singleton_eq_top fun y hy ↦ by
              rw [hg0, hg_neg y hy]; simp).symm
        _ ≤ g.measure (s ∩ Iic 0) :=
          measure_mono (singleton_subset_iff.mpr ⟨h0, mem_Iic.mpr le_rfl⟩)
    · rw [indicator_of_notMem h0, mul_zero]
      refine measure_mono_null (fun x hx ↦ ?_)
        (g.measure_Iio_eq_zero_of_forall_lt_eq_bot hg_neg)
      exact lt_of_le_of_ne hx.2 fun h ↦ h0 (h ▸ hx.1)
  -- the part of the measure on `Ioi 0` is an atom of mass `β` at `γ / β`
  have h_Ioi_univ : g.measure (Ioi 0) = ENNReal.ofReal β := by
    have h_tendsto : Tendsto g atTop (𝓝 ((a + β : ℝ) : EReal)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (γ / β)] with x hx
      rw [hg_pos x (hc.le.trans hx), ite_eq_left hx]
    rw [g.measure_Ioi h_tendsto, hg0, ← EReal.coe_sub, add_sub_cancel_left,
      EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have : IsFiniteMeasure (g.measure.restrict (Ioi 0)) := ⟨by
    rw [Measure.restrict_apply_univ, h_Ioi_univ]
    exact ENNReal.ofReal_lt_top⟩
  have h_Ioi : g.measure.restrict (Ioi 0) = ENNReal.ofReal β • Measure.dirac (γ / β) := by
    refine Measure.ext_of_Iic _ _ fun x ↦ ?_
    rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi, smul_apply,
      Measure.dirac_apply' _ measurableSet_Iic, smul_eq_mul]
    rcases le_or_gt x 0 with hx | hx
    · rw [Ioc_eq_empty (not_lt.mpr hx), measure_empty,
        indicator_of_notMem (by simp only [mem_Iic, not_le]; linarith), mul_zero]
    · rw [g.measure_Ioc, hg_pos x hx.le, hg0, ← EReal.coe_sub, add_sub_cancel_left]
      by_cases hcx : γ / β ≤ x
      · rw [ite_eq_left hcx, indicator_of_mem (mem_Iic.mpr hcx), Pi.one_apply, mul_one,
          EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
      · rw [ite_eq_right hcx, indicator_of_notMem (by simpa using hcx), mul_zero]
        simp
  rw [← Measure.restrict_add_restrict_compl (μ := g.measure) measurableSet_Iic, compl_Iic, h_Iic,
    h_Ioi]

/-- **Curvature measure of the statistical information divergence functions**: for `0 < β` and
`0 < γ`, the curvature measure of `statInfoDivFun β γ` is `β • dirac (γ / β)`, plus an infinite
atom at `0 = (statInfoDivFun β γ).xmin`. -/
theorem curvatureMeasure_statInfoDivFun (hβ : 0 < β) (hγ : 0 < γ) :
    (statInfoDivFun β γ).curvatureMeasure
      = ∞ • Measure.dirac 0 + ENNReal.ofReal β • Measure.dirac (ENNReal.ofReal (γ / β)) := by
  rw [DivFunction.curvatureMeasure, measure_rightDerivStieltjes_statInfoDivFun hβ hγ,
    Measure.map_add _ _ ENNReal.measurable_ofReal, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' ENNReal.measurable_ofReal, Measure.map_dirac' ENNReal.measurable_ofReal,
    ENNReal.ofReal_zero]
  all_goals fun_prop

/-- **Curvature measure of the statistical information divergence functions**, as a measure on
`ℝ`: for `0 < β` and `0 < γ`, it is `β • dirac (γ / β)`, plus an infinite atom at `0`. -/
theorem curvatureMeasureReal_statInfoDivFun (hβ : 0 < β) (hγ : 0 < γ) :
    (statInfoDivFun β γ).curvatureMeasureReal
      = ∞ • Measure.dirac 0 + ENNReal.ofReal β • Measure.dirac (γ / β) := by
  rw [DivFunction.curvatureMeasureReal, curvatureMeasure_statInfoDivFun hβ hγ,
    Measure.map_add _ _ ENNReal.measurable_toReal, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' ENNReal.measurable_toReal, Measure.map_dirac' ENNReal.measurable_toReal,
    ENNReal.toReal_zero, ENNReal.toReal_ofReal (div_pos hγ hβ).le]
  all_goals fun_prop

/-- The restriction to `(0, ∞)` of the curvature measure of `statInfoDivFun β γ` is the Dirac mass
`β • dirac (γ / β)`. -/
lemma curvatureMeasureReal_statInfoDivFun_restrict_Ioi (hβ : 0 < β) (hγ : 0 < γ) :
    (statInfoDivFun β γ).curvatureMeasureReal.restrict (Ioi 0)
      = ENNReal.ofReal β • Measure.dirac (γ / β) := by
  rw [curvatureMeasureReal_statInfoDivFun hβ hγ, Measure.restrict_add, Measure.restrict_smul,
    Measure.restrict_smul, restrict_dirac' measurableSet_Ioi, restrict_dirac' measurableSet_Ioi]
  simp [div_pos hγ hβ]

end CurvatureMeasure

end ProbabilityTheory
