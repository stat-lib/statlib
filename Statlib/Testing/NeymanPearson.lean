/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/
module

public import Statlib.Testing.Basic

/-!
# The Neyman–Pearson lemma for the sum of errors


## Main definitions

* `Statlib.Testing.errSum` — the sum-of-errors objective `R_{1,t}`.
* `Statlib.Testing.npTest` — the likelihood-ratio (threshold) test.
* `Statlib.Testing.thresholdTest` — `npTest` bundled as a `Test`.

## Main results

* `Statlib.Testing.npTest_isMinimizer` — `npTest` minimizes the sum of errors.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace Statlib.Testing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Sum-of-errors objective of a randomized test `T : Ω → [0,1]`:
`∫⁻ T dP + t · ∫⁻ (1 − T) dQ`. This is the risk `R_{1,t}`. -/
noncomputable def errSum (P Q : Measure Ω) (t : ℝ≥0∞) (T : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ ω, T ω ∂P) + t * ∫⁻ ω, (1 - T ω) ∂Q

/-- Likelihood ratio version of NP test with dominating measure `μ = P + Q`,
threshold `t` and randomization `η` on the boundary: `1` where `p < t·q`, `η` where
`p = t·q`, and `0` where `p > t·q`. -/
noncomputable def npTest (P Q : Measure Ω) (t η : ℝ≥0∞) : Ω → ℝ≥0∞ := fun ω =>
  if P.rnDeriv (P + Q) ω < t * Q.rnDeriv (P + Q) ω then 1
  else if P.rnDeriv (P + Q) ω = t * Q.rnDeriv (P + Q) ω then η else 0

/-- Pointwise cost `p·x + t·(q·(1 − x))` of assigning test value `x` at a point. -/
noncomputable def cost (p q t x : ℝ≥0∞) : ℝ≥0∞ := p * x + t * (q * (1 - x))

private lemma cost_one_le (p q t x' : ℝ≥0∞) (hx' : x' ≤ 1) (h : p ≤ t * q) :
    cost p q t 1 ≤ cost p q t x' := by
  simp only [cost, mul_one, tsub_self, mul_zero, mul_zero, add_zero]
  have h2 : p * (1 - x') ≤ t * (q * (1 - x')) := by
    calc p * (1 - x') = (1 - x') * p := by ring
      _ ≤ (1 - x') * (t * q) := by gcongr
      _ = t * (q * (1 - x')) := by ring
  calc p = p * x' + p * (1 - x') := by rw [← mul_add, add_tsub_cancel_of_le hx', mul_one]
    _ ≤ p * x' + t * (q * (1 - x')) := by gcongr

private lemma cost_zero_le (p q t x' : ℝ≥0∞) (hx' : x' ≤ 1) (h : t * q ≤ p) :
    cost p q t 0 ≤ cost p q t x' := by
  simp only [cost, mul_zero, zero_add, tsub_zero, mul_one]
  calc t * q = t * ((x' + (1 - x')) * q) := by rw [add_tsub_cancel_of_le hx', one_mul]
    _ = x' * (t * q) + t * (q * (1 - x')) := by ring
    _ ≤ x' * p + t * (q * (1 - x')) := by gcongr
    _ = p * x' + t * (q * (1 - x')) := by ring

private lemma cost_eq_le (p q t η x' : ℝ≥0∞) (hη : η ≤ 1) (hx' : x' ≤ 1) (h : p = t * q) :
    cost p q t η ≤ cost p q t x' := by
  have e : ∀ y : ℝ≥0∞, y ≤ 1 → cost p q t y = t * q := by
    intro y hy
    simp only [cost, h]
    calc t * q * y + t * (q * (1 - y)) = (y + (1 - y)) * (t * q) := by ring
      _ = t * q := by rw [add_tsub_cancel_of_le hy, one_mul]
  rw [e η hη, e x' hx']

/-- The Neyman–Pearson test is measurable. This might be overkill the way proof is written. -/
lemma measurable_npTest (P Q : Measure Ω) (t η : ℝ≥0∞) : Measurable (npTest P Q t η) := by
  have hp := Measure.measurable_rnDeriv P (P + Q)
  have hq := Measure.measurable_rnDeriv Q (P + Q)
  have hEq : MeasurableSet {ω | P.rnDeriv (P + Q) ω = t * Q.rnDeriv (P + Q) ω} := by
    have : {ω | P.rnDeriv (P + Q) ω = t * Q.rnDeriv (P + Q) ω}
        = {ω | P.rnDeriv (P + Q) ω ≤ t * Q.rnDeriv (P + Q) ω}
          ∩ {ω | t * Q.rnDeriv (P + Q) ω ≤ P.rnDeriv (P + Q) ω} := by
      ext ω; simp [le_antisymm_iff]
    rw [this]
    exact (measurableSet_le hp (hq.const_mul t)).inter (measurableSet_le (hq.const_mul t) hp)
  exact Measurable.ite (measurableSet_lt hp (hq.const_mul t)) measurable_const
    (Measurable.ite hEq measurable_const measurable_const)

/-- The Neyman–Pearson test takes values in `[0,1]`. -/
lemma npTest_le_one (P Q : Measure Ω) (t η : ℝ≥0∞) (hη : η ≤ 1) (ω : Ω) :
    npTest P Q t η ω ≤ 1 := by
  unfold npTest
  split_ifs <;> simp [hη]

/-- `errSum` expressed as a single `μ`-integral of the pointwise cost, via change of
measure (`lintegral_rnDeriv_mul`) applied to both `P` and `Q`. -/
lemma errSum_eq_lintegral_cost (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (t : ℝ≥0∞) {T : Ω → ℝ≥0∞} (hT : Measurable T) :
    errSum P Q t T
      = ∫⁻ ω, cost (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) t (T ω) ∂(P + Q) := by
  have hP : P ≪ P + Q := Measure.AbsolutelyContinuous.add_right .rfl Q
  have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.add_right' .rfl P
  have hp := Measure.measurable_rnDeriv P (P + Q)
  have hq := Measure.measurable_rnDeriv Q (P + Q)
  have hT1 : Measurable (fun ω => 1 - T ω) := measurable_const.sub hT
  rw [errSum, ← lintegral_rnDeriv_mul hP hT.aemeasurable,
    ← lintegral_rnDeriv_mul hQ hT1.aemeasurable]
  calc
    (∫⁻ ω, P.rnDeriv (P + Q) ω * T ω ∂(P + Q))
          + t * ∫⁻ ω, Q.rnDeriv (P + Q) ω * (1 - T ω) ∂(P + Q) =
        (∫⁻ ω, P.rnDeriv (P + Q) ω * T ω ∂(P + Q))
          + ∫⁻ ω, t * (Q.rnDeriv (P + Q) ω * (1 - T ω)) ∂(P + Q) := by
      apply congrArg (fun x => (∫⁻ ω, P.rnDeriv (P + Q) ω * T ω ∂(P + Q)) + x)
      simpa only [Pi.mul_apply] using
        (lintegral_const_mul (μ := P + Q) t (hq.mul hT1)).symm
    _ = ∫⁻ ω, cost (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) t (T ω) ∂(P + Q) := by
      rw [show
        (∫⁻ ω, P.rnDeriv (P + Q) ω * T ω ∂(P + Q))
            + ∫⁻ ω, t * (Q.rnDeriv (P + Q) ω * (1 - T ω)) ∂(P + Q) =
          ∫⁻ ω, P.rnDeriv (P + Q) ω * T ω
            + t * (Q.rnDeriv (P + Q) ω * (1 - T ω)) ∂(P + Q) by
        simpa only [Pi.mul_apply] using
          (lintegral_add_left (μ := P + Q) (hp.mul hT)
            (fun ω => t * (Q.rnDeriv (P + Q) ω * (1 - T ω)))).symm]
      rfl

/-- **Neyman–Pearson lemma for the sum of errors.** The likelihood-ratio test
`npTest` is measurable, `[0,1]`-valued, and minimizes the sum-of-errors objective
over all measurable tests `T : Ω → [0,1]`. -/
theorem npTest_isMinimizer (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (t η : ℝ≥0∞) (hη : η ≤ 1) :
    Measurable (npTest P Q t η) ∧ (∀ ω, npTest P Q t η ω ≤ 1) ∧
      ∀ T : Ω → ℝ≥0∞, Measurable T → (∀ ω, T ω ≤ 1) →
        errSum P Q t (npTest P Q t η) ≤ errSum P Q t T := by
  refine ⟨measurable_npTest P Q t η, npTest_le_one P Q t η hη, ?_⟩
  intro T hT hT1
  rw [errSum_eq_lintegral_cost P Q t (measurable_npTest P Q t η),
    errSum_eq_lintegral_cost P Q t hT]
  refine lintegral_mono (fun ω => ?_)
  set p := P.rnDeriv (P + Q) ω with hp_def
  set q := Q.rnDeriv (P + Q) ω with hq_def
  rcases lt_trichotomy p (t * q) with h | h | h
  · have : npTest P Q t η ω = 1 := by rw [npTest, ite_eq_left h]
    rw [this]; exact cost_one_le p q t (T ω) (hT1 ω) h.le
  · have hnlt : ¬ p < t * q := by rw [h]; exact lt_irrefl _
    have : npTest P Q t η ω = η := by rw [npTest, ite_eq_right hnlt, ite_eq_left h]
    rw [this]; exact cost_eq_le p q t η (T ω) hη (hT1 ω) h
  · have hnlt : ¬ p < t * q := not_lt.mpr h.le
    have hne : ¬ p = t * q := (ne_of_gt h)
    have : npTest P Q t η ω = 0 := by rw [npTest, ite_eq_right hnlt, ite_eq_right hne]
    rw [this]; exact cost_zero_le p q t (T ω) (hT1 ω) h.le

/-- The **likelihood-ratio statistic** `h = dQ/dP`, defined via the Lebesgue
decomposition of `Q` with respect to `P` (`Q.rnDeriv P`) — no common dominating
measure. On the mutually-a.c. region this agrees with the density ratio `q/p`
(Strasser Example 1.4); the `npTest` proof below works over the `P+Q`
representation of the same object. Here we are trying to see if choices of dominating
measure matters -- but can be streamlined -/
noncomputable def lrStat (P Q : Measure Ω) : Ω → ℝ≥0∞ := Q.rnDeriv P

/-- The randomised **threshold test**, bundled as a `Test` via `npTest`. -/
noncomputable def thresholdTest (P Q : Measure Ω) (t η : ℝ≥0∞) (hη : η ≤ 1) : Test Ω where
  toFun := npTest P Q t η
  measurable := measurable_npTest P Q t η
  le_one := npTest_le_one P Q t η hη

end Statlib.Testing
