/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Statlib.Divergence.KullbackLeibler.Basic

/-!
# Pinsker's inequality

This file proves **Pinsker's inequality** `KL(μ ‖ ν) ≥ 2 TV(μ, ν)²` for probability measures on an
arbitrary measurable space, following Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to
Learning*, Cambridge University Press (2024), Theorem 7.10, equation (7.27). Logarithms are natural
(the KL divergence is in nats), so the factor `log e` of (7.27) is `1`.

## Conventions

Mathlib's total variation distance `tvDist μ ν` is the total variation **norm** of `μ - ν`, which
for probability measures is `2 * sup_E |μ E - ν E|`; Polyanskiy–Wu's `TV(P, Q) = sup_E |P E - Q E|`
(their (7.3) and Theorem 7.7) is therefore `tvDist μ ν / 2`. In Mathlib's convention Pinsker's
inequality reads `tvDist μ ν ^ 2 ≤ 2 * KL(μ ‖ ν)`. All statements below are for probability
measures; the `ℝ≥0∞`-valued forms need no finiteness assumption on `KL(μ ‖ ν)`.

## Main statements (book result → Lean name)

* Binary case (the display after (7.27), `d(p ‖ q) ≥ 2 (p - q)²` for `q ∈ (0, 1)`):
  `two_mul_sq_sub_le_mul_log_div_add_mul_log_div`.
* The reduction "`D(P ‖ Q) ≥ d(P(E) ‖ Q(E))`" in the proof of Theorem 7.10, combined with the binary
  case, for every measurable event `E`: `ofReal_two_mul_sq_measureReal_sub_le_klDiv` and its
  real form `abs_measureReal_sub_le_sqrt_toReal_klDiv_div_two`.
* Theorem 7.10, (7.27): `ofReal_sq_tvDist_le_two_mul_klDiv`, `sq_etvDist_le_two_mul_klDiv` (in
  `ℝ≥0∞`), `tvDist_le_sqrt_two_mul_toReal_klDiv` and, in Polyanskiy–Wu's normalization,
  `tvDist_div_two_le_sqrt_toReal_klDiv_div_two`.

## Implementation notes

Polyanskiy–Wu reduce to Bernoulli distributions by the data-processing inequality for the map
`x ↦ 1{x ∈ E}`. We obtain the same bound `D(P ‖ Q) ≥ d(P(E) ‖ Q(E))` without pushing forward to
`Bool`: the Kullback–Leibler divergence splits over `E` and `Eᶜ`
(`klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl`), and each piece is bounded below by the
log-sum inequality for its total masses (`InformationTheory.mul_log_le_klDiv`). The binary case is
proved by calculus in the second argument `q`: for fixed `p`, the derivative of
`q ↦ d(p ‖ q) - 2 (p - q)²` is `(q - p) (1 - 2q)² / (q (1 - q))`, so the function is minimal at
`q = p`, where it vanishes. (Polyanskiy–Wu use the integral form of Taylor's theorem in `p`
instead.) The event `E` used for the total variation distance is a Hahn decomposition of
`(μ, ν)` (`MeasureTheory.exists_isHahnDecomposition`).

## References

* Y. Polyanskiy, Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press
  (2024), Section 7.4; draft at https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf.
* M. S. Pinsker, *Information and Information Stability of Random Variables and Processes*,
  Holden-Day (1964).
-/

@[expose] public section

open Real MeasureTheory Set InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

/-- The function `t ↦ -p log t - (1 - p) log (1 - t) - 2 (p - t)²`, which differs from
`t ↦ d(p ‖ t) - 2 (p - t)²` by a constant. -/
private noncomputable def pinskerAux (p t : ℝ) : ℝ :=
  -(p * log t) - (1 - p) * log (1 - t) - 2 * (p - t) ^ 2

private lemma hasDerivAt_pinskerAux (p : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (pinskerAux p) ((t - p) * (1 - 2 * t) ^ 2 / (t * (1 - t))) t := by
  have ht : t ≠ 0 := ht0.ne'
  have ht1' : 1 - t ≠ 0 := by linarith
  have h1 : HasDerivAt log t⁻¹ t := hasDerivAt_log ht
  have h2 : HasDerivAt (fun s ↦ log (1 - s)) ((1 - t)⁻¹ * (0 - 1)) t :=
    (hasDerivAt_log ht1').comp t ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have h3 : HasDerivAt (fun s ↦ (p - s) ^ 2) (2 * (p - t) ^ 1 * (0 - 1)) t :=
    ((hasDerivAt_const t p).sub (hasDerivAt_id t)).pow 2
  refine (((h1.const_mul p).neg.sub (h2.const_mul (1 - p))).sub (h3.const_mul 2)).congr_deriv ?_
  field_simp
  ring

private lemma continuousOn_pinskerAux {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b : ℝ}
    (ha : p = 0 ∨ 0 < a) (hb : p = 1 ∨ b < 1) :
    ContinuousOn (pinskerAux p) (Icc a b) := by
  have h1 : ContinuousOn (fun t ↦ p * log t) (Icc a b) := by
    rcases ha with rfl | ha
    · simpa using continuousOn_const
    exact continuousOn_const.mul <| continuousOn_log.mono fun t ht ↦ (ha.trans_le ht.1).ne'
  have h2 : ContinuousOn (fun t ↦ (1 - p) * log (1 - t)) (Icc a b) := by
    rcases hb with rfl | hb
    · simpa using continuousOn_const
    refine continuousOn_const.mul <| continuousOn_log.comp (continuousOn_const.sub continuousOn_id)
      fun t ht ↦ ?_
    exact sub_ne_zero.mpr (ht.2.trans_lt hb).ne'
  exact (h1.neg.sub h2).sub
    (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 2))

/-- For fixed `p ∈ [0, 1]`, the function `pinskerAux p` on `(0, 1)` is minimal at `p`. -/
private lemma pinskerAux_self_le {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    pinskerAux p p ≤ pinskerAux p q := by
  have h_diff {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
      DifferentiableOn ℝ (pinskerAux p) (interior (Icc a b)) := by
    rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_pinskerAux p (ha.trans_lt ht.1) (ht.2.trans_le hb)).differentiableAt
      |>.differentiableWithinAt
  have h_deriv {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
      deriv (pinskerAux p) t = (t - p) * (1 - 2 * t) ^ 2 / (t * (1 - t)) :=
    (hasDerivAt_pinskerAux p ht0 ht1).deriv
  rcases le_total p q with hpq | hqp
  · -- `pinskerAux p` is nondecreasing on `[p, q]`
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q)
      (continuousOn_pinskerAux hp0 hp1 (hp0.eq_or_lt.imp Eq.symm id) (Or.inr hq1))
      (h_diff hp0 hq1.le) (fun t ht ↦ ?_) (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq) hpq
    rw [interior_Icc] at ht
    have ht0 : 0 < t := hp0.trans_lt ht.1
    have ht1 : t < 1 := ht.2.trans hq1
    rw [h_deriv ht0 ht1]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht.1.le) (sq_nonneg _))
      (mul_nonneg ht0.le (sub_nonneg.mpr ht1.le))
  · -- `pinskerAux p` is nonincreasing on `[q, p]`
    refine antitoneOn_of_deriv_nonpos (convex_Icc q p)
      (continuousOn_pinskerAux hp0 hp1 (Or.inr hq0) (hp1.eq_or_lt.imp id id))
      (h_diff hq0.le hp1) (fun t ht ↦ ?_) (left_mem_Icc.mpr hqp) (right_mem_Icc.mpr hqp) hqp
    rw [interior_Icc] at ht
    have ht0 : 0 < t := hq0.trans ht.1
    have ht1 : t < 1 := ht.2.trans_le hp1
    rw [h_deriv ht0 ht1]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.2.le) (sq_nonneg _))
      (mul_nonneg ht0.le (sub_nonneg.mpr ht1.le))

/-- `p log (p / q) = p log p - p log q` for `p ≥ 0` and `q > 0`, with `0 log 0 = 0`. -/
private lemma mul_log_div_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * log (p / q) = p * log p - p * log q := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  rw [log_div hp.ne' hq.ne', mul_sub]

/-- **Pinsker's inequality for Bernoulli distributions**: for `p ∈ [0, 1]` and `q ∈ (0, 1)`,
the binary Kullback–Leibler divergence
`d(p ‖ q) = p log (p / q) + (1 - p) log ((1 - p) / (1 - q))` is at least `2 (p - q)²`
(Polyanskiy–Wu, proof of Theorem 7.10). The hypothesis `q ∈ (0, 1)` avoids the conventions
`log 0 = 0` of `Real.log`; for `q ∈ {0, 1}` and `p ≠ q` the divergence is infinite. -/
theorem two_mul_sq_sub_le_mul_log_div_add_mul_log_div {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  have h := pinskerAux_self_le hp0 hp1 hq0 hq1
  rw [mul_log_div_eq hp0 hq0, mul_log_div_eq (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)]
  simp only [pinskerAux, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sub_zero] at h
  linarith

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Pinsker's inequality for an event**: for probability measures `μ, ν` and a measurable set
`s`, `2 (μ s - ν s)² ≤ KL(μ ‖ ν)`. This is the bound `D(P ‖ Q) ≥ d(P(E) ‖ Q(E)) ≥ 2 (P(E) - Q(E))²`
of the proof of Theorem 7.10 of Polyanskiy–Wu. -/
theorem ofReal_two_mul_sq_measureReal_sub_le_klDiv {s : Set α} (hs : MeasurableSet s) :
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) ≤ klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap
  · simp [klDiv_of_not_ac hac]
  set p := μ.real s with hp
  set q := ν.real s with hq
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hq1 : q ≤ 1 := measureReal_le_one
  -- the degenerate cases `q = 0` and `q = 1`, where absolute continuity forces `p = q`
  rcases (measureReal_nonneg : 0 ≤ q).eq_or_lt with hq0 | hq0
  · have hq0 : q = 0 := hq0.symm
    have hμ : p = 0 := (measureReal_eq_zero_iff).mpr (hac ((measureReal_eq_zero_iff).mp hq0))
    simp [hμ, hq0]
  rcases hq1.eq_or_lt with hq1 | hq1
  · have hν : ν sᶜ = 0 := by
      rw [← measureReal_eq_zero_iff, probReal_compl_eq_one_sub hs, ← hq, hq1, sub_self]
    have hμ : p = 1 := by
      have h := hac hν
      rw [← measureReal_eq_zero_iff, probReal_compl_eq_one_sub hs] at h
      rw [hp]
      linarith
    simp [hμ, hq1]
  -- the main case `q ∈ (0, 1)`
  calc ENNReal.ofReal (2 * (p - q) ^ 2)
      ≤ ENNReal.ofReal (p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))) :=
        ENNReal.ofReal_le_ofReal (two_mul_sq_sub_le_mul_log_div_add_mul_log_div hp0 hp1 hq0 hq1)
    _ = ENNReal.ofReal (((μ.restrict s).real univ
            * log ((μ.restrict s).real univ / (ν.restrict s).real univ)
            + (ν.restrict s).real univ - (μ.restrict s).real univ)
          + ((μ.restrict sᶜ).real univ
            * log ((μ.restrict sᶜ).real univ / (ν.restrict sᶜ).real univ)
            + (ν.restrict sᶜ).real univ - (μ.restrict sᶜ).real univ)) := by
        simp only [measureReal_restrict_apply_univ, probReal_compl_eq_one_sub hs, ← hp, ← hq]
        ring_nf
    _ ≤ _ := ENNReal.ofReal_add_le
    _ ≤ klDiv (μ.restrict s) (ν.restrict s) + klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) :=
        add_le_add (mul_log_le_klDiv _ _) (mul_log_le_klDiv _ _)
    _ = klDiv μ ν :=
        (ProbabilityTheory.klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl μ ν hs).symm

/-- **Pinsker's inequality for an event**, real form: if `KL(μ ‖ ν) < ∞`, then
`|μ s - ν s| ≤ √(KL(μ ‖ ν) / 2)` for every measurable set `s`. -/
theorem abs_measureReal_sub_le_sqrt_toReal_klDiv_div_two (h : klDiv μ ν ≠ ∞) {s : Set α}
    (hs : MeasurableSet s) :
    |μ.real s - ν.real s| ≤ √((klDiv μ ν).toReal / 2) := by
  have h' := ofReal_two_mul_sq_measureReal_sub_le_klDiv (μ := μ) (ν := ν) hs
  rw [ENNReal.ofReal_le_iff_le_toReal h] at h'
  rw [← sqrt_sq_eq_abs]
  exact sqrt_le_sqrt (by linarith)

/-- For probability measures, the total variation norm `tvDist μ ν` is twice `ν s - μ s` for a Hahn
decomposition `s` of `(μ, ν)`. -/
private lemma tvDist_eq_two_mul_of_isHahnDecomposition {s : Set α}
    (hs : IsHahnDecomposition μ ν s) :
    tvDist μ ν = 2 * (ν.real s - μ.real s) := by
  rw [hs.tvDist_eq, probReal_compl_eq_one_sub hs.measurableSet,
    probReal_compl_eq_one_sub hs.measurableSet]
  ring

/-- **Pinsker's inequality** (Polyanskiy–Wu, Theorem 7.10, (7.27)), in `ℝ≥0∞`:
`tvDist μ ν ² ≤ 2 KL(μ ‖ ν)` for probability measures, where Mathlib's `tvDist μ ν` is twice the
`TV(μ, ν) = sup_E |μ E - ν E|` of Polyanskiy–Wu; that is, `KL(μ ‖ ν) ≥ 2 TV(μ, ν)²`. -/
theorem ofReal_sq_tvDist_le_two_mul_klDiv :
    ENNReal.ofReal (tvDist μ ν ^ 2) ≤ 2 * klDiv μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h := ofReal_two_mul_sq_measureReal_sub_le_klDiv (μ := μ) (ν := ν) hs.measurableSet
  calc ENNReal.ofReal (tvDist μ ν ^ 2)
      = 2 * ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) := by
        rw [tvDist_eq_two_mul_of_isHahnDecomposition hs, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul zero_le_two]
        ring_nf
    _ ≤ 2 * klDiv μ ν := by gcongr

/-- **Pinsker's inequality** (Polyanskiy–Wu, Theorem 7.10, (7.27)), for the `ℝ≥0∞`-valued total
variation norm: `etvDist μ ν ^ 2 ≤ 2 * KL(μ ‖ ν)` for probability measures. -/
theorem sq_etvDist_le_two_mul_klDiv : etvDist μ ν ^ 2 ≤ 2 * klDiv μ ν := by
  rw [← ofReal_tvDist, ← ENNReal.ofReal_pow tvDist_nonneg]
  exact ofReal_sq_tvDist_le_two_mul_klDiv

/-- **Pinsker's inequality** (Polyanskiy–Wu, Theorem 7.10, (7.27)), real form for Mathlib's total
variation norm: if `KL(μ ‖ ν) < ∞`, then `tvDist μ ν ≤ √(2 KL(μ ‖ ν))`. -/
theorem tvDist_le_sqrt_two_mul_toReal_klDiv (h : klDiv μ ν ≠ ∞) :
    tvDist μ ν ≤ √(2 * (klDiv μ ν).toReal) := by
  have h' := ofReal_sq_tvDist_le_two_mul_klDiv (μ := μ) (ν := ν)
  rw [ENNReal.ofReal_le_iff_le_toReal (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofNat] at h'
  exact le_sqrt_of_sq_le h'

/-- **Pinsker's inequality** (Polyanskiy–Wu, Theorem 7.10, (7.27)), in Polyanskiy–Wu's
normalization `TV(μ, ν) = tvDist μ ν / 2 = sup_E |μ E - ν E|`: if `KL(μ ‖ ν) < ∞`, then
`TV(μ, ν) ≤ √(KL(μ ‖ ν) / 2)`. -/
theorem tvDist_div_two_le_sqrt_toReal_klDiv_div_two (h : klDiv μ ν ≠ ∞) :
    tvDist μ ν / 2 ≤ √((klDiv μ ν).toReal / 2) := by
  have h' := tvDist_le_sqrt_two_mul_toReal_klDiv h
  have h4 : √(2 * (klDiv μ ν).toReal) = 2 * √((klDiv μ ν).toReal / 2) := by
    rw [show 2 * (klDiv μ ν).toReal = 2 ^ 2 * ((klDiv μ ν).toReal / 2) by ring,
      sqrt_mul (by positivity), sqrt_sq zero_le_two]
  linarith

end ProbabilityTheory
