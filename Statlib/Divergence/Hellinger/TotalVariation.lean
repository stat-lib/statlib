/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.BretagnolleHuber
public import Statlib.Divergence.Hellinger.Renyi

/-!
# Hellinger divergences and total variation distance

We compare the squared Hellinger distance `H²(μ, ν) = sqHellinger μ ν` with the total variation
distance, deduce bounds on the total variation distance in terms of the Rényi divergence of order
`1/2`, and prove a Bretagnolle-Huber inequality for the Hellinger divergences. Mathlib's
`tvDist μ ν` is the total variation norm of `μ - ν`, which for probability measures is twice the
distance `TV(μ, ν) = sup_E |μ E - ν E|`.

## Main statements

* `two_mul_sqHellinger_le_etvDist`, `toReal_sqHellinger_le_tvDist_div_two`:
  `2 * H²(μ, ν) ≤ ‖μ - ν‖`, that is `H²(μ, ν) ≤ TV(μ, ν)` for probability measures.
* `tvDist_sq_le_four_mul_sqHellinger_mul`: for finite measures,
  `‖μ - ν‖ ^ 2 ≤ 4 * H²(μ, ν) * (μ(X) + ν(X) - H²(μ, ν))`.
* `tvDist_div_two_le_sqrt_sqHellinger_mul`: for probability measures,
  `TV(μ, ν) ≤ √(H²(μ, ν) * (2 - H²(μ, ν)))`.
* `one_sub_sqHellinger_sq_le`, `one_sub_sqrt_le_one_sub_tvDist_div_two`: corollaries of the
  previous inequality.
* `one_sub_tvDist_div_two_le_exp`, `exp_neg_div_two_le_one_sub_tvDist_div_two`: for probability
  measures, `exp (-R_{1/2}(μ, ν)) / 2 ≤ 1 - TV(μ, ν) ≤ exp (-R_{1/2}(μ, ν) / 2)`, the lower bound
  if the measures are not mutually singular.
* `ofReal_rpow_one_sub_tvDist_div_two_le_hellingerDiv`: a **Bretagnolle-Huber** type inequality
  for the Hellinger divergence of order `1 + a`, `H_{1+a}(μ, ν) ≥ ((1 - TV(μ, ν)) ^ (-a) - 2) / a`.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer (2009), Section 2.4.
-/

@[expose] public section

open Real MeasureTheory Set Filter

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- The divergence function of the Hellinger divergence of order `1/2`, `x ↦ (1 - √x) ^ 2`, is
bounded by the divergence function `x ↦ |1 - x|` of the total variation distance. -/
lemma hellingerDivFun_inv_two_le_tvDivFun (x : ℝ≥0∞) :
    hellingerDivFun 2⁻¹ x ≤ tvDivFun x := by
  by_cases hx : x = ∞
  · simp [hx]
  rw [hellingerDivFun_apply_of_pos_of_ne_one (by norm_num) (by norm_num) hx, tvDivFun_apply hx]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `(1 - √x) ^ 2 ≤ |1 - √x| * (1 + √x) = |1 - x|`
  have hy : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  rw [show x.toReal ^ (2⁻¹ : ℝ) = √x.toReal by rw [Real.sqrt_eq_rpow, one_div]]
  have hs := Real.sq_sqrt hy
  have hs_nonneg := Real.sqrt_nonneg x.toReal
  rcases le_total x.toReal 1 with h1 | h1
  · have hs1 : √x.toReal ≤ 1 := Real.sqrt_le_one.mpr h1
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  · have hs1 : 1 ≤ √x.toReal := Real.one_le_sqrt.mpr h1
    rw [abs_of_nonpos (by linarith)]
    nlinarith

/-- The Hellinger divergence of order `1/2` is bounded by the total variation norm. If one of the
measures is not finite, `etvDist μ ν = ∞`. -/
theorem hellingerDiv_inv_two_le_etvDist (μ ν : Measure α) :
    hellingerDiv 2⁻¹ μ ν ≤ etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · have := h.1
    have := h.2
    rw [hellingerDiv, ← fDiv_tvDivFun]
    exact fDiv_mono hellingerDivFun_inv_two_le_tvDivFun
  · simp [etvDist_of_not_isFiniteMeasure h]

/-- `2 * H²(μ, ν) ≤ ‖μ - ν‖`. For probability measures, this is `H²(μ, ν) ≤ TV(μ, ν)` with
`TV(μ, ν) = tvDist μ ν / 2`. -/
theorem two_mul_sqHellinger_le_etvDist (μ ν : Measure α) :
    2 * sqHellinger μ ν ≤ etvDist μ ν := by
  rw [two_mul_sqHellinger]
  exact hellingerDiv_inv_two_le_etvDist μ ν

/-- For finite measures, `H²(μ, ν) ≤ ‖μ - ν‖ / 2`. For probability measures, this is
`H²(μ, ν) ≤ TV(μ, ν)` with `TV(μ, ν) = tvDist μ ν / 2`. -/
theorem toReal_sqHellinger_le_tvDist_div_two (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    (sqHellinger μ ν).toReal ≤ tvDist μ ν / 2 := by
  have h := two_mul_sqHellinger_le_etvDist μ ν
  rw [← ofReal_tvDist, ← ENNReal.ofReal_toReal (sqHellinger_ne_top μ ν), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_ofReal_iff tvDist_nonneg] at h
  linarith

/-- For finite measures, `‖μ - ν‖ ^ 2 ≤ 4 * H²(μ, ν) * (μ(X) + ν(X) - H²(μ, ν))`.
See `tvDist_div_two_sq_le_sqHellinger_mul` for the version for probability measures. -/
theorem tvDist_sq_le_four_mul_sqHellinger_mul (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν ^ 2 ≤ 4 * (sqHellinger μ ν).toReal
      * (μ.real univ + ν.real univ - (sqHellinger μ ν).toReal) := by
  -- Write `r = ∂μ/∂ν`, `s` for the mass of the singular part, `c = μ(X) + ν(X)` and
  -- `I = ∫ √r ∂ν = c / 2 - H²(μ, ν)`. Then `tvDist μ ν = ∫ |1 - √r| (1 + √r) ∂ν + s`, and we apply
  -- the Cauchy-Schwarz inequality to the integral, with `∫ (1 ± √r) ^ 2 ∂ν = c ± 2 * I - s`.
  set r : α → ℝ := fun x ↦ ((∂μ/∂ν) x).toReal with hr_def
  set s := (μ.singularPart ν).real univ
  set I := ∫ x, √(r x) ∂ν
  have hr_nonneg (x : α) : 0 ≤ r x := ENNReal.toReal_nonneg
  have hs_nonneg : 0 ≤ s := measureReal_nonneg
  have hr_int : Integrable r ν := Measure.integrable_toReal_rnDeriv
  have hsqrt_int : Integrable (fun x ↦ √(r x)) ν := by
    simp_rw [hr_def, Real.sqrt_eq_rpow, one_div]
    exact integrable_rpow_rnDeriv_of_lt_one (by norm_num) (by norm_num)
  have h_tv : tvDist μ ν = ∫ x, |1 - r x| ∂ν + s :=
    tvDist_eq_integral_abs_rnDeriv_add_singularPart
  have h_int_r : ∫ x, r x ∂ν = μ.real univ - s := Measure.integral_toReal_rnDeriv'
  have h_hI : (sqHellinger μ ν).toReal = 2⁻¹ * (μ.real univ + ν.real univ) - I :=
    toReal_sqHellinger_eq_integral
  -- integrals of `(1 - √r) ^ 2` and `(1 + √r) ^ 2`
  have h_sub_sq : (fun x ↦ (1 - √(r x)) ^ 2) = fun x ↦ 1 - 2 * √(r x) + r x := by
    ext x; rw [sub_sq, Real.sq_sqrt (hr_nonneg x)]; ring
  have h_add_sq : (fun x ↦ (1 + √(r x)) ^ 2) = fun x ↦ 1 + 2 * √(r x) + r x := by
    ext x; rw [add_sq, Real.sq_sqrt (hr_nonneg x)]; ring
  have h_int_sub : Integrable (fun x ↦ 1 - 2 * √(r x)) ν :=
    (integrable_const 1).sub (hsqrt_int.const_mul 2)
  have h_int_add : Integrable (fun x ↦ 1 + 2 * √(r x)) ν :=
    (integrable_const 1).add (hsqrt_int.const_mul 2)
  have hA : ∫ x, (1 - √(r x)) ^ 2 ∂ν = μ.real univ + ν.real univ - 2 * I - s := by
    rw [h_sub_sq, integral_add h_int_sub hr_int,
      integral_sub (integrable_const 1) (hsqrt_int.const_mul 2), integral_const_mul, h_int_r,
      integral_const, smul_eq_mul, mul_one]
    ring
  have hB : ∫ x, (1 + √(r x)) ^ 2 ∂ν = μ.real univ + ν.real univ + 2 * I - s := by
    rw [h_add_sq, integral_add h_int_add hr_int,
      integral_add (integrable_const 1) (hsqrt_int.const_mul 2), integral_const_mul, h_int_r,
      integral_const, smul_eq_mul, mul_one]
    ring
  -- Cauchy-Schwarz inequality
  have h_abs (x : α) : |1 - r x| = |1 - √(r x)| * (1 + √(r x)) := by
    have hs := Real.sq_sqrt (hr_nonneg x)
    rw [show 1 - r x = (1 - √(r x)) * (1 + √(r x)) by nlinarith, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 1 + √(r x))]
  have h_meas : AEStronglyMeasurable (fun x ↦ √(r x)) ν := hsqrt_int.aestronglyMeasurable
  have h_CS : ∫ x, |1 - r x| ∂ν
      ≤ √(∫ x, (1 - √(r x)) ^ 2 ∂ν) * √(∫ x, (1 + √(r x)) ^ 2 ∂ν) := by
    simp_rw [h_abs]
    have h_meas_sub : AEStronglyMeasurable (fun x ↦ |1 - √(r x)|) ν :=
      continuous_abs.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub h_meas)
    have h_meas_add : AEStronglyMeasurable (fun x ↦ 1 + √(r x)) ν :=
      aestronglyMeasurable_const.add h_meas
    have hf : MemLp (fun x ↦ |1 - √(r x)|) (ENNReal.ofReal 2) ν := by
      rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq h_meas_sub]
      simp_rw [sq_abs, h_sub_sq]
      exact h_int_sub.add hr_int
    have hg : MemLp (fun x ↦ 1 + √(r x)) (ENNReal.ofReal 2) ν := by
      rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq h_meas_add, h_add_sq]
      exact h_int_add.add hr_int
    refine (integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun _ ↦ abs_nonneg _) (ae_of_all _ fun _ ↦ by positivity) hf hg).trans_eq ?_
    simp_rw [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  -- with `A = c - 2 * I - s` and `B = c + 2 * I - s`, `tvDist μ ν ≤ √A * √B + s` and
  -- `(√A * √B + s) ^ 2 ≤ (A + s) * (B + s) = c ^ 2 - 4 * I ^ 2`
  rw [hA, hB] at h_CS
  set A := μ.real univ + ν.real univ - 2 * I - s
  set B := μ.real univ + ν.real univ + 2 * I - s
  have hA_nonneg : 0 ≤ A := by
    rw [← hA]; exact integral_nonneg fun _ ↦ sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    rw [← hB]; exact integral_nonneg fun _ ↦ sq_nonneg _
  have h_le : tvDist μ ν ≤ √A * √B + s := by linarith
  have ha := Real.sq_sqrt hA_nonneg
  have hb := Real.sq_sqrt hB_nonneg
  have ha' := Real.sqrt_nonneg A
  have hb' := Real.sqrt_nonneg B
  have h_sq : (√A * √B + s) ^ 2 ≤ (A + s) * (B + s) := by
    nlinarith [sq_nonneg (√A - √B), mul_nonneg hs_nonneg (sq_nonneg (√A - √B))]
  have key := (pow_le_pow_left₀ tvDist_nonneg h_le 2).trans h_sq
  rw [h_hI]
  linear_combination key

/-- For probability measures, `TV(μ, ν) ^ 2 ≤ H²(μ, ν) * (2 - H²(μ, ν))`, where
`TV(μ, ν) = tvDist μ ν / 2`. -/
theorem tvDist_div_two_sq_le_sqHellinger_mul [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (tvDist μ ν / 2) ^ 2 ≤ (sqHellinger μ ν).toReal * (2 - (sqHellinger μ ν).toReal) := by
  have h := tvDist_sq_le_four_mul_sqHellinger_mul μ ν
  simp only [probReal_univ] at h
  linear_combination h / 4

/-- For probability measures, `TV(μ, ν) ≤ √(H²(μ, ν) * (2 - H²(μ, ν)))`, where
`TV(μ, ν) = tvDist μ ν / 2`. -/
theorem tvDist_div_two_le_sqrt_sqHellinger_mul [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    tvDist μ ν / 2 ≤ √((sqHellinger μ ν).toReal * (2 - (sqHellinger μ ν).toReal)) :=
  Real.le_sqrt_of_sq_le tvDist_div_two_sq_le_sqHellinger_mul

/-- For probability measures, `(1 - H²(μ, ν)) ^ 2 / 2 ≤ 1 - TV(μ, ν) - (1 - TV(μ, ν)) ^ 2 / 2`,
where `TV(μ, ν) = tvDist μ ν / 2`. -/
theorem one_sub_sqHellinger_sq_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2⁻¹ * (1 - (sqHellinger μ ν).toReal) ^ 2
      ≤ 1 - tvDist μ ν / 2 - 2⁻¹ * (1 - tvDist μ ν / 2) ^ 2 := by
  have h := tvDist_div_two_sq_le_sqHellinger_mul (μ := μ) (ν := ν)
  nlinarith

/-- For probability measures, `1 - √(1 - (1 - H²(μ, ν)) ^ 2) ≤ 1 - TV(μ, ν)`, where
`TV(μ, ν) = tvDist μ ν / 2`. -/
theorem one_sub_sqrt_le_one_sub_tvDist_div_two [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    1 - √(1 - (1 - (sqHellinger μ ν).toReal) ^ 2) ≤ 1 - tvDist μ ν / 2 := by
  have h := tvDist_div_two_le_sqrt_sqHellinger_mul (μ := μ) (ν := ν)
  rw [show 1 - (1 - (sqHellinger μ ν).toReal) ^ 2
    = (sqHellinger μ ν).toReal * (2 - (sqHellinger μ ν).toReal) by ring]
  linarith

/-! ### Total variation distance and Rényi divergence of order `1/2` -/

/-- For probability measures, `1 - TV(μ, ν) ≤ exp (-R_{1/2}(μ, ν) / 2)`, where
`TV(μ, ν) = tvDist μ ν / 2`. If the measures are mutually singular, `R_{1/2}(μ, ν) = ∞` and
the right-hand side is `1` since `ENNReal.toReal ∞ = 0`. -/
theorem one_sub_tvDist_div_two_le_exp [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    1 - tvDist μ ν / 2 ≤ exp (-(renyiDiv 2⁻¹ μ ν).toReal / 2) := by
  by_cases h_ms : μ ⟂ₘ ν
  · rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)).mpr h_ms]
    simpa using div_nonneg tvDist_nonneg zero_le_two
  rw [exp_neg_toReal_renyiDiv_inv_two_div_two h_ms]
  exact sub_le_sub_left (toReal_sqHellinger_le_tvDist_div_two _ _) 1

/-- For probability measures which are not mutually singular,
`1 - √(1 - exp (-R_{1/2}(μ, ν))) ≤ 1 - TV(μ, ν)`, where `TV(μ, ν) = tvDist μ ν / 2`. -/
theorem one_sub_sqrt_one_sub_exp_le_one_sub_tvDist_div_two [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h_ms : ¬ μ ⟂ₘ ν) :
    1 - √(1 - exp (-(renyiDiv 2⁻¹ μ ν).toReal)) ≤ 1 - tvDist μ ν / 2 := by
  have h_sq : exp (-(renyiDiv 2⁻¹ μ ν).toReal) = (1 - (sqHellinger μ ν).toReal) ^ 2 := by
    rw [← exp_neg_toReal_renyiDiv_inv_two_div_two h_ms, ← exp_natCast_mul]
    congr 1
    ring
  rw [h_sq]
  exact one_sub_sqrt_le_one_sub_tvDist_div_two

/-- For probability measures which are not mutually singular,
`exp (-R_{1/2}(μ, ν)) / 2 ≤ 1 - TV(μ, ν)`, where `TV(μ, ν) = tvDist μ ν / 2`. -/
theorem exp_neg_div_two_le_one_sub_tvDist_div_two [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h_ms : ¬ μ ⟂ₘ ν) :
    exp (-(renyiDiv 2⁻¹ μ ν).toReal) / 2 ≤ 1 - tvDist μ ν / 2 := by
  refine le_trans ?_ (one_sub_sqrt_one_sub_exp_le_one_sub_tvDist_div_two h_ms)
  -- `√(1 - x) ≤ 1 - x / 2` for `x = exp (-R_{1/2}(μ, ν)) ≤ 1`
  set x := exp (-(renyiDiv 2⁻¹ μ ν).toReal)
  have hx : x ≤ 1 := by
    rw [exp_le_one_iff, neg_nonpos]
    positivity
  have h_sqrt : √(1 - x) ≤ 1 - x / 2 := by
    simpa [← sub_eq_add_neg, neg_div] using sqrt_one_add_le (x := -x) (by linarith)
  linarith

/-! ### A Bretagnolle-Huber inequality for the Hellinger divergence -/

/-- **Bretagnolle-Huber inequality for the Hellinger divergence**: for probability measures and
`0 < a`, `H_{1+a}(μ, ν) ≥ ((1 - TV(μ, ν)) ^ (-a) - 2) / a`, where `TV(μ, ν) = tvDist μ ν / 2`.
If `TV(μ, ν) = 1`, the left-hand side is `0` since `0 ^ (-a) = 0` for real powers. -/
theorem ofReal_rpow_one_sub_tvDist_div_two_le_hellingerDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (((1 - tvDist μ ν / 2) ^ (-a) - 2) / a) ≤ hellingerDiv (1 + a) μ ν := by
  set t := tvDist μ ν / 2 with ht
  have ht_nonneg : 0 ≤ t := by positivity [tvDist_nonneg (μ := μ) (ν := ν)]
  have ht_le : t ≤ 1 := by
    have := tvDist_le_add (μ := μ) (ν := ν)
    simp only [probReal_univ] at this
    linarith
  rcases ht_le.lt_or_eq with ht_lt | ht_eq
  swap
  · rw [ht_eq, sub_self, Real.zero_rpow (by linarith), zero_sub,
      ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) ha.le)]
    exact zero_le
  have h := conj_one_add_etvDist_div_two_add_conj_one_sub_le_fDiv
    (f := hellingerDivFun (1 + a)) μ ν
  have hT : etvDist μ ν / 2 = ENNReal.ofReal t := by
    rw [ht, ← ofReal_tvDist, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [hT, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one ht_nonneg,
    ← ENNReal.ofReal_sub _ ht_nonneg,
    conj_hellingerDivFun_ofReal (by linarith) (by linarith) (by linarith),
    conj_hellingerDivFun_ofReal (by linarith) (by linarith) (by linarith),
    add_sub_cancel_left, sub_add_cancel_left] at h
  refine le_trans ?_ (ENNReal.ofReal_add_le.trans h)
  refine ENNReal.ofReal_le_ofReal ?_
  -- the right-hand side is `((1 + t) ^ (-a) + (1 - t) ^ (-a) - 2) / a`
  have h_pos : 0 ≤ (1 + t) ^ (-a) := by positivity
  rw [div_eq_inv_mul]
  have ha_inv : 0 < a⁻¹ := inv_pos.mpr ha
  nlinarith

/-- **Bretagnolle-Huber inequality for the Hellinger divergence**, real version: for probability
measures and `0 < a` with `H_{1+a}(μ, ν) < ∞`,
`(1 - TV(μ, ν)) ^ (-a) ≤ 2 + a * H_{1+a}(μ, ν)`, where `TV(μ, ν) = tvDist μ ν / 2`. -/
theorem rpow_one_sub_tvDist_div_two_le_two_add_hellingerDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ} (ha : 0 < a) (h_top : hellingerDiv (1 + a) μ ν ≠ ∞) :
    (1 - tvDist μ ν / 2) ^ (-a) ≤ 2 + a * (hellingerDiv (1 + a) μ ν).toReal := by
  have h := ofReal_rpow_one_sub_tvDist_div_two_le_hellingerDiv (μ := μ) (ν := ν) ha
  rw [ENNReal.ofReal_le_iff_le_toReal h_top, div_le_iff₀ ha] at h
  linarith

end ProbabilityTheory
