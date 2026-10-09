/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib

/-!
# Convolution of Gamma distributions

The key analytic fact behind the compound-Poisson construction of the Tweedie
distribution: the convolution of two Gamma measures with the **same rate** `r`
is again a Gamma measure, with the shape parameters added:
`Gamma(a, r) ∗ Gamma(b, r) = Gamma(a + b, r)`.

This is the statement that the sum of two independent Gamma random variables with
the same rate is Gamma distributed.
-/

open MeasureTheory ProbabilityTheory Measure Real
open scoped ENNReal NNReal

namespace GammaConv

/-
The real Beta integral over `[0,1]`, expressed via the Gamma function.
-/
lemma real_betaIntegral_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0:ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1)
      = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  rw [mul_comm, eq_div_iff]
  · have h_beta : (∫ t in (0 : ℝ)..1, t^(a - 1) * (1 - t)^(b - 1))
      = Complex.betaIntegral (a : ℂ) (b : ℂ) := by
      convert intervalIntegral.integral_ofReal.symm using 1
      convert intervalIntegral.integral_congr fun x hx => ?_ using 1
      norm_num [Complex.ofReal_cpow, show 0 ≤ x by aesop, show x ≤ 1 by aesop]
    have := @Complex.Gamma_mul_Gamma_eq_betaIntegral (a : ℂ) (b : ℂ) ?_ ?_ <;> norm_cast at *
    rw [← Complex.ofReal_inj]
    simp_all only [Complex.ofReal_add, mul_comm, Complex.ofReal_mul]
    rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]; norm_cast at *
    aesop
  · positivity

/-- Real Beta integral: `∫_0^z x^(a-1) (z-x)^(b-1) dx = z^(a+b-1) * Γ a * Γ b / Γ (a+b)`
for `a, b > 0` and `z > 0`. Proved by the substitution `x = z t`. -/
lemma integral_rpow_mul_rpow_sub (a b : ℝ) (ha : 0 < a) (hb : 0 < b) {z : ℝ} (hz : 0 < z) :
    ∫ x in (0:ℝ)..z, x ^ (a - 1) * (z - x) ^ (b - 1)
      = z ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := z)
    (fun x => x ^ (a - 1) * (z - x) ^ (b - 1)) hz.ne'
  simp only [mul_zero, mul_one] at h
  have h_subst : ∫ x in (0:ℝ)..z, x ^ (a - 1) * (z - x) ^ (b - 1)
      = ∫ t in (0:ℝ)..1, (z * t) ^ (a - 1) * (z - z * t) ^ (b - 1) * z := by
    have hg : ∫ t in (0:ℝ)..1, (z * t) ^ (a - 1) * (z - z * t) ^ (b - 1) * z
        = z * ∫ t in (0:ℝ)..1, (z * t) ^ (a - 1) * (z - z * t) ^ (b - 1) := by
      rw [← intervalIntegral.integral_const_mul]; apply intervalIntegral.integral_congr
      intro x hx; ring
    rw [hg, h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hz.ne', one_mul]
  have h_simplify : ∫ t in (0:ℝ)..1, (z * t) ^ (a - 1) * (z - z * t) ^ (b - 1) * z
    = z^(a - 1) * z^(b - 1) * z * ∫ t in (0:ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    simp only
    rw [Real.mul_rpow hz.le ht0, show z - z * t = z * (1 - t) by ring,
      Real.mul_rpow hz.le (by linarith)]
    ring
  rw [h_subst, h_simplify, real_betaIntegral_eq a b ha hb]
  rw [show z ^ (a - 1) * z ^ (b - 1) * z = z ^ (a + b - 1) by
    rw [← Real.rpow_add hz, ← Real.rpow_add_one hz.ne']; ring_nf]

/-
Convolution identity for gamma densities (real, pointwise) for `z > 0`.
-/
lemma gamma_density_conv (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) {z : ℝ} (hz : 0 < z) :
    ∫ x in (0:ℝ)..z, gammaPDFReal a r x * gammaPDFReal b r (z - x)
      = gammaPDFReal (a + b) r z := by
  rw [intervalIntegral.integral_of_le hz.le]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  convert congr_arg (fun x : ℝ => (r ^ a / Real.Gamma a) * (r ^ b / Real.Gamma b)
    * Real.exp (- (r * z)) * x) (integral_rpow_mul_rpow_sub a b ha hb hz) using 1
  · rw [intervalIntegral.integral_of_le hz.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [gammaPDFReal, gammaPDFReal]
    rw [if_pos hx.1.le, if_pos (by linarith [hx.2])]
    rw [show - (r * z) = - (r * x) + (r * x - r * z) by ring]; rw [Real.exp_add]
    ring_nf
  · unfold gammaPDFReal; rw [if_pos hz.le]
    ring_nf
    rw [Real.rpow_add hr]
    norm_num [ne_of_gt (Real.Gamma_pos_of_pos ha), ne_of_gt (Real.Gamma_pos_of_pos hb)]; ring

/-
The pointwise convolution of the gamma densities, at the level of `lintegral` over all of
`ℝ` w.r.t. Lebesgue measure.
-/
lemma gammaPDF_conv_inner (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) {z : ℝ} (hz : 0 < z) :
    ∫⁻ x, gammaPDF a r x * gammaPDF b r (z - x) ∂volume = gammaPDF (a + b) r z := by
  unfold gammaPDF
  norm_num [← ENNReal.ofReal_mul, gammaPDFReal]
  -- Apply the convolution identity for gamma densities.
  have h_conv : ∫ x in Set.Ioo 0 z, (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)))
    * (r ^ b / Real.Gamma b * (z - x) ^ (b - 1) * Real.exp (-(r * (z - x))))
    = r ^ (a + b) / Real.Gamma (a + b) * z ^ (a + b - 1) * Real.exp (-(r * z)) := by
    convert congr_arg (fun x : ℝ => x * (r ^ a / Real.Gamma a) * (r ^ b / Real.Gamma b)
      * Real.exp (- (r * z))) (integral_rpow_mul_rpow_sub a b ha hb hz) using 1
      <;> ring_nf
    · rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hz.le]
      norm_num [mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add]; ring_nf
      exact Or.inl <| Or.inl <| by rw [← intervalIntegral.integral_const_mul]; congr; ext; ring_nf
    · rw [Real.rpow_add hr]
      ring_nf
      norm_num [mul_assoc, mul_comm, mul_left_comm, ne_of_gt (Real.Gamma_pos_of_pos ha),
        ne_of_gt (Real.Gamma_pos_of_pos hb)]
  rw [← h_conv, if_pos hz.le, MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · rw [← MeasureTheory.lintegral_indicator] <;> norm_num [Set.indicator]
    rw [← MeasureTheory.lintegral_congr_ae]
    filter_upwards [
      MeasureTheory.measure_eq_zero_iff_ae_notMem.1 (MeasureTheory.measure_singleton 0),
      MeasureTheory.measure_eq_zero_iff_ae_notMem.1 (MeasureTheory.measure_singleton z)]
      with x hx₁ hx₂
    split_ifs
    · rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hr.le _)
        (Real.Gamma_nonneg_of_nonneg ha.le)) (Real.rpow_nonneg (by linarith) _))
        (Real.exp_nonneg _))]
    · linarith
    · linarith
    · grind
    · grind
    · simp_all
    · simp_all
    · simp_all
  · exact (by contrapose! h_conv; rw [MeasureTheory.integral_undef h_conv]; positivity)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx using mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hx.1.le _)) (Real.exp_nonneg _))
      (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (sub_nonneg.2 hx.2.le) _))
      (Real.exp_nonneg _))

/-
The convolution of two gamma measures with the same rate `r` is a gamma measure with
the shapes added.
-/
theorem gammaMeasure_conv (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    (gammaMeasure a r) ∗ (gammaMeasure b r) = gammaMeasure (a + b) r := by
  -- By definition of gamma measure, we know that
  have h_gamma_def : ∀ c r : ℝ, 0 < c → 0 < r → gammaMeasure c r
    = volume.withDensity (fun x => gammaPDF c r x) := by
    aesop
  -- Apply the equality of measures to rewrite the goal in terms of densities.
  suffices h_conv : ∀ {g : ℝ → ENNReal}, Measurable g → ∫⁻ z, g z ∂(volume.withDensity
    (fun x => gammaPDF a r x) ∗ volume.withDensity (fun x => gammaPDF b r x))
    = ∫⁻ z, g z * gammaPDF (a + b) r z ∂volume by
    ext s hs; specialize @h_conv (Set.indicator s 1)
    simp_all only [Set.indicator, Pi.one_apply, ite_mul, one_mul, zero_mul]
    convert h_conv (measurable_const.indicator hs) using 1
    · erw [MeasureTheory.lintegral_indicator hs]; aesop
    · rw [h_gamma_def _ _ (add_pos ha hb) hr, MeasureTheory.withDensity_apply _ hs]
      rw [← MeasureTheory.lintegral_indicator] <;> norm_num [Set.indicator, hs]
  intro g hg
  have h_conv : ∫⁻ z, g z ∂(volume.withDensity (fun x => gammaPDF a r x) ∗ volume.withDensity
    (fun x => gammaPDF b r x))
    = ∫⁻ x, ∫⁻ y, g (x + y) * gammaPDF b r y * gammaPDF a r x ∂volume ∂volume := by
    rw [MeasureTheory.Measure.lintegral_conv]
    · rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul]
      · simp only [Pi.mul_apply, mul_comm, mul_left_comm]
        congr! 1
        ext x
        rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul]
        · simp only [Pi.mul_apply, mul_comm]
          · rw [← MeasureTheory.lintegral_const_mul']
            · congr; ext; ring
            · exact ENNReal.ofReal_ne_top
        · exact Measurable.ennreal_ofReal (measurable_gammaPDFReal b r)
        · exact hg.comp (measurable_const.add measurable_id')
      · exact Measurable.ennreal_ofReal (ProbabilityTheory.measurable_gammaPDFReal a r)
      · refine Measurable.lintegral_prod_right ?_
        exact hg.comp (measurable_fst.add measurable_snd)
    · exact hg
  -- By Fubini's theorem, we can interchange the order of integration.
  have h_fubini : ∫⁻ x, ∫⁻ y, g (x + y) * gammaPDF b r y * gammaPDF a r x ∂volume ∂volume
    = ∫⁻ y, ∫⁻ x, g y * gammaPDF b r (y - x) * gammaPDF a r x ∂volume ∂volume := by
    have h_fubini : ∀ x, ∫⁻ y, g (x + y) * gammaPDF b r y * gammaPDF a r x ∂volume
      = ∫⁻ y, g y * gammaPDF b r (y - x) * gammaPDF a r x ∂volume := by
      intro x; rw [← MeasureTheory.lintegral_sub_right_eq_self _ x]; congr; ext y; ring_nf
    rw [funext h_fubini, MeasureTheory.lintegral_lintegral_swap]
    refine AEMeasurable.mul ?_ ?_
    · refine AEMeasurable.mul ?_ ?_
      · exact hg.aemeasurable.comp_aemeasurable (measurable_snd.aemeasurable)
      · refine Measurable.aemeasurable ?_
        refine Measurable.ennreal_ofReal ?_
        fun_prop
    · refine Measurable.aemeasurable ?_
      exact (measurable_gammaPDFReal a r |> Measurable.comp <| measurable_fst).ennreal_ofReal
  -- By the properties of the gamma function, we know that
  -- $\int_{0}^{y} \gamma(a, r, x) \gamma(b, r, y-x) \, dx = \gamma(a+b, r, y)$ for $y > 0$.
  have h_gamma_conv : ∀ y > 0, ∫⁻ x, gammaPDF a r x * gammaPDF b r (y - x) ∂volume
    = gammaPDF (a + b) r y := by
    intro y hy; exact (by
    convert gammaPDF_conv_inner a b r ha hb hr hy using 1)
  rw [h_conv, h_fubini]
  rw [MeasureTheory.lintegral_congr_ae]
  filter_upwards [
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (MeasureTheory.measure_singleton 0)] with y hy
  by_cases hy_pos : 0 < y
  · rw [← h_gamma_conv y hy_pos, ← MeasureTheory.lintegral_const_mul]
    · congr
      ext
      ring
    · exact Measurable.mul (Measurable.ennreal_ofReal (measurable_gammaPDFReal _ _))
        (Measurable.ennreal_ofReal (measurable_gammaPDFReal _ _ |> Measurable.comp
        <| measurable_const.sub measurable_id'))
  · rw [MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero]
    · simp [gammaPDF_of_neg (show y < 0 from lt_of_le_of_ne (le_of_not_gt hy_pos) hy)]
    · filter_upwards [] with x
      by_cases hx : 0 < x
      · simp_all only [gt_iff_lt, Set.mem_singleton_iff, not_lt, mul_eq_zero]
        exact Or.inl <| Or.inr <| by rw [gammaPDF_of_neg (by linarith)]
      · simp_all;grind +suggestions

/-! ## Convolution powers and the law of a sum of i.i.d. variables -/

/-- The `n`-fold additive convolution power of a measure `G` (with `convPow G 0 = δ₀`). -/
noncomputable def convPow (G : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | (n + 1) => convPow G n ∗ G

@[simp] lemma convPow_zero (G : Measure ℝ) : convPow G 0 = Measure.dirac 0 := rfl

lemma convPow_succ (G : Measure ℝ) (n : ℕ) : convPow G (n + 1) = convPow G n ∗ G := rfl

instance convPow_isProbabilityMeasure (G : Measure ℝ) [IsProbabilityMeasure G] (n : ℕ) :
    IsProbabilityMeasure (convPow G n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; infer_instance

/-
The `n`-fold convolution power of a gamma measure (for `n ≥ 1`) is a gamma measure with the
shape scaled by `n`.
-/
lemma convPow_gamma (α γ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (n : ℕ) (hn : 0 < n) :
    convPow (gammaMeasure α γ) n = gammaMeasure ((n : ℝ) * α) γ := by
  haveI : IsProbabilityMeasure (gammaMeasure α γ) := isProbabilityMeasure_gammaMeasure hα hγ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction m with
  | zero =>
    rw [convPow_succ, convPow_zero, Measure.dirac_zero_conv]
    norm_num
  | succ k ih =>
    rw [convPow_succ, ih, gammaMeasure_conv _ _ _ (by positivity) hα hγ]
    congr 1; push_cast; ring

/-
The law of the sum of `n` i.i.d. variables (over `Fin n`) is the `n`-fold convolution power.
-/
lemma finPiSum_eq_convPow (G : Measure ℝ) [IsProbabilityMeasure G] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => G)).map (fun v => ∑ i, v i) = convPow G n := by
  induction n with
  | zero => ext s hs; simp [hs]
  | succ n ih =>
    have h_eq : (Measure.pi (fun _ : Fin (n + 1) => G)).map (fun v => ∑ i : Fin (n + 1), v i)
      = (G.prod (Measure.pi (fun _ : Fin n => G))).map (fun p : ℝ × (Fin n → ℝ)
      => p.1 + ∑ i : Fin n, p.2 i) := by
      rw [← MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => G) 0 |>.map_eq]
      rw [MeasureTheory.Measure.map_map]
      · congr with v; simp [Fin.sum_univ_succ]
        rfl
      · fun_prop
      · fun_prop
    rw [h_eq, convPow_succ]
    have hsum : (fun p : ℝ × (Fin n → ℝ) => p.1 + ∑ i : Fin n, p.2 i)
        = (fun q : ℝ × ℝ => q.1 + q.2) ∘
            (Prod.map (id : ℝ → ℝ) (fun w : Fin n → ℝ => ∑ i, w i)) := rfl
    rw [hsum, ← MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop),
      ← MeasureTheory.Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      MeasureTheory.Measure.map_id, ih]
    exact MeasureTheory.Measure.conv_comm G (convPow G n)

/-
The law of the partial sum of the first `n` coordinates of an i.i.d. sequence (the infinite
product measure) is the `n`-fold convolution power.
-/
lemma infinitePi_range_sum_eq_convPow (G : Measure ℝ) [IsProbabilityMeasure G] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => G)).map (fun y => ∑ i ∈ Finset.range n, y i)
      = convPow G n := by
  convert finPiSum_eq_convPow G n using 1
  -- By definition of product measure, we can rewrite the right-hand side.
  have h_prod : (Measure.pi fun _ : Fin n => G) = Measure.map
    (fun y : ℕ → ℝ => fun i : Fin n => y i) (infinitePi fun _ => G) := by
    refine MeasureTheory.Measure.pi_eq ?_
    intro s hs; erw [MeasureTheory.Measure.map_apply]
    · convert MeasureTheory.Measure.infinitePi_pi _ _
      any_goals exact Finset.range n
      rotate_left
      rotate_left
      · grind
      · use fun i => if hi : i < n then s ⟨ i, hi ⟩ else Set.univ
      · aesop
      · grind
      · rw [Finset.prod_range]
        grind
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
    · exact MeasurableSet.univ_pi hs
  rw [h_prod, MeasureTheory.Measure.map_map]
  · congr! 1
    ext; simp [Finset.sum_range]
  · exact Finset.measurable_sum _ fun _ _ => measurable_pi_apply _
  · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _

end GammaConv
