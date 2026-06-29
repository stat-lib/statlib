/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# Tweedie distribution: integral of the (compound-Poisson) density

  For `1 < p < 2` the Tweedie exponential dispersion model with mean `μ` and
  dispersion `φ` has a density supported on `(0, ∞)` whose integral is
  `1 - exp(-μ^(2-p) / (φ (2-p)))`; the
  remaining mass is the atom at `0`.

-/

@[expose] public section

open MeasureTheory Set Real

/-- The "a"-factor of the Tweedie density (the infinite series). -/
noncomputable def a (y φ p : ℝ) :=
  let α := (2 - p) / (1 - p)
  (1/y) * ∑' j : ℕ, (y ^ (- j * α) * (p - 1) ^(α * j)) /
  (φ ^ (j * (1 - α)) * (2 - p) ^ j * Nat.factorial j * Gamma (- j * α))

/-- The Tweedie density. -/
noncomputable def tweediePDF (μ φ p : ℝ) :=
  Set.indicator ({y | 0 < y})
  (fun y => a y φ p * exp ((1 / φ) * ((μ ^ (1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p)))))

/-- The Poisson rate `z = μ^(2-p) / (φ (2-p))`; the answer is `1 - exp(-z)`. -/
noncomputable def tw_z (μ φ p : ℝ) : ℝ := μ ^ (2 - p) / (φ * (2 - p))

/-- The `j`-th summand of the integrand `a y * exp(...)`, faithful to the definition of `a`. -/
noncomputable def tw_G (μ φ p : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  let α := (2 - p) / (1 - p)
  (1/y) * ((y ^ (- j * α) * (p - 1) ^(α * j)) /
    (φ ^ (j * (1 - α)) * (2 - p) ^ j * Nat.factorial j * Gamma (- j * α)))
  * exp ((1 / φ) * ((μ ^ (1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p))))

/-- Closed form of `tw_G j y` for `y > 0`: a constant times `y^(-jα-1) * exp(-(rate)·y)`. -/
lemma tw_pt (μ : ℝ) {φ p : ℝ} (hp₁ : 1 < p) (hφ : 0 < φ) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    tw_G μ φ p j y
    = (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ))
        / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j)
          * Gamma (-(j:ℝ)*((2-p)/(1-p)))))
      * (y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1) * exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) := by
  have h1p : (1 - p) ≠ 0 := by linarith
  have hpm1 : (p - 1) ≠ 0 := by linarith
  rw [tw_G]
  have hexp : exp ((1 / φ) * ((μ ^ (1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p))))
      = exp (-tw_z μ φ p) * exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y)) := by
    rw [← exp_add]; congr 1; rw [tw_z]; field_simp; ring
  rw [hexp]
  have hypow : (1/y) * (y ^ (-(j:ℝ)*((2-p)/(1-p)))) = y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1) := by
    rw [Real.rpow_sub hy, rpow_one]; ring
  rw [← hypow]; ring

/-- The integrand is the pointwise tsum of the `tw_G` family. -/
lemma tw_pointwise (μ φ p : ℝ) (y : ℝ) :
    a y φ p * exp ((1 / φ) * ((μ ^ (1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p))))
      = ∑' j : ℕ, tw_G μ φ p j y := by
  simp only [a, tw_G]
  rw [tsum_mul_right, tsum_mul_left]

/-- The zeroth term vanishes identically (`Γ(0) = 0`). -/
lemma tw_G_zero (μ φ p y : ℝ) : tw_G μ φ p 0 y = 0 := by
  simp [tw_G, Gamma_zero]

/-- The summand is nonnegative on `(0, ∞)`. -/
lemma tw_G_nonneg (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hφ : 0 < φ)
    (j : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ tw_G μ φ p j y := by
  cases j with
  | zero => rw [tw_G_zero]
  | succ n =>
    set j := n + 1
    have hjpos : j > 0 := by simp [j]
    have hjposR : 0 < (j:ℝ) := by exact_mod_cast hjpos
    have hαneg : (2 - p) / (1 - p) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
    have ha0pos : 0 < -(j:ℝ) * ((2-p)/(1-p)) := by
      have : -(j:ℝ) < 0 := by simpa using hjposR
      exact mul_pos_of_neg_of_neg this hαneg
    rw [tw_pt μ hp₁ hφ j hy]
    positivity


/-- Each `tw_G j` is integrable on `(0, ∞)`. -/
lemma tw_integrable_on {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ)
    (j : ℕ) : IntegrableOn (fun y => tw_G μ φ p j y) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos0
  · subst hj0; simp only [tw_G_zero]; exact integrableOn_zero
  · have hjpos : 0 < (j:ℝ) := by exact_mod_cast hjpos0
    have hαneg : (2 - p) / (1 - p) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
    have ha0pos : 0 < -(j:ℝ) * ((2-p)/(1-p)) := by
      have : -(j:ℝ) < 0 := by simpa using hjpos
      exact mul_pos_of_neg_of_neg this hαneg
    have hrpos : 0 < μ ^ (1 - p) / (φ * (p - 1)) := by positivity
    have hbase : IntegrableOn
        (fun y => y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1)
          * exp (-(μ ^ (1 - p) / (φ * (p - 1))) * y ^ (1:ℝ))) (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [ha0pos]) (le_refl 1) hrpos
    have hbase2 : IntegrableOn
        (fun y => y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1)
          * exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) (Set.Ioi 0) := by
      apply IntegrableOn.congr_fun hbase _ measurableSet_Ioi
      intro y hy; simp only [Real.rpow_one, neg_mul]
    have hconst : IntegrableOn
        (fun y => (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ))
          / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j)
            * Gamma (-(j:ℝ)*((2-p)/(1-p)))))
          * (y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1)
            * exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y)))) (Set.Ioi 0) :=
      hbase2.const_mul _
    apply IntegrableOn.congr_fun hconst _ measurableSet_Ioi
    intro y hy; simp only [Set.mem_Ioi] at hy
    exact (tw_pt μ hp₁ hφ j hy).symm

/-- The per-term integral for `j ≥ 1`: it equals `exp(-z) z^j / j!`. -/
lemma tw_integral_term {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ)
    {j : ℕ} (hj : 1 ≤ j) :
    ∫ y in Set.Ioi (0:ℝ), tw_G μ φ p j y
      = exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j) := by
  have h1p : (1 - p) ≠ 0 := by linarith
  have h2p : (2 - p) ≠ 0 := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hjpos : 0 < (j:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hj
  have hαneg : (2 - p) / (1 - p) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
  have ha0pos : 0 < -(j:ℝ) * ((2-p)/(1-p)) := by
    have : -(j:ℝ) < 0 := by simpa using hjpos
    exact mul_pos_of_neg_of_neg this hαneg
  have hμpow : 0 < μ ^ (1 - p) := rpow_pos_of_pos hμ _
  have hrpos : 0 < μ ^ (1 - p) / (φ * (p - 1)) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => tw_pt μ hp₁ hφ j hy)]
  rw [integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha0pos hrpos]
  set α := (2-p)/(1-p) with hα
  set r := μ ^ (1 - p) / (φ * (p - 1)) with hrdef
  have hrinvpos : 0 < 1/r := by positivity
  have hW : (p-1)^α * (1/r)^(-α) / (φ^(1-α)*(2-p)) = μ^(2-p)/(φ*(2-p)) := by
    have h1pneg : (1 - p) < 0 := by linarith
    have hkey : (1 - p) * α = 2 - p := by rw [hα]; field_simp
    have hrinv : (1/r) = φ * (p-1) / μ^(1-p) := by rw [hrdef, one_div_div]
    rw [hrinv]
    rw [Real.div_rpow (by positivity) (le_of_lt hμpow)]
    rw [Real.mul_rpow (le_of_lt hφ) (le_of_lt hp1)]
    rw [← rpow_mul hμ.le]
    rw [show (1 - p) * (-α) = -(2-p) by rw [mul_neg, hkey]]
    rw [Real.rpow_neg hμ.le (2-p), rpow_neg hp1.le α, rpow_neg hφ.le α]
    have hφfac : φ^(1-α) = φ^(1:ℝ) * φ^(-α) := by rw [← rpow_add hφ]; ring_nf
    rw [hφfac, rpow_one, rpow_neg hφ.le α]
    field_simp
  have hcore : (p-1)^(α*(j:ℝ)) * (1/r)^(-(j:ℝ)*α) / (φ^((j:ℝ)*(1-α))*(2-p)^j)
      = (μ^(2-p)/(φ*(2-p)))^j := by
    have hn1 : 0 ≤ (p-1)^α := rpow_nonneg hp1.le α
    have hn2 : 0 ≤ (1/r)^(-α) := rpow_nonneg hrinvpos.le _
    have hn3 : 0 ≤ φ^(1-α) := rpow_nonneg hφ.le _
    have hn4 : 0 ≤ 2-p := by linarith
    rw [Real.rpow_mul hp1.le α (j:ℝ)]
    rw [show (-(j:ℝ)*α) = (-α)*(j:ℝ) by ring]
    rw [Real.rpow_mul hrinvpos.le (-α) (j:ℝ)]
    rw [show (j:ℝ)*(1-α) = (1-α)*(j:ℝ) by ring]
    rw [Real.rpow_mul hφ.le (1-α) (j:ℝ)]
    rw [← rpow_natCast (2-p) j, ← rpow_natCast (μ^(2-p)/(φ*(2-p))) j]
    rw [← mul_rpow hn1 hn2]
    rw [← mul_rpow hn3 hn4]
    rw [← div_rpow (mul_nonneg hn1 hn2) (mul_nonneg hn3 hn4)]
    rw [hW]
  have hΓ : Gamma (-(j:ℝ)*α) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos ha0pos)
  have hfac : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [tw_z]
  rw [show exp (-(μ^(2-p)/(φ*(2-p)))) * (p-1)^(α*(j:ℝ))
        / (φ^((j:ℝ)*(1-α)) * (2-p)^j * (Nat.factorial j) * Gamma (-(j:ℝ)*α))
        * ((1/r)^(-(j:ℝ)*α) * Gamma (-(j:ℝ)*α))
      = exp (-(μ^(2-p)/(φ*(2-p)))) / (Nat.factorial j)
          * (Real.Gamma (-(j:ℝ)*α)/Real.Gamma (-(j:ℝ)*α))
        * ((p-1)^(α*(j:ℝ)) * (1/r)^(-(j:ℝ)*α) / (φ^((j:ℝ)*(1-α))*(2-p)^j))
      by field_simp]
  rw [div_self hΓ, hcore]
  ring

/-- The per-term integral for `j = 0` is `0`. -/
lemma tw_integral_zero (μ φ p : ℝ) :
    ∫ y in Set.Ioi (0:ℝ), tw_G μ φ p 0 y = 0 := by
  simp [tw_G_zero]

/-- Summability of the integral norms (needed to swap `∫` and `∑'`). -/
lemma tw_summable_norm (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    Summable (fun j : ℕ => ∫ y in Set.Ioi (0:ℝ), ‖tw_G μ φ p j y‖) := by
  have hsum2 : Summable (fun j : ℕ =>
      exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j)) := by
    have := (Real.summable_pow_div_factorial (tw_z μ φ p)).mul_left (Real.exp (-tw_z μ φ p))
    simpa [mul_div_assoc] using this
  have hnorm_eq (j) : ∫ y in Set.Ioi 0, ‖tw_G μ φ p j y‖
      = ∫ y in Set.Ioi 0, tw_G μ φ p j y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy; simp only [Set.mem_Ioi] at hy
    exact norm_of_nonneg (tw_G_nonneg μ φ p hp₁ hp₂ hφ j hy)
  apply Summable.of_nonneg_of_le _ _ hsum2
  · intro j; rw [hnorm_eq]
    exact setIntegral_nonneg measurableSet_Ioi
      fun y => tw_G_nonneg μ φ p hp₁ hp₂ hφ j
  · intro j
    rw [hnorm_eq]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rw [tw_integral_zero]; positivity
    · rw [tw_integral_term hp₁ hp₂ hμ hφ hjpos]

/-- The series of per-term values sums to `1 - exp(-z)`. -/
lemma tw_tsum (μ φ p : ℝ) :
    ∑' j : ℕ, (if j = 0 then (0:ℝ)
      else exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j))
      = 1 - exp (-tw_z μ φ p) := by
  set z := tw_z μ φ p
  have hexp : exp z = ∑' n : ℕ, z ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsum : Summable (fun n : ℕ => z ^ n / n.factorial) := summable_pow_div_factorial z
  have hsum2 : Summable (fun n : ℕ => exp (-z) * z ^ n / (Nat.factorial n)) := by
    have := hsum.mul_left (Real.exp (-z))
    simpa [mul_div_assoc] using this
  have hsum3 : Summable (fun j : ℕ =>
      (if j = 0 then exp (-z) * z ^ j / (Nat.factorial j) else 0)) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro b hb; simp at hb; simp [hb]
  have key : (fun j : ℕ => (if j = 0 then (0:ℝ) else exp (-z) * z ^ j / (Nat.factorial j)))
      = (fun j => exp (-z) * z ^ j / (Nat.factorial j)
          - (if j = 0 then exp (-z) * z ^ j / (Nat.factorial j) else 0)) := by
    funext j; by_cases hj : j = 0 <;> simp [hj]
  rw [key, Summable.tsum_sub hsum2 hsum3]
  have h1 : ∑' j : ℕ, exp (-z) * z ^ j / (Nat.factorial j) = 1 := by
    rw [show (fun j : ℕ => exp (-z) * z ^ j / (Nat.factorial j))
          = (fun j => exp (-z) * (z ^ j / (Nat.factorial j))) by funext j; ring]
    rw [tsum_mul_left, ← hexp, ← exp_add]; simp
  have h2 : ∑' j : ℕ, (if j = 0 then exp (-z) * z ^ j / (Nat.factorial j) else 0)
      = exp (-z) := by
    rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [hb]
  rw [h1, h2]

/-- The integral of the Tweedie density equals `1 - exp(-μ^(2-p)/(φ(2-p)))`. -/
lemma tweediePDF_integral {μ φ p} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ)
  (hφ : 0 < φ) :
  ∫ y, tweediePDF μ φ p y =
  1 - exp (-μ ^ (2 - p) / (φ * (2 - p))) := by
  rw [tweediePDF]
  rw [show {y : ℝ | 0 < y} = Set.Ioi 0 from rfl]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => tw_pointwise μ φ p y)]
  rw [← integral_tsum_of_summable_integral_norm
      (fun j => tw_integrable_on hp₁ hp₂ hμ hφ j)
      (tw_summable_norm μ φ p hp₁ hp₂ hμ hφ)]
  rw [show (∑' j : ℕ, ∫ y in Set.Ioi (0:ℝ), tw_G μ φ p j y)
      = ∑' j : ℕ, (if j = 0 then (0:ℝ)
        else exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j)) by
    apply tsum_congr
    intro j
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rw [tw_integral_zero]; simp
    · rw [tw_integral_term hp₁ hp₂ hμ hφ hjpos, if_neg (by omega)]]
  rw [tw_tsum, tw_z, neg_div]

open NNReal ENNReal Real
noncomputable section

/-- Probability of zero according to Tweedie distribution. -/
def tweedie_prob_zero (μ φ p : ℝ) : ℝ≥0 :=
    ⟨rexp (-μ ^ (2 - p) / (φ * (2 - p))), exp_nonneg _⟩

/-- Nonnegativity of the Tweedie PDF. -/
lemma tweediePDF_nonneg {y μ φ p : ℝ} (hφ : 0 ≤ φ)
  (hp₁ : 1 < p) (hp₂ : p ≤ 2)
  : tweediePDF μ φ p y ≥ 0 := by
    simp only [tweediePDF, indicator, mem_setOf_eq, a, one_div, neg_mul, ge_iff_le]
    split_ifs with g₀
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · refine tsum_nonneg ?_
          intro j
          apply mul_nonneg
          · positivity
          · simp only [mul_inv_rev]
            apply mul_nonneg
            · rw [inv_nonneg]
              refine Gamma_nonneg_of_nonneg ?_
              rw [mul_div, ← neg_div, ← neg_mul, mul_comm, ← mul_div]
              apply mul_nonneg
              · linarith
              · suffices 0 ≤ j / (p - 1) by
                  convert this using 1
                  have : p - 1 = -(1 - p) := by simp
                  rw [this]
                  field_simp
                positivity
            · positivity
      · exact exp_nonneg _
    simp

def tweediePDF' (μ : ℝ) {φ p : ℝ}
    (hp₁ : 1 < p) (hp₂ : p ≤ 2)
    (hφ : 0 ≤ φ) (y : ℝ) : ℝ≥0∞:=
    let nn : NNReal := (⟨tweediePDF μ φ p y, by
      by_cases H : y < 0
      · unfold tweediePDF
        simp only [indicator, mem_setOf_eq, one_div]
        rw [if_neg (by linarith)]
      · simp only [not_lt] at H
        exact tweediePDF_nonneg hφ hp₁ hp₂⟩ : NNReal)
    (nn : ENNReal)

def tweedieMeasure (μ : ℝ) {φ p : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) : Measure ℝ :=
    (tweedie_prob_zero μ φ p) • (Measure.dirac 0)
    + (volume.withDensity (tweediePDF' μ hp₁ (by linarith) hφ))

/-- The Tweedie measure is a probability measure. -/
lemma tweedieMeasure_prob (μ : ℝ) (hμ : 0 < μ) {φ p : ℝ} (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    IsProbabilityMeasure (tweedieMeasure μ (show 0 ≤ φ by linarith) hp₁ hp₂) := by
  refine isProbabilityMeasure_iff.mpr ?_
  unfold tweedieMeasure
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    ENNReal.smul_one, MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  unfold tweedie_prob_zero
  have : ∫⁻ (a : ℝ), tweediePDF' μ hp₁ (by linarith) (show 0 ≤ φ by linarith) a =
      1 - tweedie_prob_zero μ φ p := by
    have ht := tweediePDF_integral hp₁ hp₂ hμ hφ
    have : tweedie_prob_zero μ φ p ≤ 1 := by
      refine exp_le_one_iff.mpr ?_
      field_simp
      simp only [mul_zero, Left.neg_nonpos_iff]
      positivity
    have : (1 : NNReal) - ⟨rexp (-μ ^ (2 - p) / (φ * (2 - p))), exp_nonneg _⟩
      = ⟨1 - tweedie_prob_zero μ φ p, by
        generalize tweedie_prob_zero μ φ p = α at *
        exact sub_nonneg_of_le this⟩ := by
          unfold tweedie_prob_zero
          have (a : ℝ) (ha : a < 1) (ha' : 0 ≤ a) :
            (1 : NNReal) - ⟨a,ha'⟩ = ⟨1-a, by linarith⟩ := by
            refine (toNNReal_eq_iff_eq_coe ?_).mpr rfl
            have : 1 - a > 0 := by linarith
            exact Ne.symm (Std.ne_of_lt this)
          apply this
          refine exp_lt_one_iff.mpr ?_
          ring_nf
          simp only [Left.neg_neg_iff]
          apply _root_.mul_pos <| rpow_pos_of_pos hμ (2 - p)
          · simp only [inv_pos, lt_neg_add_iff_add_lt, add_zero]
            nth_rw 1 [mul_comm]
            exact (mul_lt_mul_iff_of_pos_left hφ).mpr hp₂
    have : (1 : ENNReal) - ENNReal.ofNNReal ⟨rexp (-μ ^ (2 - p) / (φ * (2 - p))), exp_nonneg _⟩
      = ENNReal.ofNNReal ⟨1 - tweedie_prob_zero μ φ p,
      sub_nonneg_of_le (by simp;tauto)⟩ := by rw [← this]; simp
    unfold tweedie_prob_zero
    rw [this]
    simp only [tweedie_prob_zero]
    have : rexp (-μ ^ (2 - p) / (φ * (2 - p))) = 1 - ∫ (y : ℝ), tweediePDF μ φ p y := by linarith
    simp_rw [this]
    have (a : Real) (ha : 0 ≤ 1 - a)
      (ha' : 0 ≤ a)
      : ofNNReal (⟨(1 : ℝ) - (⟨1 - a, ha⟩ : NNReal),
      by simp;tauto⟩ : NNReal) = ofNNReal ⟨a, ha'⟩ := by simp
    specialize this (∫ (y : ℝ), tweediePDF μ φ p y) (by
      rw [tweediePDF_integral]
      all_goals try linarith
      simp only [_root_.sub_sub_cancel]
      exact exp_nonneg (-μ ^ (2 - p) / (φ * (2 - p))))
      (by
        rw [tweediePDF_integral]
        all_goals try linarith
        simp
        field_simp
        simp only [mul_zero, Left.neg_nonpos_iff]
        apply mul_nonneg
        · refine rpow_nonneg ?_ (2 - p)
          linarith
        · simp
          linarith)
    symm
    unfold tweediePDF'
    convert this
    · rw [MeasureTheory.lintegral_coe_eq_integral]
      · refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
        all_goals simp
        · refine toReal_ofReal ?_
          refine integral_nonneg ?_
          intro
          simp
      · suffices Integrable (fun x ↦ tweediePDF μ φ p x) volume by
          convert this
        apply Integrable.of_integral_ne_zero
        rw [tweediePDF_integral hp₁ hp₂ hμ hφ]
        have (a) (ha : a ≠ 0) : 1 - rexp a ≠ 0 := by
          contrapose! ha
          apply exp_injective
          rw [exp_zero]
          linarith
        apply this
        simp only [ne_eq, _root_.div_eq_zero_iff, neg_eq_zero, mul_eq_zero, not_or]
        constructor
        · refine (rpow_ne_zero ?_ ?_).mpr ?_
          all_goals linarith
        · constructor
          all_goals linarith
  rw [this]
  unfold tweedie_prob_zero
  have (a : NNReal) (ha : 1 - a.1 > 0) :
     a + (1 - a) = 1 := by
      apply NNReal.coe_injective
      change a.toReal + (1-a).toReal = 1
      have : 1 - a.toReal = (1-a).toReal := by
        refine (toNNReal_eq_iff_eq_coe ?_).mp rfl
        apply ne_of_gt
        refine NNReal.coe_pos.mp ?_
        simp only [val_eq_coe, gt_iff_lt, sub_pos, coe_lt_one, NNReal.coe_pos,
          tsub_pos_iff_lt] at ha ⊢
        exact ha
      rw [← this]
      linarith
  have (a : NNReal) (ha : 1 - a.1 > 0) :
    ofNNReal a + ofNNReal (1 - a) = 1 := by
      rw [← ENNReal.coe_add]
      rw [this]
      · simp
      · tauto
  apply this
  simp
  field_simp
  simp only [mul_zero, Left.neg_neg_iff]
  apply div_pos
  · apply rpow_pos_of_pos
    linarith
  · linarith

def tweedieProbMeasure {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) : MeasureTheory.ProbabilityMeasure ℝ := {
      val := tweedieMeasure μ (by linarith) hp₁ hp₂
      property :=
        tweedieMeasure_prob μ hμ hφ hp₁ hp₂
    }


/-! ## Expectation of the Tweedie distribution

We now prove that the mean (expectation) of `tweedieProbMeasure` equals the parameter `μ`.
The measure is a mixture of an atom at `0` (which contributes nothing to the mean) and an
absolutely continuous part with density `tweediePDF`. The mean of the continuous part is
`∫ y, y * tweediePDF μ φ p y`, which we evaluate term-by-term.
-/

/-
Closed form of `y * tw_G j y` for `y > 0`: the same constant as in `tw_pt`, but with
the power `y^(-jα)` (the factor `y` cancels one power of `y`).
-/
lemma tw_yG_pt (μ : ℝ) {φ p : ℝ} (hp₁ : 1 < p) (hφ : 0 < φ) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    y * tw_G μ φ p j y
    = (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ))
        / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j)
          * Real.Gamma (-(j:ℝ)*((2-p)/(1-p)))))
      * (y ^ (-(j:ℝ)*((2-p)/(1-p))) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) := by
  convert congr_arg (fun x : ℝ => y * x) (tw_pt μ hp₁ hφ j hy) using 1 ; ring_nf
  have : y ^ (p * (1 - p)⁻¹ * ↑j - (1 - p)⁻¹ * ↑j * 2)
    = y * y ^ (-1 + p * (1 - p)⁻¹ * ↑j - (1 - p)⁻¹ * ↑j * 2) := by
      have (z : ℝ) : y^z * y = y ^ (z + 1) := by
        refine Eq.symm (Real.rpow_add_one ?_ z)
        linarith
      simp_rw [mul_comm] at this
      rw [this]
      ring_nf
  rw [this]
  ring_nf

/-
Each `y * tw_G j` is integrable on `(0, ∞)`.
-/
lemma tw_yG_integrable_on {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ)
    (j : ℕ) : IntegrableOn (fun y => y * tw_G μ φ p j y) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos0
  · simp [hj0, tw_G_zero]
  · have h_integrable : IntegrableOn (fun y => y ^ (-(j:ℝ)*((2-p)/(1-p))) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) (Set.Ioi 0) := by
      have h_integrable : ∀ {s b : ℝ}, -1 < s → 0 < b → IntegrableOn (fun y => y ^ s * Real.exp (-b * y)) (Set.Ioi 0) := by
        intro s b hs hb
        convert (integrableOn_rpow_mul_exp_neg_mul_rpow (show -1 < s by linarith) (show 1 ≤ (1 : ℝ) by norm_num) hb) using 1 ; norm_num
      convert h_integrable _ _ using 1
      rotate_left
      exact - (j : ℝ) * ((2 - p) / (1 - p))
      exact μ ^ (1 - p) / (φ * (p - 1))
      · nlinarith [show (j : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ (2 - p) (by linarith : (1 - p) ≠ 0)]
      · exact div_pos (Real.rpow_pos_of_pos hμ _) (mul_pos hφ (by linarith))
      · norm_num
    refine' h_integrable.const_mul _ |> fun h => h.congr _
    exact (Real.exp (-tw_z μ φ p) * (p - 1) ^ (((2 - p) / (1 - p)) * j) / (φ ^ ((j : ℝ) * (1 - (2 - p) / (1 - p))) * (2 - p) ^ j * (Nat.factorial j) * Real.Gamma (- (j : ℝ) * ((2 - p) / (1 - p)))))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy using by rw [tw_yG_pt μ hp₁ hφ j hy]

/-
The per-term mean integral: `∫ y * tw_G j = K * (j · exp(-z) z^j / j!)`,
where `K = φ(2-p)/μ^(1-p)`.  (Valid for all `j`, since both sides vanish at `j = 0`.)
-/
lemma tw_mean_term {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) (j : ℕ) :
    ∫ y in Set.Ioi (0:ℝ), y * tw_G μ φ p j y
      = (φ * (2-p) / μ^(1-p))
        * ((j:ℝ) * Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j)) := by
  by_cases hj : j = 0 <;> simp_all +decide [tw_G]
  have h_integral : ∫ y in Set.Ioi (0:ℝ), y * tw_G μ φ p j y = ∫ y in Set.Ioi (0:ℝ), (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ)) / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j) * Real.Gamma (-(j:ℝ)*((2-p)/(1-p))))) * (y ^ (-(j:ℝ)*((2-p)/(1-p))) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => tw_yG_pt μ hp₁ hφ j hy
  -- Apply the integral formula for the gamma function.
  have h_gamma : ∫ y in Set.Ioi (0:ℝ), y ^ (-(j:ℝ)*((2-p)/(1-p))) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y)) = (1 / (μ ^ (1 - p) / (φ * (p - 1)))) ^ (-(j:ℝ)*((2-p)/(1-p)) + 1) * Real.Gamma (-(j:ℝ)*((2-p)/(1-p)) + 1) := by
    convert integral_rpow_mul_exp_neg_mul_Ioi _ _ using 1
    · norm_num
    · nlinarith [show (j : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hj), mul_div_cancel₀ (2 - p) (by linarith : (1 - p) ≠ 0)]
    · exact div_pos (Real.rpow_pos_of_pos hμ _) (mul_pos hφ (by linarith))
  convert h_integral using 1
  · unfold tw_G; congr; ext
    ring_nf
  · rw [MeasureTheory.integral_const_mul, h_gamma]
    rw [Real.Gamma_add_one]
    · rw [Real.rpow_add, Real.rpow_one]
      · field_simp
        rw [eq_comm, neg_div', div_eq_iff]
        · unfold tw_z; ring_nf
          rw [show (-1 + p) = (p - 1) by ring, show (p * φ * (μ ^ (1 - p)) ⁻¹ - φ * (μ ^ (1 - p)) ⁻¹) = (p - 1) * φ * (μ ^ (1 - p)) ⁻¹ by ring] ; rw [Real.mul_rpow (by nlinarith) (by positivity), Real.mul_rpow (by nlinarith) (by positivity)] ; ring_nf
          rw [show (- (p * j * (1 - p) ⁻¹) + j * (1 - p) ⁻¹ * 2 : ℝ) = - (p * j * (1 - p) ⁻¹ - j * (1 - p) ⁻¹ * 2) by ring, Real.rpow_neg (by linarith)] ; ring_nf
          rw [show (-1 + p) = (p - 1) by ring, Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity)] ; ring_nf
          rw [Real.log_inv, Real.log_rpow (by positivity)] ; ring_nf
          rw [Real.rpow_def_of_pos (by positivity)] ; ring_nf
          rw [Real.rpow_def_of_pos (by positivity)] ; ring_nf
          rw [show (- (p * φ) + φ * 2) = φ * (2 - p) by ring, mul_inv] ; norm_num [Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log, hμ, hφ, hp₁, hp₂] ; ring_nf
          norm_num [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_sub, hμ.ne', hφ.ne', show (2 - p) ≠ 0 by linarith] ; ring_nf
          norm_num [mul_assoc, ← Real.exp_add] ; ring_nf
          grind +revert
        · exact mul_ne_zero (mul_ne_zero (by linarith) (pow_ne_zero _ (by linarith))) (ne_of_gt (Real.Gamma_pos_of_pos (by nlinarith [show (j : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hj), mul_div_cancel₀ ((2 - p) * j) (by linarith : (1 - p) ≠ 0)])))
      · exact one_div_pos.mpr (div_pos (Real.rpow_pos_of_pos hμ _) (mul_pos hφ (by linarith)))
    · exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hj)) (div_ne_zero (by linarith) (by linarith))

/-- Summability of `fun j => (j:ℝ) * z^j / j!` for any real `z`. -/
lemma tw_summable_n_pow (z : ℝ) :
    Summable (fun j : ℕ => (j:ℝ) * z ^ j / (Nat.factorial j)) := by
  refine' summable_of_ratio_norm_eventually_le _ _
  exact 2 / 3
  · norm_num
  · norm_num [Nat.factorial_succ, abs_div, abs_mul]
    refine' ⟨ ⌈3 * |z|⌉₊ + 1, fun n hn => _ ⟩ ; rw [mul_div_mul_left _ _ (by positivity)] ; ring_nf
    nlinarith [show (n : ℝ) ≥ ⌈3 * |z|⌉₊ + 1 by exact_mod_cast hn, Nat.le_ceil (3 * |z|), show (0 : ℝ) ≤ |z| ^ n * (n.factorial : ℝ) ⁻¹ by positivity]

/-- The "Poisson mean" identity: `∑' j, j z^j / j! = z · exp z`. -/
lemma tw_tsum_n_pow (z : ℝ) :
    ∑' j : ℕ, (j:ℝ) * z ^ j / (Nat.factorial j) = z * Real.exp z := by
  convert (Summable.tsum_eq_zero_add (show Summable fun j : ℕ => ((j : ℝ) * z ^ j / (j.factorial : ℝ)) from ?_)) using 1
  · norm_num [Nat.factorial_succ, pow_succ', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, tsum_mul_left]
    field_simp
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    simp +decide only [mul_div_assoc]
    exact Eq.symm _root_.tsum_mul_left
  · exact tw_summable_n_pow z

/-
Summability of the integral norms for the mean (needed to swap `∫` and `∑'`).
-/
lemma tw_mean_summable_norm (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    Summable (fun j : ℕ => ∫ y in Set.Ioi (0:ℝ), ‖y * tw_G μ φ p j y‖) := by
  convert Summable.mul_left (φ * (2 - p) / μ ^ (1 - p) * Real.exp (-tw_z μ φ p)) (tw_summable_n_pow (tw_z μ φ p)) using 2
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => Real.norm_of_nonneg (mul_nonneg hy.out.le (tw_G_nonneg μ φ p hp₁ hp₂ hφ _ hy))] ; rw [tw_mean_term hp₁ hp₂ hμ hφ]
  ring

/-
The series of per-term mean values sums to `μ`.
-/
lemma tw_mean_tsum {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    ∑' j : ℕ, (φ * (2-p) / μ^(1-p))
        * ((j:ℝ) * Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j)) = μ := by
  -- Let `z = tw_z μ φ p` and `K = φ*(2-p)/μ^(1-p)`. Each summand is `K * ((j:ℝ) * exp(-z) * z^j / j!)`.
  set z := tw_z μ φ p
  set K := φ * (2 - p) / μ ^ (1 - p) with hK
  -- So the sum equals `K * exp(-z) * (z * exp z) = K * z * (exp (-z) * exp z) = K * z` (since `exp (-z) * exp z = 1`, via `Real.exp_neg` and `inv_mul_cancel` or `← Real.exp_add`).
  have hsum : ∑' j : ℕ, (j : ℝ) * Real.exp (-z) * z ^ j / (Nat.factorial j) = z * Real.exp z * Real.exp (-z) := by
    have := @tw_tsum_n_pow z; simp_all +decide [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
    simp +decide only [← mul_assoc, ← this]
    exact _root_.tsum_mul_right
  convert congr_arg (fun x : ℝ => K * x) hsum using 1
  · exact _root_.tsum_mul_left
  · simp +zetaDelta at *
    unfold tw_z; norm_num [mul_assoc, ← Real.exp_add] ; ring_nf
    rw [show (2 - p) = (1 - p) + 1 by ring, Real.rpow_add hμ, Real.rpow_one] ; ring_nf
    nlinarith [mul_inv_cancel_left₀ (show φ * 2 - φ * p ≠ 0 by nlinarith) μ, mul_inv_cancel₀ (show μ ^ (1 - p) ≠ 0 by positivity)]

/-
The mean of the continuous part: `∫ y, tweediePDF μ φ p y * y = μ`.
-/
lemma tweedie_mean_value {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    ∫ y, tweediePDF μ φ p y * y = μ := by
  -- First, show `tweediePDF μ φ p y * y = Set.indicator (Set.Ioi 0) (fun y => (a y φ p * Real.exp (...)) * y) y`.
  have h_indicator : (∫ y, tweediePDF μ φ p y * y)
    = (∫ y in Set.Ioi (0:ℝ), (a y φ p * Real.exp ((1 / φ) * ((μ ^ (1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p)))) * y)) := by
      rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator, tweediePDF]
  rw [h_indicator]
  -- On `Ioi 0`, `(a y φ p * Real.exp (...)) * y = y * (a y φ p * Real.exp (...)) = y * ∑' j, tw_G μ φ p j y = ∑' j, y * tw_G μ φ p j y` (use `tw_pointwise` then `tsum_mul_left`). Apply `setIntegral_congr_fun measurableSet_Ioi`.
  have h_indicator : (∫ y in Set.Ioi (0:ℝ), (a y φ p * Real.exp ((1 / φ) * ((μ ^ (1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p)))) * y))
    = (∫ y in Set.Ioi (0:ℝ), ∑' j : ℕ, y * tw_G μ φ p j y) := by
      refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => _
      convert congr_arg (fun x : ℝ => x * y) (tw_pointwise μ φ p y) using 1 ; ring_nf
      exact _root_.tsum_mul_left
  rw [h_indicator]
  convert tw_mean_tsum hp₁ hp₂ hμ hφ using 1
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm]
  · exact tsum_congr fun j => tw_mean_term hp₁ hp₂ hμ hφ j
  · exact fun j => tw_yG_integrable_on hp₁ hp₂ hμ hφ j
  · convert tw_mean_summable_norm μ φ p hp₁ hp₂ hμ hφ using 1

/-- `tweediePDF μ φ p y * y` is integrable. -/
lemma tweedie_mean_integrable {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    Integrable (fun y => tweediePDF μ φ p y * y) := by
  apply Integrable.of_integral_ne_zero
  rw [tweedie_mean_value hp₁ hp₂ hμ hφ]
  exact ne_of_gt hμ

/-
The expectation of the Tweedie measure equals `μ`.
-/
theorem tweedieMeasure_expectation {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    ∫ y, y ∂(tweedieMeasure μ (show (0:ℝ) ≤ φ by linarith) hp₁ hp₂) = μ := by
  -- Let `f y := (tweediePDF μ φ p y).toNNReal`. Then `f y • y = tweediePDF μ φ p y * y`.
  set f : ℝ → ℝ≥0 := fun y => (tweediePDF μ φ p y).toNNReal
  -- Show that `volume.withDensity (tweediePDF' μ hp₁ (by linarith) _)` equals `volume.withDensity (fun y => ↑(f y))`.
  have h_withDensity : volume.withDensity (tweediePDF' μ hp₁ (by linarith) hφ.le) = volume.withDensity (fun y => f y) := by
    refine' MeasureTheory.withDensity_congr_ae _
    filter_upwards [] with y using (ENNReal.ofReal_eq_coe_nnreal _).symm
  -- Show that `Integrable (fun y => y) (volume.withDensity (fun y => ↑(f y)))`.
  have h_integrable : Integrable (fun y => y) (volume.withDensity (fun y => f y)) := by
    have h_integrable : Integrable (fun y => f y • y) volume := by
      convert tweedie_mean_integrable hp₁ hp₂ hμ hφ using 1
      ext y; exact mul_eq_mul_right_iff.mpr (Or.inl <| Real.coe_toNNReal _ <| tweediePDF_nonneg (by linarith) hp₁ (by linarith))
    rw [MeasureTheory.integrable_withDensity_iff_integrable_smul₀]
    · convert h_integrable using 1
    · have h_integrable : Integrable (fun y => tweediePDF μ φ p y) volume := by
        contrapose! h_integrable
        have := tweediePDF_integral hp₁ hp₂ hμ hφ; rw [MeasureTheory.integral_undef h_integrable] at this; linarith [Real.exp_pos (-μ ^ (2 - p) / (φ * (2 - p))), Real.exp_lt_one_iff.mpr (show -μ ^ (2 - p) / (φ * (2 - p)) < 0 by exact div_neg_of_neg_of_pos (neg_neg_of_pos (Real.rpow_pos_of_pos hμ _)) (mul_pos hφ (by linarith)))]
      exact h_integrable.1.aemeasurable.real_toNNReal
  convert congr_arg (fun x : ℝ => x + 0) (tweedie_mean_value hp₁ hp₂ hμ hφ) using 1
  · rw [tweedieMeasure, MeasureTheory.integral_add_measure] ; norm_num [h_withDensity, h_integrable]
    · convert integral_withDensity_eq_integral_smul₀ _ (fun y => y) using 1
      · simp +zetaDelta at *
        congr! 1
        ext y; simp +decide [Real.toNNReal_of_nonneg (tweediePDF_nonneg (by linarith : 0 ≤ φ) hp₁ (by linarith))]
        exact ext_cauchy rfl
      · have h_integrable : Integrable (fun y => tweediePDF μ φ p y) volume := by
          exact (by by_contra h; have := tweediePDF_integral hp₁ hp₂ hμ hφ; rw [MeasureTheory.integral_undef h] at this; linarith [Real.exp_pos (-μ ^ (2 - p) / (φ * (2 - p))), Real.exp_lt_one_iff.mpr (show -μ ^ (2 - p) / (φ * (2 - p)) < 0 by exact div_neg_of_neg_of_pos (neg_neg_of_pos (Real.rpow_pos_of_pos hμ _)) (mul_pos hφ (by linarith)))])
        exact h_integrable.1.aemeasurable.real_toNNReal
    · constructor <;> norm_num [MeasureTheory.HasFiniteIntegral]
      exact measurable_id.aestronglyMeasurable
    · aesop
  · ring

/-- The expectation of the Tweedie probability measure equals `μ`. -/
theorem tweedieProbMeasure_expectation {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    ∫ y, y ∂ (tweedieProbMeasure hμ hφ hp₁ hp₂) = μ :=
  tweedieMeasure_expectation hμ hφ hp₁ hp₂



/-! ## Variance of the Tweedie distribution

We prove the famous identity `Var = φ · μ^p`.  The argument mirrors the mean
computation: we evaluate the second moment `∫ y², dP` term-by-term and obtain
`μ² + φ·μ^p`, and then the variance is `E[Y²] - (E[Y])² = φ·μ^p`.
-/

/-
Closed form of `y² * tw_G j y` for `y > 0`: the same constant as in `tw_pt`, but with
the power `y^(-jα+1)` (the factor `y²` cancels one power of `y` and adds one).
-/
lemma tw_y2G_pt (μ : ℝ) {φ p : ℝ} (hp₁ : 1 < p) (hφ : 0 < φ) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ 2 * tw_G μ φ p j y
    = (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ))
        / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j)
          * Real.Gamma (-(j:ℝ)*((2-p)/(1-p)))))
      * (y ^ (-(j:ℝ)*((2-p)/(1-p)) + 1) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) := by
  convert congr_arg ( fun x : ℝ => y * x ) ( tw_yG_pt μ hp₁ hφ j hy ) using 1 ; ring;
  rw [ Real.rpow_add hy, Real.rpow_one ] ; ring

/-
Each `y² * tw_G j` is integrable on `(0, ∞)`.
-/
lemma tw_y2G_integrable_on {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ)
    (j : ℕ) : IntegrableOn (fun y => y ^ 2 * tw_G μ φ p j y) (Set.Ioi 0) := by
  by_cases hj : j = 0;
  · unfold tw_G; aesop;
  · have h_integrable : IntegrableOn (fun y => y ^ (-(j:ℝ)*((2-p)/(1-p)) + 1) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) (Set.Ioi 0) := by
      have h_integrable : ∀ {s b : ℝ}, -1 < s → 0 < b → IntegrableOn (fun y => y ^ s * Real.exp (-b * y)) (Set.Ioi 0) := by
        intro s b hs hb;
        convert ( integrableOn_rpow_mul_exp_neg_mul_rpow ( show -1 < s by linarith ) ( show 1 ≤ ( 1 : ℝ ) by norm_num ) hb ) using 1 ; norm_num;
      convert h_integrable _ _ using 1 <;> norm_num [ neg_div, div_neg ];
      congr! 1;
      · nlinarith [ show ( j : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hj ), mul_div_cancel₀ ( 2 - p ) ( by linarith : ( 1 - p ) ≠ 0 ) ];
      · exact div_pos ( Real.rpow_pos_of_pos hμ _ ) ( mul_pos hφ ( by linarith ) );
    refine' h_integrable.const_mul _ |> fun h => h.congr _;
    exact Real.exp ( -tw_z μ φ p ) * ( p - 1 ) ^ ( ( ( 2 - p ) / ( 1 - p ) ) * j ) / ( φ ^ ( ( j : ℝ ) * ( 1 - ( 2 - p ) / ( 1 - p ) ) ) * ( 2 - p ) ^ j * ( j.factorial : ℝ ) * Real.Gamma ( - ( j : ℝ ) * ( ( 2 - p ) / ( 1 - p ) ) ) );
    filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with y hy using by rw [ tw_y2G_pt μ hp₁ hφ j hy ] ;

/-
Recurrence relating the second-moment per-term integral to the mean per-term integral:
`∫ y², G_j = ((-jα+1)·(1/b)) · ∫ y, G_j`, where `b = μ^(1-p)/(φ(p-1))`, i.e. `1/b = φ(p-1)/μ^(1-p)`.
This follows from `∫ y^(s+1) e^{-by} = ((s+1)/b) ∫ y^s e^{-by}` (a Gamma recurrence).
-/
lemma tw_2nd_moment_recurrence {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ)
    (j : ℕ) :
    ∫ y in Set.Ioi (0:ℝ), y ^ 2 * tw_G μ φ p j y
      = ((-(j:ℝ)*((2-p)/(1-p)) + 1) * (φ * (p-1) / μ^(1-p)))
        * ∫ y in Set.Ioi (0:ℝ), y * tw_G μ φ p j y := by
  by_cases hj : j = 0;
  · unfold tw_G; aesop;
  · have h_integral : ∫ y in Set.Ioi (0:ℝ), y ^ 2 * tw_G μ φ p j y = (∫ y in Set.Ioi (0:ℝ), y ^ (-(j:ℝ)*((2-p)/(1-p)) + 1) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) * (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ)) / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j) * Real.Gamma (-(j:ℝ)*((2-p)/(1-p))))) := by
      rw [ ← MeasureTheory.integral_mul_const ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => _ ; rw [ tw_y2G_pt μ hp₁ hφ j hy ] ; ring;
    have h_integral : ∫ y in Set.Ioi (0:ℝ), y * tw_G μ φ p j y = (∫ y in Set.Ioi (0:ℝ), y ^ (-(j:ℝ)*((2-p)/(1-p))) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) * (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ)) / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j) * Real.Gamma (-(j:ℝ)*((2-p)/(1-p))))) := by
      rw [ ← MeasureTheory.integral_mul_const ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => _ ; rw [ tw_yG_pt μ hp₁ hφ j hy ] ; ring;
    rw [ ‹∫ y in Set.Ioi 0, y ^ 2 * tw_G μ φ p j y = _›, h_integral ];
    have h_integral : ∫ y in Set.Ioi (0:ℝ), y ^ (-(j:ℝ)*((2-p)/(1-p)) + 1) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y)) = (1 / (μ ^ (1 - p) / (φ * (p - 1)))) ^ (-(j:ℝ)*((2-p)/(1-p)) + 2) * Real.Gamma (-(j:ℝ)*((2-p)/(1-p)) + 2) := by
      convert integral_rpow_mul_exp_neg_mul_Ioi _ _ using 1;
      · exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by ring_nf
      · nlinarith [ show ( j : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hj ), mul_div_cancel₀ ( 2 - p ) ( by linarith : ( 1 - p ) ≠ 0 ) ];
      · exact div_pos ( Real.rpow_pos_of_pos hμ _ ) ( mul_pos hφ ( by linarith ) );
    rw [ h_integral, show ( ∫ y in Set.Ioi 0, y ^ ( - ( j : ℝ ) * ( ( 2 - p ) / ( 1 - p ) ) ) * Real.exp ( - ( μ ^ ( 1 - p ) / ( φ * ( p - 1 ) ) * y ) ) ) = ( 1 / ( μ ^ ( 1 - p ) / ( φ * ( p - 1 ) ) ) ) ^ ( - ( j : ℝ ) * ( ( 2 - p ) / ( 1 - p ) ) + 1 ) * Real.Gamma ( - ( j : ℝ ) * ( ( 2 - p ) / ( 1 - p ) ) + 1 ) from ?_ ];
    · rw [ show ( -j * ( ( 2 - p ) / ( 1 - p ) ) + 2 : ℝ ) = ( -j * ( ( 2 - p ) / ( 1 - p ) ) + 1 ) + 1 by ring, Real.rpow_add_one ] <;> norm_num;
      · rw [ show ( - ( j * ( ( 2 - p ) / ( 1 - p ) ) ) + 1 + 1 : ℝ ) = ( - ( j * ( ( 2 - p ) / ( 1 - p ) ) ) + 1 ) + 1 by ring, Real.Gamma_add_one ( by nlinarith [ show ( j : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hj ), mul_div_cancel₀ ( 2 - p ) ( by linarith : ( 1 - p ) ≠ 0 ) ] ) ] ; ring;
      · exact ⟨ ⟨ hφ.ne', by linarith ⟩, by positivity ⟩;
    · convert integral_rpow_mul_exp_neg_mul_Ioi _ _ using 1;
      · norm_num;
      · nlinarith [ show ( j : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hj ), mul_div_cancel₀ ( 2 - p ) ( by linarith : ( 1 - p ) ≠ 0 ) ];
      · exact div_pos ( Real.rpow_pos_of_pos hμ _ ) ( mul_pos hφ ( by linarith ) )

/-- The per-term second-moment integral.  (Valid for all `j`, since both sides vanish at `j = 0`.) -/
lemma tw_2nd_moment_term {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) (j : ℕ) :
    ∫ y in Set.Ioi (0:ℝ), y ^ 2 * tw_G μ φ p j y
      = (φ * (2-p) / μ^(1-p)) * (φ * (p-1) / μ^(1-p))
        * (((j:ℝ) + (2-p)/(p-1) * (j:ℝ)^2) * Real.exp (-tw_z μ φ p)
            * (tw_z μ φ p) ^ j / (Nat.factorial j)) := by
  rw [tw_2nd_moment_recurrence hp₁ hp₂ hμ hφ, tw_mean_term hp₁ hp₂ hμ hφ]
  have h1p : (1 - p) ≠ 0 := by linarith
  have hpm1 : (p - 1) ≠ 0 := by linarith
  have hμp : μ ^ (1 - p) ≠ 0 := by positivity
  field_simp
  ring

/-
Summability of `fun j => (j:ℝ)^2 * z^j / j!` for any real `z`.
-/
lemma tw_summable_n2_pow (z : ℝ) :
    Summable (fun j : ℕ => (j:ℝ)^2 * z ^ j / (Nat.factorial j)) := by
  refine' summable_of_ratio_norm_eventually_le _ _;
  exact 2 / 3;
  · norm_num;
  · -- For large enough $n$, the term $(n+1) * |z| / n^2$ will be less than $2/3$.
    have h_bound : ∃ N : ℕ, ∀ n ≥ N, (n + 1) * |z| / n^2 ≤ 2 / 3 := by
      exact ⟨ ⌈3 * |z|⌉₊ + 1, fun n hn => by rw [ div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( 3 * |z| ), show ( n : ℝ ) ≥ ⌈3 * |z|⌉₊ + 1 by exact_mod_cast hn, abs_nonneg z ] ⟩;
    obtain ⟨ N, hN ⟩ := h_bound; filter_upwards [ Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0 ] with n hn hn' ; specialize hN n hn ; simp_all +decide [ Nat.factorial_succ]
    convert mul_le_mul_of_nonneg_right hN ( show 0 ≤ ( n ^ 2 * |z| ^ n / n.factorial : ℝ ) by positivity ) using 1 ; norm_cast ; ring_nf;
    -- Simplifying the right-hand side:
    field_simp
    ring_nf
    push_cast; ring;

/-
The "Poisson second moment" identity: `∑' j, j² z^j / j! = (z²+z) · exp z`.
-/
lemma tw_tsum_n2_pow (z : ℝ) :
    ∑' j : ℕ, (j:ℝ)^2 * z ^ j / (Nat.factorial j) = (z^2 + z) * Real.exp z := by
  -- We'll use the fact that $\sum_{j=0}^{\infty} j(j-1) \frac{z^j}{j!} = z^2 e^z$.
  have h1 : ∑' j : ℕ, (j * (j - 1) : ℝ) * z ^ j / j.factorial = z^2 * Real.exp z := by
    -- Split the sum into two parts: one for $j=0$ and $j=1$, and the rest.
    have h_split : ∑' j : ℕ, (j * (j - 1) : ℝ) * z^j / j.factorial = ∑' j : ℕ, if j ≥ 2 then (j * (j - 1) : ℝ) * z^j / j.factorial else 0 := by
      exact tsum_congr fun n => by rcases n with ( _ | _ | n ) <;> norm_num;
    -- For $j \geq 2$, we can simplify the term $(j * (j - 1) : ℝ) * z^j / j.factorial$ to $z^2 * z^{j-2} / (j-2)!$.
    have h_simplify : ∀ j : ℕ, j ≥ 2 → (j * (j - 1) : ℝ) * z^j / j.factorial = z^2 * z^(j-2) / (j-2).factorial := by
      intro j hj; rcases j with ( _ | _ | j ) <;> norm_num [ Nat.factorial ] at *;
      rw [ div_eq_div_iff ] <;> first | positivity | ring!;
    -- Substitute the simplified terms back into the sum.
    have h_sum_simplified : ∑' j : ℕ, (if j ≥ 2 then (j * (j - 1) : ℝ) * z^j / j.factorial else 0) = ∑' j : ℕ, z^2 * z^j / j.factorial := by
      rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
      use fun x => x.val - 2;
      · exact fun x y h => by rcases x with ⟨ _ | _ | x, hx ⟩ <;> rcases y with ⟨ _ | _ | y, hy ⟩ <;> cases h <;> trivial;
      · intro x hx; use ⟨ x + 2, by aesop ⟩ ; aesop;
      · aesop;
    simp_all +decide [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
    simp +decide only [mul_div_assoc];
    exact _root_.tsum_mul_left;
  convert congr_arg₂ ( · + · ) h1 ( tw_tsum_n_pow z ) using 1;
  · rw [ ← Summable.tsum_add ] ; congr ; ext j ; ring;
    · contrapose! h1;
      rw [ tsum_eq_zero_of_not_summable h1 ] ; norm_num [ Real.exp_ne_zero ];
      exact fun h => h1 <| by subst h; exact ⟨ _, hasSum_single 0 fun j hj => by aesop ⟩ ;
    · convert tw_summable_n_pow z using 1;
  · ring

/-
Summability of the second-moment integral norms (needed to swap `∫` and `∑'`).
-/
lemma tw_2nd_moment_summable_norm (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    Summable (fun j : ℕ => ∫ y in Set.Ioi (0:ℝ), ‖y ^ 2 * tw_G μ φ p j y‖) := by
  have h_summable : Summable (fun j : ℕ => ∫ y in Set.Ioi (0:ℝ), y ^ 2 * tw_G μ φ p j y) := by
    simp_all +decide [ tw_2nd_moment_term ];
    refine' Summable.mul_left _ _;
    convert Summable.add ( Summable.mul_left ( Real.exp ( -tw_z μ φ p ) ) ( tw_summable_n_pow ( tw_z μ φ p ) ) ) ( Summable.mul_left ( Real.exp ( -tw_z μ φ p ) * ( 2 - p ) / ( p - 1 ) ) ( tw_summable_n2_pow ( tw_z μ φ p ) ) ) using 2 ; ring;
  convert h_summable using 1
  generalize_proofs at *;
  exact funext fun j => MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => by rw [ Real.norm_of_nonneg ( mul_nonneg ( sq_nonneg _ ) ( tw_G_nonneg μ φ p hp₁ hp₂ hφ j hy ) ) ] ;

/-
The series of per-term second-moment values sums to `μ² + φ·μ^p`.
-/
lemma tw_2nd_moment_tsum {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    ∑' j : ℕ, (φ * (2-p) / μ^(1-p)) * (φ * (p-1) / μ^(1-p))
        * (((j:ℝ) + (2-p)/(p-1) * (j:ℝ)^2) * Real.exp (-tw_z μ φ p)
            * (tw_z μ φ p) ^ j / (Nat.factorial j))
      = μ^2 + φ * μ^p := by
  -- Factor out common terms and apply the series summations.
  have h_series : ∑' j : ℕ, (j + (2 - p) / (p - 1) * j^2) * Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / j.factorial =
    Real.exp (-tw_z μ φ p) * (tw_z μ φ p * Real.exp (tw_z μ φ p) + (2 - p) / (p - 1) * ((tw_z μ φ p)^2 + tw_z μ φ p) * Real.exp (tw_z μ φ p)) := by
      have h_series : ∑' j : ℕ, (j : ℝ) * tw_z μ φ p ^ j / j.factorial = tw_z μ φ p * Real.exp (tw_z μ φ p) ∧ ∑' j : ℕ, (j : ℝ) ^ 2 * tw_z μ φ p ^ j / j.factorial = (tw_z μ φ p ^ 2 + tw_z μ φ p) * Real.exp (tw_z μ φ p) := by
        exact ⟨ by simpa using tw_tsum_n_pow ( tw_z μ φ p ), by simpa using tw_tsum_n2_pow ( tw_z μ φ p ) ⟩;
      convert congr_arg₂ ( · + · ) ( congr_arg ( fun x : ℝ => x * Real.exp ( -tw_z μ φ p ) ) h_series.1 ) ( congr_arg ( fun x : ℝ => x * ( 2 - p ) * Real.exp ( -tw_z μ φ p ) / ( p - 1 ) ) h_series.2 ) using 1;
      · norm_num [ add_mul, mul_assoc, mul_div_assoc, tsum_mul_left, tsum_mul_right ];
        convert congr_arg₂ ( · + · ) ( tsum_mul_right ) ( tsum_mul_right ) using 1;
        · rw [ ← Summable.tsum_add ] ; congr ; ext j ; ring;
          · exact Summable.mul_right _ <| by simpa only [ mul_div_assoc ] using tw_summable_n_pow _;
          · convert Summable.mul_right ( ( 2 - p ) * ( Real.exp ( -tw_z μ φ p ) / ( p - 1 ) ) ) ( tw_summable_n2_pow ( tw_z μ φ p ) ) using 2 ; ring;
        · infer_instance;
        · infer_instance;
        · infer_instance;
        · infer_instance;
      · ring;
  convert congr_arg ( fun x : ℝ => ( φ * ( 2 - p ) / μ ^ ( 1 - p ) ) * ( φ * ( p - 1 ) / μ ^ ( 1 - p ) ) * x ) h_series using 1;
  · exact _root_.tsum_mul_left;
  · unfold tw_z; norm_num [ Real.rpow_sub hμ ] ; ring_nf
    norm_num [ Real.exp_neg, Real.exp_ne_zero ] ; ring_nf
    field_simp;
    grind

/-
The second moment of the continuous part: `∫ y, tweediePDF μ φ p y * y² = μ² + φ·μ^p`.
-/
lemma tweedie_2nd_moment_value {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    ∫ y, tweediePDF μ φ p y * y ^ 2 = μ^2 + φ * μ^p := by
  -- Apply the decomposition of the integral into the sum of integrals over the components and use the fact that the integral of `y^2` with respect to the point mass part is 0.
  have h_decomp : ∫ y, tweediePDF μ φ p y * y ^ 2 = ∫ y in Set.Ioi (0:ℝ), ∑' j : ℕ, y ^ 2 * tw_G μ φ p j y := by
    rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    congr with x ; by_cases hx : 0 < x <;> simp +decide [ hx, tweediePDF ];
    convert congr_arg ( fun y : ℝ => x ^ 2 * y ) ( tw_pointwise μ φ p x ) using 1 ; ring_nf
    exact _root_.tsum_mul_left;
  rw [ h_decomp, ← tw_2nd_moment_tsum hp₁ hp₂ hμ hφ, ← MeasureTheory.integral_tsum_of_summable_integral_norm ];
  · exact tsum_congr fun j => tw_2nd_moment_term hp₁ hp₂ hμ hφ j;
  · exact fun j => tw_y2G_integrable_on hp₁ hp₂ hμ hφ j;
  · convert tw_2nd_moment_summable_norm μ φ p hp₁ hp₂ hμ hφ using 1

/-
`tweediePDF μ φ p y * y²` is integrable.
-/
lemma tweedie_2nd_moment_integrable {μ φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    Integrable (fun y => tweediePDF μ φ p y * y ^ 2) := by
  have := tweedie_2nd_moment_value hp₁ hp₂ hμ hφ;
  exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; positivity )

/-
The second moment of the Tweedie measure equals `μ² + φ·μ^p`.
-/
theorem tweedieMeasure_2nd_moment {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    ∫ y, y ^ 2 ∂(tweedieMeasure μ (show (0:ℝ) ≤ φ by linarith) hp₁ hp₂) = μ^2 + φ * μ^p := by
  set f : ℝ → ℝ≥0 := fun y => (tweediePDF μ φ p y).toNNReal
  have h_withDensity : volume.withDensity (tweediePDF' μ hp₁ (by linarith) hφ.le) = volume.withDensity (fun y => f y) := by
    refine' MeasureTheory.withDensity_congr_ae _;
    filter_upwards [ ] with y using ( ENNReal.ofReal_eq_coe_nnreal _ ).symm;
  convert congr_arg ( fun x : ℝ => x + 0 ) ( tweedie_2nd_moment_value hp₁ ( by linarith ) hμ hφ ) using 1
  generalize_proofs at *;
  · unfold tweedieMeasure; norm_num [ h_withDensity ] ;
    rw [ MeasureTheory.integral_add_measure ] <;> norm_num [ tweedie_prob_zero ];
    · convert integral_withDensity_eq_integral_smul₀ _ ( fun y => y ^ 2 ) using 1;
      · congr! 1
        generalize_proofs at *;
        ext; simp [f]; ring_nf
        exact mul_eq_mul_right_iff.mpr ( Or.inl <| by rw [ Real.toNNReal_of_nonneg <| tweediePDF_nonneg ( by linarith ) hp₁ ( by linarith ) ] ; norm_cast );
      · have h_integrable : MeasureTheory.Integrable (fun y => tweediePDF μ φ p y) volume := by
          exact ( by by_contra h; have := tweediePDF_integral hp₁ ( by linarith ) hμ hφ; rw [ MeasureTheory.integral_undef h ] at this; linarith [ Real.exp_pos ( -μ ^ ( 2 - p ) / ( φ * ( 2 - p ) ) ), Real.exp_lt_one_iff.mpr ( show -μ ^ ( 2 - p ) / ( φ * ( 2 - p ) ) < 0 by exact div_neg_of_neg_of_pos ( neg_neg_of_pos ( Real.rpow_pos_of_pos hμ _ ) ) ( mul_pos hφ ( by linarith ) ) ) ] )
        generalize_proofs at *;
        exact h_integrable.1.aemeasurable.real_toNNReal;
    · constructor;
      · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      · simp +decide [ HasFiniteIntegral ];
    · have h_integrable : Integrable (fun y => f y • y ^ 2) volume := by
        convert tweedie_2nd_moment_integrable hp₁ hp₂ hμ hφ using 1
        generalize_proofs at *;
        ext y; exact mul_eq_mul_right_iff.mpr (Or.inl <| Real.coe_toNNReal _ <| tweediePDF_nonneg (by linarith) hp₁ (by linarith));
      rw [ MeasureTheory.integrable_withDensity_iff_integrable_smul₀ ];
      · exact h_integrable;
      · have h_integrable : AEMeasurable (fun y => tweediePDF μ φ p y) volume := by
          have h_integrable : Integrable (fun y => tweediePDF μ φ p y) volume := by
            exact ( by by_contra h; have := tweediePDF_integral hp₁ ( by linarith ) hμ hφ; rw [ MeasureTheory.integral_undef h ] at this; linarith [ Real.exp_pos ( -μ ^ ( 2 - p ) / ( φ * ( 2 - p ) ) ), Real.exp_lt_one_iff.mpr ( show -μ ^ ( 2 - p ) / ( φ * ( 2 - p ) ) < 0 by exact div_neg_of_neg_of_pos ( neg_neg_of_pos ( Real.rpow_pos_of_pos hμ _ ) ) ( mul_pos hφ ( by linarith ) ) ) ] )
          generalize_proofs at *; exact h_integrable.1.aemeasurable;
        generalize_proofs at *;
        exact AEMeasurable.real_toNNReal h_integrable;
  · ring

/-- The second moment of the Tweedie probability measure equals `μ² + φ·μ^p`. -/
theorem tweedieProbMeasure_2nd_moment {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    ∫ y, y ^ 2 ∂ (tweedieProbMeasure hμ hφ hp₁ hp₂) = μ^2 + φ * μ^p :=
  tweedieMeasure_2nd_moment hμ hφ hp₁ hp₂

/-- **The variance of the Tweedie distribution is `φ · μ^p`.**
Here the variance is expressed as `E[Y²] - (E[Y])²`. -/
theorem tweedieProbMeasure_variance {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    (∫ y, y ^ 2 ∂ (tweedieProbMeasure hμ hφ hp₁ hp₂))
      - (∫ y, y ∂ (tweedieProbMeasure hμ hφ hp₁ hp₂)) ^ 2 = φ * μ^p := by
  rw [tweedieProbMeasure_2nd_moment hμ hφ hp₁ hp₂, tweedieProbMeasure_expectation hμ hφ hp₁ hp₂]
  ring

/-
`y ↦ y²` is integrable with respect to the Tweedie measure
(the second moment is finite).
-/
lemma tweedieMeasure_sq_integrable {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    Integrable (fun y => y ^ 2) (tweedieMeasure μ (show (0:ℝ) ≤ φ by linarith) hp₁ hp₂) := by
  by_contra h_contra;
  have := tweedieMeasure_2nd_moment hμ hφ hp₁ hp₂; rw [ MeasureTheory.integral_undef h_contra ] at this; nlinarith [ Real.rpow_pos_of_pos hμ p ] ;

/-- **The variance of the Tweedie distribution is `φ · μ^p`**, stated with Mathlib's
`ProbabilityTheory.variance` (`Var[Y] = 𝔼[(Y - 𝔼[Y])²]`). -/
theorem tweedieMeasure_variance {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    ProbabilityTheory.variance (fun y => y)
        (tweedieMeasure μ (show (0:ℝ) ≤ φ by linarith) hp₁ hp₂) = φ * μ^p := by
  haveI : IsProbabilityMeasure (tweedieMeasure μ (show (0:ℝ) ≤ φ by linarith) hp₁ hp₂) :=
    tweedieMeasure_prob μ hμ hφ hp₁ hp₂
  have hmem : MemLp (fun y => y) 2 (tweedieMeasure μ (show (0:ℝ) ≤ φ by linarith) hp₁ hp₂) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (by fun_prop)]
    exact tweedieMeasure_sq_integrable hμ hφ hp₁ hp₂
  rw [ProbabilityTheory.variance_eq_sub hmem]
  simp only [Pi.pow_apply]
  rw [tweedieMeasure_2nd_moment hμ hφ hp₁ hp₂, tweedieMeasure_expectation hμ hφ hp₁ hp₂]
  ring
