/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.AlphaLeakage.Basic

/-!
# α-leakage

Liao, Kosut, Sankar and Calmon (*Tunable measures for information leakage and applications to
privacy-utility tradeoffs*, IEEE Trans. Inf. Theory 65(12), 2019, arXiv:1809.09231) measure how
much an adversary learns about `X` from `Y` through the **α-loss**
`ℓ_a(x, y, P_{X̂|Y}) = a / (a - 1) · (1 - P_{X̂|Y}(x | y) ^ ((a - 1) / a))` of a soft estimator
`P_{X̂|Y}` (their eq. (19)). Minimizing the expected α-loss amounts to maximizing the *gain*
`E[P_{X̂|Y}(X | Y) ^ ((a - 1) / a)]` (their eq. (29)), and the **α-leakage** (their Definition 5)
compares the best gain with and without observing `Y`:
`L_a(X → Y) = a / (a - 1) · log (max_{P_{X̂|Y}} E[P_{X̂|Y}(X | Y) ^ ((a - 1) / a)] /
  max_{P_{X̂}} E[P_{X̂}(X) ^ ((a - 1) / a)])`.

We formalize this operational definition for `a ∈ (1, ∞)` and finite alphabets, and prove their
Theorem 1: α-leakage is the Arimoto mutual information of order `a`. The key step (their
Lemma 1, eqs. (79)–(80)) is Hölder's inequality: over probability vectors `q`,
`∑_x p(x) q(x) ^ ((a - 1) / a)` is maximized by the escort vector `q ∝ p ^ a`, with maximum
`‖p‖_a = (∑_x p(x) ^ a) ^ (1 / a)`.

## Main definitions

* `alphaLeakageRatio a π`: the ratio of the best gains, with the suprema taken over all Markov
  kernels `P_{X̂|Y}` and all probability measures `P_{X̂}`; in `ℝ≥0∞`.
* `alphaLeakage a π`: the α-leakage `a / (a - 1) · log (alphaLeakageRatio a π)`, in nats.

## Main statements

* `sum_mul_rpow_le_rpow_sum`, `sum_mul_rpow_div_eq`: the optimization behind Lemma 1.
* `iSup_lintegral_gain_eq`: **Lemma 1** in multiplicative form: the best gain from observing `Y`
  is `∑_y ‖P_{X,Y}(·, y)‖_a`, i.e. `exp ((1 - a) / a · H^A_a(X | Y))`.
* `iSup_lintegral_blindGain_eq`: the best blind gain is `‖P_X‖_a`.
* `alphaLeakageRatio_eq_arimotoSum`, `alphaLeakage_eq_arimotoMI`: **Theorem 1**,
  `L_a(X → Y) = I^A_a(X; Y)` for `a ∈ (1, ∞)`.
* `alphaLeakage_nonneg`: α-leakage is nonnegative.

The endpoint cases `a = 1` (mutual information) and `a = ∞`, which the paper defines by continuous
extension, are not formalized here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {π : Measure (α × β)} {a : ℝ}

/-- The multiplicative form of the α-leakage of Definition 5 of Liao–Kosut–Sankar–Calmon: the
ratio of the best expected gain `E[P_{X̂|Y}(X | Y) ^ ((a - 1) / a)]` over all estimators
`P_{X̂|Y}` (Markov kernels `β → α`) observing `Y`, to the best expected gain
`E[P_{X̂}(X) ^ ((a - 1) / a)]` over all blind estimators `P_{X̂}` (probability measures on `α`),
for `(X, Y) ∼ π`. -/
noncomputable def alphaLeakageRatio (a : ℝ) (π : Measure (α × β)) : ℝ≥0∞ :=
  (⨆ (g : Kernel β α) (_ : IsMarkovKernel g), ∫⁻ p, g p.2 {p.1} ^ ((a - 1) / a) ∂π) /
    ⨆ (q : Measure α) (_ : IsProbabilityMeasure q), ∫⁻ x, q {x} ^ ((a - 1) / a) ∂π.fst

/-- The **α-leakage** `L_a(X → Y)` of Definition 5 of Liao–Kosut–Sankar–Calmon, for a joint law
`π` of `(X, Y)` and an order `a ∈ (1, ∞)`, in nats:
`a / (a - 1) · log (max_{P_{X̂|Y}} E[P_{X̂|Y}(X | Y) ^ ((a - 1) / a)] /
  max_{P_{X̂}} E[P_{X̂}(X) ^ ((a - 1) / a)])`. -/
noncomputable def alphaLeakage (a : ℝ) (π : Measure (α × β)) : ℝ :=
  a / (a - 1) * Real.log (alphaLeakageRatio a π).toReal

section Holder

variable [Fintype α]

omit [MeasurableSpace α] in
/-- Hölder's inequality behind Lemma 1 of Liao–Kosut–Sankar–Calmon: for a probability vector
`q`, `∑_x p(x) q(x) ^ ((a - 1) / a) ≤ ‖p‖_a`. -/
lemma sum_mul_rpow_le_rpow_sum (ha : 1 < a) (p q : α → ℝ≥0∞) (hq : ∑ x, q x = 1) :
    ∑ x, p x * q x ^ ((a - 1) / a) ≤ (∑ x, p x ^ a) ^ a⁻¹ := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb : 1 - a⁻¹ ≠ 0 := (sub_pos.2 (inv_lt_one_of_one_lt₀ ha)).ne'
  have hpq : a.HolderConjugate (1 - a⁻¹)⁻¹ := by
    simpa using Real.HolderConjugate.inv_one_sub_inv (inv_pos.2 ha0) (inv_lt_one_of_one_lt₀ ha)
  have hr : (a - 1) / a = 1 - a⁻¹ := by field_simp
  calc ∑ x, p x * q x ^ ((a - 1) / a)
      ≤ (∑ x, p x ^ a) ^ (1 / a) *
          (∑ x, (q x ^ ((a - 1) / a)) ^ (1 - a⁻¹)⁻¹) ^ (1 / (1 - a⁻¹)⁻¹) :=
        ENNReal.inner_le_Lp_mul_Lq _ _ _ hpq
    _ = (∑ x, p x ^ a) ^ a⁻¹ := by
        simp_rw [hr, ← ENNReal.rpow_mul, mul_inv_cancel₀ hb, ENNReal.rpow_one, hq,
          ENNReal.one_rpow, mul_one, one_div]

omit [MeasurableSpace α] in
/-- The escort vector `q = p ^ a / ‖p‖_a ^ a` attains equality in `sum_mul_rpow_le_rpow_sum`
(eq. (80) of Liao–Kosut–Sankar–Calmon). -/
lemma sum_mul_rpow_div_eq (ha : 1 < a) (p : α → ℝ≥0∞) (hp : ∀ x, p x ≠ ∞)
    (h0 : ∑ x, p x ^ a ≠ 0) :
    ∑ x, p x * (p x ^ a / ∑ x', p x' ^ a) ^ ((a - 1) / a) = (∑ x, p x ^ a) ^ a⁻¹ := by
  set S := ∑ x', p x' ^ a
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hr0 : 0 ≤ (a - 1) / a := div_nonneg (by linarith) ha0.le
  have hS : S ≠ ∞ := ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.rpow_ne_top_of_nonneg ha0.le (hp x)
  have hmul : a * ((a - 1) / a) = a - 1 := by field_simp
  have h_term (x : α) : p x * (p x ^ a / S) ^ ((a - 1) / a) = p x ^ a / S ^ ((a - 1) / a) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ hr0, ← ENNReal.rpow_mul, hmul, ← mul_div_assoc]
    congr 1
    conv_rhs => rw [← sub_add_cancel a 1]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one, mul_comm]
  simp_rw [h_term, ← ENNReal.sum_div]
  calc S / S ^ ((a - 1) / a) = S ^ (1 : ℝ) / S ^ ((a - 1) / a) := by rw [ENNReal.rpow_one]
    _ = S ^ (1 - (a - 1) / a) := (ENNReal.rpow_sub _ _ h0 hS).symm
    _ = S ^ a⁻¹ := by
        congr 1
        field_simp
        ring

end Holder

section Gain

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

lemma lintegral_alphaGain_eq_sum (π : Measure (α × β)) (g : Kernel β α) :
    ∫⁻ p, g p.2 {p.1} ^ ((a - 1) / a) ∂π = ∑ y, ∑ x, π {(x, y)} * g y {x} ^ ((a - 1) / a) := by
  rw [lintegral_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [mul_comm]

/-- **Lemma 1 of Liao–Kosut–Sankar–Calmon**, multiplicative form: for `a ∈ (1, ∞)`, the best
expected gain `max_{P_{X̂|Y}} E[P_{X̂|Y}(X | Y) ^ ((a - 1) / a)]` is
`∑_y ‖P_{X,Y}(·, y)‖_a`. The gain identity holds for any finite measure `π`. When `π` is a
probability measure, this equals `exp ((1 - a) / a · H^A_a(X | Y))`, and equivalently the minimal
expected α-loss is `a / (a - 1) · (1 - ∑_y ‖P_{X,Y}(·, y)‖_a)` (eq. (22)), attained by the
estimator `P_{X̂|Y}(x | y) ∝ P_{X|Y}(x | y) ^ a` of eq. (23). -/
theorem iSup_lintegral_gain_eq (ha : 1 < a) [IsFiniteMeasure π] [Nonempty α] :
    (⨆ (g : Kernel β α) (_ : IsMarkovKernel g), ∫⁻ p, g p.2 {p.1} ^ ((a - 1) / a) ∂π) =
      ∑ y, (∑ x, π {(x, y)} ^ a) ^ a⁻¹ := by
  classical
  have ha0 : 0 < a := zero_lt_one.trans ha
  refine le_antisymm (iSup₂_le fun g _ ↦ ?_) ?_
  · rw [lintegral_alphaGain_eq_sum]
    exact Finset.sum_le_sum fun y _ ↦
      sum_mul_rpow_le_rpow_sum ha _ _ (by simp [sum_measure_singleton])
  -- The optimal estimator: the escort of the column `π (·, y)`, or a point mass if it vanishes.
  obtain ⟨x₀⟩ := ‹Nonempty α›
  set S : β → ℝ≥0∞ := fun y ↦ ∑ x, π {(x, y)} ^ a
  have hS_top (y : β) : S y ≠ ∞ := ENNReal.sum_ne_top.2 fun x _ ↦
    ENNReal.rpow_ne_top_of_nonneg ha0.le (measure_ne_top π _)
  set w : β → α → ℝ≥0∞ := fun y x ↦
    if S y = 0 then (if x = x₀ then 1 else 0) else π {(x, y)} ^ a / S y
  set g : Kernel β α := Kernel.ofFunOfCountable fun y ↦ ∑ x, w y x • Measure.dirac x
  have hg (y : β) (x : α) : g y {x} = w y x := sum_smul_dirac_apply_singleton _ _
  have hw (y : β) : ∑ x, w y x = 1 := by
    by_cases hy : S y = 0
    · simp [w, hy]
    · simp only [w, hy, ite_false]
      rw [← ENNReal.sum_div]
      exact ENNReal.div_self hy (hS_top y)
  have : IsMarkovKernel g := ⟨fun y ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hg, hw]⟩⟩
  refine le_iSup₂_of_le g this (le_of_eq ?_)
  rw [lintegral_alphaGain_eq_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hy : S y = 0
  · have h0 (x : α) : π {(x, y)} = 0 :=
      (ENNReal.rpow_eq_zero_iff_of_pos ha0).1 (Finset.sum_eq_zero_iff.1 hy x (Finset.mem_univ x))
    simp only [h0, zero_mul, Finset.sum_const_zero, ENNReal.zero_rpow_of_pos ha0,
      ENNReal.zero_rpow_of_pos (inv_pos.2 ha0)]
  · simp_rw [hg, w, hy, ite_false]
    exact (sum_mul_rpow_div_eq ha _ (fun x ↦ measure_ne_top π _) hy).symm

omit [Fintype β] [MeasurableSingletonClass β] in
/-- The best blind gain `max_{P_{X̂}} E[P_{X̂}(X) ^ ((a - 1) / a)]` for `X ∼ ρ` is `‖ρ‖_a`
(eq. (87) of Liao–Kosut–Sankar–Calmon). For `ρ ≠ 0` it is attained by the escort distribution
of `ρ`; for `ρ = 0` every probability estimator attains it (when `α` is nonempty). -/
theorem iSup_lintegral_blindGain_eq (ha : 1 < a) (ρ : Measure α) [IsFiniteMeasure ρ] :
    (⨆ (q : Measure α) (_ : IsProbabilityMeasure q), ∫⁻ x, q {x} ^ ((a - 1) / a) ∂ρ) =
      (∑ x, ρ {x} ^ a) ^ a⁻¹ := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  refine le_antisymm (iSup₂_le fun q _ ↦ ?_) ?_
  · rw [lintegral_fintype]
    simp_rw [mul_comm]
    exact sum_mul_rpow_le_rpow_sum ha _ _ (by simp [sum_measure_singleton])
  by_cases h0 : ∑ x, ρ {x} ^ a = 0
  · simp [h0, ENNReal.zero_rpow_of_pos (inv_pos.2 ha0)]
  have hρ : ρ ≠ 0 := by
    rintro rfl
    simp [ENNReal.zero_rpow_of_pos ha0] at h0
  have := isProbabilityMeasure_escort ha0 hρ
  refine le_iSup₂_of_le (escort a ρ) this (le_of_eq ?_)
  rw [lintegral_fintype, ← sum_mul_rpow_div_eq ha _ (fun x ↦ measure_ne_top ρ _) h0]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [escort_singleton, mul_comm, ENNReal.div_eq_inv_mul]

/-- **Theorem 1 of Liao–Kosut–Sankar–Calmon**, multiplicative form: for `a ∈ (1, ∞)`, the ratio of
best gains defining α-leakage is `∑_y ‖P_{X,Y}(·, y)‖_a / ‖P_X‖_a`. -/
theorem alphaLeakageRatio_eq_arimotoSum (ha : 1 < a) [IsProbabilityMeasure π] :
    alphaLeakageRatio a π = arimotoSum a π := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure π.fst
  rw [alphaLeakageRatio, iSup_lintegral_gain_eq ha, iSup_lintegral_blindGain_eq ha, arimotoSum]

/-- **Theorem 1 of Liao–Kosut–Sankar–Calmon**: for `a ∈ (1, ∞)`, the α-leakage from `X` to `Y`
is the Arimoto mutual information of order `a`, `L_a(X → Y) = I^A_a(X; Y)`. -/
theorem alphaLeakage_eq_arimotoMI (ha : 1 < a) [IsProbabilityMeasure π] :
    alphaLeakage a π = arimotoMI a π := by
  rw [alphaLeakage, arimotoMI, alphaLeakageRatio_eq_arimotoSum ha]

omit [Fintype α] [Fintype β] in
/-- α-leakage is nonnegative for `a ∈ (1, ∞)`. -/
lemma alphaLeakage_nonneg [Finite α] [Finite β] (ha : 1 < a) [IsProbabilityMeasure π] :
    0 ≤ alphaLeakage a π := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [alphaLeakage_eq_arimotoMI ha]
  exact arimotoMI_nonneg ha

end Gain

end InformationTheory
