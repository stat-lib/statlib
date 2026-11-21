/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.DP.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Probability.Kernel.WithDensity

/-!
# The exponential mechanism

The exponential mechanism privately selects an element of a set `R` of candidate outputs
according to a score (utility) function `u : 𝒟 → R → ℝ`. It is due to F. McSherry and
K. Talwar, *Mechanism design via differential privacy*, FOCS 2007, whose mechanism outputs `r`
with probability proportional to `exp (ε u(x, r)) μ(r)` for a base measure `μ` on a general range
and is `2εΔ`-differentially private when `u` has sensitivity `Δ`. We formalize the calibrated
version of C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Found.
Trends Theor. Comput. Sci. 9(3–4), 2014, Section 3.4 (result numbers refer to this book): on a
finite set `R`, output `r ∈ R` on dataset `x` with probability proportional to
`exp (ε u(x, r) / (2Δ))`, which is `ε`-differentially private.

The mechanism is a Markov kernel `𝒟 → R`, built as the measure with density
`exponentialMechanismProb u ε Δ x` with respect to the counting measure on the finite set `R`.
Privacy is measured with `IsEpsDeltaDP` from `Statlib.Privacy.DP.Basic` at `δ = 0` (pure
`ε`-differential privacy) for an arbitrary neighbouring relation `Adj` on datasets. The
sensitivity is a hypothesis: `Δ > 0` is any upper bound on `|u(x, r) - u(x', r)|` over
neighbouring `x, x'` and all `r` (Dwork–Roth use the exact sensitivity `Δu`, the smallest such
bound). The dataset space `𝒟` is an arbitrary measurable space, `R` is assumed nonempty, and
the scores `x ↦ u(x, r)` are assumed measurable, so that the construction is the mechanism of
Definition 3.4 (`exponentialMechanism_apply`, `isMarkovKernel_exponentialMechanism`). When the
density is not jointly measurable, or `R` is empty, the `Kernel.withDensity` construction
degenerates to the zero kernel (see `exponentialMechanism`).

## Main definitions

* `exponentialMechanismProb u ε Δ x r`: the probability
  `exp (ε u(x, r) / (2Δ)) / ∑_{r'} exp (ε u(x, r') / (2Δ))` of outputting `r` on dataset `x`.
* `exponentialMechanism u ε Δ`: the exponential mechanism (Definition 3.4) as a kernel `𝒟 → R`.

## Main statements (source result → Lean name)

* The exponential mechanism is a Markov kernel when `R` is nonempty and the scores are
  measurable in the dataset: `isMarkovKernel_exponentialMechanism`.
* Theorem 3.10 (privacy, for nonempty `R`): `isEpsDeltaDP_exponentialMechanism`, via the
  pointwise likelihood-ratio bound `exponentialMechanismProb_le_exp_mul`.
* The key estimate in the proof of Theorem 3.11,
  `P[u(x, M(x)) ≤ c] ≤ (|R| / |R_OPT|) exp (ε (c - OPT_u(x)) / (2Δ))`:
  `exponentialMechanism_real_le`.
* Theorem 3.11 (utility, with `|R_OPT|`): `exponentialMechanism_utility`.
* Corollary 3.12 (utility, with `|R_OPT| ≥ 1`): `exponentialMechanism_utility_log_card`.

## Not formalized

* Infinite output ranges `R`: Dwork–Roth assume `R` finite only "for clarity" in the proof of
  Theorem 3.10 and note it is not necessary, and McSherry–Talwar work with a base measure on a
  general range. Here `R` is a finite type with the counting measure.
* General base measures `μ` in McSherry–Talwar's form. (With `μ` the counting measure on a
  finite `R`, their mechanism `exp (ε u(x, r))` is `exponentialMechanism u (2 * ε * Δ) Δ` by
  `exponentialMechanismProb_two_mul_mul`, and `isEpsDeltaDP_exponentialMechanism` gives their
  `2εΔ` guarantee.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

namespace InformationTheory

variable {𝒟 R : Type*}

namespace ExponentialMechanism

/-- A kernel `x ↦ μ.withDensity (f x)` with jointly measurable, normalizable densities
satisfying the pointwise bound `f x ≤ e^ε f x'` on neighbours is `ε`-differentially private. -/
lemma isEpsDeltaDP_withDensity_const {𝒟 Y : Type*} [MeasurableSpace 𝒟] [MeasurableSpace Y]
    {μ : Measure Y} [SFinite μ] {f : 𝒟 → Y → ℝ≥0∞} {Adj : 𝒟 → 𝒟 → Prop} {ε : ℝ}
    (hf : Measurable (Function.uncurry f)) (hfin : ∀ x, ∫⁻ y, f x y ∂μ ≠ ∞)
    (h : ∀ ⦃x x'⦄, Adj x x' → ∀ y, f x y ≤ ENNReal.ofReal (exp ε) * f x' y) :
    IsEpsDeltaDP ((Kernel.const 𝒟 μ).withDensity f) Adj ε 0 := by
  intro x x' hx E
  simp only [Kernel.withDensity_apply _ hf, Kernel.const_apply, add_zero]
  have hle : μ.withDensity (f x) E ≤ ENNReal.ofReal (exp ε) * μ.withDensity (f x') E := by
    have hμ : μ.withDensity (f x) ≤ ENNReal.ofReal (exp ε) • μ.withDensity (f x') := by
      rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      exact withDensity_mono (ae_of_all _ (h hx))
    simpa using hμ E
  have hfin' : μ.withDensity (f x') E ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ E))
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hfin x'
  rw [measureReal_def, measureReal_def, ← ENNReal.toReal_ofReal (exp_pos ε).le,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin') hle

end ExponentialMechanism

open ExponentialMechanism

variable [Fintype R] {u : 𝒟 → R → ℝ} {ε Δ : ℝ}

/-- The probability that the exponential mechanism with score `u`, privacy parameter `ε` and
sensitivity bound `Δ` outputs `r` on dataset `x`:
`exp (ε u(x, r) / (2Δ)) / ∑_{r'} exp (ε u(x, r') / (2Δ))`. -/
noncomputable def exponentialMechanismProb (u : 𝒟 → R → ℝ) (ε Δ : ℝ) (x : 𝒟) (r : R) : ℝ :=
  exp (ε * u x r / (2 * Δ)) / ∑ r', exp (ε * u x r' / (2 * Δ))

namespace ExponentialMechanism

lemma one_le_card_filter_eq_ciSup [Nonempty R] (u : 𝒟 → R → ℝ) (x : 𝒟) :
    1 ≤ #{r | u x r = ⨆ r', u x r'} := by
  obtain ⟨r, hr⟩ := exists_eq_ciSup_of_finite (f := u x)
  exact Finset.card_pos.2 ⟨r, Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩⟩

lemma sum_exp_pos [Nonempty R] (u : 𝒟 → R → ℝ) (ε Δ : ℝ) (x : 𝒟) :
    0 < ∑ r, exp (ε * u x r / (2 * Δ)) :=
  Finset.sum_pos (fun _ _ ↦ exp_pos _) Finset.univ_nonempty

end ExponentialMechanism

lemma exponentialMechanismProb_nonneg (u : 𝒟 → R → ℝ) (ε Δ : ℝ) (x : 𝒟) (r : R) :
    0 ≤ exponentialMechanismProb u ε Δ x r :=
  div_nonneg (exp_pos _).le (Finset.sum_nonneg fun _ _ ↦ (exp_pos _).le)

/-- The output probabilities of the exponential mechanism sum to one. -/
lemma sum_exponentialMechanismProb [Nonempty R] (u : 𝒟 → R → ℝ) (ε Δ : ℝ) (x : 𝒟) :
    ∑ r, exponentialMechanismProb u ε Δ x r = 1 := by
  simp_rw [exponentialMechanismProb, ← Finset.sum_div]
  exact div_self (sum_exp_pos u ε Δ x).ne'

/-- McSherry–Talwar's uncalibrated mechanism with counting base measure, which outputs `r` with
probability proportional to `exp (ε u(x, r))`, is the calibrated mechanism with parameter
`2εΔ`. -/
lemma exponentialMechanismProb_two_mul_mul (hΔ : Δ ≠ 0) (x : 𝒟) (r : R) :
    exponentialMechanismProb u (2 * ε * Δ) Δ x r =
      exp (ε * u x r) / ∑ r', exp (ε * u x r') := by
  have h (r : R) : 2 * ε * Δ * u x r / (2 * Δ) = ε * u x r := by field_simp
  simp only [exponentialMechanismProb, h]

/-- **The likelihood ratio of the exponential mechanism is at most `e^ε`** (the computation in
the proof of Dwork–Roth, Theorem 3.10): if `|u(x, r') - u(x', r')| ≤ Δ` for all `r'`, then
`P[M(x) = r] ≤ e^ε P[M(x') = r]`. Half of the budget pays for the score of `r` and half for the
change of the normalizing constant. -/
lemma exponentialMechanismProb_le_exp_mul (hε : 0 ≤ ε) (hΔ : 0 < Δ) {x x' : 𝒟}
    (hu : ∀ r, |u x r - u x' r| ≤ Δ) (r : R) :
    exponentialMechanismProb u ε Δ x r ≤ exp ε * exponentialMechanismProb u ε Δ x' r := by
  have : Nonempty R := ⟨r⟩
  -- each unnormalized weight changes by a factor at most `e^{ε/2}`
  have hw (x x' : 𝒟) (hu : ∀ r, |u x r - u x' r| ≤ Δ) (r : R) :
      exp (ε * u x r / (2 * Δ)) ≤ exp (ε / 2) * exp (ε * u x' r / (2 * Δ)) := by
    have key : ε * u x r ≤ ε * Δ + ε * u x' r := by
      nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 (hu r)).2 hε]
    rw [← exp_add, exp_le_exp, show ε / 2 = ε * Δ / (2 * Δ) by field_simp, ← add_div]
    gcongr
  have hZ : ∑ r, exp (ε * u x' r / (2 * Δ)) ≤ exp (ε / 2) * ∑ r, exp (ε * u x r / (2 * Δ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ ↦ hw x' x (fun r ↦ by rw [abs_sub_comm]; exact hu r) r
  have hZx := sum_exp_pos u ε Δ x
  have hZx' := sum_exp_pos u ε Δ x'
  unfold exponentialMechanismProb
  rw [mul_div_assoc', div_le_div_iff₀ hZx hZx']
  calc exp (ε * u x r / (2 * Δ)) * ∑ r, exp (ε * u x' r / (2 * Δ))
      ≤ (exp (ε / 2) * exp (ε * u x' r / (2 * Δ))) *
          (exp (ε / 2) * ∑ r, exp (ε * u x r / (2 * Δ))) := by
        gcongr
        exact hw x x' hu r
    _ = exp ε * exp (ε * u x' r / (2 * Δ)) * ∑ r, exp (ε * u x r / (2 * Δ)) := by
        rw [show exp ε = exp (ε / 2) * exp (ε / 2) by rw [← exp_add, add_halves]]
        ring

variable [MeasurableSpace 𝒟] [MeasurableSpace R] [MeasurableSingletonClass R]

/-- **The exponential mechanism** `M_E(x, u, R)` (Dwork–Roth, Definition 3.4, after
McSherry–Talwar): on dataset `x`, output `r ∈ R` with probability proportional to
`exp (ε u(x, r) / (2Δ))`. It is built as `Kernel.withDensity` of the constant counting-measure
kernel with density `(x, r) ↦ exponentialMechanismProb u ε Δ x r`. This describes the intended
distribution only under two conditions:
* the **density** is jointly measurable (`Kernel.withDensity` returns the **zero kernel**
  otherwise). Measurability of each score `x ↦ u(x, r)` suffices (`exponentialMechanism_apply`),
  but the test is on the density, not on the raw scores: a non-measurable offset added to all
  scores cancels in the normalization;
* `R` is nonempty, so that the normalizing sum is positive and the masses sum to one (for empty
  `R` the kernel is zero).

Under both it is a Markov kernel (`isMarkovKernel_exponentialMechanism`, stated with the
sufficient condition that the scores are measurable). -/
noncomputable def exponentialMechanism (u : 𝒟 → R → ℝ) (ε Δ : ℝ) : Kernel 𝒟 R :=
  (Kernel.const 𝒟 Measure.count).withDensity
    fun x r ↦ ENNReal.ofReal (exponentialMechanismProb u ε Δ x r)

namespace ExponentialMechanism

lemma measurable_uncurry (hu : ∀ r, Measurable fun x ↦ u x r) :
    Measurable (Function.uncurry fun x r ↦ ENNReal.ofReal (exponentialMechanismProb u ε Δ x r)) :=
  measurable_from_prod_countable_left fun r ↦ by
    have hw (r : R) : Measurable fun x ↦ exp (ε * u x r / (2 * Δ)) :=
      (((hu r).const_mul ε).div_const _).exp
    exact ((hw r).div (Finset.measurable_sum _ fun r _ ↦ hw r)).ennreal_ofReal

end ExponentialMechanism

lemma exponentialMechanism_apply (hu : ∀ r, Measurable fun x ↦ u x r) (x : 𝒟) :
    exponentialMechanism u ε Δ x =
      Measure.count.withDensity fun r ↦ ENNReal.ofReal (exponentialMechanismProb u ε Δ x r) := by
  rw [exponentialMechanism, Kernel.withDensity_apply _ (measurable_uncurry hu), Kernel.const_apply]

/-- The probability that the exponential mechanism outputs an element of `E` is
`∑_{r ∈ E} P[M(x) = r]`. -/
lemma exponentialMechanism_real_apply (hu : ∀ r, Measurable fun x ↦ u x r) (x : 𝒟) (E : Set R)
    [DecidablePred (· ∈ E)] :
    (exponentialMechanism u ε Δ x).real E = ∑ r with r ∈ E, exponentialMechanismProb u ε Δ x r := by
  have hE : E = ↑(Finset.univ.filter (· ∈ E)) := by ext; simp
  rw [measureReal_def, exponentialMechanism_apply hu, withDensity_apply' _ E]
  conv_lhs => rw [hE, lintegral_finset]
  simp only [Measure.count_singleton, mul_one]
  rw [ENNReal.toReal_sum fun r _ ↦ ENNReal.ofReal_ne_top]
  exact Finset.sum_congr rfl fun r _ ↦ ENNReal.toReal_ofReal (exponentialMechanismProb_nonneg ..)

/-- The exponential mechanism is a Markov kernel when `R` is nonempty and the scores are
measurable in the dataset. -/
lemma isMarkovKernel_exponentialMechanism [Nonempty R] (hu : ∀ r, Measurable fun x ↦ u x r) :
    IsMarkovKernel (exponentialMechanism u ε Δ) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  rw [exponentialMechanism_apply hu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_fintype, ← ENNReal.ofReal_one, ← sum_exponentialMechanismProb u ε Δ x,
    ENNReal.ofReal_sum_of_nonneg fun r _ ↦ exponentialMechanismProb_nonneg u ε Δ x r]
  simp

/-- **Dwork–Roth, Theorem 3.10** (after McSherry–Talwar): the exponential mechanism on a
nonempty finite range `R` is `(ε, 0)`-differentially private, for `ε ≥ 0` and any bound `Δ > 0`
on the sensitivity of the score, `|u(x, r) - u(x', r)| ≤ Δ` for all neighbouring `x, x'` and all
`r ∈ R`. The scores are assumed measurable in the dataset, so that together with `[Nonempty R]`
the kernel is the randomized mechanism of Definition 3.4 (`isMarkovKernel_exponentialMechanism`);
for empty `R` the kernel is zero and the inequality would be vacuous. The proof does not use
`[Nonempty R]`; the general kernel inequality behind it is
`ExponentialMechanism.isEpsDeltaDP_withDensity_const`. -/
@[nolint unusedArguments]
theorem isEpsDeltaDP_exponentialMechanism [Nonempty R] {Adj : 𝒟 → 𝒟 → Prop}
    (hu : ∀ r, Measurable fun x ↦ u x r) (hε : 0 ≤ ε) (hΔ : 0 < Δ)
    (hΔu : ∀ ⦃x x'⦄, Adj x x' → ∀ r, |u x r - u x' r| ≤ Δ) :
    IsEpsDeltaDP (exponentialMechanism u ε Δ) Adj ε 0 := by
  refine isEpsDeltaDP_withDensity_const (measurable_uncurry hu) (fun x ↦ ?_)
    fun x x' hx r ↦ ?_
  · rw [lintegral_fintype]
    exact ENNReal.sum_ne_top.2 fun y _ ↦ by simp
  · rw [← ENNReal.ofReal_mul (exp_pos ε).le]
    exact ENNReal.ofReal_le_ofReal (exponentialMechanismProb_le_exp_mul hε hΔ (hΔu hx) r)

/-! ### Utility -/

/-- **The key estimate in the proof of Dwork–Roth, Theorem 3.11**: for every threshold `c`,
`P[u(x, M(x)) ≤ c] ≤ (|R| / |R_OPT|) exp (ε (c - OPT_u(x)) / (2Δ))`, where
`OPT_u(x) = max_r u(x, r)` and `R_OPT = {r : u(x, r) = OPT_u(x)}`. -/
lemma exponentialMechanism_real_le [Nonempty R] (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 < ε) (hΔ : 0 < Δ) (x : 𝒟) (c : ℝ) :
    (exponentialMechanism u ε Δ x).real {r | u x r ≤ c} ≤
      Fintype.card R / #{r | u x r = ⨆ r', u x r'} *
        exp (ε * (c - ⨆ r', u x r') / (2 * Δ)) := by
  classical
  set OPT := ⨆ r', u x r'
  set w : R → ℝ := fun r ↦ exp (ε * u x r / (2 * Δ)) with hw
  have hZ : 0 < ∑ r, w r := ExponentialMechanism.sum_exp_pos u ε Δ x
  have hK : (0 : ℝ) < #{r | u x r = OPT} := by
    exact_mod_cast ExponentialMechanism.one_le_card_filter_eq_ciSup u x
  -- the bad outputs have unnormalized mass at most `|R| exp (ε c / (2Δ))`
  have h₁ : ∑ r with u x r ≤ c, w r ≤ Fintype.card R * exp (ε * c / (2 * Δ)) :=
    calc ∑ r with u x r ≤ c, w r ≤ ∑ r with u x r ≤ c, exp (ε * c / (2 * Δ)) :=
          Finset.sum_le_sum fun r hr ↦ by
            simp only [hw, exp_le_exp]
            gcongr
            exact (Finset.mem_filter.1 hr).2
      _ ≤ Fintype.card R * exp (ε * c / (2 * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast Finset.card_filter_le _ _
  -- the optimal outputs alone have unnormalized mass `|R_OPT| exp (ε OPT / (2Δ))`
  have h₂ : #{r | u x r = OPT} * exp (ε * OPT / (2 * Δ)) ≤ ∑ r, w r :=
    calc (#{r | u x r = OPT} : ℝ) * exp (ε * OPT / (2 * Δ))
        = ∑ r with u x r = OPT, exp (ε * OPT / (2 * Δ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ r with u x r = OPT, w r := Finset.sum_congr rfl fun r hr ↦ by
          simp only [hw, (Finset.mem_filter.1 hr).2]
      _ ≤ ∑ r, w r := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun r _ _ ↦ (exp_pos _).le
  rw [exponentialMechanism_real_apply hu]
  simp only [Set.mem_ofPred_eq, exponentialMechanismProb, ← Finset.sum_div]
  calc (∑ r with u x r ≤ c, w r) / ∑ r, w r
      ≤ Fintype.card R * exp (ε * c / (2 * Δ)) / (#{r | u x r = OPT} * exp (ε * OPT / (2 * Δ))) :=
        div_le_div₀ (by positivity) h₁ (by positivity) h₂
    _ = Fintype.card R / #{r | u x r = OPT} * exp (ε * (c - OPT) / (2 * Δ)) := by
        rw [mul_sub, sub_div, exp_sub]
        field_simp

/-- **Dwork–Roth, Theorem 3.11** (utility of the exponential mechanism): for every dataset `x`
and every `t`,
`P[u(x, M(x)) ≤ OPT_u(x) - (2Δ/ε) (ln (|R| / |R_OPT|) + t)] ≤ e^{-t}`,
where `OPT_u(x) = max_r u(x, r)` and `R_OPT = {r : u(x, r) = OPT_u(x)}`. Here `R` is a nonempty
finite set, `ε > 0` and `Δ > 0`. -/
theorem exponentialMechanism_utility [Nonempty R] (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 < ε) (hΔ : 0 < Δ) (x : 𝒟) (t : ℝ) :
    (exponentialMechanism u ε Δ x).real {r | u x r ≤ (⨆ r', u x r') -
      2 * Δ / ε * (log (Fintype.card R / #{r | u x r = ⨆ r', u x r'}) + t)} ≤ exp (-t) := by
  refine (exponentialMechanism_real_le hu hε hΔ x _).trans_eq ?_
  have hK : (0 : ℝ) < #{r | u x r = ⨆ r', u x r'} := by
    exact_mod_cast ExponentialMechanism.one_le_card_filter_eq_ciSup u x
  set K : ℝ := ((#{r | u x r = ⨆ r', u x r'} : ℕ) : ℝ)
  have hN : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [show ε * ((⨆ r', u x r') - 2 * Δ / ε * (log (Fintype.card R / K) + t) - ⨆ r', u x r') /
      (2 * Δ) = -log (Fintype.card R / K) + -t by field_simp; ring,
    exp_add, exp_neg (log _), exp_log (by positivity)]
  field_simp

/-- **Dwork–Roth, Corollary 3.12** (utility of the exponential mechanism): for every dataset `x`
and every `t`, `P[u(x, M(x)) ≤ OPT_u(x) - (2Δ/ε) (ln |R| + t)] ≤ e^{-t}`, where
`OPT_u(x) = max_r u(x, r)`. Here `R` is a nonempty finite set, `ε > 0` and `Δ > 0`. -/
theorem exponentialMechanism_utility_log_card [Nonempty R] (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 < ε) (hΔ : 0 < Δ) (x : 𝒟) (t : ℝ) :
    (exponentialMechanism u ε Δ x).real
      {r | u x r ≤ (⨆ r', u x r') - 2 * Δ / ε * (log (Fintype.card R) + t)} ≤ exp (-t) := by
  refine (exponentialMechanism_real_le hu hε hΔ x _).trans ?_
  have hK : (1 : ℝ) ≤ #{r | u x r = ⨆ r', u x r'} := by
    exact_mod_cast ExponentialMechanism.one_le_card_filter_eq_ciSup u x
  set K : ℝ := ((#{r | u x r = ⨆ r', u x r'} : ℕ) : ℝ)
  have hN : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [show ε * ((⨆ r', u x r') - 2 * Δ / ε * (log (Fintype.card R) + t) - ⨆ r', u x r') /
      (2 * Δ) = -log (Fintype.card R) + -t by field_simp; ring,
    exp_add, exp_neg (log _), exp_log hN, ← mul_assoc, div_mul_eq_mul_div, mul_inv_cancel₀ hN.ne',
    one_div_mul_eq_div]
  exact div_le_self (exp_pos _).le hK

end InformationTheory
