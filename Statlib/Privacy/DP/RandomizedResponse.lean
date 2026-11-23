/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.DP.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Randomized response

Randomized response is the oldest differentially private mechanism: each respondent reports the
true answer with some probability and a different answer otherwise.

* Binary randomized response goes back to S. L. Warner, *Randomized response: a survey technique
  for eliminating evasive answer bias*, J. Amer. Statist. Assoc. 60(309), 1965: the respondent
  reports the truth with a design probability `p ≠ 1/2`. Its two-coin special case (`p = 3/4`) is
  the first mechanism of C. Dwork and A. Roth, *The Algorithmic Foundations of Differential
  Privacy*, Found. Trends Theor. Comput. Sci. 9(3–4), 2014, Section 3.2.
* The `k`-ary randomized response with privacy parameter `ε` on a finite alphabet `α` of size
  `k = |α|` is from P. Kairouz, S. Oh and P. Viswanath, *Extremal mechanisms for local
  differential privacy*, NeurIPS 2014 / J. Mach. Learn. Res. 17, 2016: on input `x` it outputs
  `x` with probability `e^ε / (e^ε + k - 1)` and each of the other `k - 1` symbols with
  probability `1 / (e^ε + k - 1)`. For `k = 2` (on `Bool`) it keeps the true bit with
  probability `e^ε / (1 + e^ε)`, which is Warner's scheme with `p = e^ε / (1 + e^ε)`, i.e.
  `ε = ln (p / (1 - p))`.

Randomized response is a *local* mechanism: it is applied to a single respondent's datum, so
every pair of inputs is neighbouring (`Adj = fun _ _ ↦ True`). Privacy is measured with
`IsEpsDeltaDP` from `Statlib.Privacy.DP.Basic` at `δ = 0` (pure `ε`-differential privacy). The
parameter `ε` may be negative (Warner's `p < 1/2`); the exact privacy level is then `|ε|`.

## Main definitions

* `randomizedResponseProb ε x y`: the probability that `k`-ary randomized response outputs `y`
  on input `x`.
* `randomizedResponse ε`: `k`-ary randomized response as a Markov kernel `α → α`.
* `binaryRandomizedResponse ε`: binary randomized response, the case `α = Bool`.
* `twoCoinRandomizedResponse`: the two-coin procedure of Dwork–Roth, Section 3.2, as the kernel
  `b ↦ ½ δ_b + ½ uniform` on `Bool`.

## Main statements (source result → Lean name)

* `randomizedResponse ε` is a Markov kernel: `isMarkovKernel_randomizedResponse`.
* `k`-ary randomized response is `|ε|`-locally differentially private:
  `isEpsDeltaDP_randomizedResponse_abs` (and `ε`-LDP for `ε ≥ 0`:
  `isEpsDeltaDP_randomizedResponse`); `|ε|` is its exact privacy level, i.e. it is
  `ε'`-differentially private iff `|ε| ≤ ε'` (as soon as `k ≥ 2`):
  `isEpsDeltaDP_randomizedResponse_iff`.
* Binary randomized response keeps the true bit with probability `e^ε / (1 + e^ε)`
  (`binaryRandomizedResponse_real_self`) and is exactly `|ε|`-LDP:
  `isEpsDeltaDP_binaryRandomizedResponse_iff`. Warner's scheme with design probability
  `p ∈ (0, 1)` is the case `ε = ln (p / (1 - p))` (`binaryRandomizedResponse_log_div_real_self`)
  and is exactly `|ln (p / (1 - p))|`-LDP: `isEpsDeltaDP_binaryRandomizedResponse_log_div_iff`.
* Dwork–Roth, Claim 3.5: the two-coin procedure is binary randomized response with `ε = ln 3`
  (`twoCoinRandomizedResponse_eq`; it keeps the true answer with probability `3/4`:
  `binaryRandomizedResponse_log_three`), and it is `(ln 3, 0)`-differentially private, with
  `ln 3` exact: `isEpsDeltaDP_twoCoinRandomizedResponse_iff`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {α : Type*}

namespace RandomizedResponse

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

end RandomizedResponse

section KAry

variable [Fintype α] {ε : ℝ}

namespace RandomizedResponse

lemma card_sub_one_nonneg (x : α) : (0 : ℝ) ≤ Fintype.card α - 1 := by
  have : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨x⟩
  rw [sub_nonneg]
  exact_mod_cast this

lemma denom_pos (ε : ℝ) (x : α) : 0 < exp ε + Fintype.card α - 1 := by
  linarith [card_sub_one_nonneg x, exp_pos ε]

end RandomizedResponse

open RandomizedResponse

variable [DecidableEq α]

/-- The probability that `k`-ary randomized response with privacy parameter `ε` outputs `y` on
input `x`, where `k = |α|`: `e^ε / (e^ε + k - 1)` if `y = x` and `1 / (e^ε + k - 1)` otherwise. -/
noncomputable def randomizedResponseProb (ε : ℝ) (x y : α) : ℝ :=
  (if x = y then exp ε else 1) / (exp ε + Fintype.card α - 1)

lemma randomizedResponseProb_nonneg (ε : ℝ) (x y : α) : 0 ≤ randomizedResponseProb ε x y := by
  have := denom_pos ε x
  unfold randomizedResponseProb
  split_ifs <;> positivity

lemma randomizedResponseProb_self (ε : ℝ) (x : α) :
    randomizedResponseProb ε x x = exp ε / (exp ε + Fintype.card α - 1) := by
  simp [randomizedResponseProb]

lemma randomizedResponseProb_of_ne (ε : ℝ) {x y : α} (h : x ≠ y) :
    randomizedResponseProb ε x y = 1 / (exp ε + Fintype.card α - 1) := by
  simp [randomizedResponseProb, h]

/-- The output probabilities of randomized response sum to one. -/
lemma sum_randomizedResponseProb (ε : ℝ) (x : α) : ∑ y, randomizedResponseProb ε x y = 1 := by
  have hd := (denom_pos ε x).ne'
  have h (y : α) : randomizedResponseProb ε x y =
      (1 + if x = y then exp ε - 1 else 0) / (exp ε + Fintype.card α - 1) := by
    unfold randomizedResponseProb; split_ifs <;> ring
  simp_rw [h, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  simp only [Finset.mem_univ, ↓reduceIte]
  field_simp
  ring

/-- The likelihood ratio of randomized response is at most `e^{|ε|}`:
`RR(y | x) ≤ e^{|ε|} RR(y | x')` for all inputs `x, x'` and outputs `y`. -/
lemma randomizedResponseProb_le_exp_abs_mul (ε : ℝ) (x x' y : α) :
    randomizedResponseProb ε x y ≤ exp |ε| * randomizedResponseProb ε x' y := by
  have hd := denom_pos ε x
  have h₁ : 1 ≤ exp |ε| := one_le_exp (abs_nonneg ε)
  have h₂ : exp ε ≤ exp |ε| := exp_le_exp.2 (le_abs_self ε)
  have h₃ : 1 ≤ exp |ε| * exp ε := by
    rw [← exp_add]
    exact one_le_exp (by linarith [neg_abs_le ε])
  have h₄ := exp_pos ε
  unfold randomizedResponseProb
  rw [mul_div_assoc']
  gcongr
  split_ifs <;> nlinarith

/-- The likelihood ratio of randomized response is at most `e^ε`: `RR(y | x) ≤ e^ε RR(y | x')`
for all inputs `x, x'` and outputs `y` (for `ε ≥ 0`). -/
lemma randomizedResponseProb_le_exp_mul (hε : 0 ≤ ε) (x x' y : α) :
    randomizedResponseProb ε x y ≤ exp ε * randomizedResponseProb ε x' y := by
  simpa [abs_of_nonneg hε] using randomizedResponseProb_le_exp_abs_mul ε x x' y

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **`k`-ary randomized response** (Kairouz–Oh–Viswanath) with privacy parameter `ε` as a Markov
kernel on the finite alphabet `α` (`k = |α|`): on input `x`, output `x` with probability
`e^ε / (e^ε + k - 1)` and each other symbol with probability `1 / (e^ε + k - 1)`. It is the
measure with density `randomizedResponseProb ε x` with respect to the counting measure. -/
noncomputable def randomizedResponse (ε : ℝ) : Kernel α α :=
  (Kernel.const α Measure.count).withDensity fun x y ↦ ENNReal.ofReal (randomizedResponseProb ε x y)

lemma randomizedResponse_apply (ε : ℝ) (x : α) :
    randomizedResponse ε x =
      Measure.count.withDensity fun y ↦ ENNReal.ofReal (randomizedResponseProb ε x y) := by
  rw [randomizedResponse, Kernel.withDensity_apply _ (measurable_of_finite _), Kernel.const_apply]

lemma randomizedResponse_apply_singleton (ε : ℝ) (x y : α) :
    randomizedResponse ε x {y} = ENNReal.ofReal (randomizedResponseProb ε x y) := by
  rw [randomizedResponse_apply, withDensity_apply _ (MeasurableSet.singleton y),
    Measure.restrict_singleton, Measure.count_singleton, one_smul, lintegral_dirac]

lemma randomizedResponse_real_singleton (ε : ℝ) (x y : α) :
    (randomizedResponse ε x).real {y} = randomizedResponseProb ε x y := by
  rw [measureReal_def, randomizedResponse_apply_singleton,
    ENNReal.toReal_ofReal (randomizedResponseProb_nonneg ε x y)]

/-- Randomized response is a Markov kernel. -/
instance isMarkovKernel_randomizedResponse (ε : ℝ) :
    IsMarkovKernel (randomizedResponse (α := α) ε) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  rw [randomizedResponse_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_fintype, ← ENNReal.ofReal_one, ← sum_randomizedResponseProb ε x,
    ENNReal.ofReal_sum_of_nonneg fun y _ ↦ randomizedResponseProb_nonneg ε x y]
  simp

/-- **`k`-ary randomized response is `|ε|`-locally differentially private**: for all inputs
`x, x'` and every event `E`, `P[RR(x) ∈ E] ≤ e^{|ε|} P[RR(x') ∈ E]`. -/
theorem isEpsDeltaDP_randomizedResponse_abs (ε : ℝ) :
    IsEpsDeltaDP (randomizedResponse (α := α) ε) (fun _ _ ↦ True) |ε| 0 := by
  refine isEpsDeltaDP_withDensity_const (measurable_of_finite _) (fun x ↦ ?_)
    fun x x' _ y ↦ ?_
  · rw [lintegral_fintype]
    exact ENNReal.sum_ne_top.2 fun y _ ↦ by simp
  · rw [← ENNReal.ofReal_mul (exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (randomizedResponseProb_le_exp_abs_mul ε x x' y)

/-- **`k`-ary randomized response is `ε`-locally differentially private** (for `ε ≥ 0`): for all
inputs `x, x'` and every event `E`, `P[RR(x) ∈ E] ≤ e^ε P[RR(x') ∈ E]`. -/
theorem isEpsDeltaDP_randomizedResponse (hε : 0 ≤ ε) :
    IsEpsDeltaDP (randomizedResponse (α := α) ε) (fun _ _ ↦ True) ε 0 := by
  simpa [abs_of_nonneg hε] using isEpsDeltaDP_randomizedResponse_abs (α := α) ε

/-- **`|ε|` is the exact privacy level of `k`-ary randomized response** (for `k ≥ 2`): it is
`ε'`-locally differentially private if and only if `|ε| ≤ ε'`. For `x ≠ x'`, the ratios
`P[RR(x) = x] / P[RR(x') = x] = e^ε` and `P[RR(x) = x'] / P[RR(x') = x'] = e^{-ε}` show that no
smaller `ε'` works. -/
theorem isEpsDeltaDP_randomizedResponse_iff [Nontrivial α] (ε : ℝ) {ε' : ℝ} :
    IsEpsDeltaDP (randomizedResponse (α := α) ε) (fun _ _ ↦ True) ε' 0 ↔ |ε| ≤ ε' := by
  refine ⟨fun h ↦ ?_, fun h S S' _ E ↦ ?_⟩
  · obtain ⟨x, x', hxx'⟩ := exists_pair_ne α
    have hd := denom_pos ε x
    have h₁ := h (S := x) (S' := x') trivial {x}
    have h₂ := h (S := x) (S' := x') trivial {x'}
    rw [randomizedResponse_real_singleton, randomizedResponse_real_singleton,
      randomizedResponseProb_self, randomizedResponseProb_of_ne _ hxx'.symm, add_zero, mul_one_div,
      div_le_div_iff_of_pos_right hd, exp_le_exp] at h₁
    rw [randomizedResponse_real_singleton, randomizedResponse_real_singleton,
      randomizedResponseProb_self, randomizedResponseProb_of_ne _ hxx', add_zero, mul_div_assoc',
      div_le_div_iff_of_pos_right hd, ← exp_add, one_le_exp_iff] at h₂
    exact abs_le.2 ⟨by linarith, h₁⟩
  · calc (randomizedResponse ε S).real E ≤ exp |ε| * (randomizedResponse ε S').real E + 0 :=
          isEpsDeltaDP_randomizedResponse_abs ε trivial E
      _ ≤ exp ε' * (randomizedResponse ε S').real E + 0 := by gcongr

end KAry

section Binary

variable {ε : ℝ}

/-- **Binary randomized response** (Warner) with privacy parameter `ε`: `k`-ary randomized
response on `Bool`, which reports the true bit with probability `e^ε / (1 + e^ε)` and flips it
with probability `1 / (1 + e^ε)` (`binaryRandomizedResponse_real_self`,
`binaryRandomizedResponse_real_not`). -/
noncomputable abbrev binaryRandomizedResponse (ε : ℝ) : Kernel Bool Bool :=
  randomizedResponse ε

/-- Binary randomized response reports the true bit with probability `e^ε / (1 + e^ε)`. -/
lemma binaryRandomizedResponse_real_self (ε : ℝ) (b : Bool) :
    (binaryRandomizedResponse ε b).real {b} = exp ε / (1 + exp ε) := by
  rw [randomizedResponse_real_singleton, randomizedResponseProb_self, Fintype.card_bool]
  congr 1
  push_cast
  ring

/-- Binary randomized response flips the bit with probability `1 / (1 + e^ε)`. -/
lemma binaryRandomizedResponse_real_not (ε : ℝ) (b : Bool) :
    (binaryRandomizedResponse ε b).real {!b} = 1 / (1 + exp ε) := by
  rw [randomizedResponse_real_singleton, randomizedResponseProb_of_ne _ (Bool.not_ne_self b).symm,
    Fintype.card_bool]
  congr 1
  push_cast
  ring

/-- **Binary randomized response is exactly `|ε|`-locally differentially private**: it is
`ε'`-differentially private if and only if `|ε| ≤ ε'`. -/
theorem isEpsDeltaDP_binaryRandomizedResponse_iff (ε : ℝ) {ε' : ℝ} :
    IsEpsDeltaDP (binaryRandomizedResponse ε) (fun _ _ ↦ True) ε' 0 ↔ |ε| ≤ ε' :=
  isEpsDeltaDP_randomizedResponse_iff ε

/-- Warner's randomized response with design probability `p ∈ (0, 1)`, which reports the truth
with probability `p`, is binary randomized response with `ε = ln (p / (1 - p))` (negative when
`p < 1/2`). -/
lemma binaryRandomizedResponse_log_div_real_self {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (b : Bool) : (binaryRandomizedResponse (log (p / (1 - p))) b).real {b} = p := by
  have : 0 < 1 - p := by linarith
  rw [binaryRandomizedResponse_real_self, exp_log (by positivity)]
  field_simp
  ring

/-- **Privacy of Warner's randomized response**: with design probability `p ∈ (0, 1)`
(`binaryRandomizedResponse_log_div_real_self`), the scheme is `ε'`-locally differentially private
if and only if `|ln (p / (1 - p))| ≤ ε'`. -/
theorem isEpsDeltaDP_binaryRandomizedResponse_log_div_iff (p : ℝ) {ε' : ℝ} :
    IsEpsDeltaDP (binaryRandomizedResponse (log (p / (1 - p)))) (fun _ _ ↦ True) ε' 0 ↔
      |log (p / (1 - p))| ≤ ε' :=
  isEpsDeltaDP_binaryRandomizedResponse_iff _

/-- The two-coin randomized response of Dwork–Roth, Section 3.2: flip a fair coin; on tails
answer truthfully, on heads answer according to a second fair coin. As a kernel on `Bool` it is
the mixture `½ · δ_b + ½ · uniform`. -/
noncomputable def twoCoinRandomizedResponse : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun b ↦
    (2⁻¹ : ℝ≥0∞) • Measure.dirac b + (2⁻¹ : ℝ≥0∞) • ((2⁻¹ : ℝ≥0∞) • Measure.count)

/-- The two-coin randomized response of Dwork–Roth, Section 3.2, is binary randomized response
with `ε = ln 3`: it reports the truth with probability `3/4` and lies with probability `1/4`
(`binaryRandomizedResponse_log_three`). -/
theorem twoCoinRandomizedResponse_eq : twoCoinRandomizedResponse =
    binaryRandomizedResponse (log 3) := by
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  ext b : 1
  refine Measure.ext_iff_singleton.2 fun c ↦ ?_
  rw [randomizedResponse_apply_singleton]
  simp [twoCoinRandomizedResponse, Kernel.ofFunOfCountable]
  cases b <;> cases c <;>
    simp only [randomizedResponseProb, exp_log (show (0 : ℝ) < 3 by norm_num), h2,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2⁻¹ by norm_num)] <;>
    norm_num [← ENNReal.ofReal_add]

/-- The two-coin randomized response reports the truth with probability `3/4` and lies with
probability `1/4`. -/
lemma binaryRandomizedResponse_log_three (b : Bool) :
    (binaryRandomizedResponse (log 3) b).real {b} = 3 / 4 ∧
      (binaryRandomizedResponse (log 3) b).real {!b} = 1 / 4 := by
  rw [binaryRandomizedResponse_real_self, binaryRandomizedResponse_real_not,
    exp_log (by norm_num)]
  norm_num

/-- **Dwork–Roth, Claim 3.5**: the two-coin randomized response of Section 3.2 is
`(ln 3, 0)`-differentially private, and `ln 3` is its exact privacy level. -/
theorem isEpsDeltaDP_twoCoinRandomizedResponse_iff {ε' : ℝ} :
    IsEpsDeltaDP twoCoinRandomizedResponse (fun _ _ ↦ True) ε' 0 ↔ log 3 ≤ ε' := by
  rw [twoCoinRandomizedResponse_eq, isEpsDeltaDP_binaryRandomizedResponse_iff,
    abs_of_nonneg (log_nonneg (by norm_num))]

end Binary

end InformationTheory
