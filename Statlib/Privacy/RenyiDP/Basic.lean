/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.DP.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Statlib.Divergence.Hellinger.CondHellinger
public import Statlib.Divergence.Renyi.ChainRule
public import Statlib.Divergence.Renyi.Prod

/-!
# Rényi differential privacy

This file formalizes I. Mironov, *Rényi differential privacy*, IEEE 30th Computer Security
Foundations Symposium (CSF), 2017 ([arXiv:1702.07476](https://arxiv.org/abs/1702.07476)); result
numbers follow arXiv v3.

A randomized mechanism `M`, given as a Markov kernel from datasets to outputs, has `ε`-Rényi
differential privacy of order `α` (is `(α, ε)`-RDP) if `D_α(M(S) ‖ M(S')) ≤ ε` for all
neighbouring datasets `S, S'`, where `D_α(P ‖ Q) = (α - 1)⁻¹ log E_Q[(P/Q)^α]` is the Rényi
divergence. The paper shows that RDP shares the basic properties of differential privacy
(post-processing, adaptive composition with additive budgets, group privacy), that pure `ε`-DP is
`(∞, ε)`-RDP, and that `(α, ε)`-RDP implies `(ε + log (1/δ) / (α - 1), δ)`-DP.

**Scope.** Except for randomized response, everything is proved for **general measurable output
spaces**: mechanisms are Markov kernels `M : Kernel 𝒟 Y`, the Rényi divergence is Statlib's
`renyiDiv` (in nats, with values in `ℝ≥0∞`), `(ε, δ)`-DP is `IsEpsDeltaDP` from
`Statlib.Privacy.DP.Basic` (pure `ε`-DP is `δ = 0`) and the neighbouring relation `Adj` is
arbitrary (symmetric where stated). Adaptive composition assumes
`CountableOrCountablyGenerated Y Z` (the first output alphabet is countable or the second one is
countably generated, e.g. standard Borel), which is what disintegrating the joint divergence
needs. Randomized response is on `Bool`, and the point-mass formula for the divergence is on
finite alphabets.

## Main definitions

* `IsRenyiDP M Adj α ε`: `(α, ε)`-Rényi differential privacy (Definition 4).
* `RenyiDP.randomizedResponseOfProb p`: randomized response with parameter `p` (Section VI.A).

## Main statements (paper result → Lean name)

* Definition 4 → `IsRenyiDP`.
* Post-processing (Section III) → `IsRenyiDP.comp` (Markov kernels), `IsRenyiDP.map`.
* Proposition 1 (adaptive sequential composition) → `IsRenyiDP.compProd`, for `α > 1`; the
  nonadaptive case, for every `α ≥ 0`, is `IsRenyiDP.prod`.
* Proposition 2 (group privacy) → `IsRenyiDP.renyiDiv_le_of_isKNeighbour` (inputs joined by
  `2 ^ c` neighbouring steps) and `IsRenyiDP.comap` (pre-processing by a `2 ^ c`-stable map).
* Proposition 3 (from RDP to `(ε, δ)`-DP) → `IsRenyiDP.isEpsDeltaDP`, and the stronger
  `P[M(S) ∈ E] ≤ max (e^{ε'} P[M(S') ∈ E], δ)` proved in the paper →
  `IsRenyiDP.measureReal_le_max`.
* Section IV, "`ε`-DP is `(∞, ε)`-RDP, hence `(α, ε)`-RDP for all finite `α`" →
  `IsEpsDeltaDP.isRenyiDP` (every finite order `α ≥ 0`), and the characterization
  `isEpsDeltaDP_zero_iff_forall_isRenyiDP` (`ε`-DP iff `(α, ε)`-RDP for every `α > 1`).
* Proposition 5 and Table II (randomized response, orders `α > 1`) →
  `isRenyiDP_randomizedResponseOfProb_comap`, with the exact divergence
  `RenyiDP.renyiDiv_randomizedResponseOfProb`.
* Proposition 9 (monotonicity in the order) → Statlib's `renyiDiv_le_renyiDiv_of_le`; for
  mechanisms, `IsRenyiDP.of_order_le`.
* Proposition 10 (probability preservation), in its **finite-divergence, bounded-budget**
  version (`D_α(P ‖ Q) ≤ c` with `c` real) → `RenyiDP.measure_le_rpow_of_renyiDiv_le`; for
  mechanisms (Table I, change in the probability of an outcome) `IsRenyiDP.measureReal_le_rpow`
  and `IsRenyiDP.le_measureReal`.
* Proposition 11 (weak triangle inequality) → `RenyiDP.renyiDiv_le_mul_renyiDiv_add_renyiDiv`;
  Corollary 4, item 1 → `RenyiDP.renyiDiv_le_mul_renyiDiv_two_mul_add`.
* Definition 3 with point masses on a finite alphabet → `RenyiDP.renyiDiv_eq_ofReal_log_sum`.

## Implementation notes

* The order is a real number `α` and the definition is stated for every `α`; the paper uses
  `α > 1`, extended by continuity to `α = 1` (the Kullback-Leibler divergence, which is also what
  `renyiDiv 1` is) and to `α = ∞`, which is pure DP and is handled through
  `isEpsDeltaDP_zero_iff_forall_isRenyiDP` (Statlib has no Rényi divergence of order `∞`).
* The privacy parameter is `ε : ℝ≥0`. The divergence takes values in `[0, ∞]`, a parameter
  `ε = ∞` would be vacuous, and with `ℝ≥0` budgets add in `ℝ≥0` and coerce both to `ℝ≥0∞` (to
  compare with `renyiDiv`) and to `ℝ` (for `IsEpsDeltaDP`) without side conditions.
* The proofs go through two characterizations, for probability measures and `α > 1`, of
  `D_α(P ‖ Q) ≤ c`: by the Hellinger integral, `P ≪ Q ∧ ∫⁻ (∂P/∂Q) ^ α ∂Q ≤ e^{(α - 1) c}`
  (`RenyiDP.renyiDiv_le_ofReal_iff_lintegral`), and by the Hellinger divergence
  (`RenyiDP.renyiDiv_le_ofReal_iff_hellingerDiv`); the latter is affine in the joint law and
  gives adaptive composition from Statlib's chain rule `renyiDiv_compProd_eq_add_condRenyiDiv`.
* In Proposition 1 the second mechanism is a kernel `N : Kernel (𝒟 × Y) Z` (Mathlib's convention
  for `M ⊗ₖ N`), and its privacy for a fixed first output `y` is that of `N.sectL y`.
* Group privacy uses `IsKNeighbour` from `Statlib.Privacy.DP.Basic` (chains in which consecutive
  datasets are neighbouring or equal).

## Notes on the paper

* Section III, paragraph *Group privacy* (arXiv v3): the definition of a `c`-stable
  transformation, read literally, has the implication reversed ("`g(A)` and `g(B)` are adjacent
  in `D′` implies that there exists a sequence ... `D_0 = A, ..., D_c = B` ... adjacent in `D`",
  for `g : D → D′`), whereas the statement and proof of Proposition 2 use the standard notion of
  McSherry for `g : D′ → D`: adjacent inputs `D, D′` are mapped to `g(D), g(D′)` joined by a
  chain of `c` adjacent steps. `IsRenyiDP.comap` uses the latter; Proposition 2 is true for it.
* Proof of Proposition 2: the middle terms `D_α(h(D) ‖ h(A))` and `D_{α-1}(h(A) ‖ h(D′))` should
  read `f(A)` instead of `h(A)`, since `A` is an input of `f`, not of `h = f ∘ g`. The argument
  is otherwise correct.

## Not formalized

* The Bayesian interpretation (inequality (1) and the Bayes-factor rows of Table I),
  Proposition 8 (nonnegativity; Statlib's `renyiDiv` is `ℝ≥0∞`-valued), Corollary 4, items 2–3
  (they involve `D_∞`) and item 4 (a finite-order `β` statement, omitted separately), adaptive
  composition at `α = 1`.
* The extended-valued form of Proposition 10 (`D_α(P ‖ Q) = ∞` allowed, with infinite-divergence
  and zero-probability events treated separately).
* Lemma 1, Proposition 4 and Corollary 1 (advanced composition), Proposition 5 at `α = 1`,
  Proposition 6 and Corollary 2 (Laplace mechanism), Proposition 7 and Corollary 3 (Gaussian
  mechanism), the differential-privacy column of Table II (e.g. randomized response with
  parameter `0 < p < 1` is `|log (p / (1 - p))|`-DP), and the numerical comparisons of
  Sections VI–VII.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace InformationTheory

variable {𝒟 Y Z : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z}

/-! ### The Rényi divergence of an order `α > 1` between probability measures -/

namespace RenyiDP

variable {P Q : Measure Y} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {α c : ℝ}

/-- For probability measures and `α > 1`, `D_α(P ‖ Q) ≤ c` iff the Hellinger divergence is finite
and the Hellinger integral `∫ (∂P/∂Q) ^ α ∂Q` is at most `exp ((α - 1) c)`. -/
lemma renyiDiv_le_ofReal_iff_integral (hα : 1 < α) (hc : 0 ≤ c) :
    renyiDiv α P Q ≤ ENNReal.ofReal c ↔
      hellingerDiv α P Q ≠ ∞ ∧ ∫ y, ((∂P/∂Q) y).toReal ^ α ∂Q ≤ exp ((α - 1) * c) := by
  rw [renyiDiv_of_one_lt hα]
  split_ifs with h
  · simp [h]
  · have hR : renyiDiv α P Q ≠ ∞ := by
      rwa [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt hα]
    have hpos := integral_rpow_rnDeriv_pos_of_renyiDiv_ne_top (by linarith) hR
    simp only [measure_univ, ENNReal.toReal_one, Real.log_one, mul_zero, add_zero, sub_zero]
    rw [ENNReal.ofReal_le_ofReal_iff hc, inv_mul_le_iff₀ (by linarith),
      Real.log_le_iff_le_exp hpos]
    simp [h]

/-- For probability measures and `α > 1`, `D_α(P ‖ Q) ≤ c` iff `P ≪ Q` and the Hellinger
integral `∫⁻ (∂P/∂Q) ^ α ∂Q` is at most `exp ((α - 1) c)`. -/
lemma renyiDiv_le_ofReal_iff_lintegral (hα : 1 < α) (hc : 0 ≤ c) :
    renyiDiv α P Q ≤ ENNReal.ofReal c ↔
      P ≪ Q ∧ ∫⁻ y, (∂P/∂Q) y ^ α ∂Q ≤ ENNReal.ofReal (exp ((α - 1) * c)) := by
  rw [renyiDiv_le_ofReal_iff_integral hα hc, hellingerDiv_ne_top_iff_of_one_lt hα,
    integrable_rpow_rnDeriv_iff_lintegral_ne_top (by linarith),
    integral_rpow_rnDeriv_eq_toReal_lintegral (by linarith)]
  constructor
  · rintro ⟨⟨hfin, hac⟩, hle⟩
    exact ⟨hac, (ENNReal.le_ofReal_iff_toReal_le hfin (exp_pos _).le).2 hle⟩
  · rintro ⟨hac, hle⟩
    have hfin : ∫⁻ y, (∂P/∂Q) y ^ α ∂Q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    exact ⟨⟨hfin, hac⟩, (ENNReal.le_ofReal_iff_toReal_le hfin (exp_pos _).le).1 hle⟩

/-- For probability measures and `α > 1`, `D_α(P ‖ Q) ≤ c` iff the Hellinger divergence of
order `α` is at most `(exp ((α - 1) c) - 1) / (α - 1)`. -/
lemma renyiDiv_le_ofReal_iff_hellingerDiv (hα : 1 < α) (hc : 0 ≤ c) :
    renyiDiv α P Q ≤ ENNReal.ofReal c ↔
      hellingerDiv α P Q ≤ ENNReal.ofReal ((exp ((α - 1) * c) - 1) / (α - 1)) := by
  rw [renyiDiv_le_ofReal_iff_integral hα hc]
  by_cases h : hellingerDiv α P Q = ∞
  · simp [h]
  have hI := mul_hellingerDiv_add_meas_eq_integral (μ := P) (ν := Q) (by linarith) hα.ne' h
  simp only [measure_univ, ENNReal.toReal_one, mul_one] at hI
  have hα' : 0 < α - 1 := by linarith
  have h1 : 1 ≤ exp ((α - 1) * c) := one_le_exp (by positivity)
  rw [ENNReal.le_ofReal_iff_toReal_le h (div_nonneg (by linarith) hα'.le), ← hI,
    le_div_iff₀ hα']
  simp only [ne_eq, h, not_false_eq_true, true_and]
  constructor <;> intro h' <;> linarith

/-- If `P(s) ≤ e^c Q(s)` for every set `s`, then `D_α(P ‖ Q) ≤ c` for every `α > 1`. -/
lemma renyiDiv_le_of_forall_le (hα : 1 < α) (hc : 0 ≤ c)
    (h : ∀ s, P s ≤ ENNReal.ofReal (exp c) * Q s) : renyiDiv α P Q ≤ ENNReal.ofReal c := by
  set C := ENNReal.ofReal (exp c)
  have hac : P ≪ Q := fun s hs ↦ le_antisymm ((h s).trans (by simp [hs])) zero_le
  have hle : ∀ᵐ y ∂Q, (∂P/∂Q) y ≤ C :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv P Q)
      fun s _ _ ↦ by rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]; exact h s
  refine (renyiDiv_le_ofReal_iff_lintegral hα hc).2 ⟨hac, ?_⟩
  calc ∫⁻ y, (∂P/∂Q) y ^ α ∂Q ≤ ∫⁻ y, C ^ (α - 1) * (∂P/∂Q) y ∂Q := by
        refine lintegral_mono_ae ?_
        filter_upwards [hle, Measure.rnDeriv_lt_top P Q] with y hy hy'
        rcases eq_or_ne ((∂P/∂Q) y) 0 with h0 | h0
        · rw [h0, ENNReal.zero_rpow_of_pos (by linarith), mul_zero]
        calc (∂P/∂Q) y ^ α = (∂P/∂Q) y ^ (α - 1) * (∂P/∂Q) y := by
              conv_lhs => rw [show α = (α - 1) + 1 by ring]
              rw [ENNReal.rpow_add _ _ h0 hy'.ne, ENNReal.rpow_one]
          _ ≤ C ^ (α - 1) * (∂P/∂Q) y := by gcongr
    _ = C ^ (α - 1) := by
        rw [lintegral_const_mul _ (Measure.measurable_rnDeriv _ _), Measure.lintegral_rnDeriv hac,
          measure_univ, mul_one]
    _ = ENNReal.ofReal (exp ((α - 1) * c)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by linarith), ← Real.exp_mul, mul_comm]

/-- **Proposition 10** of Mironov (probability preservation), **finite-divergence,
bounded-budget version**: for probability measures, `α > 1` and `D_α(P ‖ Q) ≤ c` with `c` a real
number, every set `s` satisfies `P(s) ≤ (e^c Q(s)) ^ ((α - 1) / α)`. This is not the complete
extended-valued statement (which would also allow `D_α(P ‖ Q) = ∞`). The paper assumes that `P`
and `Q` have the same support; that assumption is not needed here, because
`D_α(P ‖ Q) ≤ c < ∞` already implies `P ≪ Q` (common support alone would not make the divergence
finite). -/
theorem measure_le_rpow_of_renyiDiv_le (hα : 1 < α) (hc : 0 ≤ c)
    (h : renyiDiv α P Q ≤ ENNReal.ofReal c) (s : Set Y) :
    P s ≤ (ENNReal.ofReal (exp c) * Q s) ^ ((α - 1) / α) := by
  obtain ⟨hac, hle⟩ := (renyiDiv_le_ofReal_iff_lintegral hα hc).1 h
  have hα0 : 0 < α := by linarith
  have hpq := Real.HolderConjugate.conjExponent hα
  calc P s = ∫⁻ y in s, ((P.rnDeriv Q * fun _ ↦ 1 : Y → ℝ≥0∞)) y ∂Q := by
        simp [Measure.setLIntegral_rnDeriv hac]
    _ ≤ (∫⁻ y in s, (∂P/∂Q) y ^ α ∂Q) ^ (1 / α)
          * (∫⁻ y in s, (fun _ ↦ (1 : ℝ≥0∞)) y ^ Real.conjExponent α ∂Q)
            ^ (1 / Real.conjExponent α) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (Measure.measurable_rnDeriv _ _).aemeasurable
          aemeasurable_const
    _ ≤ ENNReal.ofReal (exp ((α - 1) * c)) ^ (1 / α) * Q s ^ ((α - 1) / α) := by
        gcongr
        · exact (setLIntegral_le_lintegral _ _).trans hle
        · rw [Real.conjExponent, one_div_div]
          simp
    _ = (ENNReal.ofReal (exp c) * Q s) ^ ((α - 1) / α) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg (by linarith) hα0.le),
          ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (div_nonneg (by linarith) hα0.le),
          ← Real.exp_mul, ← Real.exp_mul]
        congr 3
        field_simp

/-- The real inequality behind Proposition 3 of Mironov: for `α > 1`, `δ > 0` and `x ≥ 0`,
`x ^ ((α - 1) / α) ≤ max (δ ^ (-(α - 1)⁻¹) x, δ)`. -/
lemma rpow_le_max (hα : 1 < α) {δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) :
    x ^ ((α - 1) / α) ≤ max (δ ^ (-(α - 1)⁻¹) * x) δ := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  rcases le_or_gt (x ^ ((α - 1) / α)) δ with h | h
  · exact le_max_of_le_right h
  refine le_max_of_le_left ?_
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with rfl | hx0
    · rw [Real.zero_rpow (by positivity)] at h
      linarith
    · exact hx0
  calc x ^ ((α - 1) / α) = x ^ (1 + (α - 1) / α * (-(α - 1)⁻¹)) := by
        congr 1
        field_simp
        ring
    _ = x * (x ^ ((α - 1) / α)) ^ (-(α - 1)⁻¹) := by
        rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx]
    _ ≤ x * δ ^ (-(α - 1)⁻¹) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hδ h.le (neg_nonpos.2 (inv_nonneg.2 hα1.le))) hx
    _ = δ ^ (-(α - 1)⁻¹) * x := mul_comm _ _

/-- **Proposition 11** of Mironov (weak triangle inequality): for probability measures `P, Q, R`,
`α > 1` and Hölder conjugate exponents `p, q > 1`,
`D_α(P ‖ Q) ≤ (α - 1 / p) / (α - 1) · D_{pα}(P ‖ R) + D_{q (α - 1 / p)}(R ‖ Q)`. -/
theorem renyiDiv_le_mul_renyiDiv_add_renyiDiv {R : Measure Y} [IsProbabilityMeasure R] {p q : ℝ}
    (hα : 1 < α) (hpq : p.HolderConjugate q) :
    renyiDiv α P Q ≤ ENNReal.ofReal ((α - 1 / p) / (α - 1)) * renyiDiv (p * α) P R
      + renyiDiv (q * (α - 1 / p)) R Q := by
  have hp : 1 < p := hpq.lt
  have hq_eq : q = p / (p - 1) := hpq.conjugate_eq
  have hp0 : 0 < 1 / p := one_div_pos.2 (by linarith)
  have hq0 : 0 < 1 / q := one_div_pos.2 (by linarith [hpq.symm.lt])
  have hα1 : 0 < α - 1 := by linarith
  have hαp : 0 < α - 1 / p := by
    have : 1 / p < 1 := (div_lt_one (by linarith)).2 hp
    linarith
  have hcoef : 0 < (α - 1 / p) / (α - 1) := div_pos hαp hα1
  have hpα : 1 < p * α := by nlinarith
  have hqα' : q * (α - 1 / p) = q * (α - 1) + 1 := by
    rw [hq_eq]
    field_simp
    ring
  have hqα : 1 < q * (α - 1 / p) := by
    rw [hqα']
    nlinarith [hpq.symm.lt]
  set a := renyiDiv (p * α) P R
  set b := renyiDiv (q * (α - 1 / p)) R Q
  rcases eq_or_ne a ∞ with ha | ha
  · rw [ha, ENNReal.mul_top (by simpa using hcoef), top_add]
    exact le_top
  rcases eq_or_ne b ∞ with hb | hb
  · rw [hb, add_top]
    exact le_top
  obtain ⟨hPR, hIa⟩ := (renyiDiv_le_ofReal_iff_lintegral hpα ENNReal.toReal_nonneg).1
    (ENNReal.ofReal_toReal ha).ge
  obtain ⟨hRQ, hIb⟩ := (renyiDiv_le_ofReal_iff_lintegral hqα ENNReal.toReal_nonneg).1
    (ENNReal.ofReal_toReal hb).ge
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_mul hcoef.le,
    ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg]
  refine (renyiDiv_le_ofReal_iff_lintegral hα (by positivity)).2 ⟨hPR.trans hRQ, ?_⟩
  have hf := Measure.measurable_rnDeriv P R
  have hg := Measure.measurable_rnDeriv R Q
  calc ∫⁻ y, (∂P/∂Q) y ^ α ∂Q
      = ∫⁻ y, ((fun y ↦ (∂P/∂R) y ^ α * (∂R/∂Q) y ^ (1 / p))
          * fun y ↦ (∂R/∂Q) y ^ (α - 1 / p)) y ∂Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_mul_rnDeriv hPR (κ := Q)] with y hy
        rw [← hy, Pi.mul_apply, Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ (by linarith),
          mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hp0.le hαp.le, add_sub_cancel]
    _ ≤ (∫⁻ y, ((∂P/∂R) y ^ α * (∂R/∂Q) y ^ (1 / p)) ^ p ∂Q) ^ (1 / p)
          * (∫⁻ y, ((∂R/∂Q) y ^ (α - 1 / p)) ^ q ∂Q) ^ (1 / q) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq Q hpq
          ((hf.pow_const _).mul (hg.pow_const _)).aemeasurable (hg.pow_const _).aemeasurable
    _ = (∫⁻ y, (∂P/∂R) y ^ (p * α) ∂R) ^ (1 / p)
          * (∫⁻ y, (∂R/∂Q) y ^ (q * (α - 1 / p)) ∂Q) ^ (1 / q) := by
        congr 2
        · rw [← lintegral_rnDeriv_mul hRQ (hf.pow_const _).aemeasurable]
          refine lintegral_congr fun y ↦ ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            one_div_mul_cancel (by linarith), ENNReal.rpow_one, mul_comm α p, mul_comm]
        · refine lintegral_congr fun y ↦ ?_
          rw [← ENNReal.rpow_mul, mul_comm]
    _ ≤ ENNReal.ofReal (exp ((p * α - 1) * a.toReal)) ^ (1 / p)
          * ENNReal.ofReal (exp ((q * (α - 1 / p) - 1) * b.toReal)) ^ (1 / q) := by
        gcongr
    _ = ENNReal.ofReal (exp ((α - 1) * ((α - 1 / p) / (α - 1) * a.toReal + b.toReal))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hp0.le,
          ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hq0.le, ← Real.exp_mul, ← Real.exp_mul,
          ← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add, hqα', hq_eq]
        congr 2
        field_simp
        ring

/-- **Corollary 4.1** of Mironov (the weak triangle inequality with `p = q = 2`): for probability
measures and `α > 1`, `D_α(P ‖ Q) ≤ (α - 1/2) / (α - 1) · D_{2α}(P ‖ R) + D_{2α - 1}(R ‖ Q)`. The
paper assumes a common support; this is not needed. -/
theorem renyiDiv_le_mul_renyiDiv_two_mul_add {R : Measure Y} [IsProbabilityMeasure R]
    (hα : 1 < α) :
    renyiDiv α P Q ≤ ENNReal.ofReal ((α - 1 / 2) / (α - 1)) * renyiDiv (2 * α) P R
      + renyiDiv (2 * α - 1) R Q := by
  have := renyiDiv_le_mul_renyiDiv_add_renyiDiv (P := P) (Q := Q) (R := R) hα
    Real.HolderConjugate.two_two
  rwa [show (2 : ℝ) * (α - 1 / 2) = 2 * α - 1 by ring] at this

end RenyiDP

/-! ### Rényi differential privacy -/

/-- **Rényi differential privacy** (Definition 4 of Mironov): a mechanism `M`, given as a kernel
from datasets to outputs, is `(α, ε)`-RDP for the neighbouring relation `Adj` if
`D_α(M(S) ‖ M(S')) ≤ ε` for all neighbouring `S, S'`.

The divergence is Statlib's `renyiDiv`, in nats with values in `ℝ≥0∞`. The paper uses orders
`α > 1`, extended to `α = 1` by continuity (the Kullback-Leibler divergence, which is also what
`renyiDiv 1` is) and to `α = ∞` (pure differential privacy, see
`isEpsDeltaDP_zero_iff_forall_isRenyiDP`); the definition is stated for every real order and the
results below assume the range of orders they need. The definition is only meaningful for
`α ≥ 0`: for `α < 0` Statlib's Hellinger divergence vanishes and the condition carries no
information (the paper does not use orders below `1`, Remark 2). It is also only meaningful for
Markov kernels, which every result below assumes. For kernels whose output measures are nonzero
and finite, `renyiDiv` compares the normalized measures `M(S) / M(S)(univ)`; at zero measures it
takes degenerate values, and for non-finite output measures even this interpretation fails
(inverting an infinite mass gives `0`, and `renyiDiv` need not equal a divergence of normalized
measures), so such kernels are excluded. The privacy
parameter is `ε : ℝ≥0`, since the divergence is nonnegative and a parameter `ε = ∞` would be
vacuous. -/
def IsRenyiDP (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (α : ℝ) (ε : ℝ≥0) : Prop :=
  ∀ ⦃S S'⦄, Adj S S' → renyiDiv α (M S) (M S') ≤ ε

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop} {α β : ℝ} {ε ε₁ ε₂ : ℝ≥0}

/-- An `(α, ε₁)`-RDP mechanism is `(α, ε₂)`-RDP for every `ε₂ ≥ ε₁`. -/
lemma IsRenyiDP.mono (h : IsRenyiDP M Adj α ε₁) (hε : ε₁ ≤ ε₂) : IsRenyiDP M Adj α ε₂ :=
  fun _ _ hS ↦ (h hS).trans (by exact_mod_cast hε)

/-- **Proposition 9** (monotonicity in the order) for mechanisms: an `(β, ε)`-RDP mechanism is
`(α, ε)`-RDP for every `0 ≤ α ≤ β`. The paper states the monotonicity of the divergence for
`1 ≤ α < β`; it is Statlib's `renyiDiv_le_renyiDiv_of_le`, valid for `0 ≤ α ≤ β`. -/
theorem IsRenyiDP.of_order_le [IsMarkovKernel M] (h : IsRenyiDP M Adj β ε) (hα : 0 ≤ α)
    (hαβ : α ≤ β) : IsRenyiDP M Adj α ε :=
  fun _ _ hS ↦ (renyiDiv_le_renyiDiv_of_le hα hαβ).trans (h hS)

/-- **Post-processing** (Section III of Mironov): if `M` is `(α, ε)`-RDP, so is `Proc ∘ M` for
every Markov kernel `Proc`, for every order `α ≥ 0`. -/
theorem IsRenyiDP.comp [IsMarkovKernel M] (h : IsRenyiDP M Adj α ε) (hα : 0 ≤ α)
    (Proc : Kernel Y Z) [IsMarkovKernel Proc] : IsRenyiDP (Proc ∘ₖ M) Adj α ε :=
  fun S S' hS ↦ by
    rw [Kernel.comp_apply, Kernel.comp_apply]
    exact (renyiDiv_comp_right_le hα _ _ Proc).trans (h hS)

/-- **Post-processing** by a measurable map: if `M` is `(α, ε)`-RDP, so is `g ∘ M`. -/
theorem IsRenyiDP.map [IsMarkovKernel M] (h : IsRenyiDP M Adj α ε) (hα : 0 ≤ α) {g : Y → Z}
    (hg : Measurable g) : IsRenyiDP (M.map g) Adj α ε :=
  fun S S' hS ↦ by
    rw [Kernel.map_apply _ hg, Kernel.map_apply _ hg]
    exact (renyiDiv_map_le hα _ _ hg).trans (h hS)

/-- **Composition of independent mechanisms** (Proposition 1, nonadaptive case): if `M₁` is
`(α, ε₁)`-RDP and `M₂` is `(α, ε₂)`-RDP, then releasing both outputs, computed with independent
randomness, is `(α, ε₁ + ε₂)`-RDP, for every order `α ≥ 0`. -/
theorem IsRenyiDP.prod {M₁ : Kernel 𝒟 Y} {M₂ : Kernel 𝒟 Z} [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] (h₁ : IsRenyiDP M₁ Adj α ε₁) (h₂ : IsRenyiDP M₂ Adj α ε₂)
    (hα : 0 ≤ α) : IsRenyiDP (M₁ ×ₖ M₂) Adj α (ε₁ + ε₂) :=
  fun S S' hS ↦ by
    rw [Kernel.prod_apply, Kernel.prod_apply, renyiDiv_prod hα, ENNReal.coe_add]
    exact add_le_add (h₁ hS) (h₂ hS)

namespace RenyiDP

/-- For `α > 1`, the conditional Rényi divergence `D_α(ρ ⊗ κ ‖ ρ ⊗ η)` with respect to a
probability measure `ρ` is at most any uniform bound on `D_α(κ y ‖ η y)`. -/
lemma condRenyiDiv_le [MeasurableSpace.CountableOrCountablyGenerated Y Z] {κ η : Kernel Y Z}
    [IsMarkovKernel κ] [IsMarkovKernel η] {ρ : Measure Y} [IsProbabilityMeasure ρ] (hα : 1 < α)
    (h : ∀ y, renyiDiv α (κ y) (η y) ≤ ε) : condRenyiDiv α κ η ρ ≤ ε := by
  have hε : (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) := by simp
  rw [condRenyiDiv, hε, renyiDiv_le_ofReal_iff_hellingerDiv hα ε.coe_nonneg]
  change condHellingerDiv α κ η ρ ≤ _
  rw [condHellingerDiv_eq_lintegral]
  calc ∫⁻ y, hellingerDiv α (κ y) (η y) ∂ρ
      ≤ ∫⁻ _, ENNReal.ofReal ((exp ((α - 1) * ε) - 1) / (α - 1)) ∂ρ := by
        refine lintegral_mono fun y ↦ ?_
        rw [← renyiDiv_le_ofReal_iff_hellingerDiv hα ε.coe_nonneg, ← hε]
        exact h y
    _ = _ := by simp

end RenyiDP

/-- **Proposition 1** of Mironov (adaptive sequential composition): if `M` is `(α, ε₁)`-RDP and,
for every first output `y`, the mechanism `S ↦ N(S, y)` is `(α, ε₂)`-RDP, then the mechanism
`S ↦ (X, Y)` with `X ∼ M(S)` and `Y ∼ N(S, X)` (the kernel `M ⊗ₖ N`) is `(α, ε₁ + ε₂)`-RDP.
Stated for `α > 1` (the paper's range; its case `α = 1` is by continuity), with the measurability
assumption `CountableOrCountablyGenerated Y Z` (`Y` countable or `Z` countably generated, e.g. a
standard Borel space) needed to disintegrate the joint divergence. -/
theorem IsRenyiDP.compProd [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    {N : Kernel (𝒟 × Y) Z} [IsMarkovKernel M] [IsMarkovKernel N] (hM : IsRenyiDP M Adj α ε₁)
    (hN : ∀ y, IsRenyiDP (N.sectL y) Adj α ε₂) (hα : 1 < α) :
    IsRenyiDP (M ⊗ₖ N) Adj α (ε₁ + ε₂) := by
  intro S S' hS
  rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.compProd_apply_eq_compProd_sectR,
    renyiDiv_compProd_eq_add_condRenyiDiv (by linarith), ENNReal.coe_add]
  refine add_le_add (hM hS) ?_
  have hR : renyiDiv α (M S) (M S') ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hM hS)
  have := isProbabilityMeasure_renyiMeasure_of_renyiDiv_ne_top (by linarith) hR
  exact RenyiDP.condRenyiDiv_le hα fun y ↦ hN y hS

/-! ### Rényi and `(ε, δ)`-differential privacy -/

/-- **Pure differential privacy implies RDP** (Section IV of Mironov: `ε`-DP is `(∞, ε)`-RDP,
hence `(α, ε)`-RDP for every finite `α` by monotonicity): an `ε`-DP mechanism is `(α, ε)`-RDP
for every finite order `α ≥ 0`. -/
theorem IsEpsDeltaDP.isRenyiDP [IsMarkovKernel M] (h : IsEpsDeltaDP M Adj ε 0) (hα : 0 ≤ α) :
    IsRenyiDP M Adj α ε := by
  have key (β : ℝ) (hβ : 1 < β) : IsRenyiDP M Adj β ε := by
    intro S S' hS
    have hε : (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) := by simp
    rw [hε]
    refine RenyiDP.renyiDiv_le_of_forall_le hβ ε.coe_nonneg fun s ↦ ?_
    rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal ((h hS s).trans_eq (add_zero _))
  rcases le_or_gt α 1 with hα1 | hα1
  · exact (key 2 one_lt_two).of_order_le hα (by linarith)
  · exact key α hα1

/-- The "bad outcomes" guarantee of RDP (Section III and Table I of Mironov, via
Proposition 10): if `M` is `(α, ε)`-RDP with `α > 1`, then for neighbouring `S, S'` and every
event `E`, `P[M(S) ∈ E] ≤ (e^ε P[M(S') ∈ E]) ^ ((α - 1) / α)`. -/
theorem IsRenyiDP.measureReal_le_rpow [IsMarkovKernel M] (h : IsRenyiDP M Adj α ε)
    (hα : 1 < α) ⦃S S' : 𝒟⦄ (hS : Adj S S') (E : Set Y) :
    (M S).real E ≤ (exp ε * (M S').real E) ^ ((α - 1) / α) := by
  have hR : renyiDiv α (M S) (M S') ≤ ENNReal.ofReal ε := by simpa using h hS
  have := ENNReal.toReal_mono (by finiteness)
    (RenyiDP.measure_le_rpow_of_renyiDiv_le hα ε.coe_nonneg hR E)
  rwa [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at this

/-- The lower half of the "bad outcomes" guarantee of RDP (Table I of Mironov): for a symmetric
neighbouring relation, if `M` is `(α, ε)`-RDP with `α > 1`, then for neighbouring `S, S'` and every
event `E`, `e^{-ε} P[M(S') ∈ E] ^ (α / (α - 1)) ≤ P[M(S) ∈ E]`. -/
theorem IsRenyiDP.le_measureReal [IsMarkovKernel M] [Std.Symm Adj] (h : IsRenyiDP M Adj α ε)
    (hα : 1 < α) ⦃S S' : 𝒟⦄ (hS : Adj S S') (E : Set Y) :
    exp (-ε) * (M S').real E ^ (α / (α - 1)) ≤ (M S).real E := by
  have hα1 : 0 < α - 1 := by linarith
  have h1 := h.measureReal_le_rpow hα (Std.Symm.symm _ _ hS) E
  have h2 : (M S').real E ^ (α / (α - 1)) ≤ exp ε * (M S).real E := by
    calc (M S').real E ^ (α / (α - 1))
        ≤ ((exp ε * (M S).real E) ^ ((α - 1) / α)) ^ (α / (α - 1)) := by gcongr
      _ = exp ε * (M S).real E := by
          rw [← Real.rpow_mul (by positivity), div_mul_div_comm, mul_comm (α - 1),
            div_self (by positivity), Real.rpow_one]
  rw [Real.exp_neg, inv_mul_le_iff₀ (exp_pos _)]
  exact h2

/-- **Proposition 3** of Mironov, in the stronger form proved in the paper: if `M` is
`(α, ε)`-RDP with `α > 1`, then for every `δ > 0`, neighbouring `S, S'` and every event `E`,
`P[M(S) ∈ E] ≤ max (e^{ε'} P[M(S') ∈ E], δ)` with `ε' = ε + log (1 / δ) / (α - 1)`. -/
theorem IsRenyiDP.measureReal_le_max [IsMarkovKernel M] (h : IsRenyiDP M Adj α ε) (hα : 1 < α)
    {δ : ℝ} (hδ : 0 < δ) ⦃S S' : 𝒟⦄ (hS : Adj S S') (E : Set Y) :
    (M S).real E ≤ max (exp (ε + log (1 / δ) / (α - 1)) * (M S').real E) δ := by
  have h3 : δ ^ (-(α - 1)⁻¹) * (exp ε * (M S').real E)
      = exp (ε + log (1 / δ) / (α - 1)) * (M S').real E := by
    rw [Real.rpow_def_of_pos hδ, ← mul_assoc, ← Real.exp_add, one_div, Real.log_inv]
    ring_nf
  rw [← h3]
  exact (h.measureReal_le_rpow hα hS E).trans (RenyiDP.rpow_le_max hα hδ (by positivity))

/-- **Proposition 3** of Mironov (from RDP to `(ε, δ)`-DP): an `(α, ε)`-RDP mechanism with
`α > 1` is `(ε + log (1 / δ) / (α - 1), δ)`-DP for every `δ > 0`. The paper states it for
`0 < δ < 1`. -/
theorem IsRenyiDP.isEpsDeltaDP [IsMarkovKernel M] (h : IsRenyiDP M Adj α ε) (hα : 1 < α)
    {δ : ℝ} (hδ : 0 < δ) : IsEpsDeltaDP M Adj (ε + log (1 / δ) / (α - 1)) δ :=
  fun _ _ hS E ↦ (h.measureReal_le_max hα hδ hS E).trans
    (max_le_add_of_nonneg (by positivity) hδ.le)

/-- **Pure differential privacy is RDP of order `∞`** (Section IV of Mironov: `ε`-DP coincides
with `(∞, ε)`-RDP, where `D_∞ = lim_{α → ∞} D_α`): a mechanism is `ε`-DP iff it is
`(α, ε)`-RDP for every `α > 1`. -/
theorem isEpsDeltaDP_zero_iff_forall_isRenyiDP [IsMarkovKernel M] :
    IsEpsDeltaDP M Adj ε 0 ↔ ∀ α, 1 < α → IsRenyiDP M Adj α ε := by
  refine ⟨fun h α hα ↦ h.isRenyiDP (by linarith), fun h S S' hS E ↦ ?_⟩
  rw [add_zero]
  set x := exp ε * (M S').real E
  have hx : 0 ≤ x := by positivity
  have h1 : Tendsto (fun α : ℝ ↦ (α - 1) / α) atTop (𝓝 1) := by
    have : Tendsto (fun α : ℝ ↦ 1 - α⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_inv_atTop_zero
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with α hα
    field_simp
  have hlim : Tendsto (fun α : ℝ ↦ x ^ ((α - 1) / α)) atTop (𝓝 x) := by
    rcases hx.eq_or_lt with hx0 | hx0
    · rw [← hx0]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with α hα
      rw [Real.zero_rpow (div_pos (by linarith) (by linarith)).ne']
    · have := ((Real.continuousAt_const_rpow hx0.ne').tendsto).comp h1
      rwa [Real.rpow_one] at this
  exact ge_of_tendsto hlim
    ((eventually_gt_atTop 1).mono fun α hα ↦ (h α hα).measureReal_le_rpow hα hS E)

/-! ### Group privacy -/

/-- A chain of `k + m` neighbouring steps splits into a chain of `k` steps followed by a chain of
`m` steps. -/
private lemma exists_isKNeighbour_of_add {k m : ℕ} {S U : 𝒟}
    (h : IsKNeighbour Adj (k + m) S U) :
    ∃ T, IsKNeighbour Adj k S T ∧ IsKNeighbour Adj m T U := by
  induction m generalizing U with
  | zero => exact ⟨U, h, .zero U⟩
  | succ m ih =>
    cases h with
    | succ h' hTU =>
      obtain ⟨T, h₁, h₂⟩ := ih h'
      exact ⟨T, h₁, .succ h₂ hTU⟩

/-- **Proposition 2** of Mironov (group privacy), for inputs at distance `2 ^ c`: if `M` is
`(α, ε)`-RDP and `α ≥ 2 ^ (c + 1)`, then `D_{α / 2^c}(M(S) ‖ M(S')) ≤ 3^c ε` whenever `S` and
`S'` are joined by a chain of `2 ^ c` neighbouring (or equal) steps. -/
theorem IsRenyiDP.renyiDiv_le_of_isKNeighbour [IsMarkovKernel M] (h : IsRenyiDP M Adj α ε)
    (c : ℕ) (hα : 2 ^ (c + 1) ≤ α) {S S' : 𝒟} (hSS' : IsKNeighbour Adj (2 ^ c) S S') :
    renyiDiv (α / 2 ^ c) (M S) (M S') ≤ 3 ^ c * ε := by
  induction c generalizing S S' with
  | zero =>
    simp only [pow_zero, div_one, one_mul] at hSS' ⊢
    cases hSS' with
    | succ h₀ hstep =>
      cases h₀
      rcases hstep with hS | rfl
      · exact h hS
      · simp
  | succ c ih =>
    have hα' : (2 : ℝ) ^ (c + 1) ≤ α :=
      le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hα
    rw [pow_succ, mul_two] at hSS'
    obtain ⟨T, h₁, h₂⟩ := exists_isKNeighbour_of_add hSS'
    set γ := α / 2 ^ (c + 1) with hγ
    have hγ2 : 2 ≤ γ := by
      rw [hγ, le_div_iff₀ (by positivity), ← pow_succ']
      exact hα
    have h2γ : 2 * γ = α / 2 ^ c := by
      rw [hγ, pow_succ]
      field_simp
    have hcoef : ENNReal.ofReal ((γ - 1 / 2) / (γ - 1)) ≤ 2 := by
      have hle : (γ - 1 / 2) / (γ - 1) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      exact (ENNReal.ofReal_le_ofReal hle).trans_eq (by simp)
    calc renyiDiv γ (M S) (M S')
        ≤ ENNReal.ofReal ((γ - 1 / 2) / (γ - 1)) * renyiDiv (2 * γ) (M S) (M T)
          + renyiDiv (2 * γ - 1) (M T) (M S') :=
          RenyiDP.renyiDiv_le_mul_renyiDiv_two_mul_add (by linarith)
      _ ≤ 2 * (3 ^ c * ε) + 3 ^ c * ε := by
          gcongr
          · rw [h2γ]
            exact ih hα' h₁
          · calc renyiDiv (2 * γ - 1) (M T) (M S') ≤ renyiDiv (2 * γ) (M T) (M S') :=
                  renyiDiv_le_renyiDiv_of_le (by linarith) (by linarith)
              _ ≤ 3 ^ c * ε := by
                  rw [h2γ]
                  exact ih hα' h₂
      _ = 3 ^ (c + 1) * ε := by ring

/-- **Proposition 2** of Mironov (group privacy): if `M` is `(α, ε)`-RDP, `g` is `2 ^ c`-stable
(neighbouring inputs `D, D'` are mapped to datasets `g D, g D'` joined by a chain of `2 ^ c`
neighbouring or equal steps) and `α ≥ 2 ^ (c + 1)`, then `M ∘ g` is `(α / 2^c, 3^c ε)`-RDP. -/
theorem IsRenyiDP.comap [IsMarkovKernel M] (h : IsRenyiDP M Adj α ε) {𝒟' : Type*}
    {m𝒟' : MeasurableSpace 𝒟'} {Adj' : 𝒟' → 𝒟' → Prop} {g : 𝒟' → 𝒟} (hg : Measurable g) (c : ℕ)
    (hstab : ∀ ⦃D D'⦄, Adj' D D' → IsKNeighbour Adj (2 ^ c) (g D) (g D'))
    (hα : 2 ^ (c + 1) ≤ α) : IsRenyiDP (M.comap g hg) Adj' (α / 2 ^ c) (3 ^ c * ε) :=
  fun D D' hD ↦ by
    rw [Kernel.comap_apply, Kernel.comap_apply, ENNReal.coe_mul, ENNReal.coe_pow]
    exact h.renyiDiv_le_of_isKNeighbour c hα (hstab hD)

/-! ### Finite alphabets and randomized response -/

namespace RenyiDP

/-- On a finite alphabet, for probability measures with `P ≪ Q` and `α > 1`, the Rényi divergence
is given by Definition 3 of Mironov with point masses:
`D_α(P ‖ Q) = (α - 1)⁻¹ log ∑_y P(y) ^ α Q(y) ^ (1 - α)`. -/
theorem renyiDiv_eq_ofReal_log_sum [Fintype Y] [MeasurableSingletonClass Y] {P Q : Measure Y}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hα : 1 < α) (hac : P ≪ Q) :
    renyiDiv α P Q
      = ENNReal.ofReal ((α - 1)⁻¹ * log (∑ y, P.real {y} ^ α * Q.real {y} ^ (1 - α))) := by
  rw [renyiDiv_eq_log_integral_of_one_lt hα Integrable.of_finite hac,
    integral_fintype Integrable.of_finite]
  simp only [measure_univ, ENNReal.toReal_one, Real.log_one, mul_zero, add_zero, sub_zero,
    smul_eq_mul]
  congr 3
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rcases eq_or_ne (Q {y}) 0 with hQ | hQ
  · have hP : P {y} = 0 := hac hQ
    simp [measureReal_def, hQ, hP, Real.zero_rpow (by linarith : α ≠ 0)]
  have hy : P {y} = (∂P/∂Q) y * Q {y} := by
    rw [← Measure.setLIntegral_rnDeriv hac, lintegral_singleton]
  have hQr : 0 < Q.real {y} := ENNReal.toReal_pos hQ (measure_ne_top _ _)
  have hr : ((∂P/∂Q) y).toReal = P.real {y} / Q.real {y} := by
    rw [measureReal_def P, hy, ENNReal.toReal_mul, ← measureReal_def, mul_div_assoc,
      div_self hQr.ne', mul_one]
  rw [hr, Real.div_rpow measureReal_nonneg hQr.le, Real.rpow_sub hQr, Real.rpow_one]
  field_simp

open unitInterval in
/-- **Binary randomized response** with parameter `p` (Section VI.A of Mironov): on input `b`,
output `b` with probability `p` and `!b` with probability `1 - p`. Applied to a predicate `f` on
datasets, `(randomizedResponseOfProb p).comap f hf` is the mechanism `RR_p f` of the paper. It is
parametrized, as in the paper, by the probability `p` of a truthful answer. -/
noncomputable def randomizedResponseOfProb (p : I) : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun b ↦
    ENNReal.ofReal p • Measure.dirac b + ENNReal.ofReal (1 - p) • Measure.dirac (!b)

open unitInterval

lemma randomizedResponseOfProb_apply (p : I) (b : Bool) :
    randomizedResponseOfProb p b
      = ENNReal.ofReal p • Measure.dirac b + ENNReal.ofReal (1 - p) • Measure.dirac (!b) :=
  rfl

lemma randomizedResponseOfProb_apply_singleton (p : I) (b c : Bool) :
    randomizedResponseOfProb p b {c}
      = if c = b then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
  cases b <;> cases c <;> simp [randomizedResponseOfProb_apply]

instance (p : I) : IsMarkovKernel (randomizedResponseOfProb p) := by
  refine ⟨fun b ↦ ⟨?_⟩⟩
  rw [randomizedResponseOfProb_apply, ← ENNReal.ofReal_one]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add p.2.1 (sub_nonneg.2 p.2.2), add_sub_cancel]

/-- **Proposition 5** of Mironov (randomized response, order `α > 1`), the exact value behind
Table II: for `p ∈ (0, 1)`,
`D_α(RR_p(b) ‖ RR_p(!b)) = (α - 1)⁻¹ log (p ^ α (1 - p) ^ (1 - α) + (1 - p) ^ α p ^ (1 - α))`. -/
theorem renyiDiv_randomizedResponseOfProb {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hα : 1 < α) (b : Bool) :
    renyiDiv α (randomizedResponseOfProb p b) (randomizedResponseOfProb p (!b))
      = ENNReal.ofReal ((α - 1)⁻¹
        * log ((p : ℝ) ^ α * (1 - p) ^ (1 - α) + (1 - p) ^ α * (p : ℝ) ^ (1 - α))) := by
  have hreal (b c : Bool) : (randomizedResponseOfProb p b).real {c}
      = if c = b then (p : ℝ) else 1 - p := by
    rw [measureReal_def, randomizedResponseOfProb_apply_singleton]
    split_ifs
    · exact ENNReal.toReal_ofReal hp0.le
    · exact ENNReal.toReal_ofReal (by linarith)
  have hac : randomizedResponseOfProb p b ≪ randomizedResponseOfProb p (!b) := fun s hs ↦ by
    rcases s.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · simp
    · exfalso
      have h1 := measure_mono (μ := randomizedResponseOfProb p (!b))
        (Set.singleton_subset_iff.2 hc)
      rw [hs, randomizedResponseOfProb_apply_singleton] at h1
      split_ifs at h1
      · simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
        linarith
      · simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
        linarith
  rw [renyiDiv_eq_ofReal_log_sum hα hac, Fintype.sum_bool, hreal, hreal, hreal, hreal]
  cases b <;> simp [add_comm]

end RenyiDP

open RenyiDP unitInterval in
/-- **Proposition 5** of Mironov (randomized response, order `α > 1`): for a measurable predicate
`f` on datasets and `p ∈ (0, 1)`, the randomized response mechanism `RR_p f` is `(α, ε)`-RDP with
`ε = (α - 1)⁻¹ log (p ^ α (1 - p) ^ (1 - α) + (1 - p) ^ α p ^ (1 - α))` (Table II), for every
neighbouring relation. The bound is attained by every pair with `f(S) ≠ f(S')`
(`RenyiDP.renyiDiv_randomizedResponseOfProb`). -/
theorem isRenyiDP_randomizedResponseOfProb_comap {f : 𝒟 → Bool} (hf : Measurable f) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hα : 1 < α) :
    IsRenyiDP ((randomizedResponseOfProb p).comap f hf) Adj α (Real.toNNReal ((α - 1)⁻¹
      * log ((p : ℝ) ^ α * (1 - p) ^ (1 - α) + (1 - p) ^ α * (p : ℝ) ^ (1 - α)))) :=
  fun S S' _ ↦ by
    rw [Kernel.comap_apply, Kernel.comap_apply]
    change _ ≤ ENNReal.ofReal _
    rcases Bool.eq_or_eq_not (f S') (f S) with h | h
    · simp [h]
    · rw [h]
      exact (renyiDiv_randomizedResponseOfProb hp0 hp1 hα (f S)).le

end InformationTheory
