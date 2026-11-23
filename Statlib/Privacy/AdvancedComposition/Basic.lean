/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.DP.Basic
public import Statlib.Privacy.DP.RandomizedResponse
public import Statlib.Privacy.ZCDP.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The advanced composition theorem

This file formalizes the advanced composition theorem of differential privacy for `ε`-DP
mechanisms, in its adaptive `k`-fold form, from

* C. Dwork, G. N. Rothblum and S. Vadhan, *Boosting and differential privacy*, FOCS 2010
  (DRV), Theorem III.3, and
* C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Found. Trends
  Theor. Comput. Sci. 9(3–4), 2014, Theorem 3.20 and Corollary 3.21 (page numbers below are the
  printed ones of the PDF at https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf):

the `k`-fold adaptive composition of `ε`-DP mechanisms is `(ε', δ')`-DP for every `δ' > 0`, where
`ε' = √(2 k ln (1 / δ')) ε + k ε (e^ε - 1)`.

A mechanism is a kernel from datasets to outputs, `Adj` is a neighbouring relation on datasets,
assumed symmetric (as the book's `‖x - y‖₁ ≤ 1` is), and `(ε, δ)`-DP is `IsEpsDeltaDP` (pure
`ε`-DP is `IsEpsDP`), both from `Statlib.Privacy.DP.Basic`. Output spaces are
**arbitrary measurable spaces**; the adaptive results assume the common output space `Y` of the
rounds countably generated (e.g. countable, or standard Borel).

## Route

The proof is not the book's (privacy loss random variable, the bound `D(Y ‖ Z) ≤ ε (e^ε - 1)` of
Lemma 3.18 and Azuma's inequality). It follows the zero-concentrated DP route of M. Bun and
T. Steinke, *Concentrated differential privacy: simplifications, extensions, and lower bounds*,
TCC 2016 ([arXiv:1605.02065](https://arxiv.org/abs/1605.02065), v1), with the results of
`Statlib.Privacy.ZCDP.Basic`:

1. an `ε`-DP mechanism is `(ε² / 2)`-zCDP (Proposition 1.4, `IsEpsDeltaDP.isZCDP`);
2. zCDP adds up under adaptive composition (Lemma 2.3, `IsZCDP.compProd`, iterated here as
   `AdvancedComposition.isZCDP_adaptiveCompose`), so the `k`-fold composition is
   `(k ε² / 2)`-zCDP;
3. `ρ`-zCDP implies `(ρ + 2 √(ρ ln (1 / δ')), δ')`-DP (Proposition 1.3, `IsZCDP.isEpsDeltaDP'`),
   which for `ρ = k ε² / 2` is `(k ε² / 2 + ε √(2 k ln (1 / δ')), δ')`-DP;
4. `k ε² / 2 ≤ k ε (e^ε - 1)`.

This route gives the sharper second term `k ε² / 2` in place of `k ε (e^ε - 1)`. Bun and Steinke
note (Section 1.2.1, after Proposition 1.4) that Dwork and Rothblum's version of Proposition 1.4
gives `(½ ε (e^ε - 1))`-zCDP, a factor `½` better than the earlier bound of DRV, and that
Proposition 1.4 is slightly stronger still (Remark 3.4 compares the KL bounds `½ ε²` and
`½ ε (e^ε - 1)`); after their Corollary 8.11 (Section 8.3), whose first term `½ ‖ε‖₂²` is
`k ε² / 2` for equal `ε_i`, they note that it saves a constant factor in the first term over the
composition theorem of DRV. The exact bound `k ε² / 2 + ε √(2 k ln (1 / δ'))` is not displayed in
the paper.

## Main definitions

* `AdvancedComposition.adaptiveCompose M k`: the `k`-fold adaptive composition of mechanisms
  `M n : Kernel (𝒟 × (Fin n → Y)) Y`, the `n`-th of which sees the dataset and the `n` earlier
  outputs.

## Main statements (paper result → Lean name, in namespace `AdvancedComposition`)

* Theorem 3.20 of Dwork–Roth for `(ε, 0)`-DP mechanisms, adaptive (for a fixed neighbouring
  relation and history-indexed mechanisms, see the implementation notes):
  `isEpsDeltaDP_adaptiveCompose`; sharper zCDP form `isEpsDeltaDP_adaptiveCompose_sq`; with
  per-round parameters `ε n`, zCDP form: `isEpsDeltaDP_adaptiveCompose_sum_sq`. Theorem III.3 of
  DRV assumes `ε > 0` and `δ, δ' > 0`, so it gives the case `δ = 0` only in the limit `δ → 0`;
  here `δ = 0` is proved directly.
* The same for `k` mechanisms run independently on the same dataset (non-adaptive):
  `isEpsDeltaDP_composeFin` and `isEpsDeltaDP_composeFin_sq` (for `DP.composeFin`, with
  possibly different output spaces), `isEpsDeltaDP_piKernel` (for `ZCDP.piKernel`).
* Composition of zCDP (Lemmas 1.7 and 2.3 of Bun–Steinke, `k`-fold): `isZCDP_adaptiveCompose`,
  `isZCDP_composeFin`; for `ε`-DP rounds, `isZCDP_adaptiveCompose_of_isEpsDP` (`k ε² / 2`).
* Corollary 3.21 of Dwork–Roth for `(ε, 0)`-DP mechanisms, under the sufficient additional
  hypothesis `δ' ≤ e^{-ε'/8}` (see the notes below):
  `isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log` (stated as `ε' ≤ 8 ln (1 / δ')`),
  `isEpsDeltaDP_adaptiveCompose_of_le_one` (the book's `ε' ≤ 1` and `δ' ≤ e^{-1/8}`); a
  counterexample to the printed statement with `δ'` close to `1`, outside the book's intended
  regime of negligible `δ'`: `exists_not_isEpsDeltaDP_adaptiveCompose`.
* A `(1, e^{-32})`-DP guarantee in the setting of Example 3.7 of Dwork–Roth:
  `isEpsDeltaDP_adaptiveCompose_ten_thousand`.

## Implementation notes

* **The composition experiment.** The results here are stated for one fixed neighbouring
  relation `Adj` and history-indexed mechanisms, which is a special case of the book's
  adversary experiment; the encoding of the experiment below is informal (not formalized).
  Dwork–Roth (Section 3.5.2, pp. 48–49) and DRV (Section III.A)
  define `k`-fold adaptive composition through an experiment: in round `i` an adversary chooses,
  depending on the earlier outputs, two adjacent databases `x_i^0, x_i^1` and a mechanism `M_i`
  from the family, and receives an output of `M_i(x_i^b)`; the family is `(ε', δ')`-DP under
  `k`-fold adaptive composition if the adversary's views for `b = 0, 1` are
  `(ε', δ')`-indistinguishable. Here round `n` is a kernel `M n : Kernel (𝒟 × (Fin n → Y)) Y`
  that must be `ε`-DP in the dataset for every history `x`
  (`∀ x, IsEpsDP ((M n).sectL x) Adj ε`), and the conclusion is `(ε', δ')`-DP of the composed
  kernel. The experiment is the instance `𝒟 = Bool` (the secret bit `b`) with
  `Adj = fun _ _ ↦ True` and `M n (b, x)` the law of the round-`n` output in experiment `b` after
  history `x`: the hypothesis then says that the mechanism chosen after `x`, run on the two
  databases chosen after `x`, gives `ε`-indistinguishable outputs in both directions, which holds
  because that mechanism is `ε`-DP and the databases are adjacent. The adversary's choices must be
  measurable in the history (this is part of `M n` being a kernel), all rounds share the output
  space `Y`, and the adversary's coins, which the book includes in the view, can be released by
  an extra first round that does not depend on `b`, with parameter `0`
  (`isEpsDeltaDP_adaptiveCompose_sum_sq` allows per-round parameters).
* Countable generation of `Y` is the hypothesis of Statlib's chain rule for the Rényi divergence,
  on which `IsZCDP.compProd` rests. The non-adaptive results need no such hypothesis.
* The book allows `δ' = 0` (for which `ε' = ∞`); here `δ' > 0`. For `δ' ≥ 1`, Lean's
  `√(2 k ln (1 / δ'))` is `0`, and the conclusion is then the true statement that a Markov kernel
  is `(ε', δ')`-DP whenever `δ' ≥ 1`. As in the book, `ε ≥ 0`; DRV assume `ε > 0` and
  `δ, δ' > 0`.
* The Corollary 3.21 statements are totalized extensions of the book's, whose formula
  presupposes `k ≥ 1` and whose hypotheses include `0 < ε' < 1`: both allow `k = 0`, and
  `isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log` also allows `ε' = 0` with `δ' = 1`. There
  the prescribed `ε = ε' / (2 √(2 k ln (1 / δ')))` has denominator `0`, so Lean's `ε` is `0`.
  These cases are harmless: for `k = 0` the hypothesis on the rounds is vacuous and the
  conclusion is that the constant `0`-fold composition is `(ε', δ')`-DP, and for `δ' = 1` the
  conclusion holds for every Markov kernel.

## Notes on the paper

* Corollary 3.21 of Dwork–Roth (Section 3.5.2, p. 52), read literally, fails for `δ'` close to
  `1`, outside the regime it is meant for. The corollary asserts that, for `0 < ε' < 1` and
  `δ' > 0`, `k` mechanisms that are each `(ε, δ)`-DP with `ε = ε' / (2 √(2 k ln (1 / δ')))`
  compose to an `(ε', k δ + δ')`-DP mechanism; it places no further restriction on `δ'` or `k`.
  For `k = 1`, `δ = 0`, `ε' = 9/10` and `δ' = e^{-1/800} ≈ 0.99875`, this `ε` is `9`, and binary
  randomized response with parameter `9` is `9`-DP but not `(9/10, e^{-1/800})`-DP: it is
  `(9/10, δ')`-DP only for `δ' ≥ (e⁹ - e^{9/10}) / (1 + e⁹) ≈ 0.99957`
  (`exists_not_isEpsDeltaDP_adaptiveCompose`). The book states (Section 2.3, p. 25) that
  "typically, and throughout this monograph, we require that `δ` be a negligible function" of a
  security parameter, so the corollary is meant for cryptographically small `δ'`; the
  counterexample is a failure of the unrestricted printed formula outside that intended regime,
  not of the corollary as used in the book. A sufficient additional hypothesis is
  `δ' ≤ e^{-ε'/8}` (`isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log`); it is not necessary
  (for `k = 1` and `ε' = δ' = 9/10` it fails, but the prescribed `ε ≈ 0.9803`, and an `ε`-DP
  mechanism is `(9/10, 1 - e^{9/10 - ε})`-DP with `1 - e^{9/10 - ε} ≈ 0.077 < 9/10`; not
  formalized). Every counterexample with `δ = 0` has `δ' > e^{-ε'/8} > 0.88` for
  `ε' < 1`; only `δ = 0` is examined here. The proof has two gaps.
  It takes the bound of Theorem 3.20 to be `ε* = √(2 k ln (1 / δ')) ε + k ε²`, whereas
  Theorem 3.20 gives `k ε (e^ε - 1) ≥ k ε²` in the second term (for `δ = 0` the zCDP route does
  give `k ε² / 2`, so this step is repairable there). And "when `ε' < 1`, we have that
  `ε* ≤ ε'`" holds if and only if `ε' ≤ 4 ln (1 / δ')`, which fails for `δ'` close to `1`. For
  `δ = 0` the corollary holds when `δ' ≤ e^{-ε'/8}`, i.e. `ε' ≤ 8 ln (1 / δ')`, for instance when
  `ε' ≤ 1` and `δ' ≤ e^{-1/8}` (`isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log`,
  `isEpsDeltaDP_adaptiveCompose_of_le_one`).
* Example 3.7 of Dwork–Roth (p. 52) states that for `k = 10 000` mechanisms, "Theorem 3.20 says
  that, taking `δ' = e^{-32}` it suffices to have `ε₀ ≤ 1/801`" for the cumulative privacy loss to
  be at most `1` with probability at least `1 - e^{-32}`. The numerical conclusion appears to be
  true: the exact optimal composition (Kairouz–Oh–Viswanath, ICML 2015) gives
  `δ(1) ≈ e^{-38.8}` at `ε₀ = 1/801` (checked numerically only, not formalized). Only the
  attribution to Theorem 3.20 is wrong: it accounts only for the first term
  `√(2 k ln (1 / δ')) ε₀ = 800 ε₀`, and at `ε₀ = 1/801` the bound of Theorem 3.20 is
  `ε' ≈ 1.014` (it gives `ε' ≤ 1` only for `ε₀ ≤ 1/812.3`, approximately). The sharper bound
  `isEpsDeltaDP_adaptiveCompose_sq` gives `ε' ≈ 1.007` at `ε₀ = 1/801` and `ε' ≤ 1` for
  `ε₀ ≤ 1/806.2` (approximately), in particular at `ε₀ = 1/807`
  (`isEpsDeltaDP_adaptiveCompose_ten_thousand`). The book states a tail bound on the privacy
  loss, which is stronger than the `(1, e^{-32})`-DP proved here.
* In the proof of Theorem 3.20 (pp. 50–51), Azuma's inequality is applied with "`β = ε · ε₀`",
  where `ε₀` is not defined in the book (it is DRV's `ε₀ = e^ε - 1`), so `β = ε (e^ε - 1)` is
  meant; the pure case writes `δ` for `δ'` (in `Pr[V⁰ ∈ B] ≤ δ` and `z = √(2 ln (1 / δ))`); and the
  last line should read `D_∞^{δ' + kδ}(V⁰ ‖ V¹) ≤ ε'` rather than `(V⁰ ‖ W)`. These are typos; the
  theorem is true for `(ε, 0)`-DP mechanisms (`isEpsDeltaDP_adaptiveCompose`).

## Not formalized

* Theorem 3.20 (Theorem III.3 of DRV) and Corollary 3.21 for `(ε, δ)`-DP mechanisms with `δ > 0`
  (total failure probability `k δ + δ'`), whose proof uses the characterization of approximate
  max-divergence (Lemma 3.17 of Dwork–Roth).
* The book's proof through the privacy loss, Lemma 3.18 and Azuma's inequality (Lemma 3.19), and
  the adversary-view formulation of the experiment as such (see the implementation notes).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

namespace AdvancedComposition

variable {𝒟 Y : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}
  {Adj : 𝒟 → 𝒟 → Prop}

/-! ### Adaptive composition -/

/-- Appending an element to a tuple, `(x, y) ↦ (x₀, …, x_{n-1}, y)`, is measurable. -/
lemma measurable_snoc (n : ℕ) :
    Measurable fun p : (Fin n → Y) × Y ↦ (Fin.snoc p.1 p.2 : Fin (n + 1) → Y) := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_snd
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The **`k`-fold adaptive composition** of the mechanisms `M n`, `n < k`: on a dataset `S`, it
draws `y₀ ∼ M 0 (S, ())`, then `y₁ ∼ M 1 (S, (y₀))`, …, `y_{k-1} ∼ M (k-1) (S, (y₀, …, y_{k-2}))`,
and releases `(y₀, …, y_{k-1})`. The `n`-th mechanism `M n : Kernel (𝒟 × (Fin n → Y)) Y` sees the
dataset and the outputs of the `n` earlier ones (its *history*), so that it may be chosen
adaptively. It is defined by recursion on `k` with `Kernel.compProd`. -/
noncomputable def adaptiveCompose (M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y) :
    (k : ℕ) → Kernel 𝒟 (Fin k → Y)
  | 0 => Kernel.const 𝒟 (Measure.dirac isEmptyElim)
  | k + 1 => (adaptiveCompose M k ⊗ₖ M k).map fun p ↦ (Fin.snoc p.1 p.2 : Fin (k + 1) → Y)

variable {M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y}

lemma adaptiveCompose_zero (M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y) :
    adaptiveCompose M 0 = Kernel.const 𝒟 (Measure.dirac isEmptyElim) := rfl

lemma adaptiveCompose_succ (M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y) (k : ℕ) :
    adaptiveCompose M (k + 1) =
      (adaptiveCompose M k ⊗ₖ M k).map fun p ↦ (Fin.snoc p.1 p.2 : Fin (k + 1) → Y) := rfl

instance isMarkovKernel_adaptiveCompose (M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y)
    [∀ n, IsMarkovKernel (M n)] (k : ℕ) : IsMarkovKernel (adaptiveCompose M k) := by
  induction k with
  | zero => rw [adaptiveCompose_zero]; infer_instance
  | succ k ih => rw [adaptiveCompose_succ]; exact Kernel.IsMarkovKernel.map _ (measurable_snoc k)

/-- The first output of the adaptive composition is the output of `M 0` (with the empty
history). -/
lemma map_adaptiveCompose_one (M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y)
    [∀ n, IsMarkovKernel (M n)] :
    (adaptiveCompose M 1).map (fun y ↦ y 0) = (M 0).sectL isEmptyElim := by
  ext S E hE
  rw [Kernel.map_apply' _ (measurable_pi_apply 0) _ hE, adaptiveCompose_succ,
    Kernel.map_apply' _ (measurable_snoc 0) _ (measurable_pi_apply 0 hE),
    Kernel.compProd_apply ((measurable_snoc 0) (measurable_pi_apply 0 hE)), adaptiveCompose_zero,
    Kernel.const_apply, lintegral_dirac' _ Subsingleton.measurable, Kernel.sectL_apply]
  rfl

/-! ### Composition of zCDP mechanisms -/

/-- A constant mechanism with a probability distribution as output is `(0, 0)`-zCDP. -/
lemma isZCDP_const (μ : Measure Y) [IsProbabilityMeasure μ] :
    IsZCDP (Kernel.const 𝒟 μ) Adj 0 0 :=
  isZCDP_iff_toReal.2 fun S S' _ α _ ↦ by simp [renyiDiv_self]

/-- **Adaptive composition of `k` zCDP mechanisms** (Lemma 2.3 of Bun–Steinke, iterated): if, for
every `n < k` and every history `x`, the mechanism `S ↦ M n (S, x)` is `(ξ n, ρ n)`-zCDP, then
the `k`-fold adaptive composition is `(∑_{n<k} ξ n, ∑_{n<k} ρ n)`-zCDP. The output space `Y` is
assumed countably generated (e.g. countable, or standard Borel), as required by the chain rule
for the Rényi divergence. -/
theorem isZCDP_adaptiveCompose [MeasurableSpace.CountablyGenerated Y]
    [∀ n, IsMarkovKernel (M n)] {ξ ρ : ℕ → ℝ} {k : ℕ}
    (h : ∀ n < k, ∀ x, IsZCDP ((M n).sectL x) Adj (ξ n) (ρ n)) :
    IsZCDP (adaptiveCompose M k) Adj (∑ n ∈ Finset.range k, ξ n)
      (∑ n ∈ Finset.range k, ρ n) := by
  induction k with
  | zero => simpa [adaptiveCompose_zero] using isZCDP_const (𝒟 := 𝒟) (Adj := Adj) _
  | succ k ih =>
    rw [adaptiveCompose_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    exact ((ih fun n hn ↦ h n (hn.trans k.lt_succ_self)).compProd
      (h k k.lt_succ_self)).map (measurable_snoc k)

/-- **Composition of `k` zCDP mechanisms**, non-adaptive form for the `k`-fold composition
`DP.composeFin` of `Statlib.Privacy.DP.Basic` (Lemma 1.7 of Bun–Steinke, iterated): if `M i` is
`(ξ i, ρ i)`-zCDP for every `i < k`, then `S ↦ (M₀(S), …, M_{k-1}(S))` is
`(∑ ξ i, ∑ ρ i)`-zCDP. Arbitrary measurable output spaces `R i`. -/
theorem isZCDP_composeFin {k : ℕ} {R : Fin k → Type*} [∀ i, MeasurableSpace (R i)]
    {M : (i : Fin k) → Kernel 𝒟 (R i)} [∀ i, IsMarkovKernel (M i)] {ξ ρ : Fin k → ℝ}
    (h : ∀ i, IsZCDP (M i) Adj (ξ i) (ρ i)) :
    IsZCDP (DP.composeFin M) Adj (∑ i, ξ i) (∑ i, ρ i) := by
  induction k with
  | zero => simpa [DP.composeFin] using isZCDP_const (𝒟 := 𝒟) (Adj := Adj) _
  | succ k ih =>
    rw [DP.composeFin, Fin.sum_univ_succAbove _ 0, Fin.sum_univ_succAbove _ 0]
    exact ((h 0).prod (ih (M := fun j ↦ M (Fin.succAbove 0 j))
      (ξ := fun j ↦ ξ (Fin.succAbove 0 j)) (ρ := fun j ↦ ρ (Fin.succAbove 0 j))
      fun j ↦ h _)).map (MeasurableEquiv.measurable _)

/-! ### Advanced composition of pure-DP mechanisms -/

/-- `ε² / 2 ≤ ε (e^ε - 1)` for `ε ≥ 0`: the per-mechanism term of the zCDP route is at most the
term `ε (e^ε - 1)` of Dwork–Roth's Theorem 3.20. -/
lemma sq_div_two_le_mul_exp_sub_one {ε : ℝ} (hε : 0 ≤ ε) : ε ^ 2 / 2 ≤ ε * (exp ε - 1) := by
  nlinarith [add_one_le_exp ε]

/-- `2 √((k ε² / 2) L) = ε √(2 k L)` for `ε ≥ 0` (for every real `k` and `L`, as `√` of a negative
number is `0`). -/
lemma two_mul_sqrt_eq {k ε L : ℝ} (hε : 0 ≤ ε) :
    2 * √(k * ε ^ 2 / 2 * L) = ε * √(2 * k * L) := by
  rw [show k * ε ^ 2 / 2 * L = (ε / 2) ^ 2 * (2 * k * L) by ring, sqrt_mul (sq_nonneg _),
    sqrt_sq (by linarith)]
  ring

/-- **Adaptive composition of `k` pure-DP mechanisms is `(k ε² / 2)`-zCDP** (Proposition 1.4 and
Lemma 2.3 of Bun–Steinke): if, for every `n < k` and every history `x`, the mechanism
`S ↦ M n (S, x)` is `ε`-DP for the symmetric neighbouring relation `Adj`, then the `k`-fold
adaptive composition is `(k ε² / 2)`-zCDP. `Y` is countably generated. -/
theorem isZCDP_adaptiveCompose_of_isEpsDP [MeasurableSpace.CountablyGenerated Y] [Std.Symm Adj]
    [∀ n, IsMarkovKernel (M n)] {ε : ℝ} {k : ℕ}
    (h : ∀ n < k, ∀ x, IsEpsDP ((M n).sectL x) Adj ε) :
    IsZCDP (adaptiveCompose M k) Adj 0 (k * ε ^ 2 / 2) := by
  simpa [mul_div_assoc] using isZCDP_adaptiveCompose (ξ := fun _ ↦ 0) (ρ := fun _ ↦ ε ^ 2 / 2)
    fun n hn x ↦ (h n hn x).isZCDP

/-- **Advanced composition, zCDP form** (the bound obtained from Proposition 1.4, Lemma 2.3 and
Proposition 1.3 of Bun–Steinke): if, for every `n < k` and every history `x`, the mechanism
`S ↦ M n (S, x)` is `ε`-DP (`ε ≥ 0`) for the symmetric neighbouring relation `Adj`, then the
`k`-fold adaptive composition is `(k ε² / 2 + ε √(2 k ln (1 / δ)), δ)`-DP for every `δ > 0`.
This is Theorem 3.20 of Dwork–Roth for pure-DP mechanisms with the sharper second term `k ε² / 2`
in place of `k ε (e^ε - 1)` (see `isEpsDeltaDP_adaptiveCompose`). `Y` is countably generated.

The hypothesis fixes one neighbouring relation `Adj` and lets the mechanisms depend on the
history; this is a special case of the adversary experiment of Dwork–Roth (Section 3.5.2), into
which that experiment can be encoded only informally (with `𝒟 = Bool`, see the module
documentation). Releasing the adversary's coins needs an extra round with parameter `0`, which
only `isEpsDeltaDP_adaptiveCompose_sum_sq` allows. -/
theorem isEpsDeltaDP_adaptiveCompose_sq [MeasurableSpace.CountablyGenerated Y] [Std.Symm Adj]
    [∀ n, IsMarkovKernel (M n)] {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ}
    (h : ∀ n < k, ∀ x, IsEpsDP ((M n).sectL x) Adj ε) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP (adaptiveCompose M k) Adj (k * ε ^ 2 / 2 + ε * √(2 * k * log (1 / δ))) δ := by
  have := (isZCDP_adaptiveCompose_of_isEpsDP h).isEpsDeltaDP' hδ
  rwa [two_mul_sqrt_eq hε] at this

/-- **Advanced composition with per-round parameters, zCDP form** (Proposition 1.4, Lemma 2.3 and
Proposition 1.3 of Bun–Steinke): if, for every `n < k` and every history `x`, the mechanism
`S ↦ M n (S, x)` is `ε n`-DP for the symmetric neighbouring relation `Adj`, then, with
`ρ = ∑_{n<k} ε n ^ 2 / 2`, the `k`-fold adaptive composition is `(ρ + 2 √(ρ ln (1 / δ)), δ)`-DP
for every `δ > 0`. `Y` is countably generated. -/
theorem isEpsDeltaDP_adaptiveCompose_sum_sq [MeasurableSpace.CountablyGenerated Y]
    [Std.Symm Adj] [∀ n, IsMarkovKernel (M n)] {ε : ℕ → ℝ} {k : ℕ}
    (h : ∀ n < k, ∀ x, IsEpsDP ((M n).sectL x) Adj (ε n)) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP (adaptiveCompose M k) Adj ((∑ n ∈ Finset.range k, ε n ^ 2 / 2) +
      2 * √((∑ n ∈ Finset.range k, ε n ^ 2 / 2) * log (1 / δ))) δ := by
  have h0 := isZCDP_adaptiveCompose (ξ := fun _ ↦ 0) (ρ := fun n ↦ ε n ^ 2 / 2)
    fun n hn x ↦ (h n hn x).isZCDP
  rw [Finset.sum_const_zero] at h0
  exact h0.isEpsDeltaDP' hδ

/-- **Advanced composition theorem** (Theorem 3.20 of Dwork–Roth for `(ε, 0)`-DP mechanisms):
if, for every `n < k` and every history `x`, the mechanism `S ↦ M n (S, x)` is `ε`-DP (`ε ≥ 0`)
for the symmetric neighbouring relation `Adj`, then the `k`-fold adaptive composition is
`(ε', δ')`-DP for every `δ' > 0`, where `ε' = √(2 k ln (1 / δ')) ε + k ε (e^ε - 1)`. `Y` is
countably generated.

Theorem III.3 of Dwork–Rothblum–Vadhan states the same bound for `ε > 0` and `δ, δ' > 0` (total
failure probability `k δ + δ'`); the case `δ = 0` proved here follows from it only by letting
`δ → 0`.

The hypothesis fixes one neighbouring relation `Adj` and lets the mechanisms depend on the
history; this is a special case of the adversary experiment of Dwork–Roth (Section 3.5.2), into
which that experiment can be encoded only informally (with `𝒟 = Bool`, see the module
documentation). Releasing the adversary's coins needs an extra round with parameter `0`, which
only `isEpsDeltaDP_adaptiveCompose_sum_sq` allows. -/
theorem isEpsDeltaDP_adaptiveCompose [MeasurableSpace.CountablyGenerated Y] [Std.Symm Adj]
    [∀ n, IsMarkovKernel (M n)] {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ}
    (h : ∀ n < k, ∀ x, IsEpsDP ((M n).sectL x) Adj ε) {δ' : ℝ} (hδ' : 0 < δ') :
    IsEpsDeltaDP (adaptiveCompose M k) Adj
      (√(2 * k * log (1 / δ')) * ε + k * ε * (exp ε - 1)) δ' :=
  (isEpsDeltaDP_adaptiveCompose_sq hε h hδ').mono (by
    nlinarith [mul_le_mul_of_nonneg_left (sq_div_two_le_mul_exp_sub_one hε)
      (Nat.cast_nonneg (α := ℝ) k)]) le_rfl

/-- **Advanced composition, non-adaptive form, zCDP bound**: if `M i` is `ε`-DP (`ε ≥ 0`) for
every `i < k`, for the symmetric neighbouring relation `Adj`, then the `k`-fold composition
`S ↦ (M₀(S), …, M_{k-1}(S))` (`DP.composeFin`) is `(k ε² / 2 + ε √(2 k ln (1 / δ)), δ)`-DP for
every `δ > 0`. Arbitrary measurable output spaces `R i`. -/
theorem isEpsDeltaDP_composeFin_sq [Std.Symm Adj] {k : ℕ} {R : Fin k → Type*}
    [∀ i, MeasurableSpace (R i)] {M : (i : Fin k) → Kernel 𝒟 (R i)} [∀ i, IsMarkovKernel (M i)]
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, IsEpsDP (M i) Adj ε) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP (DP.composeFin M) Adj (k * ε ^ 2 / 2 + ε * √(2 * k * log (1 / δ))) δ := by
  have h0 := isZCDP_composeFin (ξ := fun _ ↦ 0) (ρ := fun _ ↦ ε ^ 2 / 2) fun i ↦ (h i).isZCDP
  simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_div_assoc] at h0
  have := h0.isEpsDeltaDP' hδ
  rwa [two_mul_sqrt_eq hε] at this

/-- **Advanced composition theorem, non-adaptive form** (Theorem 3.20 of Dwork–Roth for `k`
mechanisms run independently on the same dataset, `(ε, 0)`-DP inputs): if `M i` is `ε`-DP
(`ε ≥ 0`) for every `i < k`, for the symmetric neighbouring relation `Adj`, then
`S ↦ (M₀(S), …, M_{k-1}(S))` (`DP.composeFin`) is
`(√(2 k ln (1 / δ')) ε + k ε (e^ε - 1), δ')`-DP for every `δ' > 0`. Arbitrary measurable output
spaces `R i`. -/
theorem isEpsDeltaDP_composeFin [Std.Symm Adj] {k : ℕ} {R : Fin k → Type*}
    [∀ i, MeasurableSpace (R i)] {M : (i : Fin k) → Kernel 𝒟 (R i)} [∀ i, IsMarkovKernel (M i)]
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, IsEpsDP (M i) Adj ε) {δ' : ℝ} (hδ' : 0 < δ') :
    IsEpsDeltaDP (DP.composeFin M) Adj
      (√(2 * k * log (1 / δ')) * ε + k * ε * (exp ε - 1)) δ' :=
  (isEpsDeltaDP_composeFin_sq hε h hδ').mono (by
    nlinarith [mul_le_mul_of_nonneg_left (sq_div_two_le_mul_exp_sub_one hε)
      (Nat.cast_nonneg (α := ℝ) k)]) le_rfl

/-- **Advanced composition theorem for the product kernel** `ZCDP.piKernel` (Theorem 3.20 of
Dwork–Roth, non-adaptive, `(ε, 0)`-DP inputs): if each of the `k = |ι|` mechanisms `M i` is `ε`-DP
(`ε ≥ 0`) for the symmetric neighbouring relation `Adj`, then `S ↦ ∏ i, M i S` is
`(√(2 k ln (1 / δ')) ε + k ε (e^ε - 1), δ')`-DP for every `δ' > 0`. It follows from the sharper
`isEpsDeltaDP_pi_of_isEpsDeltaDP` of `Statlib.Privacy.ZCDP.Basic`. -/
theorem isEpsDeltaDP_piKernel {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, MeasurableSpace (R i)] {M : ∀ i, Kernel 𝒟 (R i)} [∀ i, IsMarkovKernel (M i)]
    [Std.Symm Adj] {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, IsEpsDP (M i) Adj ε) {δ' : ℝ} (hδ' : 0 < δ') :
    IsEpsDeltaDP (ZCDP.piKernel M) Adj
      (√(2 * Fintype.card ι * log (1 / δ')) * ε + Fintype.card ι * ε * (exp ε - 1)) δ' :=
  (isEpsDeltaDP_pi_of_isEpsDeltaDP hε h hδ').mono (by
    nlinarith [mul_le_mul_of_nonneg_left (sq_div_two_le_mul_exp_sub_one hε)
      (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))]) le_rfl

/-! ### Corollary 3.21: choosing the per-mechanism `ε` -/

/-- **Corollary 3.21 of Dwork–Roth with the additional hypothesis `δ' ≤ e^{-ε'/8}`, for
`(ε, 0)`-DP mechanisms**: let `ε' ≥ 0` and `δ' > 0` with `ε' ≤ 8 ln (1 / δ')`, i.e.
`δ' ≤ e^{-ε'/8}`. If, for every `n < k` and every history `x`, the mechanism `S ↦ M n (S, x)` is
`ε`-DP for the symmetric neighbouring relation `Adj`, where `ε = ε' / (2 √(2 k ln (1 / δ')))`,
then the `k`-fold adaptive composition is `(ε', δ')`-DP.

The book assumes `0 < ε' < 1` and `δ' > 0`, with `δ'` negligible by its global convention
(p. 25); a sufficient additional hypothesis is `δ' ≤ e^{-ε'/8}`. Some restriction is needed: the
printed statement fails for some `δ'` close to `1` (`exists_not_isEpsDeltaDP_adaptiveCompose`),
and every counterexample with `δ = 0` has `δ' > e^{-ε'/8}` (`> 0.88` for `ε' < 1`). The
hypothesis holds for instance when `ε' ≤ 1` and `δ' ≤ e^{-1/8}`
(`isEpsDeltaDP_adaptiveCompose_of_le_one`). `Y` is countably generated.

This is a totalized extension of the corollary: it also allows `k = 0`, and `ε' = 0` with
`δ' = 1`, where the denominator `2 √(2 k ln (1 / δ'))` is `0` and Lean's `ε` is `0`; these cases
are harmless (the `0`-fold composition is a constant kernel, and every Markov kernel is
`(ε', 1)`-DP). -/
theorem isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log [MeasurableSpace.CountablyGenerated Y]
    [Std.Symm Adj] [∀ n, IsMarkovKernel (M n)] {k : ℕ} {ε' δ' : ℝ} (hε' : 0 ≤ ε')
    (hδ' : 0 < δ') (hε'δ' : ε' ≤ 8 * log (1 / δ'))
    (h : ∀ n < k, ∀ x, IsEpsDP ((M n).sectL x) Adj (ε' / (2 * √(2 * k * log (1 / δ'))))) :
    IsEpsDeltaDP (adaptiveCompose M k) Adj ε' δ' := by
  set L := log (1 / δ')
  set s := √(2 * k * L) with hs
  refine (isEpsDeltaDP_adaptiveCompose_sq (div_nonneg hε' (by positivity)) h hδ').mono ?_ le_rfl
  rcases (sqrt_nonneg (2 * k * L)).eq_or_lt with hs0 | hspos
  · rw [hs, ← hs0]
    simpa using hε'
  have hL : 0 < 2 * k * L := sqrt_pos.1 hspos
  have hs2 : s ^ 2 = 2 * k * L := sq_sqrt hL.le
  have hk : (k : ℝ) ≠ 0 := by
    rintro hk
    simp [hk] at hL
  have hLpos : 0 < L := by
    by_contra hcon
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have h1 : k * (ε' / (2 * s)) ^ 2 / 2 = ε' ^ 2 / (16 * L) := by
    rw [div_pow, mul_pow, hs2]
    field_simp
    ring
  have hsne : s ≠ 0 := hspos.ne'
  have h2 : ε' / (2 * s) * s = ε' / 2 := by
    field_simp
  rw [h1, h2]
  have : ε' ^ 2 / (16 * L) ≤ ε' / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Corollary 3.21 of Dwork–Roth with the book's hypotheses plus `δ' ≤ e^{-1/8}`**, for
`(ε, 0)`-DP mechanisms: for `0 ≤ ε' ≤ 1` and `0 < δ' ≤ e^{-1/8}`, if every round is `ε`-DP with
`ε = ε' / (2 √(2 k ln (1 / δ')))`, then the `k`-fold adaptive composition is `(ε', δ')`-DP. For a
given `ε' < 1`, the weaker `δ' ≤ e^{-ε'/8}` is already sufficient
(`isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log`); `δ' ≤ e^{-1/8}` is the version uniform in
`ε' ≤ 1`. Some restriction on `δ'` is needed (`exists_not_isEpsDeltaDP_adaptiveCompose`).
The statement also allows `k = 0` (a totalized extension: the prescribed `ε` is then `ε' / 0 = 0`
in Lean, the hypothesis on the rounds is vacuous, and the `0`-fold composition is a constant
kernel); here `δ' < 1` holds automatically. -/
theorem isEpsDeltaDP_adaptiveCompose_of_le_one [MeasurableSpace.CountablyGenerated Y]
    [Std.Symm Adj] [∀ n, IsMarkovKernel (M n)] {k : ℕ} {ε' δ' : ℝ} (hε' : 0 ≤ ε') (hε'1 : ε' ≤ 1)
    (hδ' : 0 < δ') (hδ'e : δ' ≤ exp (-(1 / 8)))
    (h : ∀ n < k, ∀ x, IsEpsDP ((M n).sectL x) Adj (ε' / (2 * √(2 * k * log (1 / δ'))))) :
    IsEpsDeltaDP (adaptiveCompose M k) Adj ε' δ' := by
  refine isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log hε' hδ' ?_ h
  have := log_le_log hδ' hδ'e
  rw [log_exp] at this
  rw [one_div, log_inv]
  linarith

/-- **The printed Corollary 3.21 of Dwork–Roth fails without a restriction on `δ'`**, for `δ'`
close to `1`, outside the book's intended regime: the book requires `δ` to be negligible
"throughout this monograph" (Section 2.3, p. 25), while the corollary's hypotheses (p. 52) are only
`0 < ε' < 1` and `δ' > 0`. With `k = 1`,
`ε' = 9/10 ∈ (0, 1)`, `δ' = e^{-1/800} > 0` and `δ = 0`, the corollary asserts that the `1`-fold
composition of an `ε`-DP mechanism, `ε = ε' / (2 √(2 k ln (1 / δ'))) = 9`, is `(ε', δ')`-DP.
Binary randomized response with parameter `9` (on `Bool`, where any two inputs are neighbours) is
`9`-DP, but its `1`-fold composition is not `(9/10, e^{-1/800})`-DP: it reports the true bit with
probability `e⁹ / (1 + e⁹) > e^{9/10} / (1 + e⁹) + e^{-1/800}` (it is `(9/10, δ')`-DP only for
`δ' ≥ (e⁹ - e^{9/10}) / (1 + e⁹) ≈ 0.99957`, while `e^{-1/800} ≈ 0.99875`). Every counterexample
with `δ = 0` has `δ' > e^{-ε'/8}`, which exceeds `0.88` for `ε' < 1`
(`isEpsDeltaDP_adaptiveCompose_of_le_eight_mul_log`, a sufficient additional hypothesis); only
`δ = 0` is examined. -/
theorem exists_not_isEpsDeltaDP_adaptiveCompose :
    ∃ M : (n : ℕ) → Kernel (Bool × (Fin n → Bool)) Bool, (∀ n, IsMarkovKernel (M n)) ∧
      (∀ n x, IsEpsDP ((M n).sectL x) (fun _ _ ↦ True)
        (9 / 10 / (2 * √(2 * (1 : ℕ) * log (1 / exp (-(1 / 800))))))) ∧
      ¬ IsEpsDeltaDP (adaptiveCompose M 1) (fun _ _ ↦ True) (9 / 10) (exp (-(1 / 800))) := by
  have hε : 9 / 10 / (2 * √(2 * (1 : ℕ) * log (1 / exp (-(1 / 800))))) = (9 : ℝ) := by
    rw [one_div (exp _), ← exp_neg, neg_neg, log_exp, Nat.cast_one,
      show (2 : ℝ) * 1 * (1 / 800) = (1 / 20) ^ 2 by norm_num, sqrt_sq (by norm_num)]
    norm_num
  have hRR : IsEpsDP (binaryRandomizedResponse 9) (fun _ _ ↦ True) 9 :=
    (isEpsDeltaDP_binaryRandomizedResponse_iff 9).2 (by norm_num)
  refine ⟨fun n ↦ (binaryRandomizedResponse 9).comap Prod.fst measurable_fst,
    fun n ↦ inferInstance, fun n x ↦ by rw [hε]; exact fun S S' hS E ↦ hRR hS E, fun hDP ↦ ?_⟩
  have h := (hDP.map (measurable_pi_apply 0)) (S := true) (S' := false) trivial {true}
  rw [map_adaptiveCompose_one] at h
  change (binaryRandomizedResponse 9 true).real {true} ≤
    exp (9 / 10) * (binaryRandomizedResponse 9 false).real {!false} + exp (-(1 / 800)) at h
  rw [binaryRandomizedResponse_real_self, binaryRandomizedResponse_real_not] at h
  have hA : 7000 < exp 9 := by
    have h1 : (2.7 : ℝ) ^ 9 < exp 1 ^ 9 :=
      pow_lt_pow_left₀ (by linarith [exp_one_gt_d9]) (by norm_num) (by norm_num)
    rw [← exp_nat_mul] at h1
    norm_num at h1
    linarith
  have hB : exp (9 / 10) < 3 := by
    linarith [exp_le_exp.2 (show (9 / 10 : ℝ) ≤ 1 by norm_num), exp_one_lt_d9]
  have hC : exp (-(1 / 800)) ≤ 800 / 801 := by
    rw [exp_neg, show (800 / 801 : ℝ) = (1 / 800 + 1)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) (add_one_le_exp _)
  have hpos : 0 < 1 + exp 9 := by positivity
  rw [div_le_iff₀ hpos, add_mul, mul_one_div, div_mul_cancel₀ _ hpos.ne'] at h
  nlinarith [mul_le_mul_of_nonneg_right hC (exp_pos 9).le]

/-- **The setting of Example 3.7 of Dwork–Roth**: `k = 10 000` adaptively composed `ε₀`-DP
mechanisms with `ε₀ = 1/807` are `(1, e^{-32})`-DP (for the symmetric neighbouring relation `Adj`).
The book attributes `ε₀ ≤ 1/801` to Theorem 3.20; only that attribution is wrong: at
`ε₀ = 1/801` the bound of Theorem 3.20 is `ε' ≈ 1.014 > 1`, and the zCDP bound
`isEpsDeltaDP_adaptiveCompose_sq` is `ε' ≈ 1.007`, which is at most `1` at `ε₀ = 1/807`. The
book's numerical conclusion itself appears to be true: the exact optimal composition
(Kairouz–Oh–Viswanath, ICML 2015) gives `δ(1) ≈ e^{-38.8}` at `ε₀ = 1/801` (checked numerically
only, not formalized). The book states a tail bound on the privacy loss, which is stronger than
the `(1, e^{-32})`-DP proved here. `Y` is countably generated. -/
theorem isEpsDeltaDP_adaptiveCompose_ten_thousand [MeasurableSpace.CountablyGenerated Y]
    [Std.Symm Adj] [∀ n, IsMarkovKernel (M n)]
    (h : ∀ n < 10000, ∀ x, IsEpsDP ((M n).sectL x) Adj (1 / 807)) :
    IsEpsDeltaDP (adaptiveCompose M 10000) Adj 1 (exp (-32)) := by
  refine (isEpsDeltaDP_adaptiveCompose_sq (by norm_num) h (exp_pos _)).mono ?_ le_rfl
  rw [one_div (exp _), ← exp_neg, neg_neg, log_exp, Nat.cast_ofNat,
    show (2 : ℝ) * 10000 * 32 = 800 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  norm_num

end AdvancedComposition

end InformationTheory
