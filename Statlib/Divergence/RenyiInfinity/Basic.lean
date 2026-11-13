/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.Operational
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A variational formula for the Rényi divergence of order `∞`

This file formalizes, for finite alphabets, the main results of

* G. R. Kurri, O. Kosut, L. Sankar, *A Variational Formula for Infinity-Rényi Divergence with
  Applications to Information Leakage*, ISIT 2022, arXiv:2202.06040.

The Rényi divergence of order `∞` is `D∞(P ‖ Q) = log max_x P(x) / Q(x)`. The paper shows that,
for every gain function `g : [0, 1] → [0, ∞)` with `g 0 = 0`, `g` continuous at `0` and
`0 < sup g < ∞`,
`D∞(P_X ‖ Q_X) = sup_{P_{U|X}} log (G_g(P_U) / G_g(Q_U))`, where
`G_g(ν) = sup_{P_Û} E_{U ∼ ν} g(P_Û(U))` and `P_U`, `Q_U` are the laws of `U` obtained by passing
`P_X` and `Q_X` through the channel `P_{U|X}`: the ratio of the largest expected gains in
guessing `U` does not depend on `g` once it is optimized over all channels. Specializing `g` to
the `α`-loss gain gives closed forms for two variants of maximal `α`-leakage.

## Main definitions

* `expRenyiDivInf P Q`: `max_x P(x) / Q(x)` in `ℝ≥0∞`, the exponential of `D∞(P ‖ Q)`.
* `renyiDivInf P Q`: `D∞(P ‖ Q) = log max_x P(x) / Q(x)`, in `EReal` (in nats).
* `maxExpGain g ν`: `sup_{P_Û} E_{U ∼ ν} g(P_Û(U))`, the largest expected gain in guessing `U ∼ ν`.
* `alphaNorm a ν`: `(∑_u ν(u) ^ a) ^ (1 / a)`.
* `condInput μ κ y`: the conditional law `P_{X|Y=y}` of the input given the output.
* `oppMaxAlphaLeakage a μ κ`: the opportunistic maximal `α`-leakage (paper, Definition 4).
* `realMaxAlphaLeakage a μ κ`: the maximal realizable `α`-leakage (paper, Definition 5).

## Main statements

* `iSup_maxExpGain_div_eq`, `iSup_log_maxExpGain_div_eq`: **Theorem 1**, the variational formula.
* `maxExpGain_ne_zero`: the ratio in Theorem 1 is well defined (paper, (44)–(45)).
* `iSup_lintegral_rpow_eq`: the closed form of the guessing problem for the `α`-loss gain
  (Lemma 1 of Liao–Kosut–Sankar–Calmon, used for Corollary 1).
* `iSup_alphaNorm_div_eq`: **Corollary 1**.
* `iSup_lintegral_div_eq`, `iSup_log_lintegral_div_eq`: **Proposition 1**, formula (10).
* `oppMaxAlphaLeakage_eq`: **Theorem 2**, the opportunistic maximal `α`-leakage equals
  `α / (α - 1) · I∞ˢ(X; Y)`, where `I∞ˢ(X; Y) = maxLeakage μ κ` is the Sibson mutual information
  of order `∞` (the maximal leakage).
* `realMaxAlphaLeakage_eq`: **Theorem 3**, the maximal realizable `α`-leakage equals
  `α / (α - 1) · D∞(P_XY ‖ P_X × P_Y)`.

## Paper → Lean

* Definition 1, (4) → `expRenyiDivInf`, `renyiDivInf`.
* Theorem 1 → `iSup_maxExpGain_div_eq` (multiplicative), `iSup_log_maxExpGain_div_eq` (with `log`);
  its two halves are `maxExpGain_comp_div_le` ((19)–(24)) and `div_le_iSup_maxExpGain_div`
  ((25)–(43)).
* Corollary 1 → `iSup_alphaNorm_div_eq`, `iSup_log_alphaNorm_div_eq`.
* Proposition 1, (10) → `iSup_lintegral_div_eq`, `iSup_log_lintegral_div_eq`.
* Definition 4, Theorem 2 → `oppMaxAlphaLeakageSum`, `oppMaxAlphaLeakage`,
  `oppMaxAlphaLeakageSum_eq_maxLeakageSum`, `oppMaxAlphaLeakage_eq`.
* Definition 5, Theorem 3 → `realMaxAlphaLeakage`, `realMaxAlphaLeakage_eq`.

Not formalized: Proposition 1, formula (9) (in terms of relative entropies), Remark 1 and
Appendix A (the gain `g = log`, which is not covered by Theorem 1).

## Implementation notes

* Distributions are `Measure`s on finite types with measurable singletons and channels are
  Markov `Kernel`s, as in `Statlib.Divergence.MaximalLeakage`. Values are in `ℝ≥0∞`;
  `P(x) / Q(x)` uses the conventions `p / 0 = ∞` for `p ≠ 0` and `0 / 0 = 0`, so that
  `expRenyiDivInf P Q` is the maximum over the support of `P`, and is `∞` exactly when `P` is
  not absolutely continuous with respect to `Q`, as in the paper.
* The supremum over channels `P_{U|X}` ranges over all alphabets `Fin n`, which covers every
  finite alphabet up to relabelling. For a one-letter alphabet both expected gains equal `g 1`;
  if `g 1 = 0` the ratio is `0 / 0`, which `ℝ≥0∞` evaluates to `0`, and this does not change the
  supremum. On alphabets with at least two letters the denominator is nonzero
  (`maxExpGain_ne_zero`).
* A gain function is a map `g : ℝ≥0∞ → ℝ≥0∞`, of which only the values on `[0, 1]` matter. The
  hypotheses of Theorem 1 read `g 0 = 0`, `ContinuousWithinAt g (Set.Iic 1) 0` and
  `0 < ⨆ q ≤ 1, g q < ∞`; the last one also forces `g` to be finite on `[0, 1]`.
* The proof of the achievability half differs from the paper's: we spread every letter
  `x ≠ x⋆` over one common block of `m` symbols, and bound the expected gain on that block by a
  counting argument (at most `1 / δ` of the `m` symbols have probability `≥ δ`) instead of the
  upper concave envelope `g**`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {P Q : Measure α} {g : ℝ≥0∞ → ℝ≥0∞} {a : ℝ}

/-- The exponential `max_x P(x) / Q(x)` of the Rényi divergence of order `∞`, in `ℝ≥0∞`. It is
`∞` when some `x` has `P(x) ≠ 0 = Q(x)`. The supremum ranges over the atoms, so this is only
meaningful for purely atomic measures, e.g. on a finite type with measurable singletons. -/
noncomputable def expRenyiDivInf (P Q : Measure α) : ℝ≥0∞ := ⨆ x, P {x} / Q {x}

/-- The Rényi divergence of order `∞`, `D∞(P ‖ Q) = log max_x P(x) / Q(x)` (paper, Definition 1,
equation (4)), in nats, with values in `EReal`. See `expRenyiDivInf` for the conventions. -/
noncomputable def renyiDivInf (P Q : Measure α) : EReal := ENNReal.log (expRenyiDivInf P Q)

/-- The largest expected gain `sup_{P_Û} E_{U ∼ ν} g(P_Û(U))` of a guess distribution `P_Û`
for `U ∼ ν`, under the gain function `g`. -/
noncomputable def maxExpGain (g : ℝ≥0∞ → ℝ≥0∞) (ν : Measure γ) : ℝ≥0∞ :=
  ⨆ (π : Measure γ) (_ : IsProbabilityMeasure π), ∫⁻ u, g (π {u}) ∂ν

lemma le_expRenyiDivInf_mul [IsFiniteMeasure Q] (x : α) (h : expRenyiDivInf P Q ≠ ∞) :
    P {x} ≤ expRenyiDivInf P Q * Q {x} := by
  have hx : P {x} / Q {x} ≤ expRenyiDivInf P Q := le_iSup (fun x ↦ P {x} / Q {x}) x
  by_cases hQ : Q {x} = 0
  · by_contra hP
    rw [hQ, ENNReal.div_zero (fun h0 ↦ hP (by simp [h0]))] at hx
    exact h (top_le_iff.1 hx)
  · exact (ENNReal.div_le_iff hQ (measure_ne_top Q _)).1 hx

section Variational

/-! ### Theorem 1: the variational formula -/

/-- If `P ≤ c • Q` on atoms, then `∫ f d(W ∘ P) ≤ c ∫ f d(W ∘ Q)`. -/
lemma lintegral_comp_le_mul [Finite α] [MeasurableSingletonClass α] [Finite γ]
    [MeasurableSingletonClass γ] (W : Kernel α γ) (f : γ → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : ∀ x, P {x} ≤ c * Q {x}) :
    ∫⁻ u, f u ∂(W ∘ₘ P) ≤ c * ∫⁻ u, f u ∂(W ∘ₘ Q) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite γ
  simp_rw [lintegral_fintype, comp_apply_singleton, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
  calc f u * (W x {u} * P {x}) ≤ f u * (W x {u} * (c * Q {x})) := by gcongr; exact hc x
    _ = c * (f u * (W x {u} * Q {x})) := by ring

/-- **Converse half of Theorem 1** (paper, (19)–(24)): for every channel `W` and every gain
function `g`, the ratio of the largest expected gains is at most `max_x P(x) / Q(x)`. -/
lemma maxExpGain_comp_div_le [Finite α] [MeasurableSingletonClass α] [Finite γ]
    [MeasurableSingletonClass γ] [IsFiniteMeasure Q] (W : Kernel α γ) (g : ℝ≥0∞ → ℝ≥0∞) :
    maxExpGain g (W ∘ₘ P) / maxExpGain g (W ∘ₘ Q) ≤ expRenyiDivInf P Q := by
  by_cases h : expRenyiDivInf P Q = ∞
  · simp [h]
  refine ENNReal.div_le_of_le_mul' ?_
  refine iSup₂_le fun π hπ ↦ ?_
  calc ∫⁻ u, g (π {u}) ∂(W ∘ₘ P)
      ≤ expRenyiDivInf P Q * ∫⁻ u, g (π {u}) ∂(W ∘ₘ Q) :=
        lintegral_comp_le_mul W _ fun x ↦ le_expRenyiDivInf_mul x h
    _ ≤ expRenyiDivInf P Q * maxExpGain g (W ∘ₘ Q) := by
        gcongr
        exact le_iSup₂ (f := fun π (_ : IsProbabilityMeasure π) ↦ ∫⁻ u, g (π {u}) ∂(W ∘ₘ Q))
          π hπ
    _ = maxExpGain g (W ∘ₘ Q) * expRenyiDivInf P Q := mul_comm _ _

/-- Guessing `u₀` with an arbitrary probability `q` (and `u₁` otherwise) shows
`ν(u₀) · sup_{q ≤ 1} g(q) ≤ maxExpGain g ν` (paper, (29)–(30) and (44)–(45)). -/
lemma mul_iSup_le_maxExpGain [MeasurableSingletonClass γ] (ν : Measure γ) {u₀ u₁ : γ}
    (h : u₁ ≠ u₀) : ν {u₀} * ⨆ (q) (_ : q ≤ 1), g q ≤ maxExpGain g ν := by
  simp_rw [ENNReal.mul_iSup]
  refine iSup₂_le fun q hq ↦ ?_
  set π := q • Measure.dirac u₀ + (1 - q) • Measure.dirac u₁
  have hπ : IsProbabilityMeasure π := ⟨by simp [π, add_tsub_cancel_of_le hq]⟩
  have hπ0 : π {u₀} = q := by simp [π, h]
  calc ν {u₀} * g q = ∫⁻ u in {u₀}, g (π {u}) ∂ν := by rw [lintegral_singleton, hπ0, mul_comm]
    _ ≤ ∫⁻ u, g (π {u}) ∂ν := setLIntegral_le_lintegral _ _
    _ ≤ maxExpGain g ν :=
        le_iSup₂ (f := fun π (_ : IsProbabilityMeasure π) ↦ ∫⁻ u, g (π {u}) ∂ν) π hπ

/-- **The ratio in Theorem 1 is well defined** (paper, (44)–(45)): if `sup_{q ≤ 1} g(q) > 0`,
the largest expected gain of a probability measure on an alphabet with at least two letters is
nonzero. -/
lemma maxExpGain_ne_zero [Finite γ] [MeasurableSingletonClass γ] [Nontrivial γ] (ν : Measure γ)
    [IsProbabilityMeasure ν] (hG0 : ⨆ (q) (_ : q ≤ 1), g q ≠ 0) : maxExpGain g ν ≠ 0 := by
  have := Fintype.ofFinite γ
  obtain ⟨u₀, hu₀⟩ : ∃ u, ν {u} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := ν) (s := Finset.univ)
    simp [h] at this
  obtain ⟨u₁, hu₁⟩ := exists_ne u₀
  exact ((pos_iff_ne_zero.2 (mul_ne_zero hu₀ hG0)).trans_le
    (mul_iSup_le_maxExpGain ν hu₁)).ne'

/-- **Shattering bound.** If `g 0 = 0`, `g` is continuous at `0` and bounded on `[0, 1]`, then for
every `ε > 0` there is `m > 0` such that any sub-probability vector `p` on `m` symbols has total
gain `∑_j g(p_j) ≤ m ε`: at most `1 / δ` of the symbols have `p_j ≥ δ`, and the others have
`g(p_j) ≤ ε / 2`. This replaces the paper's concave-envelope bound (31)–(34). -/
lemma exists_sum_gain_le (hg0 : g 0 = 0) (hgc : ContinuousWithinAt g (Set.Iic 1) 0)
    (hG : ⨆ (q) (_ : q ≤ 1), g q ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∀ p : Fin m → ℝ≥0∞, (∀ j, p j ≤ 1) → ∑ j, p j ≤ 1 →
      ∑ j, g (p j) ≤ m * ε := by
  classical
  set G := ⨆ (q) (_ : q ≤ 1), g q
  have hε2 : ε / 2 ≠ 0 := by simp [hε]
  have hev : ∀ᶠ p in 𝓝[Set.Iic 1] 0, g p < ε / 2 := by
    have := hgc.tendsto
    rw [hg0] at this
    exact this.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε2))
  rw [eventually_nhdsWithin_iff, ENNReal.nhds_zero_basis.eventually_iff] at hev
  obtain ⟨δ, hδ, hδg⟩ := hev
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_mul_gt hε2 (b := δ⁻¹ * G)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hδ.ne') hG)
  refine ⟨m, Nat.pos_of_ne_zero fun h ↦ by simp [h] at hm, fun p hp1 hpsum ↦ ?_⟩
  set S := Finset.univ.filter fun j ↦ δ ≤ p j
  have hS : (S.card : ℝ≥0∞) * δ ≤ 1 := by
    calc (S.card : ℝ≥0∞) * δ = ∑ _j ∈ S, δ := by simp
      _ ≤ ∑ j ∈ S, p j := Finset.sum_le_sum fun j hj ↦ (Finset.mem_filter.1 hj).2
      _ ≤ ∑ j, p j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 1 := hpsum
  have hcard : (S.card : ℝ≥0∞) ≤ δ⁻¹ := ENNReal.le_inv_iff_mul_le.2 hS
  calc ∑ j, g (p j)
      = ∑ j ∈ S, g (p j) + ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ δ ≤ p j), g (p j) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ ∑ _j ∈ S, G + ∑ _j ∈ Finset.univ.filter (fun j ↦ ¬ δ ≤ p j), ε / 2 := by
        gcongr with j hj j hj
        · exact le_iSup₂ (f := fun q (_ : q ≤ 1) ↦ g q) (p j) (hp1 j)
        · exact (hδg (not_le.1 (Finset.mem_filter.1 hj).2) (hp1 j)).le
    _ ≤ δ⁻¹ * G + m * (ε / 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
    _ ≤ m * (ε / 2) + m * (ε / 2) := by gcongr
    _ = m * ε := by rw [← mul_add, ENNReal.add_halves]

/-- The **shattering channel** of the achievability proof: `x⋆` is sent to the symbol `0`, and
every other input is spread uniformly over the `m` symbols `1, …, m`. Then `P_U(0) = P(x⋆)` and
`Q_U(j) ≤ 1 / m` for `j ≠ 0` (a variant of the paper's channel (25)). -/
lemma exists_shatter_kernel [Finite α] [MeasurableSingletonClass α] [IsProbabilityMeasure Q]
    (x₀ : α) {m : ℕ} (hm : 0 < m) :
    ∃ W : Kernel α (Fin (m + 1)), IsMarkovKernel W ∧ (∀ ν : Measure α, (W ∘ₘ ν) {0} = ν {x₀}) ∧
      ∀ j : Fin m, (W ∘ₘ Q) {j.succ} ≤ (m : ℝ≥0∞)⁻¹ := by
  classical
  have := Fintype.ofFinite α
  set w : α → Fin (m + 1) → ℝ≥0∞ := fun x u ↦
    if x = x₀ then (if u = 0 then 1 else 0) else (if u = 0 then 0 else (m : ℝ≥0∞)⁻¹)
  set W : Kernel α (Fin (m + 1)) :=
    Kernel.ofFunOfCountable fun x ↦ ∑ u, w x u • Measure.dirac u
  have hW (x : α) (u : Fin (m + 1)) : W x {u} = w x u := by
    simp [W, Kernel.ofFunOfCountable, Measure.dirac_apply' _ (measurableSet_singleton u),
      Set.indicator]
  have hw_sum (x : α) : ∑ u, w x u = 1 := by
    rw [Fin.sum_univ_succ]
    by_cases hx : x = x₀
    · simp [w, hx]
    · simp only [w, hx, ite_false, ite_true, Fin.succ_ne_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hm.ne') (ENNReal.natCast_ne_top m)
  have : IsMarkovKernel W := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hW, hw_sum]⟩⟩
  refine ⟨W, this, fun ν ↦ ?_, fun j ↦ ?_⟩
  · rw [comp_apply_singleton, Finset.sum_eq_single x₀ (fun x _ hx ↦ by simp [hW, w, hx])
      (by simp)]
    simp [hW, w]
  · rw [comp_apply_singleton]
    calc ∑ x, W x {j.succ} * Q {x} ≤ ∑ x, (m : ℝ≥0∞)⁻¹ * Q {x} := by
          gcongr with x
          rw [hW]
          by_cases hx : x = x₀ <;> simp [w, hx]
      _ = (m : ℝ≥0∞)⁻¹ := by
          simp [← Finset.mul_sum, sum_measure_singleton]

/-- **Achievability half of Theorem 1** (paper, (25)–(43)): every ratio `P(x⋆) / Q(x⋆)` is at
most the supremum of the ratios of largest expected gains over channels into `Fin n`. The proof
uses the shattering channels of `exists_shatter_kernel` with more and more symbols. -/
lemma div_le_iSup_maxExpGain_div [Finite α] [MeasurableSingletonClass α]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hg0 : g 0 = 0)
    (hgc : ContinuousWithinAt g (Set.Iic 1) 0) (hG0 : ⨆ (q) (_ : q ≤ 1), g q ≠ 0)
    (hG : ⨆ (q) (_ : q ≤ 1), g q ≠ ∞) (x₀ : α) :
    P {x₀} / Q {x₀} ≤ ⨆ (n : ℕ) (W : Kernel α (Fin n)) (_ : IsMarkovKernel W),
      maxExpGain g (W ∘ₘ P) / maxExpGain g (W ∘ₘ Q) := by
  set G := ⨆ (q) (_ : q ≤ 1), g q
  have key (ε : ℝ≥0∞) (hε : ε ≠ 0) : P {x₀} * G / (Q {x₀} * G + ε) ≤
      ⨆ (n : ℕ) (W : Kernel α (Fin n)) (_ : IsMarkovKernel W),
        maxExpGain g (W ∘ₘ P) / maxExpGain g (W ∘ₘ Q) := by
    obtain ⟨m, hm, hsum⟩ := exists_sum_gain_le hg0 hgc hG hε
    obtain ⟨W, hW, hW0, hWj⟩ := exists_shatter_kernel (Q := Q) x₀ hm
    have hnum : P {x₀} * G ≤ maxExpGain g (W ∘ₘ P) := by
      have := mul_iSup_le_maxExpGain (g := g) (W ∘ₘ P) (u₀ := 0)
        (u₁ := (⟨0, hm⟩ : Fin m).succ) (Fin.succ_ne_zero _)
      rwa [hW0] at this
    have hden : maxExpGain g (W ∘ₘ Q) ≤ Q {x₀} * G + ε := by
      refine iSup₂_le fun π _ ↦ ?_
      have hπ : ∑ j : Fin m, π {j.succ} ≤ 1 :=
        calc ∑ j : Fin m, π {j.succ} ≤ π {0} + ∑ j : Fin m, π {j.succ} := le_add_self
          _ = ∑ u, π {u} := (Fin.sum_univ_succ (fun u ↦ π {u})).symm
          _ = 1 := by simp [sum_measure_singleton]
      rw [lintegral_fintype, Fin.sum_univ_succ, hW0]
      gcongr ?_ + ?_
      · rw [mul_comm]
        gcongr
        exact le_iSup₂ (f := fun q (_ : q ≤ 1) ↦ g q) _ prob_le_one
      · calc ∑ j : Fin m, g (π {j.succ}) * (W ∘ₘ Q) {j.succ}
            ≤ ∑ j : Fin m, g (π {j.succ}) * (m : ℝ≥0∞)⁻¹ := by
              gcongr with j
              exact hWj j
          _ = (∑ j : Fin m, g (π {j.succ})) * (m : ℝ≥0∞)⁻¹ := (Finset.sum_mul ..).symm
          _ ≤ (m * ε) * (m : ℝ≥0∞)⁻¹ := by
              gcongr
              exact hsum _ (fun _ ↦ prob_le_one) hπ
          _ = ε := by
              rw [mul_comm (m : ℝ≥0∞), mul_assoc,
                ENNReal.mul_inv_cancel (by exact_mod_cast hm.ne') (ENNReal.natCast_ne_top m),
                mul_one]
    calc P {x₀} * G / (Q {x₀} * G + ε)
        ≤ maxExpGain g (W ∘ₘ P) / maxExpGain g (W ∘ₘ Q) := ENNReal.div_le_div hnum hden
      _ ≤ _ := le_iSup_of_le (m + 1) <| le_iSup₂_of_le (f := fun (W : Kernel α (Fin (m + 1)))
          (_ : IsMarkovKernel W) ↦ maxExpGain g (W ∘ₘ P) / maxExpGain g (W ∘ₘ Q)) W hW le_rfl
  have hlim : Tendsto (fun k : ℕ ↦ P {x₀} * G / (Q {x₀} * G + (k : ℝ≥0∞)⁻¹)) atTop
      (𝓝 (P {x₀} * G / (Q {x₀} * G))) := by
    refine ENNReal.Tendsto.const_div ?_ (Or.inr (ENNReal.mul_ne_top (measure_ne_top _ _) hG))
    simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
  rw [← ENNReal.mul_div_mul_right _ _ hG0 hG]
  exact le_of_tendsto' hlim fun k ↦ key _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))

/-- **Theorem 1** (Kurri–Kosut–Sankar), multiplicative form. Let `P`, `Q` be probability
measures on a finite alphabet and `g` a gain function with `g 0 = 0`, `g` continuous at `0` on
`[0, 1]`, and `0 < sup_{q ≤ 1} g(q) < ∞`. Then the supremum, over all finite alphabets `Fin n`
and channels `W = P_{U|X}`, of `sup_{P_Û} E_{U ∼ P_U} g(P_Û(U)) / sup_{P_Û} E_{U ∼ Q_U} g(P_Û(U))`
equals `max_x P(x) / Q(x)`. -/
theorem iSup_maxExpGain_div_eq [Finite α] [MeasurableSingletonClass α]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hg0 : g 0 = 0)
    (hgc : ContinuousWithinAt g (Set.Iic 1) 0) (hG0 : ⨆ (q) (_ : q ≤ 1), g q ≠ 0)
    (hG : ⨆ (q) (_ : q ≤ 1), g q ≠ ∞) :
    ⨆ (n : ℕ) (W : Kernel α (Fin n)) (_ : IsMarkovKernel W),
      maxExpGain g (W ∘ₘ P) / maxExpGain g (W ∘ₘ Q) = expRenyiDivInf P Q :=
  le_antisymm (iSup_le fun _ ↦ iSup₂_le fun W _ ↦ maxExpGain_comp_div_le W g)
    (iSup_le (div_le_iSup_maxExpGain_div hg0 hgc hG0 hG))

/-- **Theorem 1** (Kurri–Kosut–Sankar), equation (5): under the hypotheses of
`iSup_maxExpGain_div_eq`,
`D∞(P ‖ Q) = sup_{P_{U|X}} log (sup_{P_Û} E_{P_U} g(P_Û(U)) / sup_{P_Û} E_{Q_U} g(P_Û(U)))`. -/
theorem iSup_log_maxExpGain_div_eq [Finite α] [MeasurableSingletonClass α]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hg0 : g 0 = 0)
    (hgc : ContinuousWithinAt g (Set.Iic 1) 0) (hG0 : ⨆ (q) (_ : q ≤ 1), g q ≠ 0)
    (hG : ⨆ (q) (_ : q ≤ 1), g q ≠ ∞) :
    ⨆ (n : ℕ) (W : Kernel α (Fin n)) (_ : IsMarkovKernel W),
      ENNReal.log (maxExpGain g (W ∘ₘ P) / maxExpGain g (W ∘ₘ Q)) = renyiDivInf P Q := by
  rw [renyiDivInf, ← iSup_maxExpGain_div_eq hg0 hgc hG0 hG]
  simp only [← ENNReal.logOrderIso_apply, OrderIso.map_iSup]

/-! ### Proposition 1: the variational formula over test functions -/

/-- **Proposition 1**, equation (10), multiplicative form: the supremum of
`E_P[f] / E_Q[f]` over functions `f : X → [0, ∞)` is `max_x P(x) / Q(x)`. -/
theorem iSup_lintegral_div_eq [Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure Q] :
    ⨆ f : α → ℝ≥0, (∫⁻ x, f x ∂P) / (∫⁻ x, f x ∂Q) = expRenyiDivInf P Q := by
  classical
  have := Fintype.ofFinite α
  refine le_antisymm (iSup_le fun f ↦ ?_) (iSup_le fun x₀ ↦ ?_)
  · by_cases h : expRenyiDivInf P Q = ∞
    · simp [h]
    refine ENNReal.div_le_of_le_mul' ?_
    calc ∫⁻ x, (f x : ℝ≥0∞) ∂P = ∑ x, (f x : ℝ≥0∞) * P {x} := lintegral_fintype _
      _ ≤ ∑ x, (f x : ℝ≥0∞) * (expRenyiDivInf P Q * Q {x}) := by
          gcongr with x
          exact le_expRenyiDivInf_mul x h
      _ = (∫⁻ x, (f x : ℝ≥0∞) ∂Q) * expRenyiDivInf P Q := by
          rw [lintegral_fintype, Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ ↦ by ring
  · refine le_iSup_of_le (fun x ↦ if x = x₀ then 1 else 0) (le_of_eq ?_)
    simp [lintegral_fintype, apply_ite]

/-- **Proposition 1**, equation (10):
`D∞(P ‖ Q) = sup_{f : X → [0, ∞)} log (E_P[f] / E_Q[f])`. -/
theorem iSup_log_lintegral_div_eq [Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure Q] :
    ⨆ f : α → ℝ≥0, ENNReal.log ((∫⁻ x, f x ∂P) / (∫⁻ x, f x ∂Q)) = renyiDivInf P Q := by
  rw [renyiDivInf, ← iSup_lintegral_div_eq]
  simp only [← ENNReal.logOrderIso_apply, OrderIso.map_iSup]

end Variational

section AlphaGain

/-! ### Corollary 1: the `α`-loss gain -/

/-- The `α`-norm `(∑_u ν(u) ^ a) ^ (1 / a)` of the masses of `ν`. -/
noncomputable def alphaNorm [Fintype γ] (a : ℝ) (ν : Measure γ) : ℝ≥0∞ :=
  (∑ u, ν {u} ^ a) ^ (1 / a)

/-- The guessing problem for the `α`-loss gain `t ↦ t ^ ((a - 1) / a)` has the closed form
`sup_{P_Û} E_{U ∼ ν} P_Û(U) ^ ((a - 1) / a) = (∑_u ν(u) ^ a) ^ (1 / a)` for `a > 1`
(Liao–Kosut–Sankar–Calmon, *Tunable measures for information leakage*, Lemma 1, quoted in the
paper before Corollary 1). The bound is Hölder's inequality, attained at `P_Û(u) ∝ ν(u) ^ a`. -/
lemma iSup_lintegral_rpow_eq [Fintype γ] [MeasurableSingletonClass γ] (ν : Measure γ)
    [IsFiniteMeasure ν] (ha : 1 < a) :
    ⨆ (π : Measure γ) (_ : IsProbabilityMeasure π), ∫⁻ u, π {u} ^ ((a - 1) / a) ∂ν =
      alphaNorm a ν := by
  classical
  have ha0 : 0 < a := one_pos.trans ha
  set s := (a - 1) / a with hs_def
  have hs0 : 0 ≤ s := div_nonneg (by linarith) ha0.le
  have hconj : a.HolderConjugate (a / (a - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent ha).2 rfl
  have hsq : s * (a / (a - 1)) = 1 := by
    rw [hs_def]
    field_simp [show a - 1 ≠ 0 by linarith]
  refine le_antisymm (iSup₂_le fun π _ ↦ ?_) ?_
  · calc ∫⁻ u, π {u} ^ s ∂ν = ∑ u, ν {u} * π {u} ^ s := by
          rw [lintegral_fintype]
          simp_rw [mul_comm]
      _ ≤ (∑ u, ν {u} ^ a) ^ (1 / a) *
            (∑ u, (π {u} ^ s) ^ (a / (a - 1))) ^ (1 / (a / (a - 1))) :=
          ENNReal.inner_le_Lp_mul_Lq _ _ _ hconj
      _ = alphaNorm a ν := by
          simp_rw [← ENNReal.rpow_mul, hsq, ENNReal.rpow_one, sum_measure_singleton]
          simp [alphaNorm]
  · set S := ∑ u, ν {u} ^ a
    by_cases hS : S = 0
    · rw [alphaNorm, show (∑ u, ν {u} ^ a) = 0 from hS,
        ENNReal.zero_rpow_of_pos (one_div_pos.2 ha0)]
      exact zero_le
    have hS_top : S ≠ ∞ := ENNReal.sum_ne_top.2 fun u _ ↦
      ENNReal.rpow_ne_top_of_nonneg ha0.le (measure_ne_top ν _)
    set π : Measure γ := ∑ u, (ν {u} ^ a / S) • Measure.dirac u
    have hπ (u : γ) : π {u} = ν {u} ^ a / S := by
      simp [π, Measure.dirac_apply' _ (measurableSet_singleton u), Set.indicator]
    have hπ1 : IsProbabilityMeasure π := ⟨by
      rw [← Finset.coe_univ, ← sum_measure_singleton, Finset.sum_congr rfl fun u _ ↦ hπ u,
        ← ENNReal.sum_div]
      exact ENNReal.div_self hS hS_top⟩
    refine le_iSup₂_of_le (f := fun (π : Measure γ) (_ : IsProbabilityMeasure π) ↦
      ∫⁻ u, π {u} ^ s ∂ν) π hπ1 (le_of_eq ?_)
    have hpow (x : ℝ≥0∞) : x ^ (a * s) * x = x ^ a := by
      conv_rhs => rw [show a = a * s + 1 by rw [hs_def]; field_simp; ring]
      rw [ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg ha0.le hs0) zero_le_one, ENNReal.rpow_one]
    calc alphaNorm a ν = S ^ (1 - s) := by
          rw [alphaNorm]
          congr 1
          rw [hs_def]
          field_simp
          ring
      _ = S / S ^ s := by rw [ENNReal.rpow_sub _ _ hS hS_top, ENNReal.rpow_one]
      _ = ∑ u, ν {u} ^ (a * s) * ν {u} / S ^ s := by
          rw [Finset.sum_congr rfl fun u _ ↦ by rw [hpow], ENNReal.sum_div]
      _ = ∫⁻ u, π {u} ^ s ∂ν := by
          rw [lintegral_fintype]
          refine Finset.sum_congr rfl fun u _ ↦ ?_
          rw [hπ, ENNReal.div_rpow_of_nonneg _ _ hs0, ← ENNReal.rpow_mul,
            ENNReal.mul_div_right_comm]

/-- The largest expected gain for the `α`-loss gain `g_α(t) = α / (α - 1) · t ^ ((α - 1) / α)`
is `α / (α - 1) · (∑_u ν(u) ^ α) ^ (1 / α)`. -/
lemma maxExpGain_alphaGain [Fintype γ] [MeasurableSingletonClass γ] (ν : Measure γ)
    [IsFiniteMeasure ν] (ha : 1 < a) :
    maxExpGain (fun t ↦ ENNReal.ofReal (a / (a - 1)) * t ^ ((a - 1) / a)) ν =
      ENNReal.ofReal (a / (a - 1)) * alphaNorm a ν := by
  rw [← iSup_lintegral_rpow_eq ν ha, maxExpGain, ENNReal.mul_iSup]
  refine iSup_congr fun π ↦ ?_
  rw [ENNReal.mul_iSup]
  exact iSup_congr fun _ ↦ lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Corollary 1** (Kurri–Kosut–Sankar), multiplicative form: for `α > 1`, the supremum over
channels `W = P_{U|X}` of `‖P_U‖_α / ‖Q_U‖_α` is `max_x P(x) / Q(x)`. It is Theorem 1 for the
gain function `g_α(t) = α / (α - 1) · t ^ ((α - 1) / α)`. -/
theorem iSup_alphaNorm_div_eq [Finite α] [MeasurableSingletonClass α]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ha : 1 < a) :
    ⨆ (n : ℕ) (W : Kernel α (Fin n)) (_ : IsMarkovKernel W),
      alphaNorm a (W ∘ₘ P) / alphaNorm a (W ∘ₘ Q) = expRenyiDivInf P Q := by
  set c := ENNReal.ofReal (a / (a - 1))
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (div_pos (by linarith) (by linarith))).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hs : 0 < (a - 1) / a := div_pos (by linarith) (by linarith)
  set g : ℝ≥0∞ → ℝ≥0∞ := fun t ↦ c * t ^ ((a - 1) / a)
  have hg0 : g 0 = 0 := by simp [g, ENNReal.zero_rpow_of_pos hs]
  have hgc : ContinuousWithinAt g (Set.Iic 1) 0 :=
    ((ENNReal.continuous_const_mul hct).comp ENNReal.continuous_rpow_const).continuousWithinAt
  have hG : ⨆ (q) (_ : q ≤ 1), g q = c :=
    le_antisymm (iSup₂_le fun q hq ↦ mul_le_of_le_one_right' (ENNReal.rpow_le_one hq hs.le))
      (le_iSup₂_of_le (f := fun q (_ : q ≤ 1) ↦ g q) 1 le_rfl (by simp [g]))
  rw [← iSup_maxExpGain_div_eq (g := g) hg0 hgc (hG ▸ hc0) (hG ▸ hct)]
  refine iSup_congr fun n ↦ iSup_congr fun W ↦ iSup_congr fun hW ↦ ?_
  rw [maxExpGain_alphaGain _ ha, maxExpGain_alphaGain _ ha, ENNReal.mul_div_mul_left _ _ hc0 hct]

/-- **Corollary 1** (Kurri–Kosut–Sankar), equation (6): for `α > 1`,
`D∞(P ‖ Q) = sup_{P_{U|X}} log ((∑_u P_U(u) ^ α) ^ (1 / α) / (∑_u Q_U(u) ^ α) ^ (1 / α))`. -/
theorem iSup_log_alphaNorm_div_eq [Finite α] [MeasurableSingletonClass α]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ha : 1 < a) :
    ⨆ (n : ℕ) (W : Kernel α (Fin n)) (_ : IsMarkovKernel W),
      ENNReal.log (alphaNorm a (W ∘ₘ P) / alphaNorm a (W ∘ₘ Q)) = renyiDivInf P Q := by
  rw [renyiDivInf, ← iSup_alphaNorm_div_eq ha]
  simp only [← ENNReal.logOrderIso_apply, OrderIso.map_iSup]

end AlphaGain

section Leakage

/-! ### Theorems 2 and 3: two variants of maximal `α`-leakage

The input `X ∼ μ` is sent through the channel `κ = P_{Y|X}`; a randomized function `U` of `X` is
given by a channel `ρ = P_{U|X}`, so that `U - X - Y` is a Markov chain, `P_U = ρ ∘ μ` and
`P_{U|Y=y} = ρ ∘ P_{X|Y=y}`. -/

variable {μ : Measure α} {κ : Kernel α β}

/-- The conditional law `P_{X|Y=y}(x) = P_{Y|X}(y | x) P_X(x) / P_Y(y)` of the input `X ∼ μ`
given the output `y` of the channel `κ`. It is a probability measure when `P_Y(y) ≠ 0`
(`isProbabilityMeasure_condInput`) and is only used for such `y`. -/
noncomputable def condInput (μ : Measure α) (κ : Kernel α β) (y : β) : Measure α :=
  ((κ ∘ₘ μ) {y})⁻¹ • μ.withDensity fun x ↦ κ x {y}

lemma condInput_singleton [MeasurableSingletonClass α] (y : β) (x : α) :
    condInput μ κ y {x} = ((κ ∘ₘ μ) {y})⁻¹ * (κ x {y} * μ {x}) := by
  rw [condInput, smul_apply, withDensity_apply _ (measurableSet_singleton x),
    lintegral_singleton, smul_eq_mul]

lemma isProbabilityMeasure_condInput [Finite α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [IsFiniteMeasure μ] [IsMarkovKernel κ] {y : β}
    (hy : (κ ∘ₘ μ) {y} ≠ 0) : IsProbabilityMeasure (condInput μ κ y) := ⟨by
  have := Fintype.ofFinite α
  rw [← Finset.coe_univ, ← sum_measure_singleton]
  simp_rw [condInput_singleton, ← Finset.mul_sum, ← comp_apply_singleton]
  exact ENNReal.inv_mul_cancel hy (measure_ne_top _ _)⟩

/-- `max_x P_{X|Y}(x | y) / P_X(x) = max_{x ∈ supp P_X} P_{Y|X}(y | x) / P_Y(y)` (Bayes' rule,
paper (47)–(48)). -/
lemma expRenyiDivInf_condInput [MeasurableSingletonClass α] [IsFiniteMeasure μ] (y : β) :
    expRenyiDivInf (condInput μ κ y) μ = ((κ ∘ₘ μ) {y})⁻¹ * ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} := by
  simp_rw [ENNReal.mul_iSup, expRenyiDivInf]
  refine iSup_congr fun x ↦ ?_
  by_cases hx : μ {x} = 0
  · simp [hx, condInput_singleton]
  · rw [iSup_pos hx, condInput_singleton, ← mul_assoc,
      ENNReal.mul_div_cancel_right hx (measure_ne_top _ _)]

/-- Corollary 1 applied to `P_{X|Y=y}` and `P_X`: for `α > 1` and `P_Y(y) ≠ 0`, the supremum
over `U - X - Y` of `‖P_{U|Y=y}‖_α / ‖P_U‖_α` is `max_x P_{X|Y}(x | y) / P_X(x)`. -/
lemma iSup_alphaNorm_condInput_div_eq [Finite α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [IsProbabilityMeasure μ] [IsMarkovKernel κ] (ha : 1 < a)
    {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ),
      alphaNorm a (ρ ∘ₘ condInput μ κ y) / alphaNorm a (ρ ∘ₘ μ) =
      expRenyiDivInf (condInput μ κ y) μ := by
  have := isProbabilityMeasure_condInput hy
  exact iSup_alphaNorm_div_eq ha

lemma iSup_kernel_eq_zero [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {y : β} (hy : (κ ∘ₘ μ) {y} = 0) : ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} = 0 := by
  have := Fintype.ofFinite α
  rw [comp_apply_singleton, Finset.sum_eq_zero_iff] at hy
  refine le_antisymm (iSup₂_le fun x hx ↦ ?_) zero_le
  exact ((mul_eq_zero.1 (hy x (Finset.mem_univ x))).resolve_right hx).le

open Classical in
/-- The sum `∑_{y ∈ supp P_Y} P_Y(y) sup_{U - X - Y} ‖P_{U|Y=y}‖_α / ‖P_U‖_α` whose logarithm,
scaled by `α / (α - 1)`, is the opportunistic maximal `α`-leakage `oppMaxAlphaLeakage`. -/
noncomputable def oppMaxAlphaLeakageSum [Fintype β] (a : ℝ) (μ : Measure α) (κ : Kernel α β) :
    ℝ≥0∞ :=
  ∑ y with (κ ∘ₘ μ) {y} ≠ 0, (κ ∘ₘ μ) {y} *
    ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ),
      alphaNorm a (ρ ∘ₘ condInput μ κ y) / alphaNorm a (ρ ∘ₘ μ)

/-- The **opportunistic maximal `α`-leakage** `L̃_α^max(X → Y)` (paper, Definition 4, (15)):
`α / (α - 1) · log ∑_{y ∈ supp P_Y} P_Y(y) sup_{U - X - Y} ‖P_{U|Y=y}‖_α / ‖P_U‖_α`,
the supremum ranging over all channels `P_{U|X}` into the alphabets `Fin n`. It is meant for
`α ∈ (1, ∞)`. -/
noncomputable def oppMaxAlphaLeakage [Fintype β] (a : ℝ) (μ : Measure α) (κ : Kernel α β) : ℝ :=
  a / (a - 1) * Real.log (oppMaxAlphaLeakageSum a μ κ).toReal

/-- **Theorem 2** (Kurri–Kosut–Sankar), multiplicative form: for `α > 1`,
`∑_{y ∈ supp P_Y} P_Y(y) sup_{U - X - Y} ‖P_{U|Y=y}‖_α / ‖P_U‖_α` equals
`∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`, i.e. `maxLeakageSum μ κ`. -/
theorem oppMaxAlphaLeakageSum_eq_maxLeakageSum [Finite α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSingletonClass β] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (ha : 1 < a) : oppMaxAlphaLeakageSum a μ κ = maxLeakageSum μ κ := by
  classical
  rw [oppMaxAlphaLeakageSum, maxLeakageSum]
  rw [← Finset.sum_filter_of_ne (p := fun y ↦ (κ ∘ₘ μ) {y} ≠ 0)
    fun y _ h hy ↦ h (iSup_kernel_eq_zero hy)]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hy : (κ ∘ₘ μ) {y} ≠ 0 := (Finset.mem_filter.1 hy).2
  rw [iSup_alphaNorm_condInput_div_eq ha hy, expRenyiDivInf_condInput, ← mul_assoc,
    ENNReal.mul_inv_cancel hy (measure_ne_top _ _), one_mul]

/-- **Theorem 2** (Kurri–Kosut–Sankar), equation (17): for `α > 1`, the opportunistic maximal
`α`-leakage is `α / (α - 1) · I∞ˢ(X; Y)`, where the Sibson mutual information of order `∞`,
`I∞ˢ(X; Y) = log ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)` (paper, (12)), is the maximal leakage
`maxLeakage μ κ`. -/
theorem oppMaxAlphaLeakage_eq [Finite α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSingletonClass β] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (ha : 1 < a) : oppMaxAlphaLeakage a μ κ = a / (a - 1) * maxLeakage μ κ := by
  rw [oppMaxAlphaLeakage, oppMaxAlphaLeakageSum_eq_maxLeakageSum ha, maxLeakage]

/-- The **maximal realizable `α`-leakage** `L_α^{r-max}(X → Y)` (paper, Definition 5, (16)):
`sup_{U - X - Y} α / (α - 1) · log max_{y ∈ supp P_Y} ‖P_{U|Y=y}‖_α / ‖P_U‖_α`,
the supremum ranging over all channels `P_{U|X}` into the alphabets `Fin n`. It is meant for
`α ∈ (1, ∞)`, and takes values in `EReal`. -/
noncomputable def realMaxAlphaLeakage (a : ℝ) (μ : Measure α) (κ : Kernel α β) : EReal :=
  ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ), ((a / (a - 1) : ℝ) : EReal) *
    ENNReal.log (⨆ (y) (_ : (κ ∘ₘ μ) {y} ≠ 0),
      alphaNorm a (ρ ∘ₘ condInput μ κ y) / alphaNorm a (ρ ∘ₘ μ))

lemma iSup_coe_mul_log {ι : Sort*} {c : ℝ} (hc : 0 < c) (f : ι → ℝ≥0∞) :
    ⨆ i, (c : EReal) * ENNReal.log (f i) = c * ENNReal.log (⨆ i, f i) := by
  simp_rw [← ENNReal.log_rpow, ENNReal.iSup_rpow_of_pos hc, ← ENNReal.logOrderIso_apply,
    OrderIso.map_iSup]

lemma compProd_singleton [MeasurableSingletonClass α] [MeasurableSingletonClass β] [SFinite μ]
    [IsSFiniteKernel κ] (x : α) (y : β) : (μ ⊗ₘ κ) {(x, y)} = κ x {y} * μ {x} := by
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod (measurableSet_singleton x)
    (measurableSet_singleton y), lintegral_singleton]

/-- `max_{y ∈ supp P_Y} max_x P_{X|Y}(x | y) / P_X(x) = max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y))`
(paper, (52)–(53)). -/
lemma iSup_expRenyiDivInf_condInput [Finite α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    ⨆ (y) (_ : (κ ∘ₘ μ) {y} ≠ 0), expRenyiDivInf (condInput μ κ y) μ =
      expRenyiDivInf (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ)) := by
  have := Fintype.ofFinite α
  rw [expRenyiDivInf, iSup_prod, iSup_comm]
  refine iSup_congr fun y ↦ ?_
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · have h0 (x : α) : κ x {y} * μ {x} = 0 := by
      rw [comp_apply_singleton, Finset.sum_eq_zero_iff] at hy
      exact hy x (Finset.mem_univ x)
    simp [hy, compProd_singleton, h0]
  rw [iSup_pos hy, expRenyiDivInf]
  refine iSup_congr fun x ↦ ?_
  rw [condInput_singleton, compProd_singleton, ← Set.singleton_prod_singleton,
    Measure.prod_prod, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (measure_ne_top _ _))]
  ring

-- `[Finite β]` is not used in the proof: it keeps the statement in the finite-alphabet setting,
-- where `renyiDivInf` (a supremum over singletons) is the max-divergence.
/-- **Theorem 3** (Kurri–Kosut–Sankar), equation (18): for `α > 1`, the maximal realizable
`α`-leakage is `α / (α - 1) · D∞(P_XY ‖ P_X × P_Y)`, with `P_XY = μ ⊗ₘ κ` and
`P_X × P_Y = μ.prod (κ ∘ₘ μ)`. -/
@[nolint unusedArguments]
theorem realMaxAlphaLeakage_eq [Finite α] [MeasurableSingletonClass α] [Finite β]
    [MeasurableSingletonClass β] [IsProbabilityMeasure μ] [IsMarkovKernel κ] (ha : 1 < a) :
    realMaxAlphaLeakage a μ κ =
      ((a / (a - 1) : ℝ) : EReal) * renyiDivInf (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ)) := by
  have hc : 0 < a / (a - 1) := div_pos (by linarith) (by linarith)
  set R : (n : ℕ) → Kernel α (Fin n) → β → ℝ≥0∞ := fun n ρ y ↦
    alphaNorm a (ρ ∘ₘ condInput μ κ y) / alphaNorm a (ρ ∘ₘ μ)
  have hsup : ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ),
      ⨆ (y) (_ : (κ ∘ₘ μ) {y} ≠ 0), R n ρ y = expRenyiDivInf (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ)) := by
    rw [← iSup_expRenyiDivInf_condInput]
    refine le_antisymm (iSup_le fun n ↦ iSup₂_le fun ρ hρ ↦ iSup₂_le fun y hy ↦ ?_)
      (iSup₂_le fun y hy ↦ ?_)
    · refine le_iSup₂_of_le (f := fun y (_ : (κ ∘ₘ μ) {y} ≠ 0) ↦
        expRenyiDivInf (condInput μ κ y) μ) y hy ?_
      rw [← iSup_alphaNorm_condInput_div_eq ha hy]
      exact le_iSup_of_le n <| le_iSup₂_of_le (f := fun (ρ : Kernel α (Fin n))
        (_ : IsMarkovKernel ρ) ↦ R n ρ y) ρ hρ le_rfl
    · rw [← iSup_alphaNorm_condInput_div_eq ha hy]
      refine iSup_le fun n ↦ iSup₂_le fun ρ hρ ↦ ?_
      exact le_iSup_of_le n <| le_iSup₂_of_le (f := fun (ρ : Kernel α (Fin n))
        (_ : IsMarkovKernel ρ) ↦ ⨆ (y) (_ : (κ ∘ₘ μ) {y} ≠ 0), R n ρ y) ρ hρ <|
          le_iSup₂_of_le (f := fun y (_ : (κ ∘ₘ μ) {y} ≠ 0) ↦ R n ρ y) y hy le_rfl
  rw [renyiDivInf, ← hsup, realMaxAlphaLeakage]
  simp_rw [iSup_coe_mul_log hc]
  rfl

end Leakage

end InformationTheory
