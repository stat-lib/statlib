/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Maximal leakage on finite output alphabets

Issa, Wagner and Kamath define the maximal leakage from `X` to `Y` operationally, as the largest
multiplicative gain an adversary observing `Y` gets in guessing any (randomized) function of `X`.
For finite alphabets they show (Theorem 1 of *An operational approach to information leakage*,
IEEE Trans. Inf. Theory 66(3), 2020) that it equals
`L(X → Y) = log ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`.

This file takes that closed form as the definition, for an input law `μ` and a channel given by a
kernel `κ : Kernel α β` with finite output alphabet `β`. Logarithms are natural (nats), as in
Mathlib's `klDiv`.

**Scope.** The supremum ranges over the atoms of `μ`, so the definition is only meaningful when
`μ` is purely atomic, e.g. when `α` is countable with measurable singletons. For an atomless `μ`
it is `0` and does *not* equal the operational maximal leakage. The lemmas below that need an
atom take it as an explicit hypothesis.

## Main definitions

* `maxLeakageSum μ κ`: the sum `∑_y ⨆_{x : μ {x} ≠ 0} κ x {y}`, in `ℝ≥0∞`.
* `maxLeakage μ κ`: its logarithm, the maximal leakage, in `ℝ`.

## Main statements

* `one_le_maxLeakageSum`, `maxLeakage_nonneg`: maximal leakage is nonnegative.
* `maxLeakageSum_le_card`, `maxLeakage_le_log_card`: `L(X → Y) ≤ log |Y|`.
* `maxLeakageSum_le_card_support`: `L(X → Y) ≤ log |supp X|`, multiplicative form.
* `maxLeakageSum_comp_le`, `maxLeakage_comp_le`: **data processing** — post-processing the output
  through another channel `η` cannot increase maximal leakage.

## See also

* `Statlib.Divergence.MaximalLeakage.Operational`: the operational definition and Theorem 1 of
  Issa–Wagner–Kamath, which shows that this closed form equals it.
* `Statlib.Divergence.MaximalLeakage.Properties`: data processing for pre-processing,
  `L(X → Y) ≤ log |supp Y|`, zero leakage iff independence, composition and additivity.
* `Statlib.Divergence.MaximalLeakage.MutualInfo`: `I(X; Y) ≤ L(X → Y)`.

## TODO

* Maximal leakage as Sibson mutual information of order `∞`, and beyond finite alphabets.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β}

/-- The sum `∑_y ⨆_{x ∈ supp μ} κ x {y}` whose logarithm is the maximal leakage `maxLeakage μ κ`.
The supremum ranges over the atoms of `μ`, so this is only meaningful when `μ` is purely atomic,
e.g. for a countable input alphabet with measurable singletons. -/
noncomputable def maxLeakageSum [Fintype β] (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  ∑ y, ⨆ (x) (_ : μ {x} ≠ 0), κ x {y}

/-- The maximal leakage `L(X → Y)` from an input `X ∼ μ` to the output `Y` of the channel `κ`,
in nats, for a finite output alphabet and a purely atomic `μ` (see `maxLeakageSum`). -/
noncomputable def maxLeakage [Fintype β] (μ : Measure α) (κ : Kernel α β) : ℝ :=
  Real.log (maxLeakageSum μ κ).toReal

section Bounds

variable [Fintype β] [MeasurableSingletonClass β] [IsMarkovKernel κ]

omit [MeasurableSingletonClass β] in
lemma maxLeakageSum_le_card : maxLeakageSum μ κ ≤ Fintype.card β := by
  calc maxLeakageSum μ κ ≤ ∑ _y : β, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x _ ↦ prob_le_one
    _ = Fintype.card β := by simp

omit [MeasurableSingletonClass β] in
lemma maxLeakageSum_ne_top : maxLeakageSum μ κ ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) maxLeakageSum_le_card

/-- Any atom `x` of `μ` already contributes the full mass `∑_y κ x {y} = 1`. -/
lemma one_le_maxLeakageSum {x : α} (hx : μ {x} ≠ 0) : 1 ≤ maxLeakageSum μ κ := by
  calc (1 : ℝ≥0∞) = ∑ y, κ x {y} := by simp [sum_measure_singleton (μ := κ x)]
    _ ≤ maxLeakageSum μ κ :=
        Finset.sum_le_sum fun y _ ↦ le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y}) x hx

lemma one_le_toReal_maxLeakageSum {x : α} (hx : μ {x} ≠ 0) :
    1 ≤ (maxLeakageSum μ κ).toReal := by
  simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top maxLeakageSum_ne_top).2
    (one_le_maxLeakageSum hx)

lemma maxLeakage_nonneg {x : α} (hx : μ {x} ≠ 0) : 0 ≤ maxLeakage μ κ :=
  Real.log_nonneg (one_le_toReal_maxLeakageSum hx)

/-- Maximal leakage is at most the logarithm of the output alphabet size. -/
lemma maxLeakage_le_log_card {x : α} (hx : μ {x} ≠ 0) :
    maxLeakage μ κ ≤ Real.log (Fintype.card β) := by
  refine Real.log_le_log (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx]) ?_
  simpa using (ENNReal.toReal_le_toReal maxLeakageSum_ne_top (ENNReal.natCast_ne_top _)).2
    maxLeakageSum_le_card

/-- Multiplicative form of `L(X → Y) ≤ log |supp X|`. -/
lemma maxLeakageSum_le_card_support [Fintype α] [DecidablePred fun x : α ↦ μ {x} ≠ 0] :
    maxLeakageSum μ κ ≤ (Finset.univ.filter fun x : α ↦ μ {x} ≠ 0).card := by
  set S := Finset.univ.filter fun x : α ↦ μ {x} ≠ 0
  calc maxLeakageSum μ κ ≤ ∑ y, ∑ x ∈ S, κ x {y} :=
        Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x hx ↦
          Finset.single_le_sum (f := fun x ↦ κ x {y}) (fun _ _ ↦ zero_le) (by simpa [S] using hx)
    _ = ∑ x ∈ S, ∑ y, κ x {y} := Finset.sum_comm
    _ = S.card := by simp [sum_measure_singleton]

end Bounds

section DataProcessing

variable [Fintype β] [MeasurableSingletonClass β] [Fintype γ] [MeasurableSingletonClass γ]

/-- **Data processing** for maximal leakage, multiplicative form: post-processing the channel
output by a Markov kernel `η` cannot increase `∑_y max_x κ x {y}`. -/
lemma maxLeakageSum_comp_le (η : Kernel β γ) [IsMarkovKernel η] :
    maxLeakageSum μ (η ∘ₖ κ) ≤ maxLeakageSum μ κ := by
  have h_comp (x : α) (z : γ) : (η ∘ₖ κ) x {z} = ∑ y, η y {z} * κ x {y} := by
    rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton z), lintegral_fintype]
  calc maxLeakageSum μ (η ∘ₖ κ)
      ≤ ∑ z, ∑ y, η y {z} * ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} := by
        refine Finset.sum_le_sum fun z _ ↦ iSup₂_le fun x hx ↦ ?_
        rw [h_comp]
        exact Finset.sum_le_sum fun y _ ↦
          mul_le_mul_right (le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y}) x hx) _
    _ = ∑ y, (∑ z, η y {z}) * ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = maxLeakageSum μ κ := by simp [maxLeakageSum, sum_measure_singleton]

/-- **Data processing** for maximal leakage: for a Markov chain `X - Y - Z` obtained by
post-processing `Y` through `η`, `L(X → Z) ≤ L(X → Y)`. -/
lemma maxLeakage_comp_le [IsMarkovKernel κ] (η : Kernel β γ) [IsMarkovKernel η] {x : α}
    (hx : μ {x} ≠ 0) :
    maxLeakage μ (η ∘ₖ κ) ≤ maxLeakage μ κ := by
  refine Real.log_le_log (by linarith [one_le_toReal_maxLeakageSum (κ := η ∘ₖ κ) hx]) ?_
  exact (ENNReal.toReal_le_toReal maxLeakageSum_ne_top maxLeakageSum_ne_top).2
    (maxLeakageSum_comp_le η)

end DataProcessing

end InformationTheory
