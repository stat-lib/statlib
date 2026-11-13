/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Differential privacy: basic theory

This file develops the basic theory of `(ε, δ)`-differential privacy following C. Dwork and
A. Roth, *The Algorithmic Foundations of Differential Privacy*, Found. Trends Theor. Comput. Sci.
9(3–4), 2014; result numbers follow that monograph. The definition is that of C. Dwork,
F. McSherry, K. Nissim and A. Smith, *Calibrating noise to sensitivity in private data analysis*,
TCC 2006 (with the `δ` of Dwork–Kenthapadi–McSherry–Mironov–Naor, Eurocrypt 2006).

A mechanism is a kernel `M : Kernel 𝒟 Y` from datasets to outputs, and `Adj` is an arbitrary
neighbouring relation on datasets (Dwork–Roth use `‖x - y‖₁ ≤ 1` on histograms). The predicate
`IsEpsDeltaDP M Adj ε δ` says `P[M(S) ∈ E] ≤ e^ε P[M(S') ∈ E] + δ` for
all `Adj S S'` and all sets `E` (Definition 2.4); pure `ε`-DP is the case `δ = 0`. Unless stated
otherwise, the output spaces are **arbitrary measurable spaces**.

`IsEpsDeltaDP` is stated with `Measure.real`, which sends `∞` to `0`, so the predicate is only
meaningful for **finite kernels** (in practice Markov kernels, as mechanisms are). The results
that use measure values assume finite kernels (basic API, post-processing) or Markov kernels
(composition); the purely order-theoretic ones (`IsEpsDeltaDP.mono`, `IsEpsDeltaDP.group`,
`IsEpsDeltaDP.comap`, …) hold for any kernel but carry content only for finite ones.

## Main definitions

* `IsEpsDeltaDP M Adj ε δ`: `(ε, δ)`-differential privacy (Definition 2.4).
* `IsEpsDP M Adj ε`: pure `ε`-DP, an abbreviation for `IsEpsDeltaDP M Adj ε 0`.
* `DP.composeFin M`: the `k`-fold composition `S ↦ (M₀(S), …, M_{k-1}(S))` of mechanisms
  `M_i : Kernel 𝒟 (R i)`, with values in `(i : Fin k) → R i`.
* `DP.ParallelAdj Adj₁ Adj₂`: neighbouring datasets made of two disjoint parts.
* `DP.AddRemoveAdj`: datasets `X, X' : Set α` of records that differ in one record.
* `IsKNeighbour Adj k`: datasets joined by a chain of `k` neighbouring (or identical) steps.

## Main statements (monograph result → Lean name)

* Basic API: `IsEpsDeltaDP.mono` (monotonicity in `ε` and `δ`), `IsEpsDeltaDP.of_le`,
  `IsEpsDeltaDP.nonneg`, `isEpsDeltaDP_iff_forall_measurableSet` (measurable events suffice),
  `isEpsDeltaDP_iff_measure_le` (`ℝ≥0∞` form), `isEpsDP_iff_le_smul` (`M(S) ≤ e^ε M(S')`),
  `isEpsDP_iff_forall_singleton` (pointwise form on countable `Y`), `isEpsDeltaDP_const`,
  `isEpsDeltaDP_of_one_le`, `IsEpsDeltaDP.comap` (change of dataset space).
* Proposition 2.1 (post-processing by an arbitrary randomized mapping): `IsEpsDeltaDP.comp`,
  deterministic case `IsEpsDeltaDP.map`.
* Theorem 2.2 (group privacy, `(ε, 0)`): `IsEpsDP.group`; the `(ε, δ)` version of footnote 1 to
  Theorem 2.2 (`(kε, k e^{(k-1)ε} δ)`): `IsEpsDeltaDP.group'`. Both derive from
  `IsEpsDeltaDP.group` (`(kε, δ ∑_{i<k} e^{iε})`, the constant that chaining gives; not in the
  book, not claimed tight). "Groups of size `k`" means datasets joined by a chain of `k`
  neighbouring steps (`IsKNeighbour Adj k`).
* Theorem 3.14 (composition of two pure-DP mechanisms): `IsEpsDP.prod`.
* Corollary 3.15 (`k` pure-DP mechanisms): `DP.isEpsDP_composeFin`.
* Theorem 3.16 (`(ε, δ)` composition): two mechanisms `IsEpsDeltaDP.prod`; `k` mechanisms
  `DP.isEpsDeltaDP_composeFin`.
* Theorem B.1 (adaptive composition), with possibly different parameters for the two mechanisms:
  `IsEpsDeltaDP.compProd`, pure case `IsEpsDP.compProd`.
* Parallel composition (F. McSherry, *Privacy integrated queries*, SIGMOD 2009, Theorem 4), for
  **two parts**: adaptive `IsEpsDP.parallel_compProd`, and for one dataset `X : Set α` split as
  `(X ∩ D, X ∩ Dᶜ)`, `IsEpsDP.parallel_compProd_inter` (via `DP.parallelAdj_inter_compl`). The
  latter is the **duplicate-free** (datasets are sets, not PINQ's multisets),
  **adjacent-dataset** (one added or removed record, not PINQ's guarantee for all pairs at a given
  symmetric-difference distance), **complementary-bipartition** version of Theorem 4.
  Non-adaptive special case `IsEpsDP.parallel`. The `(ε, δ)`
  versions `IsEpsDeltaDP.parallel_compProd` and `IsEpsDeltaDP.parallel`, giving
  `(max ε₁ ε₂, max δ₁ δ₂)`, extend PINQ, which treats pure DP only.

## Implementation notes

The `(ε, δ)` composition theorems and post-processing rest on
`DP.lintegral_le_of_forall_measure_le`: an inequality `μ(E) ≤ c ν(E) + d` on measurable events
extends to `∫ g dμ ≤ c ∫ g dν + d` for measurable `g : Y → [0, 1]`, by integrating over the
superlevel sets of `g` (layer-cake formula). This replaces both the decomposition of a randomized
mapping into deterministic ones used for Proposition 2.1 and the measure `μ` used in the proof of
Theorem B.1 (see the notes below).

## Notes on the paper

* Proof of Theorem 3.14 (Section 3.5, p. 42): in the second line of the display the second factor
  should be `Pr[M₂(x) = r₂] / Pr[M₂(y) = r₂]`, not `… = r₁`. The theorem is true
  (`IsEpsDP.prod`).
* Proof of Theorem B.1 (Appendix B, pp. 267–268): the proof integrates against `μ(ds₁)` in (B.2)
  and (B.4), which needs `μ` to be a measure, but the set function
  `μ(C₁) = (P(T₁ ∈ C₁) - e^ε P'(T₁ ∈ C₁))₊` defined there is not one in general (it is not
  additive: if `P - e^ε P'` is positive on `A` and negative on a disjoint `B`, then
  `μ(A ∪ B) < μ(A) + μ(B)`). The positive part of the Jordan decomposition of the signed measure
  `P(T₁ ∈ ·) - e^ε P'(T₁ ∈ ·)` is a measure of total mass at most `δ` satisfying (B.2), which
  repairs the argument. The theorem is true (`IsEpsDeltaDP.compProd`, proved without `μ`).
* The proof also integrates over `S₁`, the projection of `S` onto `C₁`. This is not a defect in
  the book, which works with discrete probability spaces (p. 16), where every set is measurable;
  it is only an obstacle to **generalizing** the proof to arbitrary measurable output spaces,
  where such a projection need not be measurable. Integrating over all of `C₁` avoids it.

## Not formalized

* The `k`-fold adaptive composition (Corollary B.2).
* The link between "groups of size `k`" as chains of `k` neighbouring steps (`IsKNeighbour`) and
  the book's `‖x - y‖₁ ≤ k` on histograms.
* McSherry's parallel composition for `k > 2` parts, and the bridges from the two-part set
  version to PINQ's setting: multiset datasets, and the guarantee for datasets at any
  symmetric-difference distance.
* Everything from Section 3.5.1 on (privacy loss, advanced composition, Theorem 3.20).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace InformationTheory

variable {Y Z 𝒟 : Type*} {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z}
  {m𝒟 : MeasurableSpace 𝒟}

/-! ### Pure differential privacy and the measure-level form of the definition -/

/-- **`(ε, δ)`-differential privacy** (Definition 2.4 of Dwork–Roth): for all neighbouring
`S, S'` and every event `E`, `P[M(S) ∈ E] ≤ e^ε P[M(S') ∈ E] + δ`. The inequality is required for
every set `E`; measurable events suffice (`isEpsDeltaDP_iff_forall_measurableSet`).

**Markov requirement (documented, not enforced).** `M` is an arbitrary `Kernel`, not necessarily
Markov, so this is an unrestricted algebraic extension whose privacy interpretation requires
`[IsMarkovKernel M]`: e.g. the zero kernel satisfies `IsEpsDeltaDP 0 Adj 0 0`, and for infinite
measures `Measure.real` reads `∞` as `0`. -/
def IsEpsDeltaDP (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (ε δ : ℝ) : Prop :=
  ∀ ⦃S S'⦄, Adj S S' → ∀ E : Set Y, (M S).real E ≤ exp ε * (M S').real E + δ

/-- **Pure `ε`-differential privacy** (Definition 2.4 of Dwork–Roth with `δ = 0`): for all
neighbouring `S, S'` and every event `E`, `P[M(S) ∈ E] ≤ e^ε P[M(S') ∈ E]`. -/
abbrev IsEpsDP (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (ε : ℝ) : Prop :=
  IsEpsDeltaDP M Adj ε 0

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop} {ε ε' δ δ' : ℝ}

lemma isEpsDP_iff_isEpsDeltaDP : IsEpsDP M Adj ε ↔ IsEpsDeltaDP M Adj ε 0 := Iff.rfl

lemma isEpsDP_iff : IsEpsDP M Adj ε ↔
    ∀ ⦃S S'⦄, Adj S S' → ∀ E : Set Y, (M S).real E ≤ exp ε * (M S').real E := by
  simp only [IsEpsDP, IsEpsDeltaDP, add_zero]

/-- The `δ` of an `(ε, δ)`-DP mechanism is nonnegative as soon as some pair of datasets is
neighbouring (take `E = ∅`). -/
lemma IsEpsDeltaDP.nonneg {S S' : 𝒟} (h : IsEpsDeltaDP M Adj ε δ) (hS : Adj S S') : 0 ≤ δ := by
  simpa using h hS ∅

/-- `(ε, δ)`-DP is monotone in `ε` and `δ`. -/
lemma IsEpsDeltaDP.mono (h : IsEpsDeltaDP M Adj ε δ) (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    IsEpsDeltaDP M Adj ε' δ' := fun _ _ hS E ↦ (h hS E).trans <| by gcongr

/-- `(ε, δ)`-DP is antitone in the neighbouring relation. -/
lemma IsEpsDeltaDP.of_le {Adj' : 𝒟 → 𝒟 → Prop} (h : IsEpsDeltaDP M Adj ε δ)
    (hAdj : ∀ ⦃S S'⦄, Adj' S S' → Adj S S') : IsEpsDeltaDP M Adj' ε δ :=
  fun _ _ hS ↦ h (hAdj hS)

/-- It suffices to check `(ε, δ)`-DP on measurable events: the inequality for an arbitrary set
`E` (where `(M S).real E` is an outer measure) follows from that for a common measurable hull
of `E` for `M S` and `M S'`. -/
theorem isEpsDeltaDP_iff_forall_measurableSet : IsEpsDeltaDP M Adj ε δ ↔
    ∀ ⦃S S'⦄, Adj S S' → ∀ E : Set Y, MeasurableSet E →
      (M S).real E ≤ exp ε * (M S').real E + δ := by
  refine ⟨fun h S S' hS E _ ↦ h hS E, fun h S S' hS E ↦ ?_⟩
  obtain ⟨F, -, hF, h₁, h₂⟩ := exists_measurable_superset₂ (M S) (M S') E
  simpa only [measureReal_def, h₁, h₂] using h hS F hF

namespace DP

variable {μ ν : Measure Y} {E : Set Y}

/-- The real `(ε, δ)` inequality for one event implies its `ℝ≥0∞` form. -/
lemma measure_le_of_measureReal_le [IsFiniteMeasure μ]
    (h : μ.real E ≤ exp ε * ν.real E + δ) :
    μ E ≤ ENNReal.ofReal (exp ε) * ν E + ENNReal.ofReal δ := by
  calc μ E = ENNReal.ofReal (μ.real E) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (exp ε * ν.real E + δ) := ENNReal.ofReal_le_ofReal h
    _ ≤ ENNReal.ofReal (exp ε * ν.real E) + ENNReal.ofReal δ := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (exp ε) * ν E + ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_mul (exp_pos ε).le, measureReal_def]
      gcongr
      exact ENNReal.ofReal_toReal_le

/-- The `ℝ≥0∞` form of the `(ε, δ)` inequality for one event implies its real form. -/
lemma measureReal_le_of_measure_le [IsFiniteMeasure ν] (hδ : 0 ≤ δ)
    (h : μ E ≤ ENNReal.ofReal (exp ε) * ν E + ENNReal.ofReal δ) :
    μ.real E ≤ exp ε * ν.real E + δ := by
  have hne : ENNReal.ofReal (exp ε) * ν E + ENNReal.ofReal δ ≠ ∞ := by finiteness
  calc μ.real E ≤ (ENNReal.ofReal (exp ε) * ν E + ENNReal.ofReal δ).toReal :=
        ENNReal.toReal_mono hne h
    _ = exp ε * ν.real E + δ := by
      rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (exp_pos ε).le, ENNReal.toReal_ofReal hδ, measureReal_def]

end DP

/-- An `(ε, δ)`-DP finite kernel satisfies `M(S)(E) ≤ e^ε M(S')(E) + δ` in `ℝ≥0∞`. -/
lemma IsEpsDeltaDP.measure_le [IsFiniteKernel M] (h : IsEpsDeltaDP M Adj ε δ) {S S' : 𝒟}
    (hS : Adj S S') (E : Set Y) :
    M S E ≤ ENNReal.ofReal (exp ε) * M S' E + ENNReal.ofReal δ :=
  DP.measure_le_of_measureReal_le (h hS E)

/-- For a finite kernel and `δ ≥ 0`, `(ε, δ)`-DP is equivalent to its `ℝ≥0∞` form on measurable
events. -/
theorem isEpsDeltaDP_iff_measure_le [IsFiniteKernel M] (hδ : 0 ≤ δ) :
    IsEpsDeltaDP M Adj ε δ ↔ ∀ ⦃S S'⦄, Adj S S' → ∀ E : Set Y, MeasurableSet E →
      M S E ≤ ENNReal.ofReal (exp ε) * M S' E + ENNReal.ofReal δ := by
  rw [isEpsDeltaDP_iff_forall_measurableSet]
  exact ⟨fun h S S' hS E hE ↦ DP.measure_le_of_measureReal_le (h hS E hE),
    fun h S S' hS E hE ↦ DP.measureReal_le_of_measure_le hδ (h hS E hE)⟩

/-- For a finite kernel, pure `ε`-DP says that `M(S) ≤ e^ε M(S')` as measures. -/
theorem isEpsDP_iff_le_smul [IsFiniteKernel M] :
    IsEpsDP M Adj ε ↔ ∀ ⦃S S'⦄, Adj S S' → M S ≤ ENNReal.ofReal (exp ε) • M S' := by
  simp only [isEpsDeltaDP_iff_measure_le le_rfl, ENNReal.ofReal_zero, add_zero, Measure.le_iff,
    smul_apply, smul_eq_mul]

/-- On a countable output space with measurable singletons, pure `ε`-DP of a finite kernel is
equivalent to the pointwise inequality `P[M(S) = y] ≤ e^ε P[M(S') = y]`. -/
theorem isEpsDP_iff_forall_singleton [Countable Y] [MeasurableSingletonClass Y]
    [IsFiniteKernel M] : IsEpsDP M Adj ε ↔
      ∀ ⦃S S'⦄, Adj S S' → ∀ y : Y, (M S).real {y} ≤ exp ε * (M S').real {y} := by
  refine ⟨fun h S S' hS y ↦ isEpsDP_iff.1 h hS {y}, fun h ↦ ?_⟩
  refine isEpsDP_iff_le_smul.2 fun S S' hS ↦ Measure.le_iff.2 fun E hE ↦ ?_
  have hy (y : Y) : M S {y} ≤ ENNReal.ofReal (exp ε) * M S' {y} := by
    simpa using DP.measure_le_of_measureReal_le (δ := 0) (by simpa using h hS y)
  rw [smul_apply, smul_eq_mul, ← (M S).tsum_indicator_apply_singleton E hE,
    ← (M S').tsum_indicator_apply_singleton E hE, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun y ↦ ?_
  by_cases hyE : y ∈ E <;> simp [hyE, hy]

/-- A constant mechanism (ignoring its input) with a finite output distribution is
`(ε, δ)`-DP for all `ε, δ ≥ 0`. The finiteness hypothesis is not needed by the proof; it excludes
the degenerate case of an infinite `μ`, where `Measure.real` is `0` on every set of infinite
measure. -/
@[nolint unusedArguments]
lemma isEpsDeltaDP_const (μ : Measure Y) [IsFiniteMeasure μ] (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    IsEpsDeltaDP (Kernel.const 𝒟 μ) Adj ε δ := fun _ _ _ E ↦ by
  simp only [Kernel.const_apply]
  nlinarith [one_le_exp hε, measureReal_nonneg (μ := μ) (s := E)]

/-- Every Markov kernel is `(ε, δ)`-DP when `δ ≥ 1`. -/
lemma isEpsDeltaDP_of_one_le [IsMarkovKernel M] (hδ : 1 ≤ δ) : IsEpsDeltaDP M Adj ε δ :=
  fun S S' _ E ↦ by
    nlinarith [measureReal_le_one (μ := M S) (s := E), measureReal_nonneg (μ := M S') (s := E),
      exp_pos ε]

/-! ### Post-processing -/

namespace DP

variable {μ ν : Measure Y} {c c₁ c₂ d d₁ d₂ : ℝ≥0∞}

/-- An `(ε, δ)`-type inequality `μ(E) ≤ c ν(E) + d` on all measurable events extends to all
measurable functions `g` with values in `[0, 1]`: `∫ g dμ ≤ c ∫ g dν + d`. The proof integrates
the event inequality over the superlevel sets of `g` (layer-cake formula). -/
lemma lintegral_le_of_forall_measure_le (h : ∀ E, MeasurableSet E → μ E ≤ c * ν E + d)
    {g : Y → ℝ≥0∞} (hg : Measurable g) (hg₁ : ∀ y, g y ≤ 1) :
    ∫⁻ y, g y ∂μ ≤ c * ∫⁻ y, g y ∂ν + d := by
  rw [lintegral_eq_lintegral_measure_ofReal_le μ hg.aemeasurable,
    lintegral_eq_lintegral_measure_ofReal_le ν hg.aemeasurable]
  have hmeas : Measurable fun t : ℝ ↦ ν {x | ENNReal.ofReal t ≤ g x} :=
    Antitone.measurable fun t t' htt' ↦ measure_mono fun x hx ↦
      (ENNReal.ofReal_le_ofReal htt').trans hx
  calc ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t ≤ g x}
      ≤ ∫⁻ t in Ioi 0, (c * ν {x | ENNReal.ofReal t ≤ g x} + (Iic 1).indicator (fun _ ↦ d) t) := by
        refine lintegral_mono fun t ↦ ?_
        by_cases ht : t ≤ 1
        · simpa [ht] using h _ (measurableSet_le measurable_const hg)
        · have : {x | ENNReal.ofReal t ≤ g x} = ∅ := eq_empty_iff_forall_notMem.2 fun x hx ↦
            (not_le.2 (ENNReal.one_lt_ofReal.2 (not_le.1 ht))) ((hx : _ ≤ _).trans (hg₁ x))
          simp [this]
    _ = c * (∫⁻ t in Ioi 0, ν {x | ENNReal.ofReal t ≤ g x}) + d := by
        rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Iic),
          lintegral_const_mul _ hmeas, lintegral_indicator_const measurableSet_Iic,
          Measure.restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic, Real.volume_Ioc]
        simp

/-- The integral step of the composition theorems: if `μ(E) ≤ c₁ μ'(E) + d₁` on measurable
events and `k ≤ min (1, c₂ g + d₂)` pointwise, then `∫ k dμ ≤ c₁ c₂ ∫ g dμ' + d₁ + d₂`. -/
lemma lintegral_le_mul_add [IsProbabilityMeasure μ] (h : ∀ E, MeasurableSet E → μ E ≤ c₁ * ν E + d₁)
    {k g : Y → ℝ≥0∞} (hg : Measurable g) (hk₁ : ∀ y, k y ≤ 1)
    (hk : ∀ y, k y ≤ c₂ * g y + d₂) :
    ∫⁻ y, k y ∂μ ≤ c₁ * c₂ * ∫⁻ y, g y ∂ν + (d₁ + d₂) := by
  have hpt (y : Y) : k y ≤ min 1 (c₂ * g y) + d₂ := by
    rcases le_total 1 (c₂ * g y) with h' | h'
    · rw [min_eq_left h']
      exact (hk₁ y).trans le_self_add
    · rw [min_eq_right h']
      exact hk y
  calc ∫⁻ y, k y ∂μ ≤ ∫⁻ y, (min 1 (c₂ * g y) + d₂) ∂μ := lintegral_mono hpt
    _ = ∫⁻ y, min 1 (c₂ * g y) ∂μ + d₂ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ c₁ * ∫⁻ y, min 1 (c₂ * g y) ∂ν + d₁ + d₂ := by
        gcongr
        exact lintegral_le_of_forall_measure_le h (measurable_const.min (hg.const_mul c₂))
          fun y ↦ min_le_left _ _
    _ ≤ c₁ * ∫⁻ y, c₂ * g y ∂ν + d₁ + d₂ := by
        gcongr with y
        exact min_le_right _ _
    _ = c₁ * c₂ * ∫⁻ y, g y ∂ν + (d₁ + d₂) := by
        rw [lintegral_const_mul _ hg, mul_assoc, add_assoc]

end DP

/-- **Proposition 2.1 of Dwork–Roth** (post-processing): if `M` is `(ε, δ)`-DP, then so is
`f ∘ₖ M` for every Markov kernel `f` (an arbitrary randomized mapping of the output), on
arbitrary measurable spaces. -/
theorem IsEpsDeltaDP.comp [IsFiniteKernel M] (h : IsEpsDeltaDP M Adj ε δ) (f : Kernel Y Z)
    [IsMarkovKernel f] : IsEpsDeltaDP (f ∘ₖ M) Adj ε δ := by
  rw [isEpsDeltaDP_iff_forall_measurableSet]
  intro S S' hS E hE
  refine DP.measureReal_le_of_measure_le (h.nonneg hS) ?_
  rw [Kernel.comp_apply' _ _ _ hE, Kernel.comp_apply' _ _ _ hE]
  exact DP.lintegral_le_of_forall_measure_le (fun F _ ↦ h.measure_le hS F)
    (Kernel.measurable_coe f hE) fun y ↦ prob_le_one

/-- Post-processing by a measurable function (the deterministic case of Proposition 2.1 of
Dwork–Roth). -/
theorem IsEpsDeltaDP.map [IsFiniteKernel M] (h : IsEpsDeltaDP M Adj ε δ) {φ : Y → Z}
    (hφ : Measurable φ) : IsEpsDeltaDP (M.map φ) Adj ε δ := by
  rw [← Kernel.deterministic_comp_eq_map hφ]
  exact h.comp _

/-! ### Group privacy -/

/-- `S` and `S'` are `k`-neighbours (J. Dong, A. Roth and W. J. Su, *Gaussian differential
privacy*, J. R. Stat. Soc. Ser. B 84(1), 2022, Section 2.5): they are joined by a chain
`S = S₀, S₁, …, S_k = S'` in which consecutive datasets are neighbouring or identical. -/
inductive IsKNeighbour (Adj : 𝒟 → 𝒟 → Prop) : ℕ → 𝒟 → 𝒟 → Prop
  | zero (S : 𝒟) : IsKNeighbour Adj 0 S S
  | succ {k : ℕ} {S T U : 𝒟} :
      IsKNeighbour Adj k S T → Adj T U ∨ T = U → IsKNeighbour Adj (k + 1) S U

/-- **Group privacy for `(ε, δ)`-DP, chained form**: if `M` is `(ε, δ)`-DP with `ε, δ ≥ 0`, then
for datasets joined by a chain of `k` neighbouring (or identical) steps (`IsKNeighbour Adj k`),
`P[M(S) ∈ E] ≤ e^{kε} P[M(S') ∈ E] + δ ∑_{i < k} e^{iε}`. This is the constant that chaining the
definition `k` times gives; it is sharper than the constant `k e^{(k-1)ε} δ` of footnote 1 to
Theorem 2.2 of Dwork–Roth (see `IsEpsDeltaDP.group'`), is not stated in the book, and is not
claimed to be tight. -/
theorem IsEpsDeltaDP.group (h : IsEpsDeltaDP M Adj ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (k : ℕ) :
    IsEpsDeltaDP M (IsKNeighbour Adj k) (k * ε) (δ * ∑ i ∈ Finset.range k, exp (i * ε)) := by
  intro S S' hSS' E
  induction hSS' with
  | zero S => simp
  | @succ n S T U _ hTU ih =>
    have hP := measureReal_nonneg (μ := M T) (s := E)
    have hQ := measureReal_nonneg (μ := M U) (s := E)
    have h₁ := one_le_exp hε
    have h₂ := (exp_pos (n * ε)).le
    rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul, exp_add]
    rcases hTU with hTU | rfl
    · have := h hTU E
      have : exp (n * ε) * (M T).real E ≤ exp (n * ε) * (exp ε * (M U).real E + δ) := by gcongr
      nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left h₁ (mul_nonneg h₂ hP)]

/-- **Theorem 2.2 of Dwork–Roth** (group privacy): an `ε`-DP mechanism with `ε ≥ 0` is
`kε`-DP for groups of size `k`. Here "groups of size `k`" means datasets joined by a chain of `k`
neighbouring (or identical) steps (`IsKNeighbour Adj k`); the link with the book's
`‖x - y‖₁ ≤ k` on histograms (that such `x, y` are joined by such a chain for `Adj` given by
`‖x - y‖₁ ≤ 1`) is not formalized. -/
theorem IsEpsDP.group (h : IsEpsDP M Adj ε) (hε : 0 ≤ ε) (k : ℕ) :
    IsEpsDP M (IsKNeighbour Adj k) (k * ε) := by
  simpa using IsEpsDeltaDP.group h hε le_rfl k

/-- **Group privacy for `(ε, δ)`-DP with the constant of Dwork–Roth** (footnote 1 to
Theorem 2.2, Section 2.3): an `(ε, δ)`-DP mechanism with `ε, δ ≥ 0` is
`(kε, k e^{(k-1)ε} δ)`-DP for groups of size `k`, i.e. for datasets joined by a chain of `k`
neighbouring (or identical) steps (`IsKNeighbour Adj k`; the link with `‖x - y‖₁ ≤ k` is not
formalized). -/
theorem IsEpsDeltaDP.group' (h : IsEpsDeltaDP M Adj ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (k : ℕ) :
    IsEpsDeltaDP M (IsKNeighbour Adj k) (k * ε) (k * exp ((k - 1) * ε) * δ) := by
  refine (h.group hε hδ k).mono le_rfl ?_
  have : ∑ i ∈ Finset.range k, exp (i * ε) ≤ k * exp ((k - 1) * ε) := by
    have := Finset.sum_le_card_nsmul (Finset.range k) (fun i : ℕ ↦ exp (i * ε))
      (exp ((k - 1) * ε)) fun i hi ↦ by
        have : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hi
        gcongr
        linarith
    simpa using this
  nlinarith

/-! ### Composition -/

/-- **Adaptive composition** (Theorem B.1 of Dwork–Roth, extending Theorem 3.16 to adaptively
chosen mechanisms; here with possibly different parameters): if `M₁` is `(ε₁, δ₁)`-DP and the
second mechanism `M₂`, which sees the dataset and the first output `y`, is `(ε₂, δ₂)`-DP in the
dataset for every fixed `y`, then the joint release `M₁ ⊗ₖ M₂` of both outputs is
`(ε₁ + ε₂, δ₁ + δ₂)`-DP. General measurable spaces; `M₁` and `M₂` are Markov kernels. -/
theorem IsEpsDeltaDP.compProd {M₁ : Kernel 𝒟 Y} {M₂ : Kernel (𝒟 × Y) Z} [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] {ε₁ ε₂ δ₁ δ₂ : ℝ} (h₁ : IsEpsDeltaDP M₁ Adj ε₁ δ₁)
    (h₂ : ∀ y, IsEpsDeltaDP (M₂.sectL y) Adj ε₂ δ₂) :
    IsEpsDeltaDP (M₁ ⊗ₖ M₂) Adj (ε₁ + ε₂) (δ₁ + δ₂) := by
  rw [isEpsDeltaDP_iff_forall_measurableSet]
  intro S S' hS E hE
  have hδ₁ := h₁.nonneg hS
  have hδ₂ : 0 ≤ δ₂ := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure (M₁ S)
    exact (h₂ y).nonneg hS
  refine DP.measureReal_le_of_measure_le (add_nonneg hδ₁ hδ₂) ?_
  rw [Kernel.compProd_apply hE, Kernel.compProd_apply hE, ENNReal.ofReal_add hδ₁ hδ₂, exp_add,
    ENNReal.ofReal_mul (exp_pos _).le]
  exact DP.lintegral_le_mul_add (fun F _ ↦ h₁.measure_le hS F)
    (Kernel.measurable_kernel_prodMk_left' hE S') (fun y ↦ prob_le_one)
    fun y ↦ (h₂ y).measure_le hS _

/-- **Theorem 3.16 of Dwork–Roth for two mechanisms** (basic composition): if `M₁` is
`(ε₁, δ₁)`-DP and `M₂` is `(ε₂, δ₂)`-DP, then `S ↦ (M₁(S), M₂(S))` (independent runs) is
`(ε₁ + ε₂, δ₁ + δ₂)`-DP. General measurable spaces; `M₁` and `M₂` are Markov kernels. -/
theorem IsEpsDeltaDP.prod {M₁ : Kernel 𝒟 Y} {M₂ : Kernel 𝒟 Z} [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] {ε₁ ε₂ δ₁ δ₂ : ℝ} (h₁ : IsEpsDeltaDP M₁ Adj ε₁ δ₁)
    (h₂ : IsEpsDeltaDP M₂ Adj ε₂ δ₂) :
    IsEpsDeltaDP (M₁ ×ₖ M₂) Adj (ε₁ + ε₂) (δ₁ + δ₂) := by
  rw [isEpsDeltaDP_iff_forall_measurableSet]
  intro S S' hS E hE
  have hδ₁ := h₁.nonneg hS
  have hδ₂ := h₂.nonneg hS
  refine DP.measureReal_le_of_measure_le (add_nonneg hδ₁ hδ₂) ?_
  rw [Kernel.prod_apply' _ _ _ hE, Kernel.prod_apply' _ _ _ hE, ENNReal.ofReal_add hδ₁ hδ₂,
    exp_add, ENNReal.ofReal_mul (exp_pos _).le]
  exact DP.lintegral_le_mul_add (fun F _ ↦ h₁.measure_le hS F)
    (measurable_measure_prodMk_left hE) (fun y ↦ prob_le_one) fun y ↦ h₂.measure_le hS _

/-- **Theorem 3.14 of Dwork–Roth** (composition of pure DP): if `M₁` is `ε₁`-DP and `M₂` is
`ε₂`-DP, then `S ↦ (M₁(S), M₂(S))` is `(ε₁ + ε₂)`-DP. -/
theorem IsEpsDP.prod {M₁ : Kernel 𝒟 Y} {M₂ : Kernel 𝒟 Z} [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] {ε₁ ε₂ : ℝ} (h₁ : IsEpsDP M₁ Adj ε₁) (h₂ : IsEpsDP M₂ Adj ε₂) :
    IsEpsDP (M₁ ×ₖ M₂) Adj (ε₁ + ε₂) := by
  simpa using IsEpsDeltaDP.prod h₁ h₂

/-- Adaptive composition of pure DP (the case `δ₁ = δ₂ = 0` of `IsEpsDeltaDP.compProd`). -/
theorem IsEpsDP.compProd {M₁ : Kernel 𝒟 Y} {M₂ : Kernel (𝒟 × Y) Z} [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] {ε₁ ε₂ : ℝ} (h₁ : IsEpsDP M₁ Adj ε₁)
    (h₂ : ∀ y, IsEpsDP (M₂.sectL y) Adj ε₂) : IsEpsDP (M₁ ⊗ₖ M₂) Adj (ε₁ + ε₂) := by
  simpa using IsEpsDeltaDP.compProd h₁ h₂

/-- The `k`-fold composition `S ↦ (M₀(S), …, M_{k-1}(S))` of independently run mechanisms
`M_i : Kernel 𝒟 (R i)`, with values in `(i : Fin k) → R i` (the mechanism `M_[k]` of
Corollary 3.15 and Theorem 3.16 of Dwork–Roth). It is defined by recursion on `k`, splitting off
the coordinate `0` with `MeasurableEquiv.piFinSuccAbove`. -/
noncomputable def DP.composeFin : {k : ℕ} → {R : Fin k → Type*} → [∀ i, MeasurableSpace (R i)] →
    ((i : Fin k) → Kernel 𝒟 (R i)) → Kernel 𝒟 ((i : Fin k) → R i)
  | 0, _, _, _ => Kernel.const 𝒟 (Measure.dirac isEmptyElim)
  | _ + 1, R, _, M => (M 0 ×ₖ DP.composeFin fun j ↦ M (Fin.succAbove 0 j)).map
      (MeasurableEquiv.piFinSuccAbove R 0).symm

instance DP.isMarkovKernel_composeFin {k : ℕ} {R : Fin k → Type*} [∀ i, MeasurableSpace (R i)]
    (M : (i : Fin k) → Kernel 𝒟 (R i)) [∀ i, IsMarkovKernel (M i)] :
    IsMarkovKernel (DP.composeFin M) := by
  induction k with
  | zero => rw [DP.composeFin]; infer_instance
  | succ k ih =>
    have := ih fun j ↦ M (Fin.succAbove 0 j)
    rw [DP.composeFin]
    exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

/-- **Theorem 3.16 of Dwork–Roth** (basic composition of `k` mechanisms): if
`M_i : Kernel 𝒟 (R i)` is `(ε_i, δ_i)`-DP for every `i < k`, then
`S ↦ (M₀(S), …, M_{k-1}(S))` is `(∑ ε_i, ∑ δ_i)`-DP. General measurable output spaces `R i`;
the `M_i` are Markov kernels. -/
theorem DP.isEpsDeltaDP_composeFin {k : ℕ} {R : Fin k → Type*} [∀ i, MeasurableSpace (R i)]
    {M : (i : Fin k) → Kernel 𝒟 (R i)} [∀ i, IsMarkovKernel (M i)] {ε δ : Fin k → ℝ}
    (h : ∀ i, IsEpsDeltaDP (M i) Adj (ε i) (δ i)) :
    IsEpsDeltaDP (DP.composeFin M) Adj (∑ i, ε i) (∑ i, δ i) := by
  induction k with
  | zero => simpa [DP.composeFin] using isEpsDeltaDP_const _ le_rfl le_rfl
  | succ k ih =>
    rw [DP.composeFin, Fin.sum_univ_succAbove _ 0, Fin.sum_univ_succAbove _ 0]
    exact ((h 0).prod (ih (M := fun j ↦ M (Fin.succAbove 0 j))
      (ε := fun j ↦ ε (Fin.succAbove 0 j)) (δ := fun j ↦ δ (Fin.succAbove 0 j))
      fun j ↦ h _)).map (MeasurableEquiv.measurable _)

/-- **Corollary 3.15 of Dwork–Roth** (composition of `k` pure-DP mechanisms): if
`M_i : Kernel 𝒟 (R i)` is `ε_i`-DP for every `i < k`, then `S ↦ (M₀(S), …, M_{k-1}(S))` is
`(∑ ε_i)`-DP. -/
theorem DP.isEpsDP_composeFin {k : ℕ} {R : Fin k → Type*} [∀ i, MeasurableSpace (R i)]
    {M : (i : Fin k) → Kernel 𝒟 (R i)} [∀ i, IsMarkovKernel (M i)] {ε : Fin k → ℝ}
    (h : ∀ i, IsEpsDP (M i) Adj (ε i)) : IsEpsDP (DP.composeFin M) Adj (∑ i, ε i) := by
  simpa using DP.isEpsDeltaDP_composeFin (δ := fun _ ↦ 0) h

/-! ### Change of dataset space -/

/-- `(ε, δ)`-DP transfers along a measurable map of datasets `g` that sends `Adj'`-neighbours to
`Adj`-neighbours: `S ↦ M(g S)` is then `(ε, δ)`-DP for `Adj'`. -/
theorem IsEpsDeltaDP.comap {𝒟' : Type*} [MeasurableSpace 𝒟'] {Adj' : 𝒟' → 𝒟' → Prop}
    (h : IsEpsDeltaDP M Adj ε δ) {g : 𝒟' → 𝒟} (hg : Measurable g)
    (hAdj : ∀ ⦃S S'⦄, Adj' S S' → Adj (g S) (g S')) : IsEpsDeltaDP (M.comap g hg) Adj' ε δ :=
  fun _ _ hS E ↦ h (hAdj hS) E

/-! ### Parallel composition

F. McSherry, *Privacy integrated queries*, SIGMOD 2009, Theorem 4: if `M_i` is `ε_i`-DP and the
`D_i` are disjoint, then releasing `M_i(X ∩ D_i)` for all `i`, where each `M_i` may also see the
earlier outputs, is `max_i ε_i`-DP. We formalize the case of **two parts**. The dataset is
modelled as the pair of its parts, with the relation `DP.ParallelAdj` (one part changes by a
neighbouring step); `DP.parallelAdj_inter_compl` links this to one dataset `X : Set α` split as
`(X ∩ D, X ∩ Dᶜ)`, and `IsEpsDP.parallel_compProd_inter` is the resulting statement for one
dataset: the duplicate-free (sets rather than PINQ's multisets), adjacent-dataset (rather than
all-pairs symmetric-difference distance), complementary-bipartition version of Theorem 4. -/

/-- The neighbouring relation on datasets `(S₁, S₂)` made of two disjoint parts: two such
datasets are neighbours if they differ in exactly one part, by a neighbouring step there. -/
def DP.ParallelAdj {𝒟₁ 𝒟₂ : Type*} (Adj₁ : 𝒟₁ → 𝒟₁ → Prop) (Adj₂ : 𝒟₂ → 𝒟₂ → Prop)
    (S S' : 𝒟₁ × 𝒟₂) : Prop :=
  (Adj₁ S.1 S'.1 ∧ S.2 = S'.2) ∨ (S.1 = S'.1 ∧ Adj₂ S.2 S'.2)

/-- Datasets `X, X' : Set α` of records differ in one record (one is obtained from the other by
adding or removing a record): their symmetric difference is a singleton. -/
def DP.AddRemoveAdj {α : Type*} (X X' : Set α) : Prop :=
  ∃ a, symmDiff X X' = {a}

/-- Splitting a dataset `X : Set α` along `D` and its complement turns datasets that differ in
one record into `DP.ParallelAdj`-neighbours. -/
lemma DP.parallelAdj_inter_compl {α : Type*} (D : Set α) {X X' : Set α}
    (h : DP.AddRemoveAdj X X') :
    DP.ParallelAdj DP.AddRemoveAdj DP.AddRemoveAdj (X ∩ D, X ∩ Dᶜ) (X' ∩ D, X' ∩ Dᶜ) := by
  obtain ⟨a, ha⟩ := h
  have key (U : Set α) : symmDiff (X ∩ U) (X' ∩ U) = {a} ∩ U := by
    rw [← inter_symmDiff_distrib_right, ha]
  by_cases haD : a ∈ D
  · refine Or.inl ⟨⟨a, by rw [key, singleton_inter_of_mem haD]⟩, ?_⟩
    rw [← symmDiff_eq_bot, key, singleton_inter_eq_empty.2 (notMem_compl_iff.2 haD)]
    rfl
  · refine Or.inr ⟨?_, ⟨a, by rw [key, singleton_inter_of_mem (mem_compl haD)]⟩⟩
    rw [← symmDiff_eq_bot, key, singleton_inter_eq_empty.2 haD]
    rfl

variable {𝒟₁ 𝒟₂ : Type*} {m𝒟₁ : MeasurableSpace 𝒟₁} {m𝒟₂ : MeasurableSpace 𝒟₂}
  {Adj₁ : 𝒟₁ → 𝒟₁ → Prop} {Adj₂ : 𝒟₂ → 𝒟₂ → Prop} {ε₁ ε₂ δ₁ δ₂ : ℝ}

/-- **Adaptive parallel composition, two parts** (McSherry, SIGMOD 2009, Theorem 4 for two parts,
here with the `(ε, δ)` extension): `M₁` runs on the first part `S₁` and `M₂` runs on the
second part `S₂` and also sees the first output `y`. If `M₁` is `(ε₁, δ₁)`-DP and `M₂` is
`(ε₂, δ₂)`-DP in the dataset for every fixed `y`, the joint release is
`(max ε₁ ε₂, max δ₁ δ₂)`-DP for `DP.ParallelAdj`. (PINQ treats pure DP only; the `δ` part is an
extension.) -/
theorem IsEpsDeltaDP.parallel_compProd {M₁ : Kernel 𝒟₁ Y} {M₂ : Kernel (𝒟₂ × Y) Z}
    [IsMarkovKernel M₁] [IsMarkovKernel M₂] (h₁ : IsEpsDeltaDP M₁ Adj₁ ε₁ δ₁)
    (h₂ : ∀ y, IsEpsDeltaDP (M₂.sectL y) Adj₂ ε₂ δ₂) :
    IsEpsDeltaDP (Kernel.prodMkRight 𝒟₂ M₁ ⊗ₖ
        M₂.comap (fun p : (𝒟₁ × 𝒟₂) × Y ↦ (p.1.2, p.2)) (by fun_prop))
      (DP.ParallelAdj Adj₁ Adj₂) (max ε₁ ε₂) (max δ₁ δ₂) := by
  rintro S S' (hS | hS)
  · have A : IsEpsDeltaDP (Kernel.prodMkRight 𝒟₂ M₁)
        (fun S S' ↦ Adj₁ S.1 S'.1 ∧ S.2 = S'.2) ε₁ δ₁ := fun _ _ h E ↦ h₁ h.1 E
    have B (y : Y) : IsEpsDeltaDP ((M₂.comap (fun p : (𝒟₁ × 𝒟₂) × Y ↦ (p.1.2, p.2))
        (by fun_prop)).sectL y) (fun S S' ↦ Adj₁ S.1 S'.1 ∧ S.2 = S'.2) 0 0 :=
      fun _ _ h E ↦ by simp [h.2]
    exact (A.compProd B).mono (by simp) (by simp) hS
  · have A : IsEpsDeltaDP (Kernel.prodMkRight 𝒟₂ M₁)
        (fun S S' ↦ S.1 = S'.1 ∧ Adj₂ S.2 S'.2) 0 0 := fun _ _ h E ↦ by
      simp [Kernel.prodMkRight_apply, h.1]
    have B (y : Y) : IsEpsDeltaDP ((M₂.comap (fun p : (𝒟₁ × 𝒟₂) × Y ↦ (p.1.2, p.2))
        (by fun_prop)).sectL y) (fun S S' ↦ S.1 = S'.1 ∧ Adj₂ S.2 S'.2) ε₂ δ₂ :=
      fun _ _ h E ↦ h₂ y h.2 E
    exact (A.compProd B).mono (by simp) (by simp) hS

/-- **Adaptive parallel composition for pure DP, two parts** (McSherry, SIGMOD 2009, Theorem 4
for two parts): `ε₁`- and `ε₂`-DP mechanisms run on disjoint parts of the data, the second one
also seeing the first output, give a `max ε₁ ε₂`-DP release. -/
theorem IsEpsDP.parallel_compProd {M₁ : Kernel 𝒟₁ Y} {M₂ : Kernel (𝒟₂ × Y) Z}
    [IsMarkovKernel M₁] [IsMarkovKernel M₂] (h₁ : IsEpsDP M₁ Adj₁ ε₁)
    (h₂ : ∀ y, IsEpsDP (M₂.sectL y) Adj₂ ε₂) :
    IsEpsDP (Kernel.prodMkRight 𝒟₂ M₁ ⊗ₖ
        M₂.comap (fun p : (𝒟₁ × 𝒟₂) × Y ↦ (p.1.2, p.2)) (by fun_prop))
      (DP.ParallelAdj Adj₁ Adj₂) (max ε₁ ε₂) := by
  simpa using IsEpsDeltaDP.parallel_compProd h₁ h₂

/-- **McSherry's parallel composition for one dataset split in two** (SIGMOD 2009, Theorem 4:
the duplicate-free, adjacent-dataset, complementary-bipartition version): for datasets
`X : Set α` of records, neighbouring when they differ in one record (`DP.AddRemoveAdj`), and any
`D : Set α`, releasing `y ∼ M₁(X ∩ D)` and then `M₂(X ∩ Dᶜ, y)` is `max ε₁ ε₂`-DP if `M₁` is
`ε₁`-DP and each `M₂(·, y)` is `ε₂`-DP. Datasets carry Mathlib's σ-algebra
`Set.instMeasurableSpace` on `Set α`. PINQ's datasets are multisets and its guarantee covers all
pairs of datasets at a given symmetric-difference distance; neither bridge is formalized here. -/
theorem IsEpsDP.parallel_compProd_inter {α : Type*} (D : Set α)
    {M₁ : Kernel (Set α) Y}
    {M₂ : Kernel (Set α × Y) Z} [IsMarkovKernel M₁] [IsMarkovKernel M₂]
    (h₁ : IsEpsDP M₁ DP.AddRemoveAdj ε₁) (h₂ : ∀ y, IsEpsDP (M₂.sectL y) DP.AddRemoveAdj ε₂) :
    IsEpsDP ((Kernel.prodMkRight (Set α) M₁ ⊗ₖ
        M₂.comap (fun p : (Set α × Set α) × Y ↦ (p.1.2, p.2)) (by fun_prop)).comap
          (fun X : Set α ↦ (X ∩ D, X ∩ Dᶜ))
          ((measurable_id.inter measurable_const).prodMk (measurable_id.inter measurable_const)))
      DP.AddRemoveAdj (max ε₁ ε₂) :=
  (IsEpsDP.parallel_compProd h₁ h₂).comap _ fun _ _ h ↦ DP.parallelAdj_inter_compl D h

/-- **Non-adaptive parallel composition, two parts** (the special case of
`IsEpsDeltaDP.parallel_compProd` in which `M₂` ignores the first output): running an
`(ε₁, δ₁)`-DP mechanism `M₁` on one part of the data and an `(ε₂, δ₂)`-DP mechanism `M₂` on the
other part gives a `(max ε₁ ε₂, max δ₁ δ₂)`-DP mechanism for `DP.ParallelAdj`. For `δ₁ = δ₂ = 0`
this is the non-adaptive two-part case of McSherry's Theorem 4; the `δ` part is not in PINQ. -/
theorem IsEpsDeltaDP.parallel {M₁ : Kernel 𝒟₁ Y} {M₂ : Kernel 𝒟₂ Z} [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] (h₁ : IsEpsDeltaDP M₁ Adj₁ ε₁ δ₁) (h₂ : IsEpsDeltaDP M₂ Adj₂ ε₂ δ₂) :
    IsEpsDeltaDP (Kernel.prodMkRight 𝒟₂ M₁ ×ₖ Kernel.prodMkLeft 𝒟₁ M₂)
      (DP.ParallelAdj Adj₁ Adj₂) (max ε₁ ε₂) (max δ₁ δ₂) := by
  rintro S S' (hS | hS)
  · have A : IsEpsDeltaDP (Kernel.prodMkRight 𝒟₂ M₁)
        (fun S S' ↦ Adj₁ S.1 S'.1 ∧ S.2 = S'.2) ε₁ δ₁ := fun _ _ h E ↦ h₁ h.1 E
    have B : IsEpsDeltaDP (Kernel.prodMkLeft 𝒟₁ M₂)
        (fun S S' ↦ Adj₁ S.1 S'.1 ∧ S.2 = S'.2) 0 0 := fun _ _ h E ↦ by
      simp [Kernel.prodMkLeft_apply, h.2]
    exact (A.prod B).mono (by simp) (by simp) hS
  · have A : IsEpsDeltaDP (Kernel.prodMkRight 𝒟₂ M₁)
        (fun S S' ↦ S.1 = S'.1 ∧ Adj₂ S.2 S'.2) 0 0 := fun _ _ h E ↦ by
      simp [Kernel.prodMkRight_apply, h.1]
    have B : IsEpsDeltaDP (Kernel.prodMkLeft 𝒟₁ M₂)
        (fun S S' ↦ S.1 = S'.1 ∧ Adj₂ S.2 S'.2) ε₂ δ₂ := fun _ _ h E ↦ h₂ h.2 E
    exact (A.prod B).mono (by simp) (by simp) hS

/-- **Non-adaptive parallel composition for pure DP, two parts** (the non-adaptive two-part case
of McSherry, SIGMOD 2009, Theorem 4): `ε₁`- and `ε₂`-DP mechanisms run on disjoint parts of the
data give a `max ε₁ ε₂`-DP mechanism. -/
theorem IsEpsDP.parallel {M₁ : Kernel 𝒟₁ Y} {M₂ : Kernel 𝒟₂ Z} [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] (h₁ : IsEpsDP M₁ Adj₁ ε₁) (h₂ : IsEpsDP M₂ Adj₂ ε₂) :
    IsEpsDP (Kernel.prodMkRight 𝒟₂ M₁ ×ₖ Kernel.prodMkLeft 𝒟₁ M₂)
      (DP.ParallelAdj Adj₁ Adj₂) (max ε₁ ε₂) := by
  simpa using IsEpsDeltaDP.parallel h₁ h₂

end InformationTheory
