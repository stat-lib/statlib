/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.Operational
public import Mathlib.Analysis.Convex.Deriv

/-!
# Maximal g-leakage

Kurri, Sankar and Kosut (*An operational approach to information leakage via generalized gain
functions*, IEEE Trans. Inf. Theory 70(2), 2024, arXiv:2209.13862) measure the information that
an output `Y` leaks about an input `X` through a *gain function* `g : [0, 1] → [0, ∞)` applied to
the probability that an adversary guesses a randomized function `U` of `X` correctly. With `k`
guesses `Û₁, …, Û_k`, the *maximal g-leakage under `k` guesses* (their Definition 6) is
`L_g^{(k)}(X → Y) = sup_{U - X - Y} log (sup E[g(P(⋃ᵢ Ûᵢ = U | Y))] / sup E[g(P(⋃ᵢ Ûᵢ = U))])`,
the inner suprema ranging over all guessing strategies with and without access to `Y`. For
`k = 1` it is their maximal g-leakage (Definition 5), and for `g(t) = t` it is the maximal
leakage of Issa, Wagner and Kamath.

We work with finite alphabets, as the paper does. A gain function is a map `g : ℝ → ℝ≥0`, of
which only the values on `[0, 1]` matter; nonnegativity is built into the type. Probabilities
live in `ℝ≥0∞` and are passed to `g` through `ENNReal.toReal`. As for maximal leakage, the
alphabet of `U` and of the guesses ranges over the types `Fin n`; `ratio_le_maxGLeakageRatio`
shows that any other finite alphabet gives nothing more.

## Main definitions

* `hitProb π u`: the probability `P(Û₁ = u ∨ ⋯ ∨ Û_k = u)` that `u` is among `k` guesses drawn
  jointly from `π`.
* `maxExpectedGain g k ν`: the maximal expected gain `sup_{P_Û} E_{U ∼ ν}[g(P(⋃ᵢ Ûᵢ = U))]` of
  Definition 1 (stated there for `k = 1`), with `k` guesses.
* `maxExpectedGainGiven g k μ ρ κ`: the same quantity when the guesses may depend on `Y`, for
  `X ∼ μ`, `U` drawn from `X` through `ρ` and `Y` drawn from `X` through `κ`.
* `maxGLeakageRatio g k μ κ`: the supremum over `U` of the ratio of these two gains.
* `maxGLeakage g k μ κ`: its logarithm, the maximal g-leakage under `k` guesses (Definition 6;
  Definition 5 for `k = 1`).
* `maxGainRatio g k P Q`: the variational quantity of Theorem 6, the supremum over `U` of the
  ratio of maximal expected gains when `X ∼ P` and when `X ∼ Q`.
* `posterior μ κ y`, `pointwiseMaxGLeakageRatio`, `oppMaxGLeakageRatio`, `realMaxGLeakageRatio`:
  the posterior `P_{X|Y=y}`, and the pointwise (Corollary 5), opportunistic (Definition 11) and
  realizable (Definition 12) maximal g-leakages, multiplicative forms.
* `GuessesInSupport ν π`: the guesses drawn from `π` lie in the support of `ν`, as the paper
  requires of its estimators ("with the same support as" the variable guessed).

## Main statements

* `maxExpectedGainGiven_le`, `maxGLeakage_le_maxLeakage`: **Proposition 1**, maximal leakage
  bounds maximal g-leakage under `k` guesses (for admissible gains: bounded and not identically
  `0` on `[0, 1]`; `maxGLeakage_nonneg` gives `0 ≤ L_g^{(k)}`).
  `maxGLeakageRatio_le_maxLeakageSum` is a totalized extension to every `g`, relying on `ℝ≥0∞`
  division conventions.
* `maxGLeakageRatio_eq_maxLeakageSum`, `maxGLeakage_eq_maxLeakage`: **Theorem 1**, for a concave
  gain function with `g(0) = 0` and a finite positive right derivative at `0`, maximal g-leakage
  under `k ≥ 1` guesses equals maximal leakage `log ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`.
* `maxGLeakage_id_eq_maxLeakage`: the equality case `g(t) = t` of Proposition 1.
* `maxGainRatio_eq_iSup_div`: **Theorem 6**, for `g(0) = 0`, `g` continuous at `0` and
  `0 < sup g < ∞`, `maxGainRatio g k P Q = max_x P(x) / Q(x) = exp D_∞(P ‖ Q)`.
* `pointwiseMaxGLeakageRatio_eq`, `oppMaxGLeakageRatio_eq_maxLeakageSum`,
  `realMaxGLeakageRatio_eq`: **Corollaries 5 and 4**, the pointwise, opportunistic and
  realizable maximal g-leakages do not depend on `g`.

## Paper-to-Lean map

* Definition 1 (with `k` guesses): `maxExpectedGain`.
* Definitions 5 and 6: `maxGLeakage` (Definition 5 is `k = 1`), with multiplicative form
  `maxGLeakageRatio`.
* Proposition 1, (15): `maxGLeakage_le_maxLeakage` (admissible gains); multiplicative forms
  `maxExpectedGainGiven_le` and (totalized to all gains) `maxGLeakageRatio_le_maxLeakageSum`.
* Proposition 1, equality case `g(t) = t`: `maxGLeakage_id_eq_maxLeakage`.
* Theorem 1: `maxGLeakage_eq_maxLeakage`; multiplicative form
  `maxGLeakageRatio_eq_maxLeakageSum`.
* Theorem 6, (37): `maxGainRatio_eq_iSup_div` (multiplicative form, for every `k ≥ 1`; the paper
  states `k = 1`).
* Corollary 4, (46): `oppMaxGLeakageRatio_eq_maxLeakageSum`;
  (47): `realMaxGLeakageRatio_eq`. Corollary 5, (52): `pointwiseMaxGLeakageRatio_eq`.
  All multiplicative, for every `k ≥ 1`.

Not formalized: Theorem 2 (binary alphabets, `g(t) = 1 + t`), Section IV on the α-loss
(Lemma 1, Theorems 3–5) and Proposition 2.

## Implementation notes

The paper's suprema of logarithms are written here as the logarithm of the supremum of ratios,
as for `opMaxLeakageSum`; Theorem 6 and Corollaries 4 and 5 are stated in this multiplicative
form only, in `ℝ≥0∞`, so that `D_∞ = ∞` (when `P` is not absolutely continuous with respect to
`Q`) is covered without junk values of `Real.log`.

The achievability half of Theorem 1 does not follow the paper's shattering argument verbatim: it
refines an optimal guessing problem for maximal leakage (`exists_guessProb_div_eq_of_support`) by an
independent uniform label `(b, i) ∈ Fin r × Fin k`, and lets the adversary guess the `k` labels of a
uniformly chosen block `b`. Every guess then succeeds with probability at most `1 / r`, where `g` is
nearly linear. In Theorem 6 the shattering of the paper is kept, but the symbol attached to `x₀` is
split in two (with a small weight `η` on the second), so that an adversary can tune its success
probability while only guessing in the support of `P_U`; and the paper's upper concave envelope is
replaced by the bound `g(t) ≤ ε + (sup g / δ) t`.

The guessing strategies are restricted to the support of the variable guessed (`GuessesInSupport`),
following the paper's definitions; this matters for gain functions that are not monotone.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace InformationTheory

variable {α β γ γ' : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {μ : Measure α} {κ : Kernel α β}
  {ρ : Kernel α γ} {g : ℝ → ℝ≥0} {k : ℕ}

section Definitions

/-- `P(Û₁ = u ∨ ⋯ ∨ Û_k = u)`: the probability that `u` is among the `k` guesses
`(Û₁, …, Û_k) ∼ π`. -/
noncomputable def hitProb (π : Measure (Fin k → γ)) (u : γ) : ℝ≥0∞ :=
  π {v | ∃ i, v i = u}

/-- The `k` guesses drawn from `π` almost surely all lie in the support of `ν`. Definitions 1
and 6 of Kurri–Sankar–Kosut only allow estimators "with the same support as" the variable being
guessed. We read this as containment: each guess marginal puts no mass outside `supp ν`, as in
the closed-simplex formulation of the paper's Remark 1. Requiring literally equal supports can
change the expected gain for a discontinuous `g`. -/
def GuessesInSupport (ν : Measure γ) (π : Measure (Fin k → γ)) : Prop :=
  π {v | ∃ i, ν {v i} = 0} = 0

/-- The maximal expected gain `sup_{P_Û} E_{U ∼ ν}[g(P(⋃ᵢ Ûᵢ = U))]` of an adversary who guesses
`U ∼ ν` with `k` guesses in the support of `ν` and no observation (Definition 1 of
Kurri–Sankar–Kosut for `k = 1`, and the denominator of their Definition 6). -/
noncomputable def maxExpectedGain (g : ℝ → ℝ≥0) (k : ℕ) (ν : Measure γ) : ℝ≥0∞ :=
  ⨆ (π : Measure (Fin k → γ)) (_ : IsProbabilityMeasure π) (_ : GuessesInSupport ν π),
    ∫⁻ u, g (hitProb π u).toReal ∂ν

/-- The maximal expected gain `sup_{P_{Û|Y}} E[g(P(⋃ᵢ Ûᵢ = U | Y))]` of an adversary who observes
`Y` and makes `k` guesses of `U` in the support of `P_U`, in the Markov chain `U - X - Y`:
`X ∼ μ`, `U` is drawn from `X` through `ρ` and `Y` from `X` through `κ`, independently given
`X`. -/
noncomputable def maxExpectedGainGiven (g : ℝ → ℝ≥0) (k : ℕ) (μ : Measure α) (ρ : Kernel α γ)
    (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ (G : Kernel β (Fin k → γ)) (_ : IsMarkovKernel G) (_ : ∀ y, GuessesInSupport (ρ ∘ₘ μ) (G y)),
    ∫⁻ x, ∫⁻ u, ∫⁻ y, g (hitProb (G y) u).toReal ∂(κ x) ∂(ρ x) ∂μ

/-- The multiplicative form of maximal g-leakage under `k` guesses: the supremum, over all
randomized functions `U` of `X` with values in some `Fin n`, of the ratio of the maximal
expected gains with and without observing `Y`. This raw definition is totalized: a guessing
problem whose gains are `0 / 0` contributes `0`. For admissible gains (bounded on `[0, 1]` and not
identically zero there), `one_le_maxGLeakageRatio` gives a problem with ratio `1`, so such
terms do not affect the supremum, which then equals the supremum over problems with positive
denominator. -/
noncomputable def maxGLeakageRatio (g : ℝ → ℝ≥0) (k : ℕ) (μ : Measure α) (κ : Kernel α β) :
    ℝ≥0∞ :=
  ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ),
    maxExpectedGainGiven g k μ ρ κ / maxExpectedGain g k (ρ ∘ₘ μ)

/-- The maximal g-leakage under `k` guesses `L_g^{(k)}(X → Y)` (Definition 6 of
Kurri–Sankar–Kosut; their Definition 5 of maximal g-leakage for `k = 1`), in nats. -/
noncomputable def maxGLeakage (g : ℝ → ℝ≥0) (k : ℕ) (μ : Measure α) (κ : Kernel α β) : ℝ :=
  Real.log (maxGLeakageRatio g k μ κ).toReal

end Definitions

section HitProb

lemma hitProb_le_one (π : Measure (Fin k → γ)) [IsProbabilityMeasure π] (u : γ) :
    hitProb π u ≤ 1 :=
  prob_le_one

lemma hitProb_ne_top (π : Measure (Fin k → γ)) [IsProbabilityMeasure π] (u : γ) :
    hitProb π u ≠ ∞ :=
  measure_ne_top π _

lemma toReal_hitProb_mem_Icc (π : Measure (Fin k → γ)) [IsProbabilityMeasure π] (u : γ) :
    (hitProb π u).toReal ∈ Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hitProb_le_one π u)

variable [Fintype γ] [MeasurableSingletonClass γ]

/-- `k` guesses hit at most `k` values on average: `∑_u P(⋃ᵢ Ûᵢ = u) ≤ k`. -/
lemma sum_hitProb_le (π : Measure (Fin k → γ)) [IsProbabilityMeasure π] :
    ∑ u, hitProb π u ≤ k := by
  calc ∑ u, hitProb π u ≤ ∑ u, ∑ i, π ((fun v : Fin k → γ ↦ v i) ⁻¹' {u}) := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        have h : {v : Fin k → γ | ∃ i, v i = u} = ⋃ i, (fun v : Fin k → γ ↦ v i) ⁻¹' {u} := by
          ext
          simp
        rw [hitProb, h]
        exact measure_iUnion_fintype_le π _
    _ = ∑ i, ∑ u, π ((fun v : Fin k → γ ↦ v i) ⁻¹' {u}) := Finset.sum_comm
    _ = ∑ _i : Fin k, π univ := Finset.sum_congr rfl fun i _ ↦ by
        rw [sum_measure_preimage_singleton (f := fun v : Fin k → γ ↦ v i) _ fun u _ ↦
          measurable_pi_apply i (measurableSet_singleton u)]
        simp
    _ = k := by simp

end HitProb

section Converse

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

/-- The expected gain of a guessing strategy `G` that observes `Y`, as a finite sum. -/
lemma lintegral_gain_eq_sum (G : Kernel β (Fin k → γ)) :
    ∫⁻ x, ∫⁻ u, ∫⁻ y, g (hitProb (G y) u).toReal ∂(κ x) ∂(ρ x) ∂μ =
      ∑ x, ∑ u, ∑ y, (g (hitProb (G y) u).toReal : ℝ≥0∞) * κ x {y} * ρ x {u} * μ {x} := by
  simp only [lintegral_fintype, Finset.sum_mul]

end Converse

section Converse

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Finite γ] [MeasurableSingletonClass γ]

/-- **Proposition 1 of Kurri–Sankar–Kosut**, multiplicative form: for every nonnegative gain
function `g` and every number of guesses `k`, observing `Y` multiplies the maximal expected gain
in guessing `U` by at most `∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`. -/
theorem maxExpectedGainGiven_le :
    maxExpectedGainGiven g k μ ρ κ ≤ maxLeakageSum μ κ * maxExpectedGain g k (ρ ∘ₘ μ) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite γ
  set M : β → ℝ≥0∞ := fun y ↦ ⨆ (x) (_ : μ {x} ≠ 0), κ x {y}
  refine iSup₂_le fun G _ ↦ iSup_le fun hG ↦ ?_
  set F : γ → β → ℝ≥0∞ := fun u y ↦ g (hitProb (G y) u).toReal
  calc ∫⁻ x, ∫⁻ u, ∫⁻ y, g (hitProb (G y) u).toReal ∂(κ x) ∂(ρ x) ∂μ
      = ∑ x, ∑ u, ∑ y, F u y * ρ x {u} * (κ x {y} * μ {x}) := by
        rw [lintegral_gain_eq_sum]
        refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun y _ ↦ by ring
    _ ≤ ∑ x, ∑ u, ∑ y, F u y * ρ x {u} * (M y * μ {x}) :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦ Finset.sum_le_sum fun y _ ↦
          mul_le_mul' le_rfl (mul_le_iSup_mul x y)
    _ = ∑ x, ∑ y, ∑ u, F u y * ρ x {u} * (M y * μ {x}) :=
        Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ u, F u y * ρ x {u} * (M y * μ {x}) := Finset.sum_comm
    _ = ∑ y, ∑ u, ∑ x, F u y * ρ x {u} * (M y * μ {x}) :=
        Finset.sum_congr rfl fun y _ ↦ Finset.sum_comm
    _ = ∑ y, M y * ∫⁻ u, F u y ∂(ρ ∘ₘ μ) := by
        simp_rw [lintegral_fintype, comp_apply_singleton, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun x _ ↦ by ring
    _ ≤ ∑ y, M y * maxExpectedGain g k (ρ ∘ₘ μ) := by
        gcongr with y
        exact le_iSup₂_of_le (G y) inferInstance (le_iSup_of_le (hG y) le_rfl)
    _ = maxLeakageSum μ κ * maxExpectedGain g k (ρ ∘ₘ μ) := by
        rw [maxLeakageSum, Finset.sum_mul]

end Converse

section Relabel

variable [Finite γ] [MeasurableSingletonClass γ] [Finite γ'] [MeasurableSingletonClass γ']

/-- Relabelling the guesses by a bijection `e` relabels the hit probabilities. -/
lemma hitProb_map_comp (e : γ ≃ γ') (π : Measure (Fin k → γ)) (u : γ) :
    hitProb (π.map (e ∘ ·)) (e u) = hitProb π u := by
  rw [hitProb, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  simp [hitProb]

omit [Finite γ'] in
lemma map_equiv_apply_singleton (e : γ ≃ γ') (ν : Measure γ) (u : γ) :
    ν.map e {e u} = ν {u} := by
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  congr 1
  ext v
  simp

/-- Relabelling the guesses and the target law by the same bijection preserves the support
restriction on the guesses. -/
lemma guessesInSupport_map_comp_iff (e : γ ≃ γ') (ν : Measure γ) (π : Measure (Fin k → γ)) :
    GuessesInSupport (ν.map e) (π.map (e ∘ ·)) ↔ GuessesInSupport ν π := by
  have h : (e ∘ ·) ⁻¹' {w : Fin k → γ' | ∃ i, ν.map e {w i} = 0} =
      {v | ∃ i, ν {v i} = 0} := by
    ext v
    simp [map_equiv_apply_singleton]
  rw [GuessesInSupport, GuessesInSupport,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet, h]

lemma guessesInSupport_map_symm_comp_iff (e : γ ≃ γ') (ν : Measure γ)
    (π' : Measure (Fin k → γ')) :
    GuessesInSupport ν (π'.map (e.symm ∘ ·)) ↔ GuessesInSupport (ν.map e) π' := by
  have h := guessesInSupport_map_comp_iff e.symm (ν.map e) π'
  rwa [Measure.map_map (measurable_of_finite _) (measurable_of_finite _), e.symm_comp_self,
    Measure.map_id] at h

/-- The maximal expected gain only depends on the law of `U` up to relabelling. -/
lemma maxExpectedGain_map (e : γ ≃ γ') (ν : Measure γ) :
    maxExpectedGain g k (ν.map e) = maxExpectedGain g k ν := by
  have h_int (π' : Measure (Fin k → γ')) :
      ∫⁻ u', (g (hitProb π' u').toReal : ℝ≥0∞) ∂(ν.map e) =
        ∫⁻ u, g (hitProb π' (e u)).toReal ∂ν :=
    lintegral_map (measurable_of_finite _) (measurable_of_finite _)
  refine le_antisymm (iSup₂_le fun π' _ ↦ iSup_le fun hπ' ↦ ?_)
    (iSup₂_le fun π _ ↦ iSup_le fun hπ ↦ ?_)
  · rw [h_int]
    refine le_iSup₂_of_le (π'.map (e.symm ∘ ·)) inferInstance <| le_iSup_of_le
      ((guessesInSupport_map_symm_comp_iff e ν π').2 hπ') (le_of_eq ?_)
    congr with u
    rw [← hitProb_map_comp e.symm π' (e u), e.symm_apply_apply]
  · refine le_iSup₂_of_le (π.map (e ∘ ·)) inferInstance <| le_iSup_of_le
      ((guessesInSupport_map_comp_iff e ν π).2 hπ) (le_of_eq ?_)
    simp_rw [h_int, hitProb_map_comp]

/-- The maximal expected gain with observation is invariant under relabelling `U`. -/
lemma maxExpectedGainGiven_map (e : γ ≃ γ') :
    maxExpectedGainGiven g k μ (ρ.map e) κ = maxExpectedGainGiven g k μ ρ κ := by
  have he : Measurable e := measurable_of_finite _
  have h_int (G : Kernel β (Fin k → γ')) (x : α) :
      ∫⁻ u', ∫⁻ y, (g (hitProb (G y) u').toReal : ℝ≥0∞) ∂(κ x) ∂(ρ.map e x) =
        ∫⁻ u, ∫⁻ y, g (hitProb (G y) (e u)).toReal ∂(κ x) ∂(ρ x) := by
    rw [Kernel.map_apply _ he, lintegral_map (measurable_of_finite _) he]
  have h_law : (ρ.map e) ∘ₘ μ = (ρ ∘ₘ μ).map e := (Measure.map_comp _ _ he).symm
  refine le_antisymm (iSup₂_le fun G _ ↦ iSup_le fun hG ↦ ?_)
    (iSup₂_le fun G _ ↦ iSup_le fun hG ↦ ?_)
  · simp_rw [h_int]
    have hf : Measurable (e.symm ∘ · : (Fin k → γ') → Fin k → γ) := measurable_of_finite _
    have := Kernel.IsMarkovKernel.map G hf
    have hG' (y : β) : GuessesInSupport (ρ ∘ₘ μ) (G.map (e.symm ∘ ·) y) := by
      rw [Kernel.map_apply G hf, guessesInSupport_map_symm_comp_iff, ← h_law]
      exact hG y
    refine le_iSup₂_of_le (G.map (e.symm ∘ ·)) inferInstance (le_iSup_of_le hG' (le_of_eq ?_))
    simp_rw [Kernel.map_apply G hf, ← hitProb_map_comp e.symm _ (e _), e.symm_apply_apply]
  · have hf : Measurable (e ∘ · : (Fin k → γ) → Fin k → γ') := measurable_of_finite _
    have := Kernel.IsMarkovKernel.map G hf
    have hG' (y : β) : GuessesInSupport ((ρ.map e) ∘ₘ μ) (G.map (e ∘ ·) y) := by
      rw [Kernel.map_apply G hf, h_law, guessesInSupport_map_comp_iff]
      exact hG y
    refine le_iSup₂_of_le (G.map (e ∘ ·)) inferInstance (le_iSup_of_le hG' (le_of_eq ?_))
    simp_rw [h_int, Kernel.map_apply G hf, hitProb_map_comp]

/-- The gain ratio of a randomized function `U` of `X` with values in any finite alphabet is
bounded by `maxGLeakageRatio`, whose definition only ranges over the alphabets `Fin n`. -/
lemma ratio_le_maxGLeakageRatio [IsMarkovKernel ρ] :
    maxExpectedGainGiven g k μ ρ κ / maxExpectedGain g k (ρ ∘ₘ μ) ≤ maxGLeakageRatio g k μ κ := by
  have := Fintype.ofFinite γ
  set e := Fintype.equivFin γ
  have he : Measurable e := measurable_of_finite _
  have := Kernel.IsMarkovKernel.map ρ he
  refine le_iSup_of_le (Fintype.card γ) (le_iSup₂_of_le (ρ.map e) inferInstance (le_of_eq ?_))
  rw [maxExpectedGainGiven_map, ← Measure.map_comp _ _ he, maxExpectedGain_map]

end Relabel

/-- A finite combination of Dirac masses, evaluated on a measurable set. -/
lemma sum_smul_dirac_apply {ι : Type*} [Fintype ι] (w : ι → ℝ≥0∞) (f : ι → γ) {s : Set γ}
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    (∑ p, w p • Measure.dirac (f p)) s = ∑ p, if f p ∈ s then w p else 0 := by
  simp [Measure.dirac_apply' _ hs, Set.indicator]

section ConverseRatio

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

/-- **Proposition 1 of Kurri–Sankar–Kosut**, ratio form, as a *totalized extension* to every
gain function `g : ℝ → ℝ≥0` and every `k`: `maxGLeakageRatio g k μ κ ≤ ∑_y max_{x ∈ supp P_X}
P_{Y|X}(y | x)`. For gains outside the paper's admissible class some ratios are only defined by
the conventions `0 / 0 = 0` and `∞ / ∞ = 0` of `ℝ≥0∞` (e.g. `g ≡ 0`, or `g` unbounded on
`[0, 1]`); `maxGLeakage_le_maxLeakage` is the statement for admissible gains. -/
theorem maxGLeakageRatio_le_maxLeakageSum : maxGLeakageRatio g k μ κ ≤ maxLeakageSum μ κ :=
  iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ ENNReal.div_le_of_le_mul maxExpectedGainGiven_le

omit [Fintype β] [MeasurableSingletonClass β] in
/-- For an admissible gain function (bounded on `[0, 1]` and not identically `0` there) and
`k ≥ 1`, the maximal g-leakage ratio is at least `1`: a function `U` of `X` that is independent
of `X` already gives ratio exactly `1`, with positive and finite gains. -/
lemma one_le_maxGLeakageRatio [IsProbabilityMeasure μ] [IsMarkovKernel κ] (hk : k ≠ 0)
    (hpos : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0) (hbdd : BddAbove (g '' Icc 0 1)) :
    1 ≤ maxGLeakageRatio g k μ κ := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨t₀, ht₀, hgt₀⟩ := hpos
  obtain ⟨C, hC⟩ := hbdd
  -- `U` uniform on `Fin 2`, independent of `X`.
  set ν₀ : Measure (Fin 2) := ∑ u : Fin 2, (2⁻¹ : ℝ≥0∞) • Measure.dirac u
  have hν₀ (u : Fin 2) : ν₀ {u} = 2⁻¹ := by
    rw [show ν₀ = ∑ u : Fin 2, (2⁻¹ : ℝ≥0∞) • Measure.dirac (id u) from rfl,
      sum_smul_dirac_apply _ _ (measurableSet_singleton u)]
    simp
  have : IsProbabilityMeasure ν₀ := ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp only [hν₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top⟩
  set ρ : Kernel α (Fin 2) := Kernel.const α ν₀
  have hU (u : Fin 2) : (ρ ∘ₘ μ) {u} = 2⁻¹ := by
    rw [comp_apply_singleton]
    simp [ρ, hν₀, ← Finset.mul_sum, sum_measure_singleton]
  set D := maxExpectedGain g k (ρ ∘ₘ μ)
  -- Ignoring `Y` is a valid strategy, so observing `Y` gains at least `D`.
  have hDN : D ≤ maxExpectedGainGiven g k μ ρ κ := by
    refine iSup₂_le fun π _ ↦ iSup_le fun hπ ↦ ?_
    refine le_iSup₂_of_le (Kernel.const β π) inferInstance
      (le_iSup_of_le (fun _ ↦ hπ) (le_of_eq ?_))
    simp only [Kernel.const_apply, lintegral_const, measure_univ, mul_one, ρ]
    rw [lintegral_fintype, lintegral_fintype]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [hν₀, ← hU u]
  -- `0 < D`: guess `0` with probability `t₀` and `1` otherwise.
  have hD0 : D ≠ 0 := by
    set π : Measure (Fin k → Fin 2) := ENNReal.ofReal t₀ • Measure.dirac (fun _ ↦ 0) +
      ENNReal.ofReal (1 - t₀) • Measure.dirac (fun _ ↦ 1)
    have : IsProbabilityMeasure π := ⟨by
      simp only [π, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add ht₀.1 (sub_nonneg.2 ht₀.2)]
      simp⟩
    have hπ : hitProb π 0 = ENNReal.ofReal t₀ := by
      have hs : MeasurableSet {v : Fin k → Fin 2 | ∃ i, v i = 0} := (Set.toFinite _).measurableSet
      rw [hitProb, add_apply, smul_apply, smul_apply, Measure.dirac_apply' _ hs,
        Measure.dirac_apply' _ hs]
      simp [Set.indicator, show Nonempty (Fin k) from ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩]
    have hπs : GuessesInSupport (ρ ∘ₘ μ) π := by
      simp [GuessesInSupport, hU]
    refine (lt_of_lt_of_le ?_ (le_iSup₂_of_le π this (le_iSup_of_le hπs le_rfl))).ne'
    rw [lintegral_fintype]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ 0))
    rw [hπ, ENNReal.toReal_ofReal ht₀.1, hU]
    exact ENNReal.mul_pos (by simpa using hgt₀) (by simp)
  -- `D < ∞`, since `g ≤ C` on `[0, 1]`.
  have hDtop : D ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := C))
      (iSup₂_le fun π _ ↦ iSup_le fun _ ↦ ?_)
    calc ∫⁻ u, (g (hitProb π u).toReal : ℝ≥0∞) ∂(ρ ∘ₘ μ) ≤ ∫⁻ _u, (C : ℝ≥0∞) ∂(ρ ∘ₘ μ) :=
          lintegral_mono fun u ↦ ENNReal.coe_le_coe.2 (hC ⟨_, toReal_hitProb_mem_Icc π u, rfl⟩)
      _ = C := by simp
  calc (1 : ℝ≥0∞) = D / D := (ENNReal.div_self hD0 hDtop).symm
    _ ≤ maxExpectedGainGiven g k μ ρ κ / D := ENNReal.div_le_div_right hDN _
    _ ≤ maxGLeakageRatio g k μ κ := ratio_le_maxGLeakageRatio

omit [Fintype β] in
/-- Maximal g-leakage is nonnegative for an admissible gain function (bounded on `[0, 1]` and
not identically `0` there) and `k ≥ 1`. -/
lemma maxGLeakage_nonneg [Finite β] [IsProbabilityMeasure μ] [IsMarkovKernel κ] (hk : k ≠ 0)
    (hpos : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0) (hbdd : BddAbove (g '' Icc 0 1)) :
    0 ≤ maxGLeakage g k μ κ := by
  have := Fintype.ofFinite β
  have hR : maxGLeakageRatio g k μ κ ≠ ∞ :=
    ne_top_of_le_ne_top maxLeakageSum_ne_top maxGLeakageRatio_le_maxLeakageSum
  refine Real.log_nonneg ?_
  simpa using ENNReal.toReal_mono hR (one_le_maxGLeakageRatio hk hpos hbdd)

/-- **Proposition 1 of Kurri–Sankar–Kosut**, (15): maximal leakage is an upper bound on maximal
g-leakage under `k ≥ 1` guesses, `L_g^{(k)}(X → Y) ≤ I_∞^S(X; Y) = L(X → Y)`, for every
admissible gain function `g : [0, 1] → [0, ∞)`, i.e. bounded and not identically `0`, so that
all the expected gains are finite and `L_g^{(k)}(X → Y) ≥ 0` (`maxGLeakage_nonneg`). -/
theorem maxGLeakage_le_maxLeakage [IsProbabilityMeasure μ] [IsMarkovKernel κ] (hk : k ≠ 0)
    (hpos : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0) (hbdd : BddAbove (g '' Icc 0 1)) :
    maxGLeakage g k μ κ ≤ maxLeakage μ κ := by
  have hR : maxGLeakageRatio g k μ κ ≠ ∞ :=
    ne_top_of_le_ne_top maxLeakageSum_ne_top maxGLeakageRatio_le_maxLeakageSum
  have h1 : 1 ≤ (maxGLeakageRatio g k μ κ).toReal := by
    simpa using ENNReal.toReal_mono hR (one_le_maxGLeakageRatio hk hpos hbdd)
  exact Real.log_le_log (by linarith)
    (ENNReal.toReal_mono maxLeakageSum_ne_top maxGLeakageRatio_le_maxLeakageSum)

end ConverseRatio

section ConcaveGain

variable {f : ℝ → ℝ} {d : ℝ}

/-- A concave function on `[0, 1]` vanishing at `0` lies above its chords from the origin:
`a f(t) ≤ f(a t)`. -/
lemma mul_le_apply_mul_of_concaveOn (hconc : ConcaveOn ℝ (Icc 0 1) f) (h0 : f 0 = 0) {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) : a * f t ≤ f (a * t) := by
  have := hconc.2 ht (left_mem_Icc.2 zero_le_one) ha.1 (sub_nonneg.2 ha.2) (add_sub_cancel a 1)
  simpa [h0] using this

/-- A concave function on `[0, 1]` vanishing at `0` lies below its tangent at `0`:
`f(s) ≤ f'(0) s`. -/
lemma apply_le_mul_of_concaveOn (hconc : ConcaveOn ℝ (Icc 0 1) f) (h0 : f 0 = 0)
    (hd : HasDerivWithinAt f d (Icc 0 1) 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : f s ≤ d * s := by
  rcases hs.1.eq_or_lt with rfl | hs0
  · simp [h0]
  · have := hconc.slope_le_of_hasDerivWithinAt (left_mem_Icc.2 zero_le_one) hs hs0 hd
    rwa [slope_def_field, h0, sub_zero, sub_zero, div_le_iff₀ hs0] at this

/-- The difference quotients `r f(1 / r)` of a function with `f(0) = 0` converge to its right
derivative at `0`. -/
lemma tendsto_natCast_mul_apply_one_div (h0 : f 0 = 0) (hd : HasDerivWithinAt f d (Icc 0 1) 0) :
    Tendsto (fun r : ℕ ↦ (r : ℝ) * f (1 / r)) atTop (𝓝 d) := by
  have h_inv : Tendsto (fun r : ℕ ↦ (1 : ℝ) / r) atTop (𝓝[Icc 0 1 \ {0}] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_atTop_nhds_zero_nat,
      eventually_atTop.2 ⟨1, fun r hr ↦ ⟨⟨by positivity, ?_⟩, ?_⟩⟩⟩
    · exact div_le_one_of_le₀ (by exact_mod_cast hr) (by positivity)
    · have : (0 : ℝ) < r := by exact_mod_cast hr
      simp only [mem_singleton_iff]
      positivity
  refine ((hasDerivWithinAt_iff_tendsto_slope.1 hd).comp h_inv).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with r hr
  simp [slope_def_field, h0, mul_comm]

end ConcaveGain

section DenominatorBound

variable [Finite γ] [MeasurableSingletonClass γ]

/-- If `g(s) ≤ d s` on `[0, 1]`, the maximal expected gain of `k` blind guesses is at most
`d k max_u P_U(u)`. -/
lemma maxExpectedGain_le_of_le_mul {d : ℝ} (hd : 0 ≤ d)
    (hle : ∀ s ∈ Icc (0 : ℝ) 1, (g s : ℝ) ≤ d * s) (ν : Measure γ) :
    maxExpectedGain g k ν ≤ ENNReal.ofReal d * k * ⨆ u, ν {u} := by
  have := Fintype.ofFinite γ
  refine iSup₂_le fun π _ ↦ iSup_le fun _ ↦ ?_
  set M := ⨆ u, ν {u}
  have hg (u : γ) : (g (hitProb π u).toReal : ℝ≥0∞) ≤ ENNReal.ofReal d * hitProb π u := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_toReal (hitProb_ne_top π u),
      ← ENNReal.ofReal_mul hd, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (hle _ (toReal_hitProb_mem_Icc π u))
  calc ∫⁻ u, (g (hitProb π u).toReal : ℝ≥0∞) ∂ν
      = ∑ u, (g (hitProb π u).toReal : ℝ≥0∞) * ν {u} := lintegral_fintype _
    _ ≤ ∑ u, ENNReal.ofReal d * hitProb π u * M := by
        gcongr with u
        · exact hg u
        · exact le_iSup (fun u ↦ ν {u}) u
    _ = ENNReal.ofReal d * (∑ u, hitProb π u) * M := by rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ENNReal.ofReal d * k * M := by gcongr; exact sum_hitProb_le π

end DenominatorBound

section Achievability

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

/-- An optimal guessing problem for maximal leakage, as in `exists_guessProb_div_eq`, whose guess
`Û` only takes values in the support of `P_U`: the mass that the guess puts outside the support
is moved to a point of the support, which cannot decrease `P[U = Û]`. -/
lemma exists_guessProb_div_eq_of_support [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    ∃ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ) (g : Kernel β (Fin n))
      (_ : IsMarkovKernel g), (∀ y u, (ρ ∘ₘ μ) {u} = 0 → g y {u} = 0) ∧
        guessProb μ ρ κ g / blindGuessProb μ ρ = maxLeakageSum μ κ := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨n, ρ, hρ, g, hg, h⟩ := exists_guessProb_div_eq (μ := μ) (κ := κ)
  set S : Set (Fin n) := {u | (ρ ∘ₘ μ) {u} ≠ 0}
  have hS : MeasurableSet S := (Set.toFinite S).measurableSet
  obtain ⟨u₀, hu₀⟩ : ∃ u, (ρ ∘ₘ μ) {u} ≠ 0 := by
    by_contra! h0
    have := sum_measure_singleton (μ := ρ ∘ₘ μ) (s := Finset.univ)
    simp [h0] at this
  set g' : Kernel β (Fin n) :=
    Kernel.ofFunOfCountable fun y ↦ (g y).restrict S + g y Sᶜ • Measure.dirac u₀
  have hg' (y : β) (u : Fin n) :
      g' y {u} = g y ({u} ∩ S) + g y Sᶜ * Measure.dirac u₀ {u} := by
    simp [g', Kernel.ofFunOfCountable, Measure.restrict_apply (measurableSet_singleton u)]
  have : IsMarkovKernel g' := ⟨fun y ↦ ⟨by
    simp [g', Kernel.ofFunOfCountable, measure_add_measure_compl hS]⟩⟩
  have h_supp (y : β) (u : Fin n) (hu : (ρ ∘ₘ μ) {u} = 0) : g' y {u} = 0 := by
    have hne : u₀ ≠ u := fun h ↦ hu₀ (h ▸ hu)
    rw [hg', Measure.dirac_apply' _ (measurableSet_singleton u)]
    simp [S, hu, hne]
  have h_le : guessProb μ ρ κ g ≤ guessProb μ ρ κ g' := by
    simp_rw [guessProb_eq_sum]
    refine Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦
      Finset.sum_le_sum fun y _ ↦ ?_
    by_cases hu : (ρ ∘ₘ μ) {u} = 0
    · have h0 : ρ x {u} * μ {x} = 0 := by
        rw [comp_apply_singleton] at hu
        exact Finset.sum_eq_zero_iff.1 hu x (Finset.mem_univ x)
      calc g y {u} * κ x {y} * ρ x {u} * μ {x} = g y {u} * κ x {y} * (ρ x {u} * μ {x}) := by
            ring
        _ = 0 := by rw [h0, mul_zero]
        _ ≤ _ := zero_le
    · gcongr ?_ * _ * _ * _
      rw [hg', Set.singleton_inter_of_mem (show u ∈ S from hu)]
      exact le_self_add
  exact ⟨n, ρ, hρ, g', this, h_supp, le_antisymm (ENNReal.div_le_of_le_mul guessProb_le)
    (h.symm.le.trans (ENNReal.div_le_div_right h_le _))⟩

/-- **Achievability half of Theorem 1**, for a fixed resolution `r`. Start from an optimal
guessing problem `U₀ - X - Y - Û₀` for maximal leakage. Refine `U₀` to `U = (U₀, B, I)` with an
independent uniform label `(B, I) ∈ Fin r × Fin k`, and let the adversary guess
`(Û₀, B', 0), …, (Û₀, B', k - 1)` for an independent uniform block `B'`. Every guess then hits
with probability at most `1 / r`, and concavity of `g` gives the gain ratio
`r g(1 / r) / g'(0) · exp L(X → Y)`. -/
lemma le_maxGLeakageRatio_of_concaveOn [IsProbabilityMeasure μ] [IsMarkovKernel κ] {d : ℝ}
    (hconc : ConcaveOn ℝ (Icc 0 1) fun t ↦ (g t : ℝ)) (hg0 : g 0 = 0)
    (hle : ∀ s ∈ Icc (0 : ℝ) 1, (g s : ℝ) ≤ d * s) (hd : 0 < d) (hk : k ≠ 0) {r : ℕ}
    (hr : r ≠ 0) :
    ENNReal.ofReal (r * g (1 / r)) / ENNReal.ofReal d * maxLeakageSum μ κ ≤
      maxGLeakageRatio g k μ κ := by
  classical
  have := Fintype.ofFinite α
  by_cases hgr : g (1 / r) = 0
  · rw [hgr, NNReal.coe_zero, mul_zero, ENNReal.ofReal_zero, ENNReal.zero_div, zero_mul]
    exact zero_le
  -- An optimal guessing problem `(ρ₀, g₀)` for maximal leakage.
  obtain ⟨n, ρ₀, hρ₀, g₀, hg₀, hsupp, h⟩ := exists_guessProb_div_eq_of_support (μ := μ) (κ := κ)
  set L := maxLeakageSum μ κ
  set P₀ := guessProb μ ρ₀ κ g₀
  set B₀ := blindGuessProb μ ρ₀
  obtain ⟨x₀, hx₀⟩ : ∃ x, μ {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := μ) (s := Finset.univ)
    simp [h] at this
  have hLB : L * B₀ ≤ P₀ := by
    rw [← h, mul_comm]
    exact ENNReal.mul_div_le
  have hP₀ : P₀ ≠ 0 := by
    intro h0
    rw [h0, ENNReal.zero_div] at h
    exact absurd ((one_le_maxLeakageSum (κ := κ) hx₀).trans_eq h.symm) (by simp)
  -- The refined randomization `ρ`, with `U = (U₀, B, I)`.
  set w : ℝ≥0∞ := ((r * k : ℕ) : ℝ≥0∞)⁻¹
  have hw : ∑ _q : Fin r × Fin k, w = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, w]
    exact ENNReal.mul_inv_cancel (by simp [hr, hk]) (ENNReal.natCast_ne_top _)
  set ρ : Kernel α (Fin n × Fin r × Fin k) :=
    Kernel.ofFunOfCountable fun x ↦ ∑ u, (ρ₀ x {u.1} * w) • Measure.dirac u
  have hρ (x : α) (u : Fin n × Fin r × Fin k) : ρ x {u} = ρ₀ x {u.1} * w := by
    rw [show ρ x = ∑ u, (ρ₀ x {u.1} * w) • Measure.dirac (id u) from rfl,
      sum_smul_dirac_apply _ _ (measurableSet_singleton u)]
    simp
  have : IsMarkovKernel ρ := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hρ]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hw, mul_one]
    simp⟩⟩
  -- The guessing rule `G`: the `k` labels of a uniform block `B'`, next to the guess `Û₀`.
  set G : Kernel β (Fin k → Fin n × Fin r × Fin k) :=
    Kernel.ofFunOfCountable fun y ↦
      ∑ p : Fin n × Fin r, (g₀ y {p.1} * (r : ℝ≥0∞)⁻¹) • Measure.dirac fun i ↦ (p.1, p.2, i)
  have hGy (y : β) : G y = ∑ p : Fin n × Fin r,
      (g₀ y {p.1} * (r : ℝ≥0∞)⁻¹) • Measure.dirac fun i ↦ (p.1, p.2, i) := rfl
  have hG (y : β) (u : Fin n × Fin r × Fin k) :
      hitProb (G y) u = g₀ y {u.1} * (r : ℝ≥0∞)⁻¹ := by
    have h_mem (p : Fin n × Fin r) : ((fun i ↦ (p.1, p.2, i)) ∈
        {v : Fin k → Fin n × Fin r × Fin k | ∃ i, v i = u}) ↔ p = (u.1, u.2.1) := by
      constructor
      · rintro ⟨i, rfl⟩
        rfl
      · rintro rfl
        exact ⟨u.2.2, rfl⟩
    rw [hitProb, hGy, sum_smul_dirac_apply _ _ (Set.toFinite _).measurableSet]
    simp only [h_mem]
    simp
  have : IsMarkovKernel G := ⟨fun y ↦ ⟨by
    rw [hGy, sum_smul_dirac_apply _ _ MeasurableSet.univ]
    simp only [mem_univ, ite_true]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by simpa using hr) (ENNReal.natCast_ne_top r)]
    simp⟩⟩
  -- The gain with observation is at least `g(1 / r) P[U₀ = Û₀]`.
  have h1r : (1 / r : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hr)
      (by positivity)⟩
  have hgain (y : β) (u : Fin n × Fin r × Fin k) :
      g₀ y {u.1} * (g (1 / r) : ℝ≥0∞) ≤ g (hitProb (G y) u).toReal := by
    set a := (g₀ y {u.1}).toReal
    have ha : a ∈ Icc (0 : ℝ) 1 := ⟨ENNReal.toReal_nonneg, by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := g₀ y) (s := {u.1}))⟩
    have h_toReal : (hitProb (G y) u).toReal = a * (1 / r) := by
      rw [hG, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
    calc g₀ y {u.1} * (g (1 / r) : ℝ≥0∞) = ENNReal.ofReal (a * g (1 / r)) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _),
            ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal (g (a * (1 / r))) :=
          ENNReal.ofReal_le_ofReal (mul_le_apply_mul_of_concaveOn hconc (by simp [hg0]) ha h1r)
      _ = g (hitProb (G y) u).toReal := by rw [h_toReal, ENNReal.ofReal_coe_nnreal]
  -- The guesses of `G` lie in the support of `P_U`.
  have hPU (u : Fin n × Fin r × Fin k) : (ρ ∘ₘ μ) {u} = (ρ₀ ∘ₘ μ) {u.1} * w := by
    rw [comp_apply_singleton, comp_apply_singleton, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [hρ]; ring
  have hGsupp (y : β) : GuessesInSupport (ρ ∘ₘ μ) (G y) := by
    rw [GuessesInSupport, hGy, sum_smul_dirac_apply _ _ (Set.toFinite _).measurableSet]
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    split_ifs with hp
    · obtain ⟨i, hi⟩ := hp
      have hi' : (ρ₀ ∘ₘ μ) {p.1} * w = 0 := by simpa [hPU] using hi
      rw [hsupp y p.1 ((mul_eq_zero.1 hi').resolve_right
        (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))), zero_mul]
    · rfl
  have hN : (g (1 / r) : ℝ≥0∞) * P₀ ≤ maxExpectedGainGiven g k μ ρ κ := by
    refine le_iSup₂_of_le G inferInstance (le_iSup_of_le hGsupp ?_)
    rw [lintegral_gain_eq_sum, show P₀ = _ from guessProb_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun u₀ _ ↦ ?_
    calc (g (1 / r) : ℝ≥0∞) * ∑ y, g₀ y {u₀} * κ x {y} * ρ₀ x {u₀} * μ {x}
        = ∑ _q : Fin r × Fin k, ∑ y,
            g₀ y {u₀} * g (1 / r) * κ x {y} * (ρ₀ x {u₀} * w) * μ {x} := by
          rw [← one_mul ((g (1 / r) : ℝ≥0∞) * _), ← hw, Finset.sum_mul]
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ ↦ by ring
      _ ≤ ∑ q : Fin r × Fin k, ∑ y,
            (g (hitProb (G y) (u₀, q)).toReal : ℝ≥0∞) * κ x {y} * ρ x {(u₀, q)} * μ {x} :=
          Finset.sum_le_sum fun q _ ↦ Finset.sum_le_sum fun y _ ↦ by
            rw [hρ]
            gcongr
            exact hgain y (u₀, q)
  -- The blind gain is at most `g'(0) max_u P_{U₀}(u) / r`.
  have hD : maxExpectedGain g k (ρ ∘ₘ μ) ≤ ENNReal.ofReal d * B₀ * (r : ℝ≥0∞)⁻¹ := by
    refine (maxExpectedGain_le_of_le_mul hd.le hle _).trans ?_
    have hU : ⨆ u, (ρ ∘ₘ μ) {u} ≤ B₀ * w := iSup_le fun u ↦ by
      rw [comp_apply_singleton]
      simp_rw [hρ]
      calc ∑ x, ρ₀ x {u.1} * w * μ {x} = (ρ₀ ∘ₘ μ) {u.1} * w := by
            rw [comp_apply_singleton, Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ ↦ by ring
        _ ≤ B₀ * w := by
            gcongr
            exact le_iSup (fun u ↦ (ρ₀ ∘ₘ μ) {u}) u.1
    calc ENNReal.ofReal d * k * ⨆ u, (ρ ∘ₘ μ) {u} ≤ ENNReal.ofReal d * k * (B₀ * w) := by
          gcongr
      _ = ENNReal.ofReal d * B₀ * (r : ℝ≥0∞)⁻¹ * ((k : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹) := by
          rw [show w = (r : ℝ≥0∞)⁻¹ * (k : ℝ≥0∞)⁻¹ by
            change ((r * k : ℕ) : ℝ≥0∞)⁻¹ = _
            rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl (by simpa using hr))
              (Or.inl (ENNReal.natCast_ne_top r))]]
          ring
      _ = ENNReal.ofReal d * B₀ * (r : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel (by simpa using hk) (ENNReal.natCast_ne_top k), mul_one]
  have hc : ENNReal.ofReal (r * g (1 / r)) / ENNReal.ofReal d * ENNReal.ofReal d *
      (r : ℝ≥0∞)⁻¹ = g (1 / r) := by
    rw [ENNReal.div_mul_cancel (by simpa using hd) ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal,
      mul_comm, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simpa using hr) (ENNReal.natCast_ne_top r), one_mul]
  have hN0 : maxExpectedGainGiven g k μ ρ κ ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.mul_pos (by simpa using hgr) hP₀) hN).ne'
  have hD0 : maxExpectedGain g k (ρ ∘ₘ μ) ≠ ∞ := by
    have hB₀ : B₀ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ ↦ prob_le_one)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB₀)
      (ENNReal.inv_ne_top.2 (by simpa using hr))) hD
  calc ENNReal.ofReal (r * g (1 / r)) / ENNReal.ofReal d * L
      ≤ maxExpectedGainGiven g k μ ρ κ / maxExpectedGain g k (ρ ∘ₘ μ) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inr hN0) (Or.inl hD0)]
        calc ENNReal.ofReal (r * g (1 / r)) / ENNReal.ofReal d * L *
              maxExpectedGain g k (ρ ∘ₘ μ)
            ≤ ENNReal.ofReal (r * g (1 / r)) / ENNReal.ofReal d * L *
              (ENNReal.ofReal d * B₀ * (r : ℝ≥0∞)⁻¹) := by gcongr
          _ = ENNReal.ofReal (r * g (1 / r)) / ENNReal.ofReal d * ENNReal.ofReal d *
              (r : ℝ≥0∞)⁻¹ * (L * B₀) := by ring
          _ ≤ g (1 / r) * P₀ := by rw [hc]; gcongr
          _ ≤ maxExpectedGainGiven g k μ ρ κ := hN
    _ ≤ maxGLeakageRatio g k μ κ := ratio_le_maxGLeakageRatio

end Achievability

section MainTheorem

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

/-- **Theorem 1 of Kurri–Sankar–Kosut**, multiplicative form. Let `g : [0, 1] → [0, ∞)` be
concave with `g(0) = 0` and a finite positive right derivative `g'(0) = d` at `0`. Then for every
number of guesses `k ≥ 1`, `maxGLeakageRatio g k μ κ = ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`. -/
theorem maxGLeakageRatio_eq_maxLeakageSum [IsProbabilityMeasure μ] [IsMarkovKernel κ] {d : ℝ}
    (hconc : ConcaveOn ℝ (Icc 0 1) fun t ↦ (g t : ℝ)) (hg0 : g 0 = 0)
    (hd : HasDerivWithinAt (fun t ↦ (g t : ℝ)) d (Icc 0 1) 0) (hd0 : 0 < d) (hk : k ≠ 0) :
    maxGLeakageRatio g k μ κ = maxLeakageSum μ κ := by
  refine le_antisymm maxGLeakageRatio_le_maxLeakageSum ?_
  have hg0' : (fun t ↦ (g t : ℝ)) 0 = 0 := by simp [hg0]
  have hle (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (g s : ℝ) ≤ d * s :=
    apply_le_mul_of_concaveOn hconc hg0' hd hs
  -- `r g(1 / r) / d → 1`, so the lower bounds of the achievability construction tend to `L`.
  have h_lim : Tendsto (fun r : ℕ ↦ ENNReal.ofReal (r * g (1 / r)) / ENNReal.ofReal d *
      maxLeakageSum μ κ) atTop (𝓝 (maxLeakageSum μ κ)) := by
    have h := ENNReal.Tendsto.div_const (b := ENNReal.ofReal d)
      (ENNReal.tendsto_ofReal (tendsto_natCast_mul_apply_one_div hg0' hd))
      (Or.inr (by simpa using hd0))
    rw [ENNReal.div_self (by simpa using hd0) ENNReal.ofReal_ne_top] at h
    simpa using ENNReal.Tendsto.mul_const h (Or.inl one_ne_zero)
  exact le_of_tendsto h_lim (eventually_atTop.2 ⟨1, fun r hr ↦
    le_maxGLeakageRatio_of_concaveOn hconc hg0 hle hd0 hk (Nat.one_le_iff_ne_zero.1 hr)⟩)

/-- **Theorem 1 of Kurri–Sankar–Kosut**: if `g : [0, 1] → [0, ∞)` is concave with `g(0) = 0` and
`0 < g'(0) < ∞` (right derivative at `0`), then for every `k ≥ 1` the maximal g-leakage under `k`
guesses equals maximal leakage, `L_g^{(k)}(X → Y) = I_∞^S(X; Y) = L(X → Y)`. -/
theorem maxGLeakage_eq_maxLeakage [IsProbabilityMeasure μ] [IsMarkovKernel κ] {d : ℝ}
    (hconc : ConcaveOn ℝ (Icc 0 1) fun t ↦ (g t : ℝ)) (hg0 : g 0 = 0)
    (hd : HasDerivWithinAt (fun t ↦ (g t : ℝ)) d (Icc 0 1) 0) (hd0 : 0 < d) (hk : k ≠ 0) :
    maxGLeakage g k μ κ = maxLeakage μ κ := by
  rw [maxGLeakage, maxGLeakageRatio_eq_maxLeakageSum hconc hg0 hd hd0 hk, maxLeakage]

/-- The equality case of **Proposition 1 of Kurri–Sankar–Kosut**: for the identity gain
`g(t) = t`, maximal g-leakage under `k ≥ 1` guesses is maximal leakage (this is maximal leakage
under `k` guesses, Theorem 4 of Issa–Wagner–Kamath). -/
theorem maxGLeakage_id_eq_maxLeakage [IsProbabilityMeasure μ] [IsMarkovKernel κ] (hk : k ≠ 0) :
    maxGLeakage (fun t ↦ t.toNNReal) k μ κ = maxLeakage μ κ := by
  have h_eq : EqOn id (fun t : ℝ ↦ (t.toNNReal : ℝ)) (Icc 0 1) := fun t ht ↦
    (Real.coe_toNNReal t ht.1).symm
  exact maxGLeakage_eq_maxLeakage (d := 1) ((concaveOn_id (convex_Icc 0 1)).congr h_eq)
    (by simp) ((hasDerivWithinAt_id 0 _).congr_of_mem (fun t ht ↦ (h_eq ht).symm)
      ⟨le_rfl, zero_le_one⟩) one_pos hk

end MainTheorem

section Variational

/-- The variational quantity of Theorem 6 of Kurri–Sankar–Kosut, multiplicative form: the
supremum, over all randomized functions `U` of `X` with values in some `Fin n`, of the ratio of
the maximal expected gains (with `k` guesses) of guessing `U` when `X ∼ P` and when `X ∼ Q`. -/
noncomputable def maxGainRatio (g : ℝ → ℝ≥0) (k : ℕ) (P Q : Measure α) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ),
    maxExpectedGain g k (ρ ∘ₘ P) / maxExpectedGain g k (ρ ∘ₘ Q)

variable [Finite α] [MeasurableSingletonClass α] {P Q : Measure α}

omit [Finite α] [MeasurableSingletonClass α] in
/-- The gain ratio of any finite alphabet is bounded by `maxGainRatio`. -/
lemma gainRatio_le_maxGainRatio [Finite γ] [MeasurableSingletonClass γ] [IsMarkovKernel ρ] :
    maxExpectedGain g k (ρ ∘ₘ P) / maxExpectedGain g k (ρ ∘ₘ Q) ≤ maxGainRatio g k P Q := by
  have := Fintype.ofFinite γ
  set e := Fintype.equivFin γ
  have he : Measurable e := measurable_of_finite _
  have := Kernel.IsMarkovKernel.map ρ he
  refine le_iSup_of_le (Fintype.card γ) (le_iSup₂_of_le (ρ.map e) inferInstance (le_of_eq ?_))
  rw [← Measure.map_comp _ _ he, ← Measure.map_comp _ _ he, maxExpectedGain_map,
    maxExpectedGain_map]

/-- Upper half of Theorem 6: for every nonnegative gain function, every `k` and every `U`, the
gain ratio is at most `exp D_∞(P ‖ Q) = max_x P(x) / Q(x)`. -/
lemma gainRatio_le_iSup_div [Finite γ] [MeasurableSingletonClass γ] [IsFiniteMeasure Q] :
    maxExpectedGain g k (ρ ∘ₘ P) / maxExpectedGain g k (ρ ∘ₘ Q) ≤ ⨆ x, P {x} / Q {x} := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite γ
  set R := ⨆ x, P {x} / Q {x}
  rcases eq_or_ne R ∞ with hR | hR
  · rw [hR]
    exact le_top
  refine ENNReal.div_le_of_le_mul (iSup₂_le fun π _ ↦ iSup_le fun hπ ↦ ?_)
  have hPQ (x : α) : P {x} ≤ R * Q {x} := by
    have hx : P {x} / Q {x} ≤ R := le_iSup (fun x ↦ P {x} / Q {x}) x
    rcases eq_or_ne (Q {x}) 0 with hQ | hQ
    · rw [hQ] at hx
      by_cases h : P {x} = 0
      · simp [h]
      · rw [ENNReal.div_zero h, top_le_iff] at hx
        exact absurd hx hR
    · calc P {x} = P {x} / Q {x} * Q {x} :=
            (ENNReal.div_mul_cancel hQ (measure_ne_top Q _)).symm
        _ ≤ R * Q {x} := by gcongr
  -- `P ≪ Q`, so guesses in the support of `P_U` lie in the support of `Q_U`.
  have hπQ : GuessesInSupport (ρ ∘ₘ Q) π := by
    refine measure_mono_null (t := {v | ∃ i, (ρ ∘ₘ P) {v i} = 0}) (fun v hv ↦ ?_) hπ
    obtain ⟨i, hi⟩ := hv
    refine ⟨i, ?_⟩
    have h_le : (ρ ∘ₘ P) {v i} ≤ R * (ρ ∘ₘ Q) {v i} := by
      rw [comp_apply_singleton, comp_apply_singleton, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ ↦ ?_
      calc ρ x {v i} * P {x} ≤ ρ x {v i} * (R * Q {x}) := by gcongr; exact hPQ x
        _ = R * (ρ x {v i} * Q {x}) := by ring
    rw [hi, mul_zero] at h_le
    exact nonpos_iff_eq_zero.1 h_le
  calc ∫⁻ u, (g (hitProb π u).toReal : ℝ≥0∞) ∂(ρ ∘ₘ P)
      = ∑ u, (g (hitProb π u).toReal : ℝ≥0∞) * ∑ x, ρ x {u} * P {x} := by
        rw [lintegral_fintype]
        simp_rw [comp_apply_singleton]
    _ ≤ ∑ u, (g (hitProb π u).toReal : ℝ≥0∞) * ∑ x, ρ x {u} * (R * Q {x}) := by
        gcongr with u _ x _
        exact hPQ x
    _ = R * ∫⁻ u, (g (hitProb π u).toReal : ℝ≥0∞) ∂(ρ ∘ₘ Q) := by
        rw [lintegral_fintype]
        simp_rw [comp_apply_singleton, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
    _ ≤ R * maxExpectedGain g k (ρ ∘ₘ Q) := by
        gcongr
        exact le_iSup₂_of_le π inferInstance (le_iSup_of_le hπQ le_rfl)

/-- Lower half of Theorem 6, quantitative form. Fix `x₀`. Let `U` be one of two symbols `a`, `b`
(with probabilities `1 - η` and `η`) when `X = x₀`, and a uniform one of `m` symbols attached to
`X` otherwise ("shattering"). Under `P` an adversary can guess `a` with any success probability
`q` (putting the rest of its mass on `b`, so that it only guesses in the support of `P_U`), so
the gain is at least `(1 - η) P(x₀) sup g`; under `Q`, continuity of `g` at `0` makes the
shattered symbols worth little for large `m`, so the gain is at most `Q(x₀) sup g + c`. -/
lemma mul_iSup_le_maxGainRatio_mul [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hk : k ≠ 0)
    (hg0 : g 0 = 0) (hcont : ContinuousWithinAt (fun t ↦ (g t : ℝ)) (Icc 0 1) 0)
    (hS : (⨆ t ∈ Icc (0 : ℝ) 1, (g t : ℝ≥0∞)) ≠ ∞) (x₀ : α) {c : ℝ} (hc : 0 < c) :
    P {x₀} * (⨆ t ∈ Icc (0 : ℝ) 1, (g t : ℝ≥0∞)) ≤
      maxGainRatio g k P Q * (Q {x₀} * (⨆ t ∈ Icc (0 : ℝ) 1, (g t : ℝ≥0∞)) + ENNReal.ofReal c) +
        ENNReal.ofReal c := by
  classical
  have := Fintype.ofFinite α
  set S := ⨆ t ∈ Icc (0 : ℝ) 1, (g t : ℝ≥0∞)
  rcases eq_or_ne (P {x₀}) 0 with hP | hP
  · rw [hP, zero_mul]
    exact zero_le
  set c' := c / 2
  have hc' : 0 < c' := by positivity
  -- The weight `η` of the second symbol `b`, with `η S ≤ c'`.
  set η' := min (1 / 2) (c' / (S.toReal + 1))
  have hη'0 : 0 < η' := lt_min (by norm_num) (by positivity)
  have hη'1 : η' ≤ 1 / 2 := min_le_left _ _
  set η := ENNReal.ofReal η'
  have hη1 : η ≤ 1 := ENNReal.ofReal_le_one.2 (by linarith)
  have hη0 : η ≠ 0 := by simpa [η] using hη'0
  have h1η : 1 - η ≠ 0 := by
    have : η < 1 := (ENNReal.ofReal_lt_one).2 (by linarith)
    exact (tsub_pos_of_lt this).ne'
  have hηS : η * S ≤ ENNReal.ofReal c' := by
    rw [← ENNReal.ofReal_toReal hS, ← ENNReal.ofReal_mul hη'0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hS0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    calc η' * S.toReal ≤ c' / (S.toReal + 1) * S.toReal := by
          gcongr
          exact min_le_right _ _
      _ ≤ c' := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  set N := Fintype.card α
  have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos_iff.2 ⟨x₀⟩
  -- `g ≤ ε` near `0`, with `N ε = c' / 2`.
  set ε := c' / (2 * N)
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 hcont ε (by positivity)
  have hg_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (g t : ℝ≥0∞) ≤ ENNReal.ofReal ε + S * ENNReal.ofReal δ⁻¹ * ENNReal.ofReal t := by
    rcases lt_or_ge t δ with htδ | htδ
    · refine le_add_right ?_
      have := hδg ht (by simpa [abs_of_nonneg ht.1] using htδ)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by simpa [hg0, abs_of_nonneg] using this.le)
    · refine le_add_left ?_
      calc (g t : ℝ≥0∞) ≤ S := le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) ↦ (g t : ℝ≥0∞)) t ht
        _ = S * 1 := (mul_one S).symm
        _ ≤ S * ENNReal.ofReal δ⁻¹ * ENNReal.ofReal t := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          gcongr
          rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hδ]
          exact htδ
  -- The number `m ≥ 2` of shattered symbols.
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * S.toReal * k / (δ * c') + 2)
  have hm2 : 2 < m := by
    have : (0 : ℝ) ≤ 2 * S.toReal * k / (δ * c') := by positivity
    exact_mod_cast (by linarith : (2 : ℝ) < m)
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by simp; omega
  set j₀ : Fin m := ⟨0, by omega⟩
  set j₁ : Fin m := ⟨1, by omega⟩
  have hj : (x₀, j₀) ≠ (x₀, j₁) := by simp [j₀, j₁, Fin.ext_iff]
  -- The shattering randomization `ρ`.
  set w : α → α × Fin m → ℝ≥0∞ := fun x u ↦
    if x = x₀ then (if u = (x₀, j₀) then 1 - η else 0) + (if u = (x₀, j₁) then η else 0)
    else (if u.1 = x then (m : ℝ≥0∞)⁻¹ else 0)
  set ρ : Kernel α (α × Fin m) := Kernel.ofFunOfCountable fun x ↦ ∑ u, w x u • Measure.dirac u
  have hρ (x : α) (u : α × Fin m) : ρ x {u} = w x u := by
    rw [show ρ x = ∑ u, w x u • Measure.dirac (id u) from rfl,
      sum_smul_dirac_apply _ _ (measurableSet_singleton u)]
    simp
  have : IsMarkovKernel ρ := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hρ]
    by_cases hx : x = x₀
    · simp [w, hx, Finset.sum_add_distrib, tsub_add_cancel_of_le hη1]
    · simp only [w, hx, ite_false]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel hm0 (ENNReal.natCast_ne_top m)⟩⟩
  -- Under `P`, guessing `a = (x₀, j₀)` with probability `q` gains `(1 - η) P(x₀) g(q)`.
  have hPU (u : α × Fin m) : ρ x₀ {u} * P {x₀} ≤ (ρ ∘ₘ P) {u} := by
    rw [comp_apply_singleton]
    exact Finset.single_le_sum (f := fun x ↦ ρ x {u} * P {x}) (fun _ _ ↦ zero_le)
      (Finset.mem_univ x₀)
  have hρa : ρ x₀ {(x₀, j₀)} = 1 - η := by simp [hρ, w, hj]
  have hρb : ρ x₀ {(x₀, j₁)} = η := by simp [hρ, w, hj.symm]
  have hNum : (1 - η) * P {x₀} * S ≤ maxExpectedGain g k (ρ ∘ₘ P) := by
    rw [ENNReal.mul_iSup]
    refine iSup_le fun q ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hq ↦ ?_
    set π : Measure (Fin k → α × Fin m) :=
      ENNReal.ofReal q • Measure.dirac (fun _ ↦ (x₀, j₀)) +
        ENNReal.ofReal (1 - q) • Measure.dirac (fun _ ↦ (x₀, j₁))
    have : IsProbabilityMeasure π := ⟨by
      simp only [π, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add hq.1 (sub_nonneg.2 hq.2)]
      simp⟩
    have hπ : hitProb π (x₀, j₀) = ENNReal.ofReal q := by
      have hs : MeasurableSet {v : Fin k → α × Fin m | ∃ i, v i = (x₀, j₀)} :=
        (Set.toFinite _).measurableSet
      have hj : j₁ ≠ j₀ := by simp [j₀, j₁, Fin.ext_iff]
      rw [hitProb, add_apply, smul_apply, smul_apply,
        Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs]
      have hj' : j₁ ≠ j₀ := by simp [j₀, j₁, Fin.ext_iff]
      simp [Set.indicator, hj', show Nonempty (Fin k) from ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩]
    have hπsupp : GuessesInSupport (ρ ∘ₘ P) π := by
      have ha : (ρ ∘ₘ P) {(x₀, j₀)} ≠ 0 :=
        ((ENNReal.mul_pos h1η hP).trans_le (hρa ▸ hPU (x₀, j₀))).ne'
      have hb : (ρ ∘ₘ P) {(x₀, j₁)} ≠ 0 :=
        ((ENNReal.mul_pos hη0 hP).trans_le (hρb ▸ hPU (x₀, j₁))).ne'
      have hs : MeasurableSet {v : Fin k → α × Fin m | ∃ i, (ρ ∘ₘ P) {v i} = 0} :=
        (Set.toFinite _).measurableSet
      rw [GuessesInSupport, add_apply, smul_apply, smul_apply,
        Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs]
      simp [Set.indicator, ha, hb]
    refine le_iSup₂_of_le π this (le_iSup_of_le hπsupp ?_)
    calc (1 - η) * P {x₀} * g q
        = (g (hitProb π (x₀, j₀)).toReal : ℝ≥0∞) * (ρ x₀ {(x₀, j₀)} * P {x₀}) := by
          rw [hπ, ENNReal.toReal_ofReal hq.1, hρa]
          ring
      _ ≤ (g (hitProb π (x₀, j₀)).toReal : ℝ≥0∞) * (ρ ∘ₘ P) {(x₀, j₀)} := by
          gcongr
          exact hPU _
      _ ≤ ∫⁻ u, (g (hitProb π u).toReal : ℝ≥0∞) ∂(ρ ∘ₘ P) := by
          rw [lintegral_fintype]
          exact Finset.single_le_sum
            (f := fun u ↦ (g (hitProb π u).toReal : ℝ≥0∞) * (ρ ∘ₘ P) {u}) (fun _ _ ↦ zero_le)
            (Finset.mem_univ _)
  -- Under `Q`, every symbol other than `a` and `b` has probability at most `1 / m`.
  have hQU (u : α × Fin m) : (ρ ∘ₘ Q) {u} ≤
      (if u = (x₀, j₀) then Q {x₀} else 0) + (if u = (x₀, j₁) then η else 0) +
        (m : ℝ≥0∞)⁻¹ := by
    rw [comp_apply_singleton]
    simp_rw [hρ]
    calc ∑ x, w x u * Q {x}
        ≤ ∑ x, ((if x = x₀ then (if u = (x₀, j₀) then 1 else 0) else 0) +
            (if x = x₀ then (if u = (x₀, j₁) then η else 0) else 0) +
            (if u.1 = x then (m : ℝ≥0∞)⁻¹ else 0)) * Q {x} := by
          gcongr with x _
          by_cases hx : x = x₀
          · simp only [w, hx, ite_true]
            refine le_add_right (add_le_add ?_ le_rfl)
            split_ifs <;> simp
          · simp [w, hx]
      _ = (if u = (x₀, j₀) then Q {x₀} else 0) + (if u = (x₀, j₁) then η * Q {x₀} else 0) +
            (m : ℝ≥0∞)⁻¹ * Q {u.1} := by
          simp [add_mul, Finset.sum_add_distrib, ite_mul]
      _ ≤ (if u = (x₀, j₀) then Q {x₀} else 0) + (if u = (x₀, j₁) then η else 0) +
            (m : ℝ≥0∞)⁻¹ := by
          gcongr
          · split_ifs
            · exact mul_le_of_le_one_right zero_le prob_le_one
            · exact le_rfl
          · exact mul_le_of_le_one_right zero_le prob_le_one
  have hDen : maxExpectedGain g k (ρ ∘ₘ Q) ≤ Q {x₀} * S + ENNReal.ofReal c := by
    refine iSup₂_le fun π _ ↦ iSup_le fun _ ↦ ?_
    have hsum : ∑ u, (g (hitProb π u).toReal : ℝ≥0∞) ≤
        N * m * ENNReal.ofReal ε + S * ENNReal.ofReal δ⁻¹ * k := by
      calc ∑ u, (g (hitProb π u).toReal : ℝ≥0∞)
          ≤ ∑ u, (ENNReal.ofReal ε + S * ENNReal.ofReal δ⁻¹ * hitProb π u) := by
            gcongr with u _
            simpa [ENNReal.ofReal_toReal (hitProb_ne_top π u)] using
              hg_le _ (toReal_hitProb_mem_Icc π u)
        _ = N * m * ENNReal.ofReal ε + S * ENNReal.ofReal δ⁻¹ * ∑ u, hitProb π u := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp [N]
        _ ≤ N * m * ENNReal.ofReal ε + S * ENNReal.ofReal δ⁻¹ * k := by
            gcongr
            exact sum_hitProb_le π
    have h1 : (m : ℝ≥0∞)⁻¹ * (N * m * ENNReal.ofReal ε) = ENNReal.ofReal (c' / 2) := by
      rw [mul_comm (N : ℝ≥0∞), mul_assoc, ← mul_assoc _ (m : ℝ≥0∞),
        ENNReal.inv_mul_cancel hm0 (ENNReal.natCast_ne_top m), one_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      simp only [ε]
      field_simp
    have h2 : (m : ℝ≥0∞)⁻¹ * (S * ENNReal.ofReal δ⁻¹ * k) ≤ ENNReal.ofReal (c' / 2) := by
      have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      rw [ENNReal.le_ofReal_iff_toReal_le (by finiteness) (by positivity)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (inv_nonneg.2 hδ.le)]
      rw [inv_mul_le_iff₀ hm']
      have h3 : 2 * S.toReal * k / (δ * c') < m := by linarith
      rw [div_lt_iff₀ (by positivity)] at h3
      have : S.toReal * δ⁻¹ * k = (2 * S.toReal * k) / δ / 2 := by field_simp
      rw [this, div_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hSup (u : α × Fin m) : (g (hitProb π u).toReal : ℝ≥0∞) ≤ S :=
      le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) ↦ (g t : ℝ≥0∞)) _ (toReal_hitProb_mem_Icc π u)
    calc ∫⁻ u, (g (hitProb π u).toReal : ℝ≥0∞) ∂(ρ ∘ₘ Q)
        = ∑ u, (g (hitProb π u).toReal : ℝ≥0∞) * (ρ ∘ₘ Q) {u} := lintegral_fintype _
      _ ≤ ∑ u, (g (hitProb π u).toReal : ℝ≥0∞) *
            ((if u = (x₀, j₀) then Q {x₀} else 0) + (if u = (x₀, j₁) then η else 0) +
              (m : ℝ≥0∞)⁻¹) := by
          gcongr with u _
          exact hQU u
      _ = (g (hitProb π (x₀, j₀)).toReal : ℝ≥0∞) * Q {x₀} +
            (g (hitProb π (x₀, j₁)).toReal : ℝ≥0∞) * η +
            (m : ℝ≥0∞)⁻¹ * ∑ u, (g (hitProb π u).toReal : ℝ≥0∞) := by
          simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
      _ ≤ S * Q {x₀} + S * η +
            (m : ℝ≥0∞)⁻¹ * (N * m * ENNReal.ofReal ε + S * ENNReal.ofReal δ⁻¹ * k) := by
          gcongr
          · exact hSup _
          · exact hSup _
      _ ≤ Q {x₀} * S + ENNReal.ofReal c' + (ENNReal.ofReal (c' / 2) + ENNReal.ofReal (c' / 2)) := by
          rw [mul_add, h1, mul_comm S, mul_comm S η]
          gcongr
      _ = Q {x₀} * S + ENNReal.ofReal c := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, add_assoc,
            ← ENNReal.ofReal_add hc'.le hc'.le]
          congr 2
          simp only [c']
          ring
  -- Combine with the ratio bound.
  have hratio := gainRatio_le_maxGainRatio (g := g) (k := k) (P := P) (Q := Q) (ρ := ρ)
  rcases eq_or_ne (maxGainRatio g k P Q) ∞ with hR | hR
  · rw [hR, ENNReal.top_mul ((ENNReal.ofReal_pos.2 hc).trans_le le_add_self).ne', top_add]
    exact le_top
  have hDtop : maxExpectedGain g k (ρ ∘ₘ Q) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) hDen
  have hηPS : η * (P {x₀} * S) ≤ ENNReal.ofReal c :=
    calc η * (P {x₀} * S) ≤ η * S := by
          gcongr
          exact mul_le_of_le_one_left zero_le prob_le_one
      _ ≤ ENNReal.ofReal c' := hηS
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal (by simp only [c']; linarith)
  calc P {x₀} * S = (1 - η) * P {x₀} * S + η * (P {x₀} * S) := by
        rw [mul_assoc, ← add_mul, tsub_add_cancel_of_le hη1, one_mul]
    _ ≤ maxExpectedGain g k (ρ ∘ₘ P) + ENNReal.ofReal c := add_le_add hNum hηPS
    _ ≤ maxGainRatio g k P Q * maxExpectedGain g k (ρ ∘ₘ Q) + ENNReal.ofReal c := by
        gcongr
        exact (ENNReal.div_le_iff_le_mul (Or.inr hR) (Or.inl hDtop)).1 hratio
    _ ≤ maxGainRatio g k P Q * (Q {x₀} * S + ENNReal.ofReal c) + ENNReal.ofReal c := by gcongr

/-- **Theorem 6 of Kurri–Sankar–Kosut** (variational characterization of `D_∞`), multiplicative
form. Let `g : [0, 1] → [0, ∞)` satisfy `g(0) = 0`, be continuous at `0`, and have
`0 < sup_{[0, 1]} g < ∞`. Then for probability measures `P`, `Q` on a finite alphabet,
`sup_{P_{U|X}} (sup_{P_Û} E_{P_U}[g(P_Û(U))]) / (sup_{P_Û} E_{Q_U}[g(P_Û(U))]) = max_x P(x) / Q(x)`,
which is `exp D_∞(P ‖ Q)` (and `∞` unless `P ≪ Q`). The paper states this for a single guess,
`k = 1`; the proof works verbatim for any number of guesses `k ≥ 1`, which is what we state. -/
theorem maxGainRatio_eq_iSup_div [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hk : k ≠ 0)
    (hg0 : g 0 = 0) (hcont : ContinuousWithinAt (fun t ↦ (g t : ℝ)) (Icc 0 1) 0)
    (hpos : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0) (hbdd : BddAbove (g '' Icc 0 1)) :
    maxGainRatio g k P Q = ⨆ x, P {x} / Q {x} := by
  refine le_antisymm (iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ gainRatio_le_iSup_div) ?_
  set S := ⨆ t ∈ Icc (0 : ℝ) 1, (g t : ℝ≥0∞)
  set R := maxGainRatio g k P Q
  obtain ⟨C, hC⟩ := hbdd
  have hS : S ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top
    (iSup₂_le fun t ht ↦ ENNReal.coe_le_coe.2 (hC ⟨t, ht, rfl⟩))
  have hS0 : S ≠ 0 := by
    obtain ⟨t, ht, hgt⟩ := hpos
    exact ((ENNReal.coe_pos.2 (pos_iff_ne_zero.2 hgt)).trans_le
      (le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) ↦ (g t : ℝ≥0∞)) t ht)).ne'
  refine iSup_le fun x₀ ↦ ?_
  rcases eq_or_ne R ∞ with hR | hR
  · rw [hR]
    exact le_top
  have h {c : ℝ} (hc : 0 < c) :
      P {x₀} * S ≤ R * (Q {x₀} * S + ENNReal.ofReal c) + ENNReal.ofReal c :=
    mul_iSup_le_maxGainRatio_mul hk hg0 hcont hS x₀ hc
  -- Let `c → 0`: `P(x₀) S ≤ R Q(x₀) S`.
  have hPS : P {x₀} * S ≤ R * Q {x₀} * S := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hR1 : 0 < R.toReal + 1 := by positivity
    have hRε : R * ENNReal.ofReal (ε / (R.toReal + 1)) + ENNReal.ofReal (ε / (R.toReal + 1)) =
        ε := by
      have hR' : R + 1 = ENNReal.ofReal (R.toReal + 1) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hR,
          ENNReal.ofReal_one]
      rw [← add_one_mul, hR', ← ENNReal.ofReal_mul hR1.le, mul_div_cancel₀ _ hR1.ne',
        ENNReal.ofReal_coe_nnreal]
    calc P {x₀} * S ≤ R * (Q {x₀} * S + ENNReal.ofReal (ε / (R.toReal + 1))) +
          ENNReal.ofReal (ε / (R.toReal + 1)) := h (by positivity)
      _ = R * Q {x₀} * S + ε := by rw [mul_add, add_assoc, hRε, ← mul_assoc]
  rw [ENNReal.mul_le_mul_iff_left hS0 hS] at hPS
  exact ENNReal.div_le_of_le_mul hPS

end Variational

section Pointwise

variable [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- The posterior law `P_{X|Y=y}` of the input `X ∼ μ` given the output `Y = y` of the channel
`κ`, on a finite input alphabet. It is a probability measure when `P_Y(y) ≠ 0`. -/
noncomputable def posterior (μ : Measure α) (κ : Kernel α β) (y : β) : Measure α :=
  ((κ ∘ₘ μ) {y})⁻¹ • ∑ x, (κ x {y} * μ {x}) • Measure.dirac x

omit [MeasurableSingletonClass β] in
lemma posterior_apply_singleton (y : β) (x : α) :
    posterior μ κ y {x} = ((κ ∘ₘ μ) {y})⁻¹ * (κ x {y} * μ {x}) := by
  classical
  rw [posterior, smul_apply, show (∑ x, (κ x {y} * μ {x}) • Measure.dirac x) =
    ∑ x, (κ x {y} * μ {x}) • Measure.dirac (id x) from rfl,
    sum_smul_dirac_apply _ _ (measurableSet_singleton x)]
  simp

/-- The pointwise maximal g-leakage of Corollary 5 of Kurri–Sankar–Kosut, multiplicative form:
the supremum over `U` of the ratio of the maximal expected gains (with `k` guesses) of guessing
`U` after observing the outcome `Y = y` and without observation. -/
noncomputable def pointwiseMaxGLeakageRatio (g : ℝ → ℝ≥0) (k : ℕ) (μ : Measure α)
    (κ : Kernel α β) (y : β) : ℝ≥0∞ :=
  maxGainRatio g k (posterior μ κ y) μ

/-- The opportunistic maximal g-leakage of Definition 11 of Kurri–Sankar–Kosut, multiplicative
form: the sum over `y` of `P_Y(y)` times the pointwise ratio `pointwiseMaxGLeakageRatio`, so
that the adversary may pick the function `U` after seeing `Y = y`. Outcomes with `P_Y(y) = 0` carry
weight `0`, as in the paper's sum over `supp(Y)`. -/
noncomputable def oppMaxGLeakageRatio [Fintype β] (g : ℝ → ℝ≥0) (k : ℕ) (μ : Measure α)
    (κ : Kernel α β) : ℝ≥0∞ :=
  ∑ y, (κ ∘ₘ μ) {y} * pointwiseMaxGLeakageRatio g k μ κ y

/-- The maximal realizable g-leakage of Definition 12 of Kurri–Sankar–Kosut, multiplicative form,
for a finite output alphabet: the largest pointwise ratio `pointwiseMaxGLeakageRatio` over the
outcomes `y ∈ supp P_Y`. -/
noncomputable def realMaxGLeakageRatio [Fintype β] (g : ℝ → ℝ≥0) (k : ℕ) (μ : Measure α)
    (κ : Kernel α β) : ℝ≥0∞ :=
  Finset.univ.sup fun y ↦ ⨆ (_ : (κ ∘ₘ μ) {y} ≠ 0), pointwiseMaxGLeakageRatio g k μ κ y

variable [IsProbabilityMeasure μ] [IsMarkovKernel κ]

lemma isProbabilityMeasure_posterior {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    IsProbabilityMeasure (posterior μ κ y) := ⟨by
  rw [← Finset.coe_univ, ← sum_measure_singleton]
  simp_rw [posterior_apply_singleton]
  rw [← Finset.mul_sum, ← comp_apply_singleton]
  exact ENNReal.inv_mul_cancel hy (measure_ne_top _ _)⟩


/-- **Corollary 5 of Kurri–Sankar–Kosut** (pointwise maximal g-leakage), multiplicative form: for a
gain function as in Theorem 6 and an outcome with `P_Y(y) > 0`, the pointwise maximal g-leakage
is `exp D_∞(P_{X|Y=y} ‖ P_X) = max_{x ∈ supp P_X} P_{Y|X}(y | x) / P_Y(y)`, whatever `g`. The
paper states this for `k = 1`. -/
theorem pointwiseMaxGLeakageRatio_eq (hk : k ≠ 0) (hg0 : g 0 = 0)
    (hcont : ContinuousWithinAt (fun t ↦ (g t : ℝ)) (Icc 0 1) 0)
    (hpos : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0) (hbdd : BddAbove (g '' Icc 0 1)) {y : β}
    (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxGLeakageRatio g k μ κ y = ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} / (κ ∘ₘ μ) {y} := by
  have := isProbabilityMeasure_posterior hy
  rw [pointwiseMaxGLeakageRatio, maxGainRatio_eq_iSup_div hk hg0 hcont hpos hbdd]
  refine iSup_congr fun x ↦ ?_
  by_cases hx : μ {x} = 0
  · simp [hx, posterior_apply_singleton]
  · rw [iSup_pos hx, posterior_apply_singleton, ← mul_assoc,
      ENNReal.mul_div_cancel_right hx (measure_ne_top μ _), ENNReal.div_eq_inv_mul]

/-- **Corollary 4 of Kurri–Sankar–Kosut**, (46), multiplicative form: for a gain function as in
Theorem 6, the opportunistic maximal g-leakage equals maximal leakage,
`exp L̃_g(X → Y) = ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x) = exp I_∞^S(X; Y)`. The paper states
this for `k = 1`. -/
theorem oppMaxGLeakageRatio_eq_maxLeakageSum [Fintype β] (hk : k ≠ 0) (hg0 : g 0 = 0)
    (hcont : ContinuousWithinAt (fun t ↦ (g t : ℝ)) (Icc 0 1) 0)
    (hpos : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0) (hbdd : BddAbove (g '' Icc 0 1)) :
    oppMaxGLeakageRatio g k μ κ = maxLeakageSum μ κ := by
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · rw [hy, zero_mul]
    refine (iSup₂_le fun x hx ↦ ?_).antisymm' zero_le
    have : κ x {y} * μ {x} = 0 := by
      rw [comp_apply_singleton] at hy
      exact (Finset.sum_eq_zero_iff.1 hy) x (Finset.mem_univ x)
    exact ((mul_eq_zero.1 this).resolve_right hx).le
  · rw [pointwiseMaxGLeakageRatio_eq hk hg0 hcont hpos hbdd hy, ENNReal.mul_iSup]
    refine iSup_congr fun x ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun _ ↦ ?_
    exact ENNReal.mul_div_cancel hy (measure_ne_top _ _)

/-- **Corollary 4 of Kurri–Sankar–Kosut**, (47), multiplicative form: for a gain function as in
Theorem 6 and a finite output alphabet, the maximal realizable g-leakage (Definition 12) is
`max_{y ∈ supp P_Y} max_{x ∈ supp P_X} P_{Y|X}(y | x) / P_Y(y)`, which for finite alphabets is
`exp D_∞(P_{XY} ‖ P_X × P_Y)`. The paper states this for `k = 1`. -/
theorem realMaxGLeakageRatio_eq [Fintype β] (hk : k ≠ 0) (hg0 : g 0 = 0)
    (hcont : ContinuousWithinAt (fun t ↦ (g t : ℝ)) (Icc 0 1) 0)
    (hpos : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0) (hbdd : BddAbove (g '' Icc 0 1)) :
    realMaxGLeakageRatio g k μ κ = Finset.univ.sup fun y ↦
      ⨆ (_ : (κ ∘ₘ μ) {y} ≠ 0) (x) (_ : μ {x} ≠ 0), κ x {y} / (κ ∘ₘ μ) {y} :=
  Finset.sup_congr rfl fun _ _ ↦ iSup_congr fun hy ↦
    pointwiseMaxGLeakageRatio_eq hk hg0 hcont hpos hbdd hy

end Pointwise

end InformationTheory
