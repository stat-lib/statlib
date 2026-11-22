/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Statlib.ForMathlib.MeasureTheory.Constructions.Pi
public import Statlib.Testing.Binary

/-!
# Sample complexity

In a sequence of estimation problems `(P n)_{n ∈ ℕ}`, for example the problems in which the data
consists of `n` i.i.d. samples, the sample complexity at risk level `δ` is the smallest `n` such
that the Bayes risk of `P n` is at most `δ`.

## Main definitions

* `priorSampleComplexity ℓ P π δ`: the sample complexity of Bayesian estimation for the sequence of
  data generating kernels `P`, the loss `ℓ`, the prior `π` and the risk level `δ`.
* `binaryPriorSampleComplexity μ ν π δ`: the sample complexity of simple binary hypothesis testing
  between `μ` and `ν` from i.i.d. samples, with prior `π` and risk level `δ`.

## Main statements

* `div_le_priorSampleComplexity_of_forall`, `priorSampleComplexity_le_div_add_one_of_forall`: lower
  and upper bounds on the sample complexity from bounds on the Bayes risk at each `n`, of the form
  `x / D ≤ n(δ)` and `n(δ) ≤ x / D + 1`. They are the common form of the bounds of
  `Statlib.Testing.SampleComplexityBounds`.
* `bayesBinaryRisk_pi_le_of_le`: the Bayes binary risk between `μ^⊗m` and `ν^⊗m` is
  non-increasing in `m`.
* `binaryPriorSampleComplexity_le_iff`: `n(μ, ν, π, δ) ≤ n ↔ B_π(μ^⊗n, ν^⊗n) ≤ δ`.
* `binaryPriorSampleComplexity_eq_zero_iff`: no sample is needed if and only if
  `min (π {false}) (π {true}) ≤ δ`.

## Implementation notes

The sample complexity takes values in `ℕ∞`, with value `⊤` if the risk level `δ` is never reached.
It is defined for an arbitrary sequence of data generating kernels `P n : Kernel Θ (𝓩 n)`, not
only for `n` i.i.d. observations: the Bayes risk of `P n` need not be monotone in `n`, and the
characterization `n(δ) ≤ n ↔ R(P n) ≤ δ` holds under the hypothesis that it is
(`priorSampleComplexity_le_iff_of_antitone`).
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

section General

variable {Θ 𝓨 : Type*} {mΘ : MeasurableSpace Θ} [MeasurableSpace 𝓨] {𝓩 : ℕ → Type*}
  [∀ n, MeasurableSpace (𝓩 n)] {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : (n : ℕ) → Kernel Θ (𝓩 n)}
  {π : Measure Θ} {δ : ℝ≥0∞} {n : ℕ}

/-- The sample complexity of Bayesian estimation for a sequence of estimation problems with data
generating kernels `P n` (for example `n` i.i.d. observations), loss `ℓ`, prior `π` and risk
level `δ`: the smallest `n` such that the Bayes risk of `P n` is at most `δ`, or `⊤` if there is
no such `n`. -/
noncomputable
def priorSampleComplexity (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : (n : ℕ) → Kernel Θ (𝓩 n)) (π : Measure Θ)
    (δ : ℝ≥0∞) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : bayesRisk ℓ (P n) π ≤ δ), (n : ℕ∞)

lemma priorSampleComplexity_le (h : bayesRisk ℓ (P n) π ≤ δ) :
    priorSampleComplexity ℓ P π δ ≤ n :=
  iInf₂_le n h

lemma le_priorSampleComplexity_iff {m : ℕ∞} :
    m ≤ priorSampleComplexity ℓ P π δ ↔ ∀ n, bayesRisk ℓ (P n) π ≤ δ → m ≤ n := by
  simp [priorSampleComplexity]

lemma priorSampleComplexity_eq_top_iff :
    priorSampleComplexity ℓ P π δ = ⊤ ↔ ∀ n, δ < bayesRisk ℓ (P n) π := by
  simp [priorSampleComplexity, not_le]

/-- The infimum defining the sample complexity is attained. -/
lemma bayesRisk_le_of_priorSampleComplexity_eq (h : priorSampleComplexity ℓ P π δ = n) :
    bayesRisk ℓ (P n) π ≤ δ := by
  obtain ⟨m, hm⟩ : ∃ m, bayesRisk ℓ (P m) π ≤ δ := by
    by_contra! h_not
    simp [priorSampleComplexity_eq_top_iff.mpr h_not] at h
  have hs : {m | bayesRisk ℓ (P m) π ≤ δ}.Nonempty := ⟨m, hm⟩
  -- the sample complexity is the cast of the infimum of the nonempty set `hs` of natural numbers
  have h_eq : sInf {m | bayesRisk ℓ (P m) π ≤ δ} = n :=
    Nat.cast_inj.1 ((ENat.natCast_sInf hs).trans h)
  exact h_eq ▸ Nat.sInf_mem hs

/-- The sample complexity is `0` if and only if the risk level `δ` is reached without samples. -/
lemma priorSampleComplexity_eq_zero_iff :
    priorSampleComplexity ℓ P π δ = 0 ↔ bayesRisk ℓ (P 0) π ≤ δ := by
  refine ⟨fun h ↦ bayesRisk_le_of_priorSampleComplexity_eq (by simpa using h), fun h ↦ ?_⟩
  simpa using priorSampleComplexity_le (n := 0) h

/-- **Lower bound on the sample complexity**: if `x ≤ n * D` for every `n` such that the Bayes risk
of `P n` is at most `δ`, then `x / D` is at most the sample complexity. -/
lemma div_le_priorSampleComplexity_of_forall {x D : ℝ≥0∞}
    (h : ∀ n : ℕ, bayesRisk ℓ (P n) π ≤ δ → x ≤ n * D) :
    x / D ≤ priorSampleComplexity ℓ P π δ := by
  rcases eq_or_ne (priorSampleComplexity ℓ P π δ) ⊤ with htop | htop
  · simp [htop]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  rw [← hn, ENat.toENNReal_coe]
  exact ENNReal.div_le_of_le_mul (h n (bayesRisk_le_of_priorSampleComplexity_eq hn.symm))

/-- **Upper bound on the sample complexity**: if the Bayes risk of `P n` is at most `δ` for every
`n` such that `x ≤ n * D`, then the sample complexity is at most `x / D + 1`. -/
lemma priorSampleComplexity_le_div_add_one_of_forall {x D : ℝ≥0∞}
    (h : ∀ n : ℕ, x ≤ n * D → bayesRisk ℓ (P n) π ≤ δ) :
    priorSampleComplexity ℓ P π δ ≤ x / D + 1 := by
  rcases eq_or_ne (x / D) ∞ with hxD | hxD
  · simp [hxD]
  -- `N = ⌊x / D⌋ + 1` samples suffice
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ≥0∞) = x / D := ⟨_, ENNReal.coe_toNNReal hxD⟩
  have hN : priorSampleComplexity ℓ P π δ ≤ (⌊q⌋₊ + 1 : ℕ) := by
    refine priorSampleComplexity_le (h _ ?_)
    rw [← ENNReal.div_le_iff_le_mul (by simp) (by simp), ← hq]
    exact_mod_cast (Nat.lt_floor_add_one q).le
  calc (priorSampleComplexity ℓ P π δ : ℝ≥0∞)
  _ ≤ ((⌊q⌋₊ + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hN
  _ ≤ x / D + 1 := by
    rw [← hq, Nat.cast_add, Nat.cast_one]
    gcongr
    exact_mod_cast Nat.floor_le q.property

/-- If the Bayes risk is non-increasing in the number of samples, then the sample complexity is
at most `n` if and only if the Bayes risk of `P n` is at most `δ`. -/
lemma priorSampleComplexity_le_iff_of_antitone (hP : Antitone fun n ↦ bayesRisk ℓ (P n) π) :
    priorSampleComplexity ℓ P π δ ≤ n ↔ bayesRisk ℓ (P n) π ≤ δ := by
  refine ⟨fun h ↦ ?_, priorSampleComplexity_le⟩
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)
  rw [← hm, Nat.cast_le] at h
  exact (hP h).trans (bayesRisk_le_of_priorSampleComplexity_eq hm.symm)

end General

section Binary

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The Bayes binary risk between `μ^⊗m` and `ν^⊗m` is non-increasing in `m`. -/
lemma bayesBinaryRisk_pi_le_of_le (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (π : Measure Bool) {n m : ℕ} (hnm : n ≤ m) :
    bayesBinaryRisk (Measure.pi fun _ : Fin m ↦ μ) (Measure.pi fun _ : Fin m ↦ ν) π
      ≤ bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) π := by
  have hf : Measurable (fun x (i : Fin n) ↦ x (Fin.castLE hnm i) : (Fin m → 𝓧) → Fin n → 𝓧) := by
    fun_prop
  have h := bayesBinaryRisk_le_bayesBinaryRisk_comp (Measure.pi fun _ : Fin m ↦ μ)
    (Measure.pi fun _ : Fin m ↦ ν) π (Kernel.deterministic _ hf)
  rwa [Measure.deterministic_comp_eq_map, Measure.deterministic_comp_eq_map,
    Measure.pi_map_comp_of_injective _ (Fin.castLE_injective hnm),
    Measure.pi_map_comp_of_injective _ (Fin.castLE_injective hnm)] at h

/-- The sample complexity of simple binary hypothesis testing between `μ` and `ν` with prior `π`
and risk level `δ`: the smallest `n` such that the Bayes binary risk between the product measures
`μ^⊗n` and `ν^⊗n` is at most `δ`, or `⊤` if there is no such `n`. -/
noncomputable
def binaryPriorSampleComplexity (μ ν : Measure 𝓧) (π : Measure Bool) (δ : ℝ≥0∞) : ℕ∞ :=
  priorSampleComplexity zeroOneLoss
    (fun n ↦ Kernel.boolKernel (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν)) π δ

variable {μ ν : Measure 𝓧} {π : Measure Bool} {δ : ℝ≥0∞} {n : ℕ}

lemma binaryPriorSampleComplexity_le
    (h : bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) π ≤ δ) :
    binaryPriorSampleComplexity μ ν π δ ≤ n :=
  priorSampleComplexity_le h

lemma le_binaryPriorSampleComplexity_iff {m : ℕ∞} :
    m ≤ binaryPriorSampleComplexity μ ν π δ ↔ ∀ n,
      bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) π ≤ δ →
        m ≤ n :=
  le_priorSampleComplexity_iff

lemma div_le_binaryPriorSampleComplexity_of_forall {x D : ℝ≥0∞}
    (h : ∀ n : ℕ, bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) π
      ≤ δ → x ≤ n * D) :
    x / D ≤ binaryPriorSampleComplexity μ ν π δ :=
  div_le_priorSampleComplexity_of_forall h

lemma binaryPriorSampleComplexity_le_div_add_one_of_forall {x D : ℝ≥0∞}
    (h : ∀ n : ℕ, x ≤ n * D →
      bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) π ≤ δ) :
    binaryPriorSampleComplexity μ ν π δ ≤ x / D + 1 :=
  priorSampleComplexity_le_div_add_one_of_forall h

lemma bayesBinaryRisk_le_of_binaryPriorSampleComplexity_eq
    (h : binaryPriorSampleComplexity μ ν π δ = n) :
    bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) π ≤ δ :=
  bayesRisk_le_of_priorSampleComplexity_eq h

lemma binaryPriorSampleComplexity_le_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    binaryPriorSampleComplexity μ ν π δ ≤ n
      ↔ bayesBinaryRisk (Measure.pi fun _ : Fin n ↦ μ) (Measure.pi fun _ : Fin n ↦ ν) π ≤ δ :=
  priorSampleComplexity_le_iff_of_antitone fun _ _ h ↦ bayesBinaryRisk_pi_le_of_le μ ν π h

/-- The sample complexity of simple binary hypothesis testing is `0` if and only if
`min (π {false}) (π {true}) ≤ δ`. -/
lemma binaryPriorSampleComplexity_eq_zero_iff :
    binaryPriorSampleComplexity μ ν π δ = 0 ↔ min (π {false}) (π {true}) ≤ δ := by
  rw [binaryPriorSampleComplexity, priorSampleComplexity_eq_zero_iff, ← bayesBinaryRisk,
    Measure.pi_of_empty, Measure.pi_of_empty]
  simp

end Binary

end ProbabilityTheory
