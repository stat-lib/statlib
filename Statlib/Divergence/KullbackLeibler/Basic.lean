/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Statlib.Divergence.KullbackLeibler.KLDivFun
public import Statlib.Divergence.FDiv.Convex
public import Statlib.Divergence.FDiv.Measurable

import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence `klDiv` is defined in Mathlib (`InformationTheory.klDiv`).
This file relates it to the f-divergence for the divergence function `klDivFun`, and deduces
properties of `klDiv` from those of `fDiv`.

## Main statements

* `klDiv_eq_fDiv`: `klDiv μ ν = fDiv klDivFun μ ν` for finite measures `μ, ν`.
* `klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl`: `KL(μ, ν)` is the sum of the divergences
  between the restrictions to an event and to its complement.
* `measurable_klDiv`: measurability of `a ↦ klDiv (κ a) (η a)` for finite kernels `κ, η`.
* `klDiv_add_add_le`: `KL(μ₀ + μ₁, ν₀ + ν₁) ≤ KL(μ₀, ν₀) + KL(μ₁, ν₁)`.
* `klDiv_smul_add_smul_le`: **joint convexity** of the Kullback-Leibler divergence,
  `KL(a • μ₀ + b • μ₁, a • ν₀ + b • ν₁) ≤ a * KL(μ₀, ν₀) + b * KL(μ₁, ν₁)`.
* `klDiv_finsetSum_smul_le`, `klDiv_sum_smul_le`: joint convexity for finite mixtures,
  `KL(∑ i, c i • μ i, ∑ i, c i • ν i) ≤ ∑ i, c i * KL(μ i, ν i)`.
* `klDiv_finsetSum_smul_left_le`, `klDiv_sum_smul_left_le`,
  `klDiv_finsetSum_smul_right_le`, `klDiv_sum_smul_right_le`: convexity in each argument, for
  weights summing to `1`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- The Kullback-Leibler divergence between two finite measures is the f-divergence for the
divergence function `klDivFun`. -/
lemma klDiv_eq_fDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = fDiv klDivFun μ ν := by
  classical
  rw [klDiv_eq_lintegral_klFun, fDiv_of_derivAtTop_eq_top derivAtTop_klDivFun,
    lintegral_klDivFun_rnDeriv]

/-- The Kullback-Leibler divergence between two finite measures is the sum of the
Kullback-Leibler divergences between their restrictions to an event and to its complement. -/
lemma klDiv_eq_klDiv_restrict_add_klDiv_restrict_compl (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {s : Set α} (hs : MeasurableSet s) :
    klDiv μ ν = klDiv (μ.restrict s) (ν.restrict s) + klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) := by
  rw [klDiv_eq_fDiv, klDiv_eq_fDiv, klDiv_eq_fDiv,
    fDiv_eq_fDiv_restrict_add_fDiv_restrict_compl _ _ hs]

/-- For finite kernels `κ, η`, the function `a ↦ klDiv (κ a) (η a)` is measurable. -/
lemma measurable_klDiv {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ klDiv (κ a) (η a)) := by
  simp_rw [klDiv_eq_fDiv]
  exact measurable_fDiv _ _

/-- The Kullback-Leibler divergence of the sum of two pairs of measures is at most the sum of the
divergences. -/
theorem klDiv_add_add_le (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] :
    klDiv (μ₀ + μ₁) (ν₀ + ν₁) ≤ klDiv μ₀ ν₀ + klDiv μ₁ ν₁ := by
  simp_rw [klDiv_eq_fDiv]
  exact fDiv_add_add_le _ _ _ _

/-- **Joint convexity** of the Kullback-Leibler divergence. -/
theorem klDiv_smul_add_smul_le (μ₀ μ₁ ν₀ ν₁ : Measure α) [IsFiniteMeasure μ₀]
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (a b : ℝ≥0) :
    klDiv (a • μ₀ + b • μ₁) (a • ν₀ + b • ν₁) ≤ a * klDiv μ₀ ν₀ + b * klDiv μ₁ ν₁ := by
  simp_rw [klDiv_eq_fDiv]
  exact fDiv_smul_add_smul_le _ _ _ _ a b

section Mixture

variable {ι : Type*}

/-- **Joint convexity** of the Kullback-Leibler divergence, for a finite mixture indexed by a
`Finset`: for finite measures `μ i`, `ν i` and weights `c i ≥ 0`,
`klDiv (∑ i ∈ s, c i • μ i) (∑ i ∈ s, c i • ν i) ≤ ∑ i ∈ s, c i * klDiv (μ i) (ν i)`. -/
theorem klDiv_finsetSum_smul_le {μ ν : ι → Measure α} [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] (s : Finset ι) (c : ι → ℝ≥0) :
    klDiv (∑ i ∈ s, (c i : ℝ≥0∞) • μ i) (∑ i ∈ s, (c i : ℝ≥0∞) • ν i)
      ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv (μ i) (ν i) := by
  classical
  have h_fin (ρ : ι → Measure α) [∀ i, IsFiniteMeasure (ρ i)] (t : Finset ι) :
      IsFiniteMeasure (∑ i ∈ t, (c i : ℝ≥0∞) • ρ i) :=
    ⟨by simpa using ENNReal.sum_lt_top.mpr fun i _ ↦
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (ρ i) univ)⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have := h_fin μ s
    have := h_fin ν s
    have := h_fin μ {j}
    have := h_fin ν {j}
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    calc _ ≤ klDiv ((c j : ℝ≥0∞) • μ j) ((c j : ℝ≥0∞) • ν j)
          + klDiv (∑ i ∈ s, (c i : ℝ≥0∞) • μ i) (∑ i ∈ s, (c i : ℝ≥0∞) • ν i) := by
          have := klDiv_add_add_le (∑ i ∈ {j}, (c i : ℝ≥0∞) • μ i)
            (∑ i ∈ s, (c i : ℝ≥0∞) • μ i) (∑ i ∈ {j}, (c i : ℝ≥0∞) • ν i)
            (∑ i ∈ s, (c i : ℝ≥0∞) • ν i)
          simpa using this
      _ ≤ _ := by
        rw [klDiv_smul_same' ENNReal.coe_ne_top]
        gcongr

/-- **Joint convexity** of the Kullback-Leibler divergence, for a finite mixture: for finite
measures `μ i`, `ν i` and weights `c i ≥ 0`,
`klDiv (∑ i, c i • μ i) (∑ i, c i • ν i) ≤ ∑ i, c i * klDiv (μ i) (ν i)`. -/
theorem klDiv_sum_smul_le [Fintype ι] {μ ν : ι → Measure α} [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] (c : ι → ℝ≥0) :
    klDiv (∑ i, (c i : ℝ≥0∞) • μ i) (∑ i, (c i : ℝ≥0∞) • ν i)
      ≤ ∑ i, (c i : ℝ≥0∞) * klDiv (μ i) (ν i) :=
  klDiv_finsetSum_smul_le Finset.univ c

/-- **Convexity of the Kullback-Leibler divergence in its first argument**, for a finite mixture
indexed by a `Finset`: for finite measures `μ i`, `ν` and weights `c i ≥ 0` summing to `1`,
`klDiv (∑ i ∈ s, c i • μ i) ν ≤ ∑ i ∈ s, c i * klDiv (μ i) ν`. -/
theorem klDiv_finsetSum_smul_left_le {μ : ι → Measure α} {ν : Measure α}
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] {s : Finset ι} {c : ι → ℝ≥0}
    (hc : ∑ i ∈ s, c i = 1) :
    klDiv (∑ i ∈ s, (c i : ℝ≥0∞) • μ i) ν ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv (μ i) ν := by
  have h := klDiv_finsetSum_smul_le (μ := μ) (ν := fun _ ↦ ν) s c
  rwa [← Finset.sum_smul, ← ENNReal.ofNNReal_finsetSum, hc, ENNReal.coe_one, one_smul] at h

/-- **Convexity of the Kullback-Leibler divergence in its first argument**: for finite measures
`μ i`, `ν` and weights `c i ≥ 0` summing to `1`,
`klDiv (∑ i, c i • μ i) ν ≤ ∑ i, c i * klDiv (μ i) ν`. -/
theorem klDiv_sum_smul_left_le [Fintype ι] {μ : ι → Measure α} {ν : Measure α}
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] {c : ι → ℝ≥0} (hc : ∑ i, c i = 1) :
    klDiv (∑ i, (c i : ℝ≥0∞) • μ i) ν ≤ ∑ i, (c i : ℝ≥0∞) * klDiv (μ i) ν :=
  klDiv_finsetSum_smul_left_le hc

/-- **Convexity of the Kullback-Leibler divergence in its second argument**, for a finite mixture
indexed by a `Finset`: for finite measures `μ`, `ν i` and weights `c i ≥ 0` summing to `1`,
`klDiv μ (∑ i ∈ s, c i • ν i) ≤ ∑ i ∈ s, c i * klDiv μ (ν i)`. -/
theorem klDiv_finsetSum_smul_right_le {μ : Measure α} {ν : ι → Measure α} [IsFiniteMeasure μ]
    [∀ i, IsFiniteMeasure (ν i)] {s : Finset ι} {c : ι → ℝ≥0} (hc : ∑ i ∈ s, c i = 1) :
    klDiv μ (∑ i ∈ s, (c i : ℝ≥0∞) • ν i) ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv μ (ν i) := by
  have h := klDiv_finsetSum_smul_le (μ := fun _ ↦ μ) (ν := ν) s c
  rwa [← Finset.sum_smul, ← ENNReal.ofNNReal_finsetSum, hc, ENNReal.coe_one, one_smul] at h

/-- **Convexity of the Kullback-Leibler divergence in its second argument**: for finite measures
`μ`, `ν i` and weights `c i ≥ 0` summing to `1`,
`klDiv μ (∑ i, c i • ν i) ≤ ∑ i, c i * klDiv μ (ν i)`. -/
theorem klDiv_sum_smul_right_le [Fintype ι] {μ : Measure α} {ν : ι → Measure α}
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (ν i)] {c : ι → ℝ≥0} (hc : ∑ i, c i = 1) :
    klDiv μ (∑ i, (c i : ℝ≥0∞) • ν i) ≤ ∑ i, (c i : ℝ≥0∞) * klDiv μ (ν i) :=
  klDiv_finsetSum_smul_right_le hc

end Mixture

end ProbabilityTheory
