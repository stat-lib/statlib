/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import Statlib.EValues.Product
public import Statlib.EValues.RIPr
public import Statlib.Divergence.Chernoff
public import Statlib.Divergence.Renyi.Variational

/-!
# E-variable divergences

We define analogues of the Rényi and Chernoff divergences between two sets of measures, built from
the maximal logarithmic utility of e-variables, `maxUtility R S logUtility`. For `α ∈ (0, 1)`,
the e-Rényi divergence of order `α` between `S` and `T` is
`(1 - α)⁻¹ * ⨅ R, (α * maxUtility R S logUtility + (1 - α) * maxUtility R T logUtility)`,
and the e-Chernoff divergence is `⨅ R, max (maxUtility R S logUtility) (maxUtility R T logUtility)`,
where the infima are over probability measures `R`. For a probability measure `P`,
`maxUtility R {P} logUtility` is the Kullback-Leibler divergence of `R` from `P`
(`maxUtility_singleton_eq_klDiv`), and for singletons these formulas are the variational
characterizations of the Rényi divergence and of the Chernoff information.

They share the properties of the classical divergences: they satisfy a data processing inequality,
the e-Rényi divergence is additive on products, and the e-Chernoff divergence is subadditive.

## Main definitions

* `erenyiDiv α S T`: the e-Rényi divergence of order `α` between two sets of measures `S` and `T`.
* `echernoffDiv S T`: the e-Chernoff divergence between two sets of measures `S` and `T`.

## Main statements

* `erenyiDiv_comp_le`, `echernoffDiv_comp_le`: data processing inequalities for Markov kernels.
* `erenyiDiv_prod`: the e-Rényi divergence between sets of product measures is the sum of the
  e-Rényi divergences.
* `echernoffDiv_prod_le`: the e-Chernoff divergence between sets of product measures is at most the
  sum of the e-Chernoff divergences.
* `one_sub_mul_erenyiDiv_le_echernoffDiv`: `(1 - α) * erenyiDiv α S T ≤ echernoffDiv S T`.
* `erenyiDiv_singleton`, `echernoffDiv_singleton`: for probability measures `P` and `Q`,
  `erenyiDiv α {P} {Q} = renyiDiv α P Q` for `α ∈ (0, 1)` and
  `echernoffDiv {P} {Q} = chernoffDiv 1 P Q`.
* `erenyiDiv_eq_two_mul_echernoffDiv_of_involutive`: if `T` is the image of `S` by a measurable
  involution, the e-Rényi divergence of order `1/2` is twice the e-Chernoff divergence.

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014), for the variational formula
  `(1 - α) * D_α(P, Q) = ⨅ R, (α * KL(R, P) + (1 - α) * KL(R, Q))` that `erenyiDiv` generalizes.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {S T : Set (Measure 𝓧)} {α : ℝ≥0∞}

/-- The e-Rényi divergence of order `α` between two sets of measures `S` and `T`: the infimum over
probability measures `R` of `α * maxUtility R S logUtility + (1 - α) * maxUtility R T logUtility`,
divided by `1 - α`. It is meant for `α ∈ (0, 1)`: for `α ≥ 1`, `1 - α = 0` in `ℝ≥0∞`, and
`erenyiDiv 0 S T = ⨅ R, maxUtility R T logUtility` is `0` as soon as `T` contains a probability
measure, unlike the Rényi divergence of order `0`.

If the measures of `S` and `T` have mass at most one, the maximal logarithmic utilities are
nonnegative (`maxUtility_nonneg`), so `EReal.toENNReal` does not truncate. -/
noncomputable
def erenyiDiv (α : ℝ≥0∞) (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  (1 - α)⁻¹ * ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    α * (maxUtility R S logUtility).toENNReal + (1 - α) * (maxUtility R T logUtility).toENNReal

/-- The e-Chernoff divergence between two sets of measures `S` and `T`: the infimum over
probability measures `R` of the maximum of `maxUtility R S logUtility` and
`maxUtility R T logUtility`. -/
noncomputable
def echernoffDiv (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal

lemma erenyiDiv_empty_left (hα : α ≠ 0) : erenyiDiv α ∅ T = ⊤ := by
  have h_top (R : Measure 𝓧) [IsProbabilityMeasure R] :
      α * (maxUtility R ∅ logUtility).toENNReal + (1 - α) * (maxUtility R T logUtility).toENNReal
        = ⊤ := by
    simp [hα]
  rw [erenyiDiv, iInf₂_eq_top.mpr fun R hR ↦ @h_top R hR, ENNReal.mul_top (by simp)]

lemma erenyiDiv_empty_right (hα : α < 1) : erenyiDiv α S ∅ = ⊤ := by
  have h_top (R : Measure 𝓧) [IsProbabilityMeasure R] :
      α * (maxUtility R S logUtility).toENNReal + (1 - α) * (maxUtility R ∅ logUtility).toENNReal
        = ⊤ := by
    simp [(tsub_pos_of_lt hα).ne']
  rw [erenyiDiv, iInf₂_eq_top.mpr fun R hR ↦ @h_top R hR, ENNReal.mul_top (by simp)]

@[simp]
lemma erenyiDiv_empty : erenyiDiv α (∅ : Set (Measure 𝓧)) ∅ = ⊤ := by
  rcases eq_or_ne α 0 with rfl | hα
  · exact erenyiDiv_empty_right zero_lt_one
  · exact erenyiDiv_empty_left hα

@[simp]
lemma echernoffDiv_empty_left : echernoffDiv ∅ T = ⊤ := by
  have h_top (R : Measure 𝓧) [IsProbabilityMeasure R] :
      max (maxUtility R ∅ logUtility).toENNReal (maxUtility R T logUtility).toENNReal = ⊤ := by
    simp
  exact iInf₂_eq_top.mpr fun R hR ↦ @h_top R hR

lemma echernoffDiv_comm : echernoffDiv S T = echernoffDiv T S := by
  simp_rw [echernoffDiv, max_comm]

@[simp]
lemma echernoffDiv_empty_right : echernoffDiv S ∅ = ⊤ := by
  rw [echernoffDiv_comm, echernoffDiv_empty_left]

lemma erenyiDiv_anti {S₁ S₂ T₁ T₂ : Set (Measure 𝓧)} (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    erenyiDiv α S₂ T₂ ≤ erenyiDiv α S₁ T₁ := by
  unfold erenyiDiv
  gcongr
  · exact maxUtility_anti hS
  · exact maxUtility_anti hT

lemma echernoffDiv_anti {S₁ S₂ T₁ T₂ : Set (Measure 𝓧)} (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    echernoffDiv S₂ T₂ ≤ echernoffDiv S₁ T₁ := by
  unfold echernoffDiv
  gcongr
  · exact maxUtility_anti hS
  · exact maxUtility_anti hT

/-- The e-Chernoff divergence dominates the e-Rényi divergences, scaled by `1 - α`. This is one
inequality of the classical identity between the Chernoff information and the supremum over `α`
of `(1 - α) * D_α`. -/
lemma one_sub_mul_erenyiDiv_le_echernoffDiv : (1 - α) * erenyiDiv α S T ≤ echernoffDiv S T := by
  rcases le_or_gt 1 α with hα | hα
  · simp [tsub_eq_zero_of_le hα]
  rw [erenyiDiv, ← mul_assoc, ENNReal.mul_inv_cancel (tsub_pos_of_lt hα).ne' (by simp), one_mul]
  refine iInf₂_mono fun R _ ↦ ?_
  set a := (maxUtility R S logUtility).toENNReal
  set b := (maxUtility R T logUtility).toENNReal
  calc α * a + (1 - α) * b
  _ ≤ α * max a b + (1 - α) * max a b := by
    gcongr
    exacts [le_max_left _ _, le_max_right _ _]
  _ = max a b := by rw [← add_mul, add_tsub_cancel_of_le hα.le, one_mul]

/-! ### Singletons

For probability measures, `maxUtility R {P} logUtility = klDiv R P`
(`maxUtility_singleton_eq_klDiv`), so the e-divergences between singletons are the classical
divergences. -/

/-- For probability measures `P`, `Q` and `α ∈ (0, 1)`, the e-Rényi divergence between `{P}` and
`{Q}` is the Rényi divergence of order `α`. This is the variational formula
`(1 - α) * Rα(P, Q) = ⨅ R, (α * KL(R, P) + (1 - α) * KL(R, Q))` (`mul_renyiDiv_eq_iInf_klDiv`). -/
theorem erenyiDiv_singleton (P Q : Measure 𝓧) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hα0 : 0 < α) (hα1 : α < 1) :
    erenyiDiv α {P} {Q} = renyiDiv α.toReal P Q := by
  obtain ⟨a, ha0, rfl⟩ : ∃ a : ℝ, 0 ≤ a ∧ α = ENNReal.ofReal a :=
    ⟨α.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hα1.ne_top).symm⟩
  have ha1 : a < 1 := ENNReal.ofReal_lt_one.mp hα1
  have h1α : 1 - ENNReal.ofReal a = ENNReal.ofReal (1 - a) := by
    rw [ENNReal.ofReal_sub _ ha0, ENNReal.ofReal_one]
  have h_inf : ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      ENNReal.ofReal a * (maxUtility R {P} logUtility).toENNReal
        + ENNReal.ofReal (1 - a) * (maxUtility R {Q} logUtility).toENNReal
      = ENNReal.ofReal (1 - a) * renyiDiv a P Q := by
    rw [mul_renyiDiv_eq_iInf_klDiv (ENNReal.ofReal_pos.mp hα0) ha1]
    refine iInf_congr fun R ↦ iInf_congr fun _ ↦ ?_
    rw [maxUtility_singleton_eq_klDiv, maxUtility_singleton_eq_klDiv, EReal.toENNReal_coe,
      EReal.toENNReal_coe]
  rw [erenyiDiv, ENNReal.toReal_ofReal ha0, h1α, h_inf,
    ENNReal.inv_mul_cancel_left (ENNReal.ofReal_pos.mpr (sub_pos.mpr ha1)).ne'
      ENNReal.ofReal_ne_top]

/-- For probability measures `P` and `Q`, the e-Chernoff divergence between `{P}` and `{Q}` is the
Chernoff information `chernoffDiv 1 P Q = ⨅ R, max (KL(R, P)) (KL(R, Q))`. -/
theorem echernoffDiv_singleton (P Q : Measure 𝓧) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    echernoffDiv {P} {Q} = chernoffDiv 1 P Q := by
  rw [echernoffDiv, chernoffDiv_one]
  refine iInf_congr fun R ↦ iInf_congr fun _ ↦ ?_
  rw [maxUtility_singleton_eq_klDiv, maxUtility_singleton_eq_klDiv, EReal.toENNReal_coe,
    EReal.toENNReal_coe]

/-! ### Data processing inequalities -/

/-- Data processing inequality for the e-Rényi divergence with a Markov kernel. -/
lemma erenyiDiv_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    erenyiDiv α {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T} ≤ erenyiDiv α S T := by
  unfold erenyiDiv
  gcongr 1
  refine le_iInf₂ fun R hR ↦ iInf₂_le_of_le (κ ∘ₘ R) inferInstance ?_
  gcongr <;> exact maxUtility_comp_le R κ

/-- Data processing inequality for the e-Rényi divergence with a measurable function. -/
lemma erenyiDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    erenyiDiv α {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ erenyiDiv α S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact erenyiDiv_comp_le (Kernel.deterministic f hf)

/-- Data processing inequality for the e-Chernoff divergence with a Markov kernel. -/
lemma echernoffDiv_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    echernoffDiv {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T} ≤ echernoffDiv S T := by
  refine le_iInf₂ fun R hR ↦ iInf₂_le_of_le (κ ∘ₘ R) inferInstance ?_
  gcongr <;> exact maxUtility_comp_le R κ

/-- Data processing inequality for the e-Chernoff divergence with a measurable function. -/
lemma echernoffDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    echernoffDiv {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ echernoffDiv S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact echernoffDiv_comp_le (Kernel.deterministic f hf)

/-! ### Products -/

private lemma toENNReal_maxUtility_add_maxUtility {R₁ : Measure 𝓧} {R₂ : Measure 𝓨}
    {S : Set (Measure 𝓧)} {T : Set (Measure 𝓨)} (hS : ∀ μ ∈ S, μ Set.univ ≤ 1)
    (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    (maxUtility R₁ S logUtility + maxUtility R₂ T logUtility).toENNReal
      = (maxUtility R₁ S logUtility).toENNReal + (maxUtility R₂ T logUtility).toENNReal :=
  EReal.toENNReal_add (maxUtility_nonneg _ hS) (maxUtility_nonneg _ hT)

/-- The sum of two e-Rényi divergences, as an infimum over pairs of probability measures. -/
private lemma erenyiDiv_add_eq_iInf {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, μ Set.univ ≤ 1) (hS₂ : ∀ μ ∈ S₂, μ Set.univ ≤ 1)
    (hT₁ : ∀ μ ∈ T₁, μ Set.univ ≤ 1) (hT₂ : ∀ μ ∈ T₂, μ Set.univ ≤ 1) :
    erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ = (1 - α)⁻¹ * ⨅ (R₁ : Measure 𝓧)
      (_ : IsProbabilityMeasure R₁) (R₂ : Measure 𝓨) (_ : IsProbabilityMeasure R₂),
      α * (maxUtility R₁ S₁ logUtility + maxUtility R₂ T₁ logUtility).toENNReal
        + (1 - α) * (maxUtility R₁ S₂ logUtility + maxUtility R₂ T₂ logUtility).toENNReal := by
  rw [erenyiDiv, erenyiDiv, ← mul_add, ENNReal.iInf₂_add]
  simp_rw [ENNReal.add_iInf₂, toENNReal_maxUtility_add_maxUtility hS₁ hT₁,
    toENNReal_maxUtility_add_maxUtility hS₂ hT₂]
  refine congrArg _ (iInf_congr fun R₁ ↦ iInf_congr fun _ ↦ iInf_congr fun R₂ ↦
    iInf_congr fun _ ↦ ?_)
  ring

/-- The e-Rényi divergence between sets of product measures is the sum of the e-Rényi
divergences. -/
theorem erenyiDiv_prod {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, μ Set.univ ≤ 1) (hS₂ : ∀ μ ∈ S₂, μ Set.univ ≤ 1)
    (hT₁ : ∀ μ ∈ T₁, μ Set.univ ≤ 1) (hT₂ : ∀ μ ∈ T₂, μ Set.univ ≤ 1) :
    erenyiDiv α (Set.image2 Measure.prod S₁ T₁) (Set.image2 Measure.prod S₂ T₂)
      = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  rw [erenyiDiv_add_eq_iInf hS₁ hS₂ hT₁ hT₂, erenyiDiv]
  congr 1
  refine le_antisymm ?_ ?_
  · -- the product of two probability measures is a probability measure on the product
    refine le_iInf₂ fun R₁ _ ↦ le_iInf₂ fun R₂ _ ↦ iInf₂_le_of_le (R₁.prod R₂) inferInstance ?_
    rw [maxUtility_prod_eq_add _ _ hS₁ hT₁, maxUtility_prod_eq_add _ _ hS₂ hT₂]
  -- replacing a measure on the product by its marginals does not increase the objective
  refine le_iInf₂ fun R _ ↦ iInf₂_le_of_le R.fst inferInstance (iInf₂_le_of_le R.snd
    inferInstance ?_)
  gcongr
  · exact maxUtility_fst_add_maxUtility_snd_le R hS₁ hT₁
  · exact maxUtility_fst_add_maxUtility_snd_le R hS₂ hT₂

/-- The e-Chernoff divergence between sets of product measures is at most the sum of the
e-Chernoff divergences. -/
theorem echernoffDiv_prod_le {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, μ Set.univ ≤ 1) (hS₂ : ∀ μ ∈ S₂, μ Set.univ ≤ 1)
    (hT₁ : ∀ μ ∈ T₁, μ Set.univ ≤ 1) (hT₂ : ∀ μ ∈ T₂, μ Set.univ ≤ 1) :
    echernoffDiv (Set.image2 Measure.prod S₁ T₁) (Set.image2 Measure.prod S₂ T₂)
      ≤ echernoffDiv S₁ S₂ + echernoffDiv T₁ T₂ := by
  unfold echernoffDiv
  rw [ENNReal.iInf₂_add]
  simp_rw [ENNReal.add_iInf₂]
  refine le_iInf₂ fun R₁ _ ↦ le_iInf₂ fun R₂ _ ↦ iInf₂_le_of_le (R₁.prod R₂) inferInstance ?_
  rw [maxUtility_prod_eq_add _ _ hS₁ hT₁, maxUtility_prod_eq_add _ _ hS₂ hT₂,
    toENNReal_maxUtility_add_maxUtility hS₁ hT₁, toENNReal_maxUtility_add_maxUtility hS₂ hT₂]
  exact max_add_add_le_max_add_max

/-! ### Sets of measures exchanged by an involution -/

section Involutive

variable {φ : 𝓧 → 𝓧}

/-- If a measurable involution `φ` maps `S` to `T`, then for every probability measure `R`, the
`φ`-invariant probability measure `2⁻¹ • (R + R.map φ)` has a maximal utility for `S` at most the
average of the maximal utilities of `R` for `S` and `T`. -/
private lemma exists_map_eq_self_maxUtility_le (hφ : Measurable φ)
    (hφ_inv : Function.Involutive φ) (hφST : {μ.map φ | μ ∈ S} = T) (R : Measure 𝓧)
    [IsProbabilityMeasure R] :
    ∃ R' : Measure 𝓧, IsProbabilityMeasure R' ∧ R'.map φ = R' ∧
      (maxUtility R' S logUtility).toENNReal
        ≤ 2⁻¹ * (maxUtility R S logUtility).toENNReal
          + 2⁻¹ * (maxUtility R T logUtility).toENNReal := by
  refine ⟨(2 : ℝ≥0∞)⁻¹ • R + (2 : ℝ≥0∞)⁻¹ • R.map φ, ⟨?_⟩, ?_, ?_⟩
  · simp [ENNReal.inv_two_add_inv_two]
  · rw [Measure.map_add _ _ hφ, Measure.map_smul _ hφ.aemeasurable,
      Measure.map_smul _ hφ.aemeasurable, Measure.map_map hφ hφ, hφ_inv.comp_self, Measure.map_id,
      add_comm]
  -- convexity of the maximal utility in the measure
  have h_conv := (convexOn_maxUtility S (U := logUtility)).2 (Set.mem_univ R)
    (Set.mem_univ (R.map φ)) zero_le zero_le ENNReal.inv_two_add_inv_two
  dsimp only at h_conv
  rw [← maxUtility_involutive _ _ hφ hφ_inv, hφST] at h_conv
  refine (EReal.toENNReal_le_toENNReal h_conv).trans ?_
  simp_rw [EReal.smul_ennreal_eq_mul]
  refine EReal.toENNReal_add_le.trans_eq ?_
  rw [EReal.toENNReal_mul (by positivity), EReal.toENNReal_mul (by positivity),
    EReal.toENNReal_coe]

/-- If a measurable involution maps `S` to `T`, the e-Rényi divergence of order `1/2` between `S`
and `T` is an infimum over invariant probability measures. -/
lemma erenyiDiv_inv_two_eq_iInf_of_involutive (hφ : Measurable φ) (hφ_inv : Function.Involutive φ)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    erenyiDiv 2⁻¹ S T = 2 * ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
      (maxUtility R S logUtility).toENNReal := by
  rw [erenyiDiv, ENNReal.one_sub_inv_two, inv_inv]
  congr 1
  refine le_antisymm (le_iInf₂ fun R hR ↦ le_iInf fun hRφ ↦ ?_) (le_iInf₂ fun R hR ↦ ?_)
  · -- for an invariant measure, the maximal utilities for `S` and `T` are equal
    refine iInf₂_le_of_le R hR (le_of_eq ?_)
    rw [← hφST, maxUtility_involutive _ _ hφ hφ_inv, hRφ, ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]
  · obtain ⟨R', hR', hR'φ, h_le⟩ := exists_map_eq_self_maxUtility_le hφ hφ_inv hφST R
    exact iInf₂_le_of_le R' hR' (iInf_le_of_le hR'φ h_le)

/-- If a measurable involution maps `S` to `T`, the e-Chernoff divergence between `S` and `T` is
an infimum over invariant probability measures. -/
lemma echernoffDiv_eq_iInf_of_involutive (hφ : Measurable φ) (hφ_inv : Function.Involutive φ)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    echernoffDiv S T = ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
      (maxUtility R S logUtility).toENNReal := by
  refine le_antisymm (le_iInf₂ fun R hR ↦ le_iInf fun hRφ ↦ ?_) (le_iInf₂ fun R hR ↦ ?_)
  · -- for an invariant measure, the maximal utilities for `S` and `T` are equal
    refine iInf₂_le_of_le R hR (le_of_eq ?_)
    rw [← hφST, maxUtility_involutive _ _ hφ hφ_inv, hRφ, max_self]
  · obtain ⟨R', hR', hR'φ, h_le⟩ := exists_map_eq_self_maxUtility_le hφ hφ_inv hφST R
    refine iInf₂_le_of_le R' hR' (iInf_le_of_le hR'φ (h_le.trans ?_))
    set a := (maxUtility R S logUtility).toENNReal
    set b := (maxUtility R T logUtility).toENNReal
    calc 2⁻¹ * a + 2⁻¹ * b
    _ ≤ 2⁻¹ * max a b + 2⁻¹ * max a b := by
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]
    _ = max a b := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- If a measurable involution maps `S` to `T`, the e-Rényi divergence of order `1/2` between `S`
and `T` is twice their e-Chernoff divergence. -/
theorem erenyiDiv_eq_two_mul_echernoffDiv_of_involutive (hφ : Measurable φ)
    (hφ_inv : Function.Involutive φ) (hφST : {μ.map φ | μ ∈ S} = T) :
    erenyiDiv 2⁻¹ S T = 2 * echernoffDiv S T := by
  rw [erenyiDiv_inv_two_eq_iInf_of_involutive hφ hφ_inv hφST,
    echernoffDiv_eq_iInf_of_involutive hφ hφ_inv hφST]

end Involutive

end ProbabilityTheory
