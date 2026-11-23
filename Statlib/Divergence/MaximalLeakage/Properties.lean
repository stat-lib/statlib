/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.Basic
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Properties of maximal leakage

This file proves the structural properties of maximal leakage `maxLeakage μ κ` on finite
alphabets listed in Lemma 1, Corollary 1 and Lemma 6 of Issa, Wagner and Kamath,
*An operational approach to information leakage*, IEEE Trans. Inf. Theory 66(3), 2020
(arXiv:1807.07878). Each statement comes in a multiplicative form about `maxLeakageSum` and,
where natural, in logarithmic form about `maxLeakage`.

Throughout, `X ∼ μ` is the channel input and `Y` is the output of `κ : Kernel α β`, so that
`Y ∼ κ ∘ₘ μ`.

## Main statements

* `maxLeakageSum_comp_le_comp`, `maxLeakage_comp_le_comp`: **data processing** for
  pre-processing: for a Markov chain `X - Y - Z`, `L(X → Z) ≤ L(Y → Z)`.
* `maxLeakageSum_le_card_support_comp`, `maxLeakage_le_log_card_support_comp`:
  `L(X → Y) ≤ log |supp Y|`.
* `maxLeakageSum_eq_one_iff`, `maxLeakage_eq_zero_iff`: `L(X → Y) = 0` iff all rows of the
  channel on the support of `X` coincide.
* `maxLeakage_eq_zero_iff_compProd_eq_prod`: `L(X → Y) = 0` iff `X` and `Y` are independent,
  i.e. iff the joint law `μ ⊗ₘ κ` is the product of its marginals.
* `maxLeakageSum_prod_le`, `maxLeakage_prod_le`: for the channel `κ ×ₖ η` producing two
  conditionally independent outputs `Y` and `Z` of `X`, `L(X → (Y, Z)) ≤ L(X → Y) + L(X → Z)`.
* `maxLeakageSum_parallelComp`, `maxLeakage_parallelComp`: for independent pairs
  `(X₁, Y₁)` and `(X₂, Y₂)`, `L((X₁, X₂) → (Y₁, Y₂)) = L(X₁ → Y₁) + L(X₂ → Y₂)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Auxiliary lemmas

The lemmas in this section are not specific to maximal leakage and are candidates for a
`ForMathlib` file. -/

section ForMathlib

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β}

/-- Over a finite intermediate alphabet, a composite kernel is a finite mixture. -/
lemma ProbabilityTheory.Kernel.comp_apply_eq_sum [Fintype β] [MeasurableSingletonClass β]
    (η : Kernel β γ) (κ : Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∑ b, η b s * κ a {b} := by
  rw [Kernel.comp_apply' _ _ _ hs, lintegral_fintype]

/-- If `a` is an atom of `μ` and `κ a` charges `s`, then so does `κ ∘ₘ μ`. -/
lemma MeasureTheory.Measure.comp_apply_ne_zero {s : Set β} (hs : MeasurableSet s) {a : α}
    (ha : μ {a} ≠ 0) (hκ : κ a s ≠ 0) :
    (κ ∘ₘ μ) s ≠ 0 := by
  have h_le : κ a s * μ {a} ≤ (κ ∘ₘ μ) s :=
    calc κ a s * μ {a} = ∫⁻ x in {a}, κ x s ∂μ :=
          (lintegral_singleton' (κ.measurable_coe hs) a).symm
      _ ≤ ∫⁻ x, κ x s ∂μ := setLIntegral_le_lintegral _ _
      _ = (κ ∘ₘ μ) s := (Measure.bind_apply hs κ.aemeasurable).symm
  exact (pos_iff_ne_zero.2 (mul_ne_zero hκ ha)).trans_le h_le |>.ne'

end ForMathlib

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β}

section PreProcessing

variable [MeasurableSingletonClass β]

/-- **Data processing** for maximal leakage under pre-processing, multiplicative form: for a
Markov chain `X - Y - Z` with `Y` the output of `κ` and `Z` the output of `η`,
`L(X → Z) ≤ L(Y → Z)`. -/
lemma maxLeakageSum_comp_le_comp [Finite β] [Fintype γ] [MeasurableSingletonClass γ]
    [IsMarkovKernel κ] (η : Kernel β γ) :
    maxLeakageSum μ (η ∘ₖ κ) ≤ maxLeakageSum (κ ∘ₘ μ) η := by
  have := Fintype.ofFinite β
  refine Finset.sum_le_sum fun z _ ↦ iSup₂_le fun x hx ↦ ?_
  set M := ⨆ (y) (_ : (κ ∘ₘ μ) {y} ≠ 0), η y {z}
  -- Every `y` reachable from an atom `x` of `μ` is an atom of `κ ∘ₘ μ`, so `η y {z} ≤ M`.
  have h_le (y : β) : η y {z} * κ x {y} ≤ M * κ x {y} := by
    obtain hy | hy := eq_or_ne (κ x {y}) 0
    · simp [hy]
    exact mul_le_mul_left
      (le_iSup₂ (f := fun y (_ : (κ ∘ₘ μ) {y} ≠ 0) ↦ η y {z}) y
        (Measure.comp_apply_ne_zero (measurableSet_singleton y) hx hy)) _
  calc (η ∘ₖ κ) x {z} = ∑ y, η y {z} * κ x {y} :=
        Kernel.comp_apply_eq_sum _ _ _ (measurableSet_singleton z)
    _ ≤ ∑ y, M * κ x {y} := Finset.sum_le_sum fun y _ ↦ h_le y
    _ = M := by
        rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]

/-- **Data processing** for maximal leakage under pre-processing: for a Markov chain
`X - Y - Z` with `Y` the output of `κ` and `Z` the output of `η`, `L(X → Z) ≤ L(Y → Z)`. -/
lemma maxLeakage_comp_le_comp [Finite β] [Fintype γ] [MeasurableSingletonClass γ]
    [IsMarkovKernel κ] (η : Kernel β γ) [IsMarkovKernel η] {x : α} (hx : μ {x} ≠ 0) :
    maxLeakage μ (η ∘ₖ κ) ≤ maxLeakage (κ ∘ₘ μ) η := by
  refine Real.log_le_log (by linarith [one_le_toReal_maxLeakageSum (κ := η ∘ₖ κ) hx]) ?_
  exact (ENNReal.toReal_le_toReal maxLeakageSum_ne_top maxLeakageSum_ne_top).2
    (maxLeakageSum_comp_le_comp η)

/-- Multiplicative form of `L(X → Y) ≤ log |supp Y|`: maximal leakage is at most the logarithm of
the number of output symbols that occur with positive probability. -/
lemma maxLeakageSum_le_card_support_comp [Fintype β] [IsMarkovKernel κ]
    [DecidablePred fun y : β ↦ (κ ∘ₘ μ) {y} ≠ 0] :
    maxLeakageSum μ κ ≤ (Finset.univ.filter fun y : β ↦ (κ ∘ₘ μ) {y} ≠ 0).card :=
  calc maxLeakageSum μ κ = maxLeakageSum μ (Kernel.id ∘ₖ κ) := by rw [Kernel.id_comp]
    _ ≤ maxLeakageSum (κ ∘ₘ μ) Kernel.id := maxLeakageSum_comp_le_comp _
    _ ≤ _ := maxLeakageSum_le_card_support

/-- Maximal leakage is at most the logarithm of the size of the support of the output:
`L(X → Y) ≤ log |supp Y|`. -/
lemma maxLeakage_le_log_card_support_comp [Fintype β] [IsMarkovKernel κ]
    [DecidablePred fun y : β ↦ (κ ∘ₘ μ) {y} ≠ 0] {x : α} (hx : μ {x} ≠ 0) :
    maxLeakage μ κ ≤ Real.log (Finset.univ.filter fun y : β ↦ (κ ∘ₘ μ) {y} ≠ 0).card := by
  refine Real.log_le_log (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx]) ?_
  simpa using (ENNReal.toReal_le_toReal maxLeakageSum_ne_top (ENNReal.natCast_ne_top _)).2
    maxLeakageSum_le_card_support_comp

end PreProcessing

section ZeroLeakage

variable [Fintype β] [MeasurableSingletonClass β] [IsMarkovKernel κ]

/-- Multiplicative form of `maxLeakage_eq_zero_iff`: given an atom of `μ`, `∑_y max_x κ x {y} = 1`
iff all rows of the channel on the support of `μ` coincide. -/
lemma maxLeakageSum_eq_one_iff {x₀ : α} (hx₀ : μ {x₀} ≠ 0) :
    maxLeakageSum μ κ = 1 ↔ ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → κ x = κ x' := by
  set M : β → ℝ≥0∞ := fun y ↦ ⨆ (x) (_ : μ {x} ≠ 0), κ x {y}
  have hM_ne_top (y : β) : M y ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup₂_le fun _ _ ↦ prob_le_one)
  have h_le {x : α} (hx : μ {x} ≠ 0) (y : β) : κ x {y} ≤ M y :=
    le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y}) x hx
  constructor
  · intro h
    -- A row on the support is dominated by `M` and has the same total mass `1 = ∑ y, M y`,
    -- so it equals `M`.
    have h_row {x : α} (hx : μ {x} ≠ 0) (y : β) : κ x {y} = M y := by
      have h_sum : ∑ y, (κ x {y}).toReal = ∑ y, (M y).toReal := by
        rw [← ENNReal.toReal_sum fun y _ ↦ measure_ne_top _ _,
          ← ENNReal.toReal_sum fun y _ ↦ hM_ne_top y, sum_measure_singleton, Finset.coe_univ,
          measure_univ]
        exact congrArg ENNReal.toReal h.symm
      refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (hM_ne_top y)).1 ?_
      exact (Finset.sum_eq_sum_iff_of_le fun y _ ↦ ENNReal.toReal_mono (hM_ne_top y) (h_le hx y)).1
        h_sum y (Finset.mem_univ y)
    intro x x' hx hx'
    exact Measure.ext_of_singleton fun y ↦ (h_row hx y).trans (h_row hx' y).symm
  · intro h
    have hM (y : β) : M y = κ x₀ {y} :=
      le_antisymm (iSup₂_le fun x hx ↦ by rw [h x x₀ hx hx₀]) (h_le hx₀ y)
    calc maxLeakageSum μ κ = ∑ y, κ x₀ {y} := Finset.sum_congr rfl fun y _ ↦ hM y
      _ = 1 := by rw [sum_measure_singleton, Finset.coe_univ, measure_univ]

/-- **Zero leakage**, characterization on atoms: `L(X → Y) = 0` iff the channel rows `κ x`
coincide for all atoms `x` of `μ`. This is independence of `X` and `Y` only when `μ` is purely
atomic; see `maxLeakage_eq_zero_iff_compProd_eq_prod` for the independence statement. If `μ`
has no atoms, both sides hold trivially. -/
lemma maxLeakage_eq_zero_iff :
    maxLeakage μ κ = 0 ↔ ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → κ x = κ x' := by
  by_cases h_atom : ∃ x, μ {x} ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h_atom
    rw [← maxLeakageSum_eq_one_iff hx₀, ← ENNReal.toReal_eq_one_iff]
    have h_pos : 0 < (maxLeakageSum μ κ).toReal := by
      linarith [one_le_toReal_maxLeakageSum (κ := κ) hx₀]
    exact ⟨Real.eq_one_of_pos_of_log_eq_zero h_pos, fun h ↦ by rw [maxLeakage, h, Real.log_one]⟩
  · -- Without atoms both sides hold trivially.
    push Not at h_atom
    simp [maxLeakage, maxLeakageSum, h_atom]

/-- **Zero leakage iff independence**: for a probability measure `μ` on a countable input
alphabet, `L(X → Y) = 0` iff `X` and `Y` are independent, i.e. iff the joint law `μ ⊗ₘ κ` is the
product of the marginals `μ` and `κ ∘ₘ μ`. -/
lemma maxLeakage_eq_zero_iff_compProd_eq_prod [Countable α] [IsProbabilityMeasure μ] :
    maxLeakage μ κ = 0 ↔ μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ) := by
  rw [maxLeakage_eq_zero_iff, ← Measure.compProd_const, Kernel.compProd_eq_iff,
    Filter.EventuallyEq, ae_iff_of_countable]
  simp only [Kernel.const_apply]
  constructor
  · intro h x hx
    have h_ae : ∀ᵐ x' ∂μ, κ x' = Kernel.const α (κ x) x' :=
      ae_iff_of_countable.2 fun x' hx' ↦ h x' x hx' hx
    rw [Measure.comp_congr h_ae, Measure.const_comp, measure_univ, one_smul]
  · intro h x x' hx hx'
    rw [h x hx, h x' hx']

end ZeroLeakage

section Composition

variable [Fintype β] [Fintype γ]

/-- **Composition** for maximal leakage, multiplicative form: if `Y` and `Z` are conditionally
independent outputs of `X`, through the channel `κ ×ₖ η`, then
`L(X → (Y, Z)) ≤ L(X → Y) + L(X → Z)`. -/
lemma maxLeakageSum_prod_le (η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    maxLeakageSum μ (κ ×ₖ η) ≤ maxLeakageSum μ κ * maxLeakageSum μ η := by
  calc maxLeakageSum μ (κ ×ₖ η)
      = ∑ y, ∑ z, ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} * η x {z} := by
        simp_rw [maxLeakageSum, Fintype.sum_prod_type, ← Set.singleton_prod_singleton,
          Kernel.prod_apply_prod]
    _ ≤ ∑ y, ∑ z, (⨆ (x) (_ : μ {x} ≠ 0), κ x {y}) * ⨆ (x) (_ : μ {x} ≠ 0), η x {z} := by
        refine Finset.sum_le_sum fun y _ ↦ Finset.sum_le_sum fun z _ ↦ ?_
        exact iSup₂_le fun x hx ↦ mul_le_mul'
          (le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y}) x hx)
          (le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ η x {z}) x hx)
    _ = maxLeakageSum μ κ * maxLeakageSum μ η := (Finset.sum_mul_sum _ _ _ _).symm

/-- **Composition** for maximal leakage: if `Y` and `Z` are conditionally independent outputs of
`X`, through the channel `κ ×ₖ η`, then `L(X → (Y, Z)) ≤ L(X → Y) + L(X → Z)`. -/
lemma maxLeakage_prod_le [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    [IsMarkovKernel κ] (η : Kernel α γ) [IsMarkovKernel η] {x : α} (hx : μ {x} ≠ 0) :
    maxLeakage μ (κ ×ₖ η) ≤ maxLeakage μ κ + maxLeakage μ η := by
  have hκ := one_le_toReal_maxLeakageSum (κ := κ) hx
  have hη := one_le_toReal_maxLeakageSum (κ := η) hx
  rw [maxLeakage, maxLeakage, maxLeakage, ← Real.log_mul (by positivity) (by positivity),
    ← ENNReal.toReal_mul]
  refine Real.log_le_log (by linarith [one_le_toReal_maxLeakageSum (κ := κ ×ₖ η) hx]) ?_
  exact (ENNReal.toReal_le_toReal maxLeakageSum_ne_top
    (ENNReal.mul_ne_top maxLeakageSum_ne_top maxLeakageSum_ne_top)).2 (maxLeakageSum_prod_le η)

end Composition

section Independent

variable {α₁ α₂ β₁ β₂ : Type*} {mα₁ : MeasurableSpace α₁} {mα₂ : MeasurableSpace α₂}
  {mβ₁ : MeasurableSpace β₁} {mβ₂ : MeasurableSpace β₂} [Fintype β₁] [Fintype β₂]
  {μ₁ : Measure α₁} {μ₂ : Measure α₂} {κ₁ : Kernel α₁ β₁} {κ₂ : Kernel α₂ β₂}

/-- **Additivity** of maximal leakage for independent pairs, multiplicative form: if `X₁ ∼ μ₁` and
`X₂ ∼ μ₂` are independent and fed through the independent channels `κ₁` and `κ₂`, then
`L((X₁, X₂) → (Y₁, Y₂)) = L(X₁ → Y₁) + L(X₂ → Y₂)`. -/
lemma maxLeakageSum_parallelComp [SFinite μ₂] [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    maxLeakageSum (μ₁.prod μ₂) (κ₁ ∥ₖ κ₂) = maxLeakageSum μ₁ κ₁ * maxLeakageSum μ₂ κ₂ := by
  -- The maximum over the product support of a product of rows is the product of the maxima.
  have h_sup (y₁ : β₁) (y₂ : β₂) :
      ⨆ (x) (_ : (μ₁.prod μ₂) {x} ≠ 0), (κ₁ ∥ₖ κ₂) x {(y₁, y₂)} =
        (⨆ (x₁) (_ : μ₁ {x₁} ≠ 0), κ₁ x₁ {y₁}) * ⨆ (x₂) (_ : μ₂ {x₂} ≠ 0), κ₂ x₂ {y₂} := by
    simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
    refine le_antisymm (iSup₂_le fun ⟨x₁, x₂⟩ hx ↦ ?_)
      (iSup₂_le fun x₁ hx₁ ↦ iSup₂_le fun x₂ hx₂ ↦ ?_)
    · rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_ne_zero_iff] at hx
      rw [← Set.singleton_prod_singleton, Kernel.parallelComp_apply_prod]
      exact le_iSup₂_of_le x₁ hx.1 (le_iSup₂_of_le x₂ hx.2 le_rfl)
    · have hx : (μ₁.prod μ₂) {(x₁, x₂)} ≠ 0 := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod]
        exact mul_ne_zero hx₁ hx₂
      refine le_iSup₂_of_le (f := fun x (_ : (μ₁.prod μ₂) {x} ≠ 0) ↦ (κ₁ ∥ₖ κ₂) x {(y₁, y₂)})
        (x₁, x₂) hx ?_
      rw [← Set.singleton_prod_singleton, Kernel.parallelComp_apply_prod]
  calc maxLeakageSum (μ₁.prod μ₂) (κ₁ ∥ₖ κ₂)
      = ∑ y₁, ∑ y₂, (⨆ (x₁) (_ : μ₁ {x₁} ≠ 0), κ₁ x₁ {y₁}) *
          ⨆ (x₂) (_ : μ₂ {x₂} ≠ 0), κ₂ x₂ {y₂} := by
        simp_rw [maxLeakageSum, Fintype.sum_prod_type, h_sup]
    _ = maxLeakageSum μ₁ κ₁ * maxLeakageSum μ₂ κ₂ := (Finset.sum_mul_sum _ _ _ _).symm

/-- **Additivity** of maximal leakage for independent pairs: if `X₁ ∼ μ₁` and `X₂ ∼ μ₂` are
independent and fed through the independent channels `κ₁` and `κ₂`, then
`L((X₁, X₂) → (Y₁, Y₂)) = L(X₁ → Y₁) + L(X₂ → Y₂)`. -/
lemma maxLeakage_parallelComp [MeasurableSingletonClass β₁] [MeasurableSingletonClass β₂]
    [SFinite μ₂] [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ : α₁} (hx₁ : μ₁ {x₁} ≠ 0)
    {x₂ : α₂} (hx₂ : μ₂ {x₂} ≠ 0) :
    maxLeakage (μ₁.prod μ₂) (κ₁ ∥ₖ κ₂) = maxLeakage μ₁ κ₁ + maxLeakage μ₂ κ₂ := by
  have h₁ := one_le_toReal_maxLeakageSum (κ := κ₁) hx₁
  have h₂ := one_le_toReal_maxLeakageSum (κ := κ₂) hx₂
  rw [maxLeakage, maxLeakageSum_parallelComp, ENNReal.toReal_mul,
    Real.log_mul (by positivity) (by positivity), maxLeakage, maxLeakage]

end Independent

end InformationTheory
