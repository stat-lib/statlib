/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Statlib.ForMathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Chain rule for the Kullback-Leibler divergence with an arbitrary joint measure

Mathlib's chain rule `InformationTheory.klDiv_compProd_eq_add` decomposes
`KL(μ ⊗ₘ κ, ν ⊗ₘ η)` along the first coordinate. The first argument does not need to be a
composition-product: for any finite measure `ρ` on `α × β`, any finite measure `μ` on `α` and any
Markov kernel `η`, `KL(ρ, μ ⊗ₘ η) = KL(ρ.fst, μ) + KL(ρ, ρ.fst ⊗ₘ η)`. Since `ρ` is not
disintegrated, this holds without assumptions on the measurable spaces.

Applied after swapping the coordinates, with a constant kernel, this decomposes the divergence with
respect to a product measure: `KL(ρ, μ × ξ) = KL(ρ.snd, ξ) + KL(ρ, μ × ρ.snd)` for a probability
measure `μ`.

## Main statements

* `InformationTheory.llr_compProd_ae_eq_add`: for `ρ ≪ μ ⊗ₘ η`, the log-likelihood ratio
  `llr ρ (μ ⊗ₘ η)` is `ρ`-a.e. equal to `(x, y) ↦ llr ρ.fst μ x + llr ρ (ρ.fst ⊗ₘ η) (x, y)`.
* `InformationTheory.integrable_llr_compProd_iff_fst`: the corresponding equivalence for the
  integrability of the log-likelihood ratios.
* `InformationTheory.klDiv_compProd_eq_klDiv_fst_add`: **chain rule**,
  `KL(ρ, μ ⊗ₘ η) = KL(ρ.fst, μ) + KL(ρ, ρ.fst ⊗ₘ η)`.
* `InformationTheory.klDiv_prod_eq_klDiv_snd_add`: `KL(ρ, μ × ξ) = KL(ρ.snd, ξ) + KL(ρ, μ × ρ.snd)`
  for a probability measure `μ`.
* `InformationTheory.klDiv_compProd_left_of_ae`: `KL(μ ⊗ₘ κ, ν ⊗ₘ κ) = KL(μ, ν)` for a kernel `κ`
  which is a probability measure on a measurable set of full `μ`- and `ν`-measure.

## Implementation notes

As for Mathlib's chain rule, the proof treats separately the cases in which absolute continuity
fails (`MeasureTheory.Measure.absolutelyContinuous_compProd_iff_fst`) and in which the
log-likelihood ratios are not integrable. The integrability of `llr ρ (ρ.fst ⊗ₘ η)` follows from
those of `llr ρ (μ ⊗ₘ η)` and `llr ρ.fst μ`, the latter given by the data-processing inequality
`KL(ρ.fst, μ) ≤ KL(ρ, μ ⊗ₘ η)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {ρ : Measure (α × β)} {μ : Measure α} {η : Kernel α β}
  [IsFiniteMeasure ρ] [IsFiniteMeasure μ] [IsMarkovKernel η]

/-- For `ρ ≪ μ ⊗ₘ η`, the log-likelihood ratio of `ρ` with respect to `μ ⊗ₘ η` is the sum of the
log-likelihood ratio of the first marginals and of that of `ρ` with respect to `ρ.fst ⊗ₘ η`. -/
lemma llr_compProd_ae_eq_add (h_ac : ρ ≪ μ ⊗ₘ η) :
    llr ρ (μ ⊗ₘ η) =ᵐ[ρ] fun p ↦ llr ρ.fst μ p.1 + llr ρ (ρ.fst ⊗ₘ η) p := by
  obtain ⟨h_fst, h_ac'⟩ := Measure.absolutelyContinuous_compProd_iff_fst.mp h_ac
  have h_ae_fst {P : α → Prop} (h : ∀ᵐ x ∂ρ.fst, P x) : ∀ᵐ p ∂ρ, P p.1 :=
    ae_of_ae_map measurable_fst.aemeasurable h
  -- `∂ρ/∂(μ ⊗ₘ η) = ∂ρ/∂(ρ.fst ⊗ₘ η) * (∂ρ.fst/∂μ ∘ fst)`, both factors being positive and finite
  filter_upwards [h_ac.ae_le (Measure.rnDeriv_mul_rnDeriv (κ := μ ⊗ₘ η) h_ac'),
    h_ac.ae_le (rnDeriv_measure_compProd_left ρ.fst μ η), Measure.rnDeriv_pos h_ac',
    h_ac'.ae_le (Measure.rnDeriv_lt_top ρ (ρ.fst ⊗ₘ η)), h_ae_fst (Measure.rnDeriv_pos h_fst),
    h_ae_fst (h_fst.ae_le (Measure.rnDeriv_lt_top ρ.fst μ))] with p h1 h2 h3 h4 h5 h6
  rw [llr, llr, llr, ← h1, Pi.mul_apply, h2, ENNReal.toReal_mul,
    log_mul (ENNReal.toReal_pos h3.ne' h4.ne).ne' (ENNReal.toReal_pos h5.ne' h6.ne).ne', add_comm]

/-- For `ρ ≪ μ ⊗ₘ η`, the log-likelihood ratio `llr ρ (μ ⊗ₘ η)` is integrable if and only if
`llr ρ.fst μ` and `llr ρ (ρ.fst ⊗ₘ η)` are. -/
lemma integrable_llr_compProd_iff_fst (h_ac : ρ ≪ μ ⊗ₘ η) :
    Integrable (llr ρ (μ ⊗ₘ η)) ρ
      ↔ Integrable (llr ρ.fst μ) ρ.fst ∧ Integrable (llr ρ (ρ.fst ⊗ₘ η)) ρ := by
  have h_fst_iff : Integrable (llr ρ.fst μ) ρ.fst ↔ Integrable (fun p ↦ llr ρ.fst μ p.1) ρ :=
    integrable_map_measure (measurable_llr _ _).aestronglyMeasurable measurable_fst.aemeasurable
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- data processing: `KL(ρ.fst, μ) ≤ KL(ρ, μ ⊗ₘ η) < ∞`
    have h_le : klDiv ρ.fst μ ≤ klDiv ρ (μ ⊗ₘ η) := by
      simpa [Measure.fst_compProd] using klDiv_fst_le ρ (μ ⊗ₘ η)
    have h_int_fst : Integrable (llr ρ.fst μ) ρ.fst :=
      (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top (klDiv_ne_top h_ac h) h_le)).2
    refine ⟨h_int_fst, (h.sub (h_fst_iff.mp h_int_fst)).congr ?_⟩
    filter_upwards [llr_compProd_ae_eq_add h_ac] with p hp
    rw [Pi.sub_apply, hp, add_sub_cancel_left]
  · exact (integrable_congr (llr_compProd_ae_eq_add h_ac)).mpr ((h_fst_iff.mp h.1).add h.2)

variable (ρ μ η) in
/-- **Chain rule** for the Kullback-Leibler divergence with an arbitrary joint measure `ρ`:
`KL(ρ, μ ⊗ₘ η) = KL(ρ.fst, μ) + KL(ρ, ρ.fst ⊗ₘ η)`. Mathlib's `klDiv_compProd_eq_add` is the case
of a composition-product `ρ`. This holds without assumptions on the measurable spaces. -/
theorem klDiv_compProd_eq_klDiv_fst_add :
    klDiv ρ (μ ⊗ₘ η) = klDiv ρ.fst μ + klDiv ρ (ρ.fst ⊗ₘ η) := by
  -- if absolute continuity does not hold, both sides are `∞`
  by_cases h_ac : ρ ≪ μ ⊗ₘ η
  swap
  · rw [klDiv_of_not_ac h_ac]
    rw [Measure.absolutelyContinuous_compProd_iff_fst, not_and_or] at h_ac
    rcases h_ac with h | h <;> simp [klDiv_of_not_ac h]
  -- same if the log-likelihood ratio is not integrable
  by_cases h_int : Integrable (llr ρ (μ ⊗ₘ η)) ρ
  swap
  · rw [klDiv_of_not_integrable h_int]
    rw [integrable_llr_compProd_iff_fst h_ac, not_and_or] at h_int
    rcases h_int with h | h <;> simp [klDiv_of_not_integrable h]
  obtain ⟨h_ac_fst, h_ac'⟩ := Measure.absolutelyContinuous_compProd_iff_fst.mp h_ac
  obtain ⟨h_int_fst, h_int'⟩ := (integrable_llr_compProd_iff_fst h_ac).mp h_int
  -- the integral of the log-likelihood ratio splits
  have h_integral : ∫ p, llr ρ (μ ⊗ₘ η) p ∂ρ
      = ∫ x, llr ρ.fst μ x ∂ρ.fst + ∫ p, llr ρ (ρ.fst ⊗ₘ η) p ∂ρ := by
    have h_int_fst' : Integrable (fun p ↦ llr ρ.fst μ p.1) ρ :=
      (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable
        measurable_fst.aemeasurable).mp h_int_fst
    rw [integral_congr_ae (llr_compProd_ae_eq_add h_ac), integral_add h_int_fst' h_int']
    congr 1
    exact (integral_map measurable_fst.aemeasurable
      (measurable_llr _ _).aestronglyMeasurable).symm
  rw [klDiv_of_ac_of_integrable h_ac h_int, klDiv_of_ac_of_integrable h_ac_fst h_int_fst,
    klDiv_of_ac_of_integrable h_ac' h_int',
    ← ENNReal.ofReal_add (integral_llr_add_sub_measure_univ_nonneg h_ac_fst h_int_fst)
      (integral_llr_add_sub_measure_univ_nonneg h_ac' h_int'), h_integral]
  simp only [measureReal_def, Measure.compProd_apply_univ, Measure.fst_univ]
  ring_nf

/-- The Kullback-Leibler divergence between a measure `ρ` on `α × β` and a product measure
`μ × ξ`, for a probability measure `μ`: `KL(ρ, μ × ξ) = KL(ρ.snd, ξ) + KL(ρ, μ × ρ.snd)`. -/
theorem klDiv_prod_eq_klDiv_snd_add (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (μ : Measure α)
    [IsProbabilityMeasure μ] (ξ : Measure β) [IsFiniteMeasure ξ] :
    klDiv ρ (μ.prod ξ) = klDiv ρ.snd ξ + klDiv ρ (μ.prod ρ.snd) := by
  -- swap the coordinates and apply the chain rule with the constant kernel `Kernel.const β μ`
  have h := klDiv_compProd_eq_klDiv_fst_add (ρ.map Prod.swap) ξ (Kernel.const β μ)
  rw [Measure.fst_map_swap, Measure.compProd_const, Measure.compProd_const, ← Measure.prod_swap,
    ← Measure.prod_swap (μ := μ), klDiv_map_swap, klDiv_map_swap] at h
  exact h

/-- `klDiv_compProd_left` for a kernel which is only a probability measure on a measurable set of
full measure for both `μ` and `ν`. -/
lemma klDiv_compProd_left_of_ae (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : Kernel α β) [IsSFiniteKernel κ] {S : Set α} (hS : MeasurableSet S)
    (hκ : ∀ a ∈ S, IsProbabilityMeasure (κ a)) (hμ : ∀ᵐ a ∂μ, a ∈ S) (hν : ∀ᵐ a ∂ν, a ∈ S) :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν := by
  classical
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b⟩⟩
  · -- if `β` is empty, then `S` is empty, hence `μ = ν = 0`
    have hS_empty (a : α) (ha : a ∈ S) : False :=
      have := hκ a ha; IsProbabilityMeasure.ne_zero (κ a) (κ a).eq_zero_of_isEmpty
    have hμ0 : μ = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (hμ.mono hS_empty))
    have hν0 : ν = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (hν.mono hS_empty))
    simp [hμ0, hν0]
  let κ' : Kernel α β := Kernel.piecewise hS κ (Kernel.const α (Measure.dirac b))
  have hκ' : IsMarkovKernel κ' := ⟨fun a ↦ by
    by_cases ha : a ∈ S
    · simp only [κ', Kernel.piecewise_apply, ha, ite_true]
      exact hκ a ha
    · simp only [κ', Kernel.piecewise_apply, ha, ite_false, Kernel.const_apply]
      infer_instance⟩
  have hμκ : μ ⊗ₘ κ = μ ⊗ₘ κ' := Measure.compProd_congr (by
    filter_upwards [hμ] with a ha
    simp [κ', Kernel.piecewise_apply, ha])
  have hνκ : ν ⊗ₘ κ = ν ⊗ₘ κ' := Measure.compProd_congr (by
    filter_upwards [hν] with a ha
    simp [κ', Kernel.piecewise_apply, ha])
  rw [hμκ, hνκ, klDiv_compProd_left]

end InformationTheory
