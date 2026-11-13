/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Radon-Nikodym derivatives and Lebesgue decomposition

## Main statements

* `MeasureTheory.Measure.singularPart_add_setLIntegral_rnDeriv`:
  `μ.singularPart ν s + ∫⁻ x in s, ∂μ/∂ν x ∂ν = μ s` for a measurable set `s`.
* `MeasureTheory.Measure.rnDeriv_restrict_restrict`,
  `MeasureTheory.Measure.singularPart_restrict_restrict`: Radon-Nikodym derivative and singular
  part of `μ.restrict s` with respect to `ν.restrict s`.
* `MeasureTheory.Measure.singularPart_eq_restrict_rnDeriv_add_eq_zero`: the singular part of `μ`
  with respect to `ν` is the restriction of `μ` to the set where `∂ν/∂(μ + ν)` vanishes.
* `MeasureTheory.Measure.rnDeriv_eq_inv_rnDeriv_of_ne_zero`: `∂ν/∂μ = (∂μ/∂ν)⁻¹`, `ν`-almost
  everywhere on the set where `∂μ/∂ν ≠ 0`.
* `MeasureTheory.lintegral_eq_add_singularPart_withDensity`: decomposition of `∫⁻ x, g x ∂ν` along
  the Lebesgue decomposition of `ν` with respect to `μ`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- The mass of a measurable set `s` under `μ` splits into the mass of the singular part of `μ`
with respect to `ν` and the integral of `∂μ/∂ν` over `s`. -/
lemma singularPart_add_setLIntegral_rnDeriv (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
    {s : Set α} (hs : MeasurableSet s) :
    μ.singularPart ν s + ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [add_apply, withDensity_apply _ hs]

lemma singularPart_add_lintegral_rnDeriv (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.singularPart ν Set.univ + ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ := by
  simpa using singularPart_add_setLIntegral_rnDeriv μ ν MeasurableSet.univ

lemma rnDeriv_restrict_restrict (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
    [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
  refine (eq_rnDeriv (s := (μ.singularPart ν).restrict s) (measurable_rnDeriv μ ν)
    (((mutuallySingular_singularPart μ ν).restrict s).symm.restrict s).symm ?_).symm
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [restrict_add, restrict_withDensity hs]

lemma singularPart_restrict_restrict (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).singularPart (ν.restrict s) = (μ.singularPart ν).restrict s := by
  refine (eq_singularPart (measurable_rnDeriv μ ν)
    (((mutuallySingular_singularPart μ ν).restrict s).symm.restrict s).symm ?_).symm
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [restrict_add, restrict_withDensity hs]

/-- The singular part of `μ` with respect to `ν` is the restriction of `μ` to the set where
`∂ν/∂(μ + ν)` vanishes. -/
lemma singularPart_eq_restrict_rnDeriv_add_eq_zero (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] :
    μ.singularPart ν = μ.restrict {x | ν.rnDeriv (μ + ν) x = 0} := by
  set N := {x | ν.rnDeriv (μ + ν) x = 0}
  have hN : MeasurableSet N := measurableSet_eq_fun (ν.measurable_rnDeriv _) measurable_const
  have hνρ : ν ≪ μ + ν := AbsolutelyContinuous.rfl.add_right' μ
  have hνN : ν N = 0 := by
    rw [← setLIntegral_rnDeriv hνρ, setLIntegral_congr_fun hN (g := 0) fun x hx ↦ hx]
    simp
  -- outside of `N`, `μ` is absolutely continuous with respect to `ν`
  have h_ac : μ.restrict Nᶜ ≪ ν := by
    refine AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
    rw [restrict_apply hs]
    refine AbsolutelyContinuous.rfl.add_right ν ?_
    rw [← setLIntegral_rnDeriv hνρ, setLIntegral_eq_zero_iff hs (ν.measurable_rnDeriv _)] at hνs
    rw [← compl_compl (s ∩ Nᶜ), ← mem_ae_iff]
    filter_upwards [hνs] with x hx hxN
    exact hxN.2 (hx hxN.1)
  refine singularPart_eq_restrict ?_ hνN
  rw [← restrict_apply_univ, ← singularPart_restrict μ ν hN.compl, singularPart_eq_zero_of_ac h_ac,
    FunLike.coe_zero, Pi.zero_apply]

/-- On the set where `∂μ/∂ν` does not vanish, `∂ν/∂μ` is its inverse, `ν`-almost everywhere. -/
lemma rnDeriv_eq_inv_rnDeriv_of_ne_zero (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ 0 → ν.rnDeriv μ x = (μ.rnDeriv ν x)⁻¹ := by
  have h1 : ((ν.withDensity (μ.rnDeriv ν)).rnDeriv ν)⁻¹
      =ᵐ[ν.withDensity (μ.rnDeriv ν)] ν.rnDeriv (ν.withDensity (μ.rnDeriv ν)) :=
    inv_rnDeriv (withDensity_absolutelyContinuous ν (μ.rnDeriv ν))
  have h2 := rnDeriv_withDensity ν (measurable_rnDeriv μ ν)
  have h3 : ν.rnDeriv μ
      =ᵐ[ν.withDensity (μ.rnDeriv ν)] ν.rnDeriv (ν.withDensity (μ.rnDeriv ν)) := by
    have := rnDeriv_add_right_of_mutuallySingular (μ := ν) (ν := ν.withDensity (μ.rnDeriv ν))
      (mutuallySingular_singularPart μ ν).symm.withDensity
    rwa [add_comm, ← μ.haveLebesgueDecomposition_add ν] at this
  rw [Filter.EventuallyEq, ae_withDensity_iff (measurable_rnDeriv _ _)] at h1 h3
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hx0
  rw [hx3 hx0, ← hx1 hx0, Pi.inv_apply, hx2]

/-- Decomposition of `∫⁻ x, g x ∂ν` along the Lebesgue decomposition of `ν` with respect to `μ`. -/
lemma _root_.MeasureTheory.lintegral_eq_add_singularPart_withDensity (μ ν : Measure α)
    [ν.HaveLebesgueDecomposition μ] {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂ν = ∫⁻ x, g x ∂(ν.singularPart μ) + ∫⁻ x, ν.rnDeriv μ x * g x ∂μ := by
  conv_lhs => rw [ν.haveLebesgueDecomposition_add μ]
  rw [lintegral_add_measure, lintegral_withDensity_eq_lintegral_mul _ (measurable_rnDeriv _ _) hg]
  rfl

end MeasureTheory.Measure
