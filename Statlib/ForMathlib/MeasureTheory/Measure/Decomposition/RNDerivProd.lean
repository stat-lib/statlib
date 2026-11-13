/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Statlib.ForMathlib.MeasureTheory.Constructions.Pi
public import Statlib.ForMathlib.MeasureTheory.Integral.Pi

/-!
# Densities and Radon-Nikodym derivatives of products of measures

For σ-finite measures `μ i` and `ν i` indexed by a finite type, the Radon-Nikodym derivative of the
product measure `Measure.pi μ` with respect to `Measure.pi ν` is `x ↦ ∏ i, ∂(μ i)/∂(ν i) (x i)`,
and similarly for binary products.

## Main statements

* `MeasureTheory.Measure.rnDeriv_prod`: `∂(μ₁.prod μ₂)/∂(ν₁.prod ν₂) =ᵐ ∂μ₁/∂ν₁ p.1 * ∂μ₂/∂ν₂ p.2`.
* `MeasureTheory.Measure.pi_withDensity`: the product of the measures `(ν i).withDensity (f i)` is
  `(Measure.pi ν).withDensity (fun x ↦ ∏ i, f i (x i))`.
* `MeasureTheory.Measure.pi_eq_withDensity_prod_rnDeriv`: if `μ i ≪ ν i` for all `i`, then
  `Measure.pi μ = (Measure.pi ν).withDensity (fun x ↦ ∏ i, ∂(μ i)/∂(ν i) (x i))`.
* `MeasureTheory.Measure.rnDeriv_pi`: `∂(Measure.pi μ)/∂(Measure.pi ν) =ᵐ ∏ i, ∂(μ i)/∂(ν i) (x i)`.
* `MeasureTheory.Measure.AbsolutelyContinuous.pi'`: if `μ i ≪ ν i` for all `i`, then
  `Measure.pi μ ≪ Measure.pi ν`.
* `MeasureTheory.Measure.not_mutuallySingular_pi`: products of σ-finite measures which are not
  mutually singular are not mutually singular.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

namespace Measure

section Prod

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The Radon-Nikodym derivative of a product of σ-finite measures is the product of the
Radon-Nikodym derivatives. -/
lemma rnDeriv_prod (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β) [SigmaFinite μ₁] [SigmaFinite ν₁]
    [SigmaFinite μ₂] [SigmaFinite ν₂] :
    (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) =ᵐ[ν₁.prod ν₂]
      fun p ↦ μ₁.rnDeriv ν₁ p.1 * μ₂.rnDeriv ν₂ p.2 := by
  -- both products have product densities with respect to `ξ₁.prod ξ₂`, where `ξᵢ = μᵢ + νᵢ`
  set ξ₁ := μ₁ + ν₁
  set ξ₂ := μ₂ + ν₂
  have h_rn {ρ₁ : Measure α} {ρ₂ : Measure β} [SigmaFinite ρ₁] [SigmaFinite ρ₂] (h₁ : ρ₁ ≪ ξ₁)
      (h₂ : ρ₂ ≪ ξ₂) : (ρ₁.prod ρ₂).rnDeriv (ξ₁.prod ξ₂)
        =ᵐ[ξ₁.prod ξ₂] fun p ↦ ρ₁.rnDeriv ξ₁ p.1 * ρ₂.rnDeriv ξ₂ p.2 := by
    conv_lhs => rw [← withDensity_rnDeriv_eq _ _ h₁, ← withDensity_rnDeriv_eq _ _ h₂,
      prod_withDensity (measurable_rnDeriv _ _) (measurable_rnDeriv _ _)]
    exact rnDeriv_withDensity _ (by fun_prop)
  have hμ₁ : μ₁ ≪ ξ₁ := AbsolutelyContinuous.rfl.add_right _
  have hν₁ : ν₁ ≪ ξ₁ := AbsolutelyContinuous.rfl.add_right' _
  have hμ₂ : μ₂ ≪ ξ₂ := AbsolutelyContinuous.rfl.add_right _
  have hν₂ : ν₂ ≪ ξ₂ := AbsolutelyContinuous.rfl.add_right' _
  have hν := hν₁.prod hν₂
  -- coordinatewise, `∂μᵢ/∂νᵢ = ∂μᵢ/∂ξᵢ / ∂νᵢ/∂ξᵢ`
  filter_upwards [rnDeriv_eq_div (hμ₁.prod hμ₂) hν, hν (h_rn hμ₁ hμ₂), hν (h_rn hν₁ hν₂),
    quasiMeasurePreserving_fst.ae (rnDeriv_eq_div hμ₁ hν₁),
    quasiMeasurePreserving_snd.ae (rnDeriv_eq_div hμ₂ hν₂),
    quasiMeasurePreserving_fst.ae (hν₁.ae_le (rnDeriv_ne_top ν₁ ξ₁)),
    quasiMeasurePreserving_snd.ae (hν₂.ae_le (rnDeriv_ne_top ν₂ ξ₂))] with p h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, h4, h5, ENNReal.mul_div_mul_comm (.inr h7) (.inl h6)]

end Prod

section Pi

variable {ι : Type*} [Fintype ι] {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  {μ ν : (i : ι) → Measure (X i)}

/-- The product of the measures `(ν i).withDensity (f i)` is the measure with density
`x ↦ ∏ i, f i (x i)` with respect to `Measure.pi ν`. -/
lemma pi_withDensity [∀ i, SigmaFinite (ν i)] {f : (i : ι) → X i → ℝ≥0∞}
    [∀ i, SigmaFinite ((ν i).withDensity (f i))] (hf : ∀ i, AEMeasurable (f i) (ν i)) :
    Measure.pi (fun i ↦ (ν i).withDensity (f i))
      = (Measure.pi ν).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (.univ_pi hs)]
  have h_ind : (Set.univ.pi s).indicator (fun x ↦ ∏ i, f i (x i))
      = fun x ↦ ∏ i, (s i).indicator (f i) (x i) := by
    ext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ ↦ (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [h_ind, lintegral_fintype_prod_eq_prod fun i ↦ (hf i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

/-- If `μ i ≪ ν i` for all `i`, the product measure `Measure.pi μ` has density
`x ↦ ∏ i, ∂(μ i)/∂(ν i) (x i)` with respect to `Measure.pi ν`. -/
lemma pi_eq_withDensity_prod_rnDeriv [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hμν : ∀ i, μ i ≪ ν i) :
    Measure.pi μ = (Measure.pi ν).withDensity (fun x ↦ ∏ i, (μ i).rnDeriv (ν i) (x i)) := by
  have h_eq : μ = fun i ↦ (ν i).withDensity ((μ i).rnDeriv (ν i)) :=
    funext fun i ↦ (withDensity_rnDeriv_eq _ _ (hμν i)).symm
  have (i : ι) : SigmaFinite ((ν i).withDensity ((μ i).rnDeriv (ν i))) := by
    rw [withDensity_rnDeriv_eq _ _ (hμν i)]
    infer_instance
  conv_lhs => rw [h_eq]
  exact pi_withDensity fun i ↦ (measurable_rnDeriv _ _).aemeasurable

/-- The Radon-Nikodym derivative of `Measure.pi μ` with respect to `Measure.pi ν` is
`x ↦ ∏ i, ∂(μ i)/∂(ν i) (x i)`. -/
lemma rnDeriv_pi [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    (Measure.pi μ).rnDeriv (Measure.pi ν)
      =ᵐ[Measure.pi ν] fun x ↦ ∏ i, (μ i).rnDeriv (ν i) (x i) := by
  -- both `Measure.pi μ` and `Measure.pi ν` have product densities with respect to
  -- `Measure.pi ξ`, where `ξ i = μ i + ν i`
  set ξ : (i : ι) → Measure (X i) := fun i ↦ μ i + ν i
  have hμξ (i : ι) : μ i ≪ ξ i := AbsolutelyContinuous.rfl.add_right _
  have hνξ (i : ι) : ν i ≪ ξ i := AbsolutelyContinuous.rfl.add_right' _
  have h_meas (κ : (i : ι) → Measure (X i)) :
      Measurable fun x : (i : ι) → X i ↦ ∏ i, (κ i).rnDeriv (ξ i) (x i) :=
    Finset.measurable_prod _ fun i _ ↦ (measurable_rnDeriv _ _).comp (measurable_pi_apply i)
  have hμ := pi_eq_withDensity_prod_rnDeriv hμξ
  have hν := pi_eq_withDensity_prod_rnDeriv hνξ
  have h_acμ : Measure.pi μ ≪ Measure.pi ξ := hμ ▸ withDensity_absolutelyContinuous _ _
  have h_acν : Measure.pi ν ≪ Measure.pi ξ := hν ▸ withDensity_absolutelyContinuous _ _
  have h_rnμ : (Measure.pi μ).rnDeriv (Measure.pi ξ)
      =ᵐ[Measure.pi ξ] fun x ↦ ∏ i, (μ i).rnDeriv (ξ i) (x i) := by
    conv_lhs => rw [hμ]
    exact rnDeriv_withDensity _ (h_meas μ)
  have h_rnν : (Measure.pi ν).rnDeriv (Measure.pi ξ)
      =ᵐ[Measure.pi ξ] fun x ↦ ∏ i, (ν i).rnDeriv (ξ i) (x i) := by
    conv_lhs => rw [hν]
    exact rnDeriv_withDensity _ (h_meas ν)
  -- coordinatewise, `∂(μ i)/∂(ν i) = ∂(μ i)/∂(ξ i) / ∂(ν i)/∂(ξ i)`
  have h_coord : ∀ᵐ x ∂(Measure.pi ν), ∀ i, (μ i).rnDeriv (ν i) (x i)
      = (μ i).rnDeriv (ξ i) (x i) / (ν i).rnDeriv (ξ i) (x i) :=
    ae_all_iff.2 fun i ↦ tendsto_eval_ae_ae.eventually (rnDeriv_eq_div (hμξ i) (hνξ i))
  have h_top : ∀ᵐ x ∂(Measure.pi ν), ∀ i, (ν i).rnDeriv (ξ i) (x i) ≠ ∞ :=
    ae_all_iff.2 fun i ↦ tendsto_eval_ae_ae.eventually ((hνξ i).ae_le (rnDeriv_ne_top _ _))
  filter_upwards [rnDeriv_eq_div h_acμ h_acν, h_acν h_rnμ, h_acν h_rnν, h_coord, h_top]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, Finset.prod_congr rfl fun i _ ↦ h4 i,
    ENNReal.prod_div_distrib_of_ne_top fun i _ ↦ h5 i]

/-- If `μ i ≪ ν i` for all `i`, then `Measure.pi μ ≪ Measure.pi ν`. -/
lemma AbsolutelyContinuous.pi' [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  rw [pi_eq_withDensity_prod_rnDeriv h]
  exact withDensity_absolutelyContinuous _ _

/-- Products of σ-finite measures which are not mutually singular are not mutually singular. -/
lemma not_mutuallySingular_pi [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, ¬ μ i ⟂ₘ ν i) :
    ¬ Measure.pi μ ⟂ₘ Measure.pi ν := by
  -- the absolutely continuous part `ρ i` of `μ i` with respect to `ν i` is nonzero, and the
  -- product of the `ρ i` is absolutely continuous with respect to both products
  set ρ : (i : ι) → Measure (X i) := fun i ↦ (ν i).withDensity ((μ i).rnDeriv (ν i))
  have (i : ι) : NeZero (ρ i) := ⟨by simpa [ρ] using h i⟩
  have hρμ : Measure.pi ρ ≪ Measure.pi μ := AbsolutelyContinuous.pi' fun i ↦
    absolutelyContinuous_of_le (withDensity_rnDeriv_le (μ i) (ν i))
  have hρν : Measure.pi ρ ≪ Measure.pi ν := AbsolutelyContinuous.pi' fun i ↦
    withDensity_absolutelyContinuous (ν i) ((μ i).rnDeriv (ν i))
  intro h_ms
  exact NeZero.ne _ ((MutuallySingular.self_iff _).mp (h_ms.mono_ac hρμ hρν))

end Pi

end Measure

end MeasureTheory
