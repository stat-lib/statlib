/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Quadratic mean differentiability

This file defines quadratic mean differentiability (QMD) for a parametrized family of measures.
The main theorem proves the standard mean-zero score identity for a Hadamard QMD derivative.

## Main definitions

* `HasQuadraticMeanDerivWithinAt P μ s x A`: QMD within `s` at `x`, expressed as an `L²(μ)` little-o
  estimate for square-root densities.
* `HasHadamardQuadraticMeanDerivWithinAt P μ s θ A`: Hadamard-style QMD within `s` at `θ`, tested
  along local paths `θ + t • a` with `t → 0` and `a → h`. The motivation for introducing this
  definition is that it is weaker than the classical one, but still sufficient for the proof of
  `integral_score_eq_zero`. In fact, it also makes the formalization easier.

## Main statements

* `HasQuadraticMeanDerivWithinAt.hasHadamardQuadraticMeanDerivWithinAt`: QMD within a set implies
  the Hadamard-style local-path formulation.
* `integral_score_eq_zero`: if `A` is a Hadamard QMD derivative and a local path `θ + t • a` with
  `t → 0` and `a → h` stays in `s`, then the score has mean zero: `∫ ω, A h ω ∂P θ = 0`.
* `integral_score_eq_zero_of_mem_nhds`: the same conclusion when `s` is a neighborhood of `θ`.

## TODO

Develop a fuller API for `HasQuadraticMeanDerivWithinAt`, analogous to the APIs around
`HasFDerivWithinAt`, `DifferentiableWithinAt`, and `fderivWithin`.  In particular:

* add convenient variants, such as QMD-at and QMD-on predicates;
* add uniqueness and congruence lemmas for QMD derivatives under appropriate hypotheses;
* define and develop a canonical derivative object, analogous to `fderivWithin`.

-/

@[expose] public section

noncomputable section

open scoped Topology NNReal ENNReal

open Asymptotics Filter MeasureTheory Real

namespace QMD

section Definitions

/-- Quadratic mean differentiability within a set.  The `L²(μ)` remainder is `o(y - x)` as
`y → x` within `s`. We do not assume that the derivative is continuous. -/
-- ANCHOR: hasQuadraticMeanDeriv
def HasQuadraticMeanDerivWithinAt {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] (P : E → Measure Ω) (μ : Measure Ω) (s : Set E) (x : E)
    (A : E →ₗ[ℝ] (Ω →₂[P x] ℝ)) : Prop :=
  (fun y =>
    lpNorm (fun ω => √((P y).rnDeriv μ ω).toReal - √((P x).rnDeriv μ ω).toReal -
    2⁻¹ * A (y - x) ω * √((P x).rnDeriv μ ω).toReal) 2 μ) =o[ℝ; 𝓝[s] x] (fun y => y - x)
-- ANCHOR_END: hasQuadraticMeanDeriv

/-- Hadamard-style quadratic mean differentiability within a set. Along every path `θ + t • a` with
`t → 0`, `a → h`, and eventually staying in `s`, the `L²(μ)` remainder with direction `h` tends to
zero. We do not assume that the derivative is continuous. -/
-- ANCHOR: hasHadamardQuadraticMeanDeriv
def HasHadamardQuadraticMeanDerivWithinAt {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] (P : E → Measure Ω) (μ : Measure Ω) (s : Set E) (θ : E)
    (A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)) : Prop :=
  ∀ (h : E) (l : Filter (ℝ × E)), Tendsto Prod.fst l (𝓝 0) →
    Tendsto Prod.snd l (𝓝 h) → (∀ᶠ p in l, θ + p.1 • p.2 ∈ s) → Tendsto (fun p =>
    p.1⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
    √((P θ).rnDeriv μ ω).toReal -
    2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0)
-- ANCHOR_END: hasHadamardQuadraticMeanDeriv

/-- A quadratic-mean derivative implies that the scaled QMD remainder along any local path tends to
zero, with the linear term evaluated at `p.1 • p.2`. -/
theorem HasQuadraticMeanDerivWithinAt.tendsto_local_path_remainder {Ω E : Type*}
    {mΩ : MeasurableSpace Ω} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {P : E → Measure Ω} {μ : Measure Ω} {s : Set E} {θ h : E} {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasQuadraticMeanDerivWithinAt P μ s θ A) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    Tendsto (fun p => p.1⁻¹ * lpNorm (fun ω =>
      √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal -
      2⁻¹ * A (p.1 • p.2) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0) := by
  have : Tendsto (fun p => θ + p.1 • p.2) l (𝓝[s] θ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, he⟩
    simpa using (hzero.smul hh).const_add θ
  have hbigO : ((fun y ↦ y - θ) ∘ fun p ↦ θ + p.1 • p.2) =O[l] (fun p => p.1) := by
    obtain ⟨C, hC⟩ := hh.norm.isBoundedUnder_le
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC] with p hp
    simp only [Function.comp_apply, add_sub_cancel_left, norm_eq_abs]
    calc
      ‖p.1 • p.2‖ = ‖p.1‖ * ‖p.2‖ := norm_smul _ _
      _ ≤ ‖p.1‖ * C := by simp at hp; gcongr
      _ = C * ‖p.1‖ := by rw [mul_comm]
  simpa using ((isLittleOTVS_iff_isLittleO.1 (hA.comp_tendsto this)).trans_isBigO
    hbigO).tendsto_inv_smul_nhds_zero

/-- The squared `ℝ≥0∞`-norm of `√((dm/dμ).toReal)` is `dm/dμ`, almost everywhere. -/
private lemma enorm_sqrt_toReal_rnDeriv_rpow_two {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (m μ : Measure Ω) [SigmaFinite m] :
    ∀ᵐ ω ∂μ, ‖√(m.rnDeriv μ ω).toReal‖ₑ ^ (2 : ℝ) = m.rnDeriv μ ω := by
  filter_upwards [Measure.rnDeriv_lt_top m μ] with ω hω
  simp only [← ofReal_norm, norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), Nat.ofNat_nonneg,
    ENNReal.ofReal_rpow_of_nonneg (sqrt_nonneg _), rpow_ofNat, sq_sqrt ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal_eq_iff]
  exact hω.ne

/-- The `L²` lintegral is unchanged after transporting `u` from `m` to `μ` by `√(dm/dμ)`. -/
private lemma Lp.lintegral_enorm_mul_sqrt_rnDeriv_rpow_two {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {m μ : Measure Ω} [SigmaFinite m] [m.HaveLebesgueDecomposition μ] (hm : m ≪ μ) (u : Ω →₂[m] ℝ) :
    ∫⁻ a, ‖u a * √(m.rnDeriv μ a).toReal‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ a, ‖u a‖ₑ ^ (2 : ℝ) ∂m := by
  calc
    ∫⁻ a, ‖u a * √(m.rnDeriv μ a).toReal‖ₑ ^ (2 : ℝ) ∂μ
        = ∫⁻ a, m.rnDeriv μ a * ‖u a‖ₑ ^ (2 : ℝ) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [enorm_sqrt_toReal_rnDeriv_rpow_two m μ] with a hsqrt
      calc
        ‖u a * √(m.rnDeriv μ a).toReal‖ₑ ^ (2 : ℝ)
            = ‖u a‖ₑ ^ (2 : ℝ) * ‖√(m.rnDeriv μ a).toReal‖ₑ ^ (2 : ℝ) := by
          rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        _ = ‖u a‖ₑ ^ (2 : ℝ) * m.rnDeriv μ a := by rw [hsqrt]
        _ = m.rnDeriv μ a * ‖u a‖ₑ ^ (2 : ℝ) := by rw [mul_comm]
    _ = ∫⁻ a, ‖u a‖ₑ ^ (2 : ℝ) ∂(μ.withDensity (m.rnDeriv μ)) := by
      rw [lintegral_withDensity_eq_lintegral_mul₀]
      · simp [Pi.mul_apply]
      all_goals fun_prop
    _ = ∫⁻ a, ‖u a‖ₑ ^ (2 : ℝ) ∂m := by rw [Measure.withDensity_rnDeriv_eq m μ hm]

/-- Multiplication by `√(dm/dμ)` transports the `L²(m)` seminorm to the `L²(μ)` seminorm. -/
private lemma Lp.eLpNorm_mul_sqrt_rnDeriv {Ω : Type*} {mΩ : MeasurableSpace Ω} {m μ : Measure Ω}
    [SigmaFinite m] [m.HaveLebesgueDecomposition μ] (hm : m ≪ μ) (u : Ω →₂[m] ℝ) :
    eLpNorm (fun ω => u ω * √(m.rnDeriv μ ω).toReal) 2 μ = eLpNorm u 2 m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp)]
  simpa using congrArg (fun x => x ^ (1 / ENNReal.toReal (2 : ℝ≥0∞)))
    (Lp.lintegral_enorm_mul_sqrt_rnDeriv_rpow_two hm u)

/-- The square root of a Radon-Nikodym derivative of a finite measure is in `L²`. -/
private lemma memLp_sqrt_rnDeriv {Ω : Type*} {mΩ : MeasurableSpace Ω} (m μ : Measure Ω)
    [IsFiniteMeasure m] :
    MemLp (fun ω => √(m.rnDeriv μ ω).toReal) 2 μ := by
  refine
    ⟨((Measure.measurable_rnDeriv _ _).aemeasurable.ennreal_toReal.sqrt).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
  calc
    ∫⁻ a, ‖√(m.rnDeriv μ a).toReal‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ a, m.rnDeriv μ a ∂μ :=
      lintegral_congr_ae (enorm_sqrt_toReal_rnDeriv_rpow_two m μ)
    _ < ∞ := Measure.lintegral_rnDeriv_lt_top m μ

/-- If `u ∈ L²(m)` and `m ≪ μ`, then `u * √(dm/dμ)` belongs to `L²(μ)`. -/
private lemma Lp.memLp_mul_sqrt_rnDeriv {Ω : Type*} {mΩ : MeasurableSpace Ω} {m μ : Measure Ω}
    [SigmaFinite m] [m.HaveLebesgueDecomposition μ] (hm : m ≪ μ) (u : Ω →₂[m] ℝ) :
    MemLp (fun ω => u ω * √(m.rnDeriv μ ω).toReal) 2 μ := by
  refine ⟨(Lp.stronglyMeasurable u).aestronglyMeasurable.mul
    ((Measure.measurable_rnDeriv _ _).aemeasurable.ennreal_toReal.sqrt).aestronglyMeasurable, ?_⟩
  rw [Lp.eLpNorm_mul_sqrt_rnDeriv hm u]
  exact (Lp.memLp u).2

/-- Multiplication by `√(dm/dμ)` transports the real `L²` seminorm. -/
private lemma Lp.lpNorm_mul_sqrt_rnDeriv {Ω : Type*} {mΩ : MeasurableSpace Ω} {m μ : Measure Ω}
    [SigmaFinite m] [m.HaveLebesgueDecomposition μ] (hm : m ≪ μ) (u : Ω →₂[m] ℝ) :
    lpNorm (fun ω => u ω * √(m.rnDeriv μ ω).toReal) 2 μ = lpNorm u 2 m := by
  rw [← toReal_eLpNorm (Lp.memLp_mul_sqrt_rnDeriv hm u).aestronglyMeasurable,
    ← toReal_eLpNorm (Lp.memLp u).aestronglyMeasurable, Lp.eLpNorm_mul_sqrt_rnDeriv hm u]

/-- The real `Lᵖ` seminorm is invariant under almost-everywhere equality. -/
private lemma lpNorm_congr_ae {Ω F : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup F]
    {μ : Measure Ω} {p : ℝ≥0∞} {f g : Ω → F} (hfg : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have hg : AEStronglyMeasurable g μ := hf.congr hfg
    rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg, eLpNorm_congr_ae hfg]
  · have hg : ¬ AEStronglyMeasurable g μ := fun hg => hf (hg.congr hfg.symm)
    simp [lpNorm, hf, hg]

/-- If two versions of a random variable agree almost everywhere under a measure with density
`p` with respect to `μ`, then the density `p` vanishes `μ`-almost everywhere on the set where the
two versions differ. -/
private lemma _root_.MeasureTheory.Measure.density_eq_zero_of_ae_eq_withDensity {Ω β : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {p : Ω → ℝ≥0∞} {Z Z' : Ω → β}
    (hp : AEMeasurable p μ) (hZ : Z =ᵐ[μ.withDensity p] Z') :
    ∀ᵐ ω ∂μ, Z ω ≠ Z' ω → p ω = 0 := by
  rw [EventuallyEq, ae_withDensity_iff' hp] at hZ
  filter_upwards [hZ] with ω hω hne using not_ne_iff.1 fun hp ↦ hne (hω hp)

/-- If two versions of a random variable agree almost everywhere under a measure `ν` that is
absolutely continuous with respect to `μ`, then the Radon-Nikodym derivative of `ν` with respect
to `μ` vanishes `μ`-almost everywhere on the set where the two versions differ. -/
private lemma _root_.MeasureTheory.Measure.rnDeriv_eq_zero_of_ae_eq {Ω β : Type*}
    {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} [ν.HaveLebesgueDecomposition μ] {Z Z' : Ω → β}
    (hνμ : ν ≪ μ) (hZ : Z =ᵐ[ν] Z') :
    ∀ᵐ ω ∂μ, Z ω ≠ Z' ω → ν.rnDeriv μ ω = 0 := by
  rw [← Measure.withDensity_rnDeriv_eq ν μ hνμ] at hZ
  exact Measure.density_eq_zero_of_ae_eq_withDensity
    (Measure.measurable_rnDeriv ν μ).aemeasurable hZ

/-- The transported `L²` seminorm is unchanged if the representative agrees with the `Lp`
representative almost everywhere under the source measure. -/
private lemma Lp.lpNorm_mul_sqrt_rnDeriv_of_ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {m μ : Measure Ω} [SigmaFinite m] [m.HaveLebesgueDecomposition μ] (hm : m ≪ μ)
    (u : Ω →₂[m] ℝ) {f : Ω → ℝ} (hf : f =ᵐ[m] u) :
    lpNorm (fun ω => f ω * √(m.rnDeriv μ ω).toReal) 2 μ = lpNorm u 2 m := by
  calc
    lpNorm (fun ω => f ω * √(m.rnDeriv μ ω).toReal) 2 μ =
      lpNorm (fun ω => u ω * √(m.rnDeriv μ ω).toReal) 2 μ := by
      apply lpNorm_congr_ae
      filter_upwards [Measure.rnDeriv_eq_zero_of_ae_eq hm hf] with ω hω
      by_cases hne : f ω ≠ u ω
      · simp [hω hne]
      · rw [not_ne_iff.1 hne]
    _ = lpNorm u 2 m := Lp.lpNorm_mul_sqrt_rnDeriv hm u

/-- Transporting a score term by `√(dPθ/dμ)` has the same `L²(μ)` seminorm as the original
`L²(Pθ)` norm. -/
private lemma lpNorm_score_eq_norm {Ω E : Type*} {mΩ : MeasurableSpace Ω} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ] {θ : E}
    [IsProbabilityMeasure (P θ)] (hsθ : P θ ≪ μ) (A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)) (v : E) :
    lpNorm (fun ω => 2⁻¹ * A v ω * √((P θ).rnDeriv μ ω).toReal) 2 μ = ‖(2⁻¹ : ℝ) • A v‖ := calc
  _ = lpNorm ((2⁻¹ : ℝ) • A v) 2 (P θ) := by
    refine Lp.lpNorm_mul_sqrt_rnDeriv_of_ae_eq hsθ ((2⁻¹ : ℝ) • A v) ?_
    exact (Lp.coeFn_smul (2⁻¹ : ℝ) (A v)).symm
  _ = ‖(2⁻¹ : ℝ) • A v‖ := by
    rw [← toReal_eLpNorm (Lp.memLp ((2⁻¹ : ℝ) • A v)).aestronglyMeasurable, ← Lp.norm_def]

/-- After dividing by the scalar used in a local path, the transported score term is bounded above
by the unscaled score term. -/
private lemma abs_inv_mul_lpNorm_score_smul_le {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {P : E → Measure Ω} {μ : Measure Ω}
    [SigmaFinite μ] {θ : E} [IsProbabilityMeasure (P θ)] (hsθ : P θ ≪ μ)
    (A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)) (t : ℝ) (v : E) :
    |t|⁻¹ * lpNorm (fun ω => 2⁻¹ * (t • A v) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ ≤
      lpNorm (fun ω => 2⁻¹ * A v ω * √((P θ).rnDeriv μ ω).toReal) 2 μ := by
  by_cases! ht : t = 0
  · simp [ht]
  · simp only [← map_smul, lpNorm_score_eq_norm hsθ, smul_comm (2⁻¹ : ℝ) t]
    simp [norm_smul, field]

/-- The linear score part of the Hadamard QMD expansion is itself `o(1)` in `L²(μ)` along a local
path. -/
private lemma score_tendsto_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ : E} (h : E) (A : E →L[ℝ] (Ω →₂[P θ] ℝ)) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    (hh : Tendsto Prod.snd l (𝓝 h)) :
    Tendsto (fun p => lpNorm (fun ω =>
      2⁻¹ * A (p.2 - h) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0) := by
  have : IsProbabilityMeasure (P θ) := hprob _ hθ
  have hscore_Lp : Tendsto (fun p => (2⁻¹ : ℝ) • A (p.2 - h)) l (𝓝 0) := by
    have hsub : Tendsto (fun p : ℝ × E => p.2 - h) l (𝓝 0) := by
      simpa [sub_self] using hh.sub_const h
    simpa using ((A.continuous.tendsto 0).comp hsub).const_smul (2⁻¹ : ℝ)
  refine (tendsto_zero_iff_norm_tendsto_zero.1 hscore_Lp).congr' (.of_forall fun p => ?_)
  exact (lpNorm_score_eq_norm (hs _ hθ) A (p.2 - h)).symm

/-- In the Hadamard QMD condition it does not matter whether `A` evaluates at `p.1 • h` or
`p.1 • p.2`. -/
theorem hasHadamardQuadraticMeanDerivWithinAt_iff {Ω E : Type*}
    {mΩ : MeasurableSpace Ω} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {P : E → Measure Ω}
    {μ : Measure Ω} [SigmaFinite μ] {s : Set E} {θ : E} (A : E →L[ℝ] (Ω →₂[P θ] ℝ))
    (hθ : θ ∈ s) (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) :
    HasHadamardQuadraticMeanDerivWithinAt P μ s θ A ↔ ∀ (h : E) (l : Filter (ℝ × E)),
      Tendsto Prod.fst l (𝓝 0) → Tendsto Prod.snd l (𝓝 h) →
      (∀ᶠ p in l, θ + p.1 • p.2 ∈ s) → Tendsto (fun p => p.1⁻¹ * lpNorm (fun ω =>
      √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal -
      2⁻¹ * A (p.1 • p.2) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0) := by
  refine ⟨fun hA h l hzero hh he => ?_, fun hA h l hzero hh he => ?_⟩
  all_goals
    refine tendsto_zero_iff_norm_tendsto_zero.2 <| squeeze_zero' ?_ ?_
      ((zero_add (0 : ℝ)) ▸ (tendsto_zero_iff_norm_tendsto_zero.1 (hA h l hzero hh he)).add
      (tendsto_zero_iff_norm_tendsto_zero.1 (score_tendsto_zero h A hθ hprob hs hh)))
    · filter_upwards with p using by positivity
  · filter_upwards [he] with p hp
    have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
    have : IsProbabilityMeasure (P θ) := hprob _ hθ
    simp only [map_smul, norm_mul, norm_inv, norm_eq_abs, abs_of_nonneg lpNorm_nonneg]
    calc
      |p.1|⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          √((P θ).rnDeriv μ ω).toReal - 2⁻¹ * (p.1 • A p.2) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ
          = |p.1|⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * (p.1 • A (p.2 - h + h)) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ := by simp
      _ = |p.1|⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * (p.1 • A h) ω * √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * (p.1 • A (p.2 - h)) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ := by
        congr 1
        apply lpNorm_congr_ae
        have hscore_ae : (fun ω => (p.1 • A (p.2 - h + h)) ω) =ᵐ[P θ]
            fun ω => (p.1 • A h) ω + (p.1 • A (p.2 - h)) ω := by
          filter_upwards [Lp.coeFn_add (p.1 • A h) (p.1 • A (p.2 - h))] with ω hω
          rw [add_comm, map_add, smul_add, hω, Pi.add_apply]
        filter_upwards [Measure.rnDeriv_eq_zero_of_ae_eq (hs _ hθ) hscore_ae] with ω hω
        by_cases! hne : (p.1 • A (p.2 - h + h)) ω ≠ (p.1 • A h) ω + (p.1 • A (p.2 - h)) ω
        · simp [hω hne]
        · rw [hne]; ring
      _ ≤ |p.1|⁻¹ * (lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * (p.1 • A h) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ +
            lpNorm (fun ω => 2⁻¹ * (p.1 • A (p.2 - h)) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) := by
        gcongr
        refine lpNorm_sub_le ?_ (by norm_num)
        refine ((memLp_sqrt_rnDeriv (P (θ + p.1 • p.2)) μ).sub (memLp_sqrt_rnDeriv (P θ) μ)).sub ?_
        simpa [mul_assoc] using (Lp.memLp_mul_sqrt_rnDeriv (hs _ hθ) (A (p.1 • h))).const_mul 2⁻¹
      _ ≤ _ := by
        simp only [mul_add]
        gcongr
        · trivial
        · exact abs_inv_mul_lpNorm_score_smul_le (hs _ hθ) A p.1 (p.2 - h)
  · filter_upwards [he] with p hp
    have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
    have : IsProbabilityMeasure (P θ) := hprob _ hθ
    simp only [map_smul, norm_mul, norm_inv, norm_eq_abs, abs_of_nonneg lpNorm_nonneg]
    calc
      |p.1|⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          √((P θ).rnDeriv μ ω).toReal -
          2⁻¹ * (p.1 • A h) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ
          = |p.1|⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal - 2⁻¹ * (p.1 • A (p.2 - (p.2 - h))) ω *
            √((P θ).rnDeriv μ ω).toReal) 2 μ := by simp
      _ = |p.1|⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * (p.1 • A p.2) ω * √((P θ).rnDeriv μ ω).toReal +
            2⁻¹ * (p.1 • A (p.2 - h)) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ := by
        congr 1
        apply lpNorm_congr_ae
        have hscore_ae : (fun ω => (p.1 • A (p.2 - (p.2 - h))) ω) =ᵐ[P θ]
          fun ω => (p.1 • A p.2) ω - (p.1 • A (p.2 - h)) ω := by
          filter_upwards [Lp.coeFn_sub (p.1 • A p.2) (p.1 • A (p.2 - h))] with ω hω
          rw [map_sub, smul_sub, hω, Pi.sub_apply]
        filter_upwards [Measure.rnDeriv_eq_zero_of_ae_eq (hs _ hθ) hscore_ae] with ω hω
        by_cases! hne : (p.1 • A (p.2 - (p.2 - h))) ω ≠ (p.1 • A p.2) ω - (p.1 • A (p.2 - h)) ω
        · simp [hω hne]
        · rw [hne]; ring
      _ ≤ |p.1|⁻¹ * (lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * (p.1 • A p.2) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ +
            lpNorm (fun ω => 2⁻¹ * (p.1 • A (p.2 - h)) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) := by
        gcongr
        refine lpNorm_add_le ?_ (by norm_num)
        refine ((memLp_sqrt_rnDeriv (P (θ + p.1 • p.2)) μ).sub (memLp_sqrt_rnDeriv (P θ) μ)).sub ?_
        simpa [mul_assoc] using (Lp.memLp_mul_sqrt_rnDeriv (hs _ hθ) (A (p.1 • p.2))).const_mul 2⁻¹
      _ ≤ _ := by
        simp only [mul_add]
        gcongr
        exact abs_inv_mul_lpNorm_score_smul_le (hs _ hθ) A p.1 (p.2 - h)

/-- A quadratic-mean derivative within a set is a Hadamard QMD derivative. -/
-- ANCHOR: qmdImpliesHadamard
theorem HasQuadraticMeanDerivWithinAt.hasHadamardQuadraticMeanDerivWithinAt {Ω E : Type*}
    {mΩ : MeasurableSpace Ω} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {P : E → Measure Ω}
    {μ : Measure Ω} [SigmaFinite μ] {s : Set E} {θ : E} {A : E →L[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) :
    HasHadamardQuadraticMeanDerivWithinAt P μ s θ A :=
  (hasHadamardQuadraticMeanDerivWithinAt_iff A hθ hprob hs).2
    fun _ _ hzero hh he => hA.tendsto_local_path_remainder hzero hh he
-- ANCHOR_END: qmdImpliesHadamard

end Definitions

section TendstoZero

/-- The `L²` norm of the sum of two square root densities is bounded above by `2`. -/
private lemma integral_sq_sum_le_two {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {m₁ m₂ μ : Measure Ω} [SigmaFinite μ]
    [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂] (hm₁ : m₁ ≪ μ) (hm₂ : m₂ ≪ μ) :
    (∫ ω, ‖√(m₁.rnDeriv μ ω).toReal +
      √(m₂.rnDeriv μ ω).toReal‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ 2 := by
  rw [← Real.sqrt_eq_rpow]
  nth_rw 2 [show 2 = √4 from by symm; rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num]
  apply Real.sqrt_le_sqrt
  calc
  _ ≤ ∫ ω, 2 * (m₁.rnDeriv μ ω).toReal + 2 * (m₂.rnDeriv μ ω).toReal ∂μ := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with ω using Real.rpow_nonneg (norm_nonneg _) _
    · refine Integrable.add ?_ ?_
      <;> exact Measure.integrable_toReal_rnDeriv.const_mul 2
    · filter_upwards with ω
      calc
        _ = (√(m₁.rnDeriv μ ω).toReal + √(m₂.rnDeriv μ ω).toReal) ^ 2 := by simp [sq_abs]
        _ ≤ 2 * (√(m₁.rnDeriv μ ω).toReal) ^ 2 + 2 * (√(m₂.rnDeriv μ ω).toReal) ^ 2 := by
          linarith [sq_nonneg (√(m₁.rnDeriv μ ω).toReal - √(m₂.rnDeriv μ ω).toReal)]
        _ = 2 * (m₁.rnDeriv μ ω).toReal + 2 * (m₂.rnDeriv μ ω).toReal := by
          simp [sq_sqrt ENNReal.toReal_nonneg]
  _ = 2 * ∫ ω, (m₁.rnDeriv μ ω).toReal ∂μ + 2 * ∫ ω, (m₂.rnDeriv μ ω).toReal ∂μ := by
    rw [integral_add, integral_const_mul, integral_const_mul]
    <;> exact Measure.integrable_toReal_rnDeriv.const_mul 2
  _ = 4 := by
    rw [Measure.integral_toReal_rnDeriv hm₁, Measure.integral_toReal_rnDeriv hm₂]
    norm_num

/-- The QMD remainder, formed by subtracting an `L²(m₂)` term transported to `μ` by
multiplication by `√(dm₂/dμ)`, is in `L²(μ)`. -/
private lemma Lp.memLp_sqrt_rnDeriv_sub_sqrt_rnDeriv_sub_const_mul {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {m₁ m₂ μ : Measure Ω} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    [SigmaFinite m₂] [m₂.HaveLebesgueDecomposition μ] (hm₂ : m₂ ≪ μ) (c : ℝ)
    (u : Ω →₂[m₂] ℝ) :
    MemLp (fun ω => √(m₁.rnDeriv μ ω).toReal - √(m₂.rnDeriv μ ω).toReal -
      c * u ω * √(m₂.rnDeriv μ ω).toReal) 2 μ := by
  refine ((memLp_sqrt_rnDeriv m₁ μ).sub (memLp_sqrt_rnDeriv m₂ μ)).sub ?_
  simpa [mul_assoc] using (Lp.memLp_mul_sqrt_rnDeriv hm₂ u).const_mul c

/-- The scaled integral of the QMD remainder against the sum of square-root densities tends to
zero. -/
private lemma tendsto_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ h : E} {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    Tendsto (fun p => p.1⁻¹ * ∫ ω,
      (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal -
      2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) *
      (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + √((P θ).rnDeriv μ ω).toReal) ∂μ) l
      (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 <| squeeze_zero' (g := fun p => ‖p.1‖⁻¹ *
    lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
    √((P θ).rnDeriv μ ω).toReal -
    2⁻¹ * (A (p.1 • h) ω) * √((P θ).rnDeriv μ ω).toReal) 2 μ * 2) ?_ ?_ ?_
  · filter_upwards with p using norm_nonneg _
  · filter_upwards [he] with p hp
    simp only [norm_mul, norm_inv]
    nth_rw 1 [mul_assoc]
    gcongr
    have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
    have : IsProbabilityMeasure (P θ) := hprob _ hθ
    calc
      ‖∫ ω, (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal -
        2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) *
        (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + √((P θ).rnDeriv μ ω).toReal) ∂μ‖
        ≤ ∫ ω, ‖(√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal)‖ *
            ‖(√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal
            + √((P θ).rnDeriv μ ω).toReal)‖ ∂μ := by grw [norm_integral_le_integral_norm]; simp
      _ ≤ (∫ ω, ‖(√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal -
            2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal)‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
            (∫ ω, ‖(√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal
            + √((P θ).rnDeriv μ ω).toReal)‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
        refine integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two ?_ ?_
        · simpa using Lp.memLp_sqrt_rnDeriv_sub_sqrt_rnDeriv_sub_const_mul (hs _ hθ) 2⁻¹
            (A (p.1 • h))
        · simpa [Pi.add_def] using (memLp_sqrt_rnDeriv (P (θ + p.1 • p.2)) μ).add
            (memLp_sqrt_rnDeriv (P θ) μ)
      _ ≤ _ := by
        gcongr
        · exact lpNorm_nonneg
        · rw [lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp)]
          · simp
          · refine (AEStronglyMeasurable.sub ?_ ?_).sub (AEStronglyMeasurable.mul ?_ ?_)
            rotate_left 2
            · exact (Lp.stronglyMeasurable (A (p.1 • h))).aestronglyMeasurable.const_mul _
            all_goals exact ((Measure.measurable_rnDeriv
              _ _).aemeasurable.ennreal_toReal.sqrt).aestronglyMeasurable
        · exact integral_sq_sum_le_two (hs _ hp) (hs _ hθ)
  · have := ((tendsto_zero_iff_abs_tendsto_zero _).1 <| hA h l hzero hh he).mul_const 2
    rw [zero_mul 2] at this
    exact this.congr fun p => by simp

end TendstoZero

section TendstoIntegralScore

/-- The unscaled Hadamard QMD remainder tends to zero along any admissible local path. -/
private lemma unscaled_remainder_tendsto_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω}
    [SigmaFinite μ] {s : Set E} {θ h : E} {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝[≠] 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    Tendsto (fun p => lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
      √((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) l
      (𝓝 0) := by
  refine (zero_mul (0 : ℝ) ▸ (tendsto_nhds_of_tendsto_nhdsWithin hzero).mul
    (hA h l (tendsto_nhds_of_tendsto_nhdsWithin hzero) hh he)).congr' ?_
  filter_upwards [(tendsto_nhdsWithin_iff.1 hzero).2] with p hp
  simp_all

/-- This is similar to `score_tendsto_zero`. -/
private lemma score_tendsto_zero' {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ : E} (h : E) (A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝 0)) :
    Tendsto (fun p => lpNorm (fun ω =>
      2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0) := by
  have : IsProbabilityMeasure (P θ) := hprob _ hθ
  have hscore_Lp : Tendsto (fun p : ℝ × E => (2⁻¹ : ℝ) • A (p.1 • h)) l (𝓝 0) := by
    simpa [smul_smul] using (hzero.const_mul (2⁻¹ : ℝ)).smul_const (A h)
  refine (tendsto_zero_iff_norm_tendsto_zero.1 hscore_Lp).congr' (.of_forall fun p => ?_)
  rw [Lp.norm_def, toReal_eLpNorm]
  · refine (Lp.lpNorm_mul_sqrt_rnDeriv_of_ae_eq (hs _ hθ) ((2⁻¹ : ℝ) • A (p.1 • h)) ?_).symm
    exact(Lp.coeFn_smul (2⁻¹ : ℝ) (A (p.1 • h))).symm
  · fun_prop

/-- The square-root density itself is continuous along an admissible Hadamard path in `L²(μ)`. -/
private lemma tendsto_sqrt_density {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ h : E} {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝[≠] 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    Tendsto (fun p => lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
      √((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ ((zero_add (0 : ℝ)) ▸
    (unscaled_remainder_tendsto_zero hA hzero hh he).add
    (score_tendsto_zero' h A hθ hprob hs (tendsto_nhds_of_tendsto_nhdsWithin hzero)))
  · filter_upwards with p using lpNorm_nonneg
  · filter_upwards [he] with p hp
    have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
    have : IsProbabilityMeasure (P θ) := hprob _ hθ
    rw [add_comm (lpNorm _ 2 μ)]
    refine lpNorm_le_lpNorm_add_lpNorm_sub' ?_ (by norm_num)
    simpa [mul_assoc] using (Lp.memLp_mul_sqrt_rnDeriv (hs _ hθ) (A (p.1 • h))).const_mul 2⁻¹

/-- Integrability for `u * √(dm₁/dμ) * (√(dm₂/dμ) + √(dm₁/dμ))`. -/
private lemma Lp.integrable_mul_sqrt_rnDeriv_mul_sqrt_rnDeriv_add {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {m₁ μ : Measure Ω} [IsFiniteMeasure m₁] (m₂ : Measure Ω)
    [IsFiniteMeasure m₂] [SigmaFinite m₁] [m₁.HaveLebesgueDecomposition μ] (hm₁ : m₁ ≪ μ)
    (u : Ω →₂[m₁] ℝ) :
    Integrable (fun ω => u ω * √(m₁.rnDeriv μ ω).toReal *
      (√(m₂.rnDeriv μ ω).toReal + √(m₁.rnDeriv μ ω).toReal)) μ :=
  (Lp.memLp_mul_sqrt_rnDeriv hm₁ u).integrable_mul
    ((memLp_sqrt_rnDeriv m₂ μ).add (memLp_sqrt_rnDeriv m₁ μ))

/-- The score term paired with the sum of square-root densities converges to the score integral. -/
private lemma tendsto_integral_score {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ h : E} {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝[≠] 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    Tendsto (fun p => ∫ ω, 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal *
      (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + √((P θ).rnDeriv μ ω).toReal) ∂μ) l
      (𝓝 <| ∫ ω, A h ω ∂P θ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun p =>
    lpNorm (fun ω => 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal) 2 μ *
    lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
      √((P θ).rnDeriv μ ω).toReal) 2 μ) ?_ ?_ ?_
  · filter_upwards with p using norm_nonneg _
  · filter_upwards [he] with p hp
    have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
    have : IsProbabilityMeasure (P θ) := hprob _ hθ
    have hf' : MemLp (fun ω => 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal) (ENNReal.ofReal 2) μ := by
      simpa [mul_assoc] using (Lp.memLp_mul_sqrt_rnDeriv (hs _ hθ) (A h)).const_mul 2⁻¹
    have hg' : MemLp (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
      √((P θ).rnDeriv μ ω).toReal) (ENNReal.ofReal 2) μ := by
      simpa [Pi.sub_def] using (memLp_sqrt_rnDeriv (P (θ + p.1 • p.2)) μ).sub
        (memLp_sqrt_rnDeriv (P θ) μ)
    calc
      ‖∫ ω, 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal * (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
        √((P θ).rnDeriv μ ω).toReal) ∂μ - ∫ ω, A h ω ∂P θ‖
        = ‖∫ ω, 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal *
            (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + √((P θ).rnDeriv μ ω).toReal) ∂μ -
            ∫ ω, 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal *
            (2 * √((P θ).rnDeriv μ ω).toReal) ∂μ‖ := by
        suffices ∫ ω, A h ω ∂P θ = ∫ ω, 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal *
          (2 * √((P θ).rnDeriv μ ω).toReal) ∂μ from by rw [this]
        field_simp
        simp [mul_comm, ← integral_toReal_rnDeriv_mul (hs _ hθ)]
      _ = ‖∫ ω, 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal *
            (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal) ∂μ‖ := by
        rw [← integral_sub]
        · ring_nf
        · simpa [mul_assoc] using (Lp.integrable_mul_sqrt_rnDeriv_mul_sqrt_rnDeriv_add _ (hs _ hθ)
            (A h)).const_mul 2⁻¹
        · convert (Lp.integrable_mul_sqrt_rnDeriv_mul_sqrt_rnDeriv_add (P θ) (hs _ hθ)
            (A h)).const_mul (2⁻¹ : ℝ) using 1
          ring_nf
      _ ≤ ∫ ω, ‖2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal *
            (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - √((P θ).rnDeriv μ ω).toReal)‖ ∂μ := by
        grw [norm_integral_le_integral_norm]
      _ ≤ (∫ ω, ‖2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
            (∫ ω, ‖√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
        have hf' :
          MemLp (fun ω => 2⁻¹ * A h ω * √((P θ).rnDeriv μ ω).toReal) (ENNReal.ofReal 2) μ := by
          simpa [mul_assoc] using (Lp.memLp_mul_sqrt_rnDeriv (hs _ hθ) (A h)).const_mul 2⁻¹
        have hg' : MemLp (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
            √((P θ).rnDeriv μ ω).toReal) (ENNReal.ofReal 2) μ := by
          simpa [Pi.sub_def] using (memLp_sqrt_rnDeriv (P (θ + p.1 • p.2)) μ).sub
            (memLp_sqrt_rnDeriv (P θ) μ)
        simpa using integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
      _ = _:= by
        rw [lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hg'.aestronglyMeasurable,
          lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hf'.aestronglyMeasurable]
        simp
  · simpa using tendsto_const_nhds.mul (tendsto_sqrt_density hA hθ hprob hs hzero hh he)

end TendstoIntegralScore

section MeanZeroScore

/-- The difference of squares formula for two square root densities of probability measures. -/
private lemma integral_diff_sq_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {m₁ m₂ μ : Measure Ω} [SigmaFinite μ]
    [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂] (hm₁ : m₁ ≪ μ) (hm₂ : m₂ ≪ μ) :
    ∫ ω, (√(m₁.rnDeriv μ ω).toReal - √(m₂.rnDeriv μ ω).toReal) *
      (√(m₁.rnDeriv μ ω).toReal + √(m₂.rnDeriv μ ω).toReal) ∂μ = 0 := by
  rw [integral_congr_ae, integral_sub (Measure.integrable_toReal_rnDeriv (μ := m₁) (ν := μ))
      (Measure.integrable_toReal_rnDeriv (μ := m₂) (ν := μ)),
      Measure.integral_toReal_rnDeriv hm₁, Measure.integral_toReal_rnDeriv hm₂]
  · norm_num
  · filter_upwards with ω
    calc
      _ = √(m₁.rnDeriv μ ω).toReal ^ 2 - √(m₂.rnDeriv μ ω).toReal ^ 2 := by ring
      _ = (m₁.rnDeriv μ ω).toReal - (m₂.rnDeriv μ ω).toReal := by
        simp [sq_sqrt ENNReal.toReal_nonneg]

/-- Integrability for the QMD remainder multiplied by the sum of the two square-root densities. -/
private lemma Lp.integrable_sqrt_rnDeriv_sub_sqrt_rnDeriv_sub_const_mul_mul_sqrt_rnDeriv_add
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {m₁ m₂ μ : Measure Ω} [IsFiniteMeasure m₁]
    [IsFiniteMeasure m₂] [SigmaFinite m₂] [m₂.HaveLebesgueDecomposition μ] (hm₂ : m₂ ≪ μ)
    (c : ℝ) (u : Ω →₂[m₂] ℝ) :
    Integrable (fun ω => (√(m₁.rnDeriv μ ω).toReal - √(m₂.rnDeriv μ ω).toReal -
      c * u ω * √(m₂.rnDeriv μ ω).toReal) *
      (√(m₁.rnDeriv μ ω).toReal + √(m₂.rnDeriv μ ω).toReal)) μ :=
  (Lp.memLp_sqrt_rnDeriv_sub_sqrt_rnDeriv_sub_const_mul hm₂ c u).integrable_mul
    ((memLp_sqrt_rnDeriv m₁ μ).add (memLp_sqrt_rnDeriv m₂ μ))

/-- **Mean zero score** for a Hadamard quadratic mean derivative. -/
-- ANCHOR: integralScoreEqZero
theorem integral_score_eq_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ h : E} {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    [l.NeBot] (hzero : Tendsto Prod.fst l (𝓝[≠] 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    ∫ ω, A h ω ∂P θ = 0 := by
-- ANCHOR_END: integralScoreEqZeroSig
  refine tendsto_nhds_unique (zero_add (∫ ω, A h ω ∂P θ) ▸
    (tendsto_zero hA hθ hprob hs (tendsto_nhds_of_tendsto_nhdsWithin hzero) hh he).add
    (tendsto_integral_score hA hθ hprob hs hzero hh he)) ?_
  apply EventuallyEq.tendsto (EventuallyEq.symm ?_)
  filter_upwards [he, (tendsto_nhdsWithin_iff.1 hzero).2] with p hp hn
  have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
  have : IsProbabilityMeasure (P θ) := hprob _ hθ
  calc
    0 = p.1⁻¹ * 0 := by simp
    _ = p.1⁻¹ * (∫ ω, (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          √((P θ).rnDeriv μ ω).toReal) * (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          √((P θ).rnDeriv μ ω).toReal) ∂μ) := by rw [integral_diff_sq_eq_zero (hs _ hp) (hs _ hθ)]
    _ = p.1⁻¹ * (∫ ω, (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          √((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal +
          2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) *
          (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          √((P θ).rnDeriv μ ω).toReal) ∂μ) := by simp
    _ = p.1⁻¹ * (∫ ω, (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          √((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) *
          (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + √((P θ).rnDeriv μ ω).toReal) ∂μ +
          ∫ ω, 2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal *
          (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          √((P θ).rnDeriv μ ω).toReal) ∂μ) := by
        simp only [add_mul]
        rw [integral_add]
        · exact Lp.integrable_sqrt_rnDeriv_sub_sqrt_rnDeriv_sub_const_mul_mul_sqrt_rnDeriv_add
            (hs _ hθ) 2⁻¹ (A (p.1 • h))
        · simpa [mul_assoc] using (Lp.integrable_mul_sqrt_rnDeriv_mul_sqrt_rnDeriv_add _ (hs _ hθ)
            (A (p.1 • h))).const_mul 2⁻¹
    _ = p.1⁻¹ * (∫ ω, (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          √((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) *
          (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + √((P θ).rnDeriv μ ω).toReal) ∂μ) +
          p.1⁻¹ * (∫ ω, 2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal *
          (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          √((P θ).rnDeriv μ ω).toReal) ∂μ) := by simp [mul_add]
    _ = p.1⁻¹ * (∫ ω, (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          √((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) *
          (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + √((P θ).rnDeriv μ ω).toReal) ∂μ) +
          p.1⁻¹ * (∫ ω, 2⁻¹ * p.1 * A h ω * √((P θ).rnDeriv μ ω).toReal *
          (√((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          √((P θ).rnDeriv μ ω).toReal) ∂μ) := by
        simp only [map_smul, add_right_inj, mul_eq_mul_left_iff, inv_eq_zero,
          fun ω => mul_assoc 2⁻¹ ((p.1 • A h) ω) (√((P θ).rnDeriv μ ω).toReal),
          fun ω => mul_assoc 2⁻¹  p.1 (A h ω),
          fun ω => mul_assoc 2⁻¹ (p.1 * A h ω) (√((P θ).rnDeriv μ ω).toReal)]
        refine Or.inl (integral_congr_ae ?_)
        filter_upwards [Measure.rnDeriv_eq_zero_of_ae_eq (hs _ hθ) (Lp.coeFn_smul p.1 (A h))] with
          ω hω
        by_cases! hne : (p.1 • A h) ω ≠ (p.1 • (A h : Ω → ℝ)) ω
        · simp [hω hne]
        · rw [hne]
          simp [Pi.smul_apply, smul_eq_mul]
    _ = _ := by
        simp only [map_smul, mul_comm 2⁻¹ p.1, add_right_inj, mul_assoc]
        rw [integral_const_mul_of_integrable (c := p.1), inv_mul_cancel_left₀ hn]
        simpa [mul_assoc] using (Lp.integrable_mul_sqrt_rnDeriv_mul_sqrt_rnDeriv_add _ (hs _ hθ)
          (A h)).const_mul 2⁻¹
-- ANCHOR_END: integralScoreEqZero

/-- **Mean zero score** when the parameter set `s` is a neighborhood of `θ`. -/
theorem integral_score_eq_zero_of_mem_nhds {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] [SeparatelyContinuousAdd E] [ContinuousSMul ℝ E]
    {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ] {s : Set E} {θ h : E}
    {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)} (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A)
    (hs_nhds : s ∈ 𝓝 θ) (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) :
    ∫ ω, A h ω ∂P θ = 0 := by
  refine integral_score_eq_zero hA (mem_of_mem_nhds hs_nhds) hprob hs tendsto_fst tendsto_snd
    (Tendsto.eventually ?_ hs_nhds)
  simpa using ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_fst).smul
    (tendsto_snd (f := 𝓝[≠] (0 : ℝ)))).const_add θ

end MeanZeroScore

end QMD
