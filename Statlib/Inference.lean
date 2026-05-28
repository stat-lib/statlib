/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

module

public import Mathlib.Probability.Kernel.Defs

/-!
# Statistical Inference

We define two models for statistical inference: one based on collections of measures and the other
on collections of kernels. We show that the former is a special case of the latter by endowing the
space of kernels with a measurable-space structure and constructing a canonical map from the space
of measures into the space of kernels.

## Main definitions

* `InferenceModelofMeasure`: a measure-based inference model, consisting of a collection of
  measures, a measurable functional of the underlying measure, observed data, a randomized decision
  rule, and a measurable loss function.
* `ProbabilityTheory.Kernel.of_measure`: the constant kernel induced by a measure.
* `ProbabilityTheory.Kernel.measurableEquiv_rangeFactorization_of_measure`: the measurable
  equivalence between measures and the range of the constant-kernel map.
* `InferenceModelofKernel`: a kernel-based inference model.
* `InferenceModelofKernel.of_InferenceModelofMeasure`: the construction turning a measure-based
  inference model into a kernel-based one by using constant kernels.

-/

@[expose] public section

open scoped ENNReal Topology

open MeasureTheory ProbabilityTheory Filter

structure InferenceModelofMeasure (ι : Type*) (Ω S X Y : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] where
  domain (i : ι) : Set (Measure (Ω i))
  functional (i : ι) : domain i → S i
  measurable_functional (i : ι) : Measurable (functional i)
  data (i : ι) : Ω i → X i
  measurable_data (i : ι) : Measurable (data i)
  decision_rule (i : ι) : Kernel (X i) (Y i)
  loss_function (i : ι) : (Y i) → (S i) → ℝ≥0∞
  measurable_loss_function (i : ι) : Measurable (loss_function i).uncurry

namespace InferenceModelofMeasure

variable {ι : Type*} {θ Ω S X Y : ι → Type} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]

noncomputable def conditionalRisk (I : InferenceModelofMeasure ι Ω S X Y) {i : ι}
    {μ : Measure (Ω i)} (hμ : μ ∈ I.domain i) : ℝ≥0∞ :=
  ∫⁻ ω : Ω i, ∫⁻ y : Y i,
    (I.loss_function i) y (I.functional i ⟨μ, hμ⟩) ∂(I.decision_rule i) ((I.data i) ω) ∂μ

def IsConsistent (l : Filter ι) (I : InferenceModelofMeasure ι Ω S X Y) : Prop :=
  ∀ (μ : ∀ i, Measure (Ω i)), (hμ : ∀ i, μ i ∈ I.domain i) →
    Tendsto (fun i => conditionalRisk I (hμ i)) l (𝓝 0)

def IsUniformlyConsistent (l : Filter ι) (I : InferenceModelofMeasure ι Ω S X Y) : Prop :=
  Tendsto (fun i =>
    ⨆ (μ : ∀ i, Measure (Ω i)), ⨆ (hμ : ∀ i, μ i ∈ I.domain i), conditionalRisk I (hμ i))
    l (𝓝 0)

def HasRateOfConvergence (l : Filter ι) (I : InferenceModelofMeasure ι Ω S X Y) (r : ι → ℝ≥0∞) :
    Prop :=
  0 < l.liminf (fun i => (⨆ (μ : ∀ i, Measure (Ω i)),
    ⨆ (hμ : ∀ i, μ i ∈ I.domain i), conditionalRisk I (hμ i)) / r i) ∧
    l.limsup (fun i => (⨆ (μ : ∀ i, Measure (Ω i)),
    ⨆ (hμ : ∀ i, μ i ∈ I.domain i), conditionalRisk I (hμ i)) / r i) < ∞

end InferenceModelofMeasure

-- In this section, we define a measurable space structure on the space of kernels and a canonical
-- map from the space of measures to the space of kernels.

namespace ProbabilityTheory

namespace Kernel

/-- Each measure induces a constant kernel. -/
def of_measure (θ Ω : Type*) [MeasurableSpace θ]
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) : Kernel θ Ω where
  toFun := fun _ => μ
  measurable' := measurable_const

theorem injective_kernel_of_measure (θ Ω : Type*) [MeasurableSpace θ]
    [hθ : Nonempty θ] [mΩ : MeasurableSpace Ω] : Function.Injective (of_measure θ Ω) := by
  refine fun μ ν hμν => ?_
  simp_all only [of_measure, mk.injEq]
  exact congr_fun hμν Classical.ofNonempty

instance instMeasurableSpaceKernel (θ Ω : Type*) [MeasurableSpace θ] [MeasurableSpace Ω] :
    MeasurableSpace (Kernel θ Ω) :=
  ⨆ (t : θ), Measure.instMeasurableSpace.comap fun κ => κ t

theorem measurable_eval {θ Ω : Type*} [MeasurableSpace θ]
    [MeasurableSpace Ω] (t : θ) :
    Measurable fun κ : Kernel θ Ω => κ t :=
  Measurable.of_comap_le <| le_iSup_of_le t <| le_rfl

theorem measurable_eval' {θ Ω : Type*} [MeasurableSpace θ]
    [MeasurableSpace Ω] (t : θ) {s : Set Ω} (hs : MeasurableSet s) :
    Measurable fun κ : Kernel θ Ω => κ t s :=
  (Measure.measurable_coe hs).comp (measurable_eval t)

theorem measurable_of_measurable_eval {α θ Ω : Type*} [MeasurableSpace α]
    [MeasurableSpace θ] [MeasurableSpace Ω] (κ : α → Kernel θ Ω)
    (hκ : ∀ t, Measurable fun a => κ a t) :
    Measurable κ := by
  simp only [measurable_iff_comap_le, instMeasurableSpaceKernel, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp]
  exact iSup_le fun t => (hκ t).comap_le

/-- A function into the space of kernels is measurable iff all its evaluation maps are
measurable. -/
theorem measurable_iff {α θ Ω : Type*} [MeasurableSpace α]
    [MeasurableSpace θ] [MeasurableSpace Ω] {κ : α → Kernel θ Ω} :
    Measurable κ ↔ ∀ t, Measurable fun a => κ a t :=
  ⟨fun hκ t => (measurable_eval t).comp hκ, measurable_of_measurable_eval κ⟩

theorem measurable_kernel_of_measure (θ Ω : Type*) [MeasurableSpace θ]
    [mΩ : MeasurableSpace Ω] : Measurable (of_measure θ Ω) :=
  measurable_iff.2 fun _ => measurable_id

/-- The inverse of the range factorization of the constant-kernel map. -/
noncomputable def inv_rangeFactorization_of_measure (θ Ω : Type*)
    [MeasurableSpace θ] [Nonempty θ] [mΩ : MeasurableSpace Ω] :
    Set.range (of_measure θ Ω) → Measure Ω :=
  fun κ => κ.1 Classical.ofNonempty

@[simp]
theorem inv_rangeFactorization_of_measure_apply (θ Ω : Type*)
    [MeasurableSpace θ] [Nonempty θ] [mΩ : MeasurableSpace Ω] (μ : Measure Ω) :
    inv_rangeFactorization_of_measure θ Ω
      (Set.rangeFactorization (of_measure θ Ω) μ) = μ :=
  rfl

@[simp]
theorem rangeFactorization_of_measure_inv (θ Ω : Type*)
    [MeasurableSpace θ] [Nonempty θ] [mΩ : MeasurableSpace Ω]
    (κ : Set.range (of_measure θ Ω)) :
    Set.rangeFactorization (of_measure θ Ω)
      (inv_rangeFactorization_of_measure θ Ω κ) = κ := by
  rcases κ with ⟨κ, μ, rfl⟩
  rfl

/-- The inverse is measurable. -/
theorem measurable_inv_rangeFactorization_of_measure (θ Ω : Type*)
    [MeasurableSpace θ] [Nonempty θ] [mΩ : MeasurableSpace Ω] :
    Measurable (inv_rangeFactorization_of_measure θ Ω) :=
  (measurable_eval Classical.ofNonempty).comp measurable_subtype_coe

/-- The range factorization of the constant-kernel map as a measurable equivalence. -/
noncomputable def measurableEquiv_rangeFactorization_of_measure
    (θ Ω : Type*) [MeasurableSpace θ] [Nonempty θ] [mΩ : MeasurableSpace Ω] :
    Measure Ω ≃ᵐ Set.range (of_measure θ Ω) where
  toFun := Set.rangeFactorization (of_measure θ Ω)
  invFun := inv_rangeFactorization_of_measure θ Ω
  left_inv := inv_rangeFactorization_of_measure_apply θ Ω
  right_inv := rangeFactorization_of_measure_inv θ Ω
  measurable_toFun := (measurable_kernel_of_measure θ Ω).subtype_mk
  measurable_invFun := measurable_inv_rangeFactorization_of_measure θ Ω

/-- The inverse from an image of measures under `of_measure` back to those measures. -/
noncomputable def imageToMeasure (θ Ω : Type*) [MeasurableSpace θ]
    [Nonempty θ] [mΩ : MeasurableSpace Ω] (s : Set (Measure Ω)) :
    (of_measure θ Ω) '' s → s :=
  fun κ => ⟨inv_rangeFactorization_of_measure θ Ω
    (Set.inclusion (Set.image_subset_range (of_measure θ Ω) s) κ), by
    obtain ⟨μ, hμ, hκ⟩ := κ.2
    simpa [inv_rangeFactorization_of_measure, ← hκ, of_measure]⟩

theorem measurable_imageToMeasure (θ Ω : Type*) [MeasurableSpace θ]
    [Nonempty θ] [mΩ : MeasurableSpace Ω] (s : Set (Measure Ω)) :
    Measurable (imageToMeasure θ Ω s) :=
  ((measurable_inv_rangeFactorization_of_measure θ Ω).comp
    measurable_subtype_coe.subtype_mk).subtype_mk

end Kernel

end ProbabilityTheory

structure InferenceModelofKernel (ι : Type*) (θ Ω S X Y : ι → Type) [∀ i, MeasurableSpace (θ i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSpace (Y i)] where
  domain (i : ι) : Set (Kernel (θ i) (Ω i))
  functional (i : ι) : domain i → S i
  measurable_functional (i : ι) : Measurable (functional i)
  data (i : ι) : Ω i → X i
  measurable_data (i : ι) : Measurable (data i)
  decision_rule (i : ι) : Kernel (X i) (Y i)
  loss_function (i : ι) : (Y i) → (S i) → ℝ≥0∞
  measurable_loss_function (i : ι) : Measurable (loss_function i).uncurry

namespace InferenceModelofKernel

variable {ι : Type*} {θ Ω S X Y : ι → Type} [∀ i, MeasurableSpace (θ i)]
  [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, MeasurableSpace (Y i)]

noncomputable def of_InferenceModelofMeasure [∀ i, Nonempty (θ i)]
    (I : InferenceModelofMeasure ι Ω S X Y) :
    InferenceModelofKernel ι θ Ω S X Y where
  domain (i : ι) := (Kernel.of_measure (θ i) (Ω i)) '' (I.domain i)
  functional (i : ι) := (I.functional i) ∘ Kernel.imageToMeasure (θ i) (Ω i) (I.domain i)
  measurable_functional (i : ι) :=
    (I.measurable_functional i).comp (Kernel.measurable_imageToMeasure (θ i) (Ω i) (I.domain i))
  data := I.data
  measurable_data := I.measurable_data
  decision_rule := I.decision_rule
  loss_function := I.loss_function
  measurable_loss_function := I.measurable_loss_function

noncomputable def conditionalRisk (I : InferenceModelofKernel ι θ Ω S X Y) {i : ι} (t : θ i)
    {κ : Kernel (θ i) (Ω i)} (hκ : κ ∈ I.domain i) : ℝ≥0∞ :=
  ∫⁻ ω : Ω i, ∫⁻ y : Y i,
    (I.loss_function i) y (I.functional i ⟨κ, hκ⟩) ∂(I.decision_rule i) ((I.data i) ω) ∂κ t

def IsConsistent (l : Filter ι) (I : InferenceModelofKernel ι θ Ω S X Y) : Prop :=
  ∀ (t : ∀ i, θ i) (κ : ∀ i, Kernel (θ i) (Ω i)), (hκ : ∀ i, κ i ∈ I.domain i) →
    Tendsto (fun i => conditionalRisk I (t i) (hκ i)) l (𝓝 0)

def IsUniformlyConsistent (l : Filter ι) (I : InferenceModelofKernel ι θ Ω S X Y) : Prop :=
  ∀ (t : ∀ i, θ i), Tendsto (fun i =>
    ⨆ (κ : ∀ i, Kernel (θ i) (Ω i)), ⨆ (hκ : ∀ i, κ i ∈ I.domain i), conditionalRisk I (t i) (hκ i))
    l (𝓝 0)

end InferenceModelofKernel
