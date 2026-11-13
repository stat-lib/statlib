/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.Risk.Basic
public import Statlib.ForMathlib.Probability.Decision.BayesEstimator
public import Statlib.ForMathlib.Probability.Decision.Risk.Basic
public import Statlib.ForMathlib.Probability.Decision.ZeroOneLoss

/-!
# Simple Bayesian binary hypothesis testing

We test between two measures `μ` and `ν`, with a prior `π` on `Bool` (`false` stands for `μ` and
`true` for `ν`) and the 0-1 loss. This is the estimation problem with parameter space `Bool`,
data generating kernel `Kernel.boolKernel μ ν` and the 0-1 loss `zeroOneLoss` on `Bool`.

## Main definitions

* `binaryArgminEstimator μ ν π`: the test that answers `true` (that is, `ν`) where
  `π {false} * ∂μ/∂P ≤ π {true} * ∂ν/∂P`, for `P = Kernel.boolKernel μ ν ∘ₘ π`.
* `bayesBinaryRisk μ ν π`: the Bayes risk of the simple binary hypothesis testing problem between
  `μ` and `ν` with respect to the prior `π`.

## Main statements

* `isArgminEstimator_binaryArgminEstimator`: `binaryArgminEstimator μ ν π` is an argmin estimator,
  hence a Bayes estimator.
* `bayesBinaryRisk_le_bayesBinaryRisk_comp`: data-processing inequality.
* `bayesBinaryRisk_eq_iInf_measurableSet`: the Bayes binary risk is the infimum over the measurable
  sets `E` of the risk `π {false} * μ E + π {true} * ν Eᶜ` of the test with rejection region `E`.
* `bayesBinaryRisk_eq_lintegral_min_rnDeriv`: the Bayes binary risk is
  `∫⁻ x, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν`.
* `bayesBinaryRisk_eq_zero_iff_mutuallySingular`: for a prior with positive weights, the Bayes
  binary risk vanishes if and only if `μ ⟂ₘ ν`.
* `bayesBinaryRisk_eq_lintegral_min`, `toReal_bayesBinaryRisk_eq_integral_abs`: integral formulas
  for the Bayes binary risk with respect to the joint law `Kernel.boolKernel μ ν ∘ₘ π`.

This file is adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds).
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳}

section SimpleBinaryHypTest

@[simp] lemma zeroOneLoss_true_false : zeroOneLoss true false = 1 := zeroOneLoss_of_ne (by simp)

@[simp] lemma zeroOneLoss_false_true : zeroOneLoss false true = 1 := zeroOneLoss_of_ne (by simp)

@[simp]
lemma lintegral_zeroOneLoss_true (ξ : Measure Bool) :
    ∫⁻ z, zeroOneLoss true z ∂ξ = ξ {false} := by
  simp [lintegral_fintype]

@[simp]
lemma lintegral_zeroOneLoss_false (ξ : Measure Bool) :
    ∫⁻ z, zeroOneLoss false z ∂ξ = ξ {true} := by
  simp [lintegral_fintype]

/-- For a measure `ζ` on `Bool`, the smallest expected 0-1 loss of an action is
`min (ζ {false}) (ζ {true})`: this is the Bayes risk of a constant kernel for simple binary
hypothesis testing with prior `ζ`. -/
lemma iInf_lintegral_zeroOneLoss_bool (ζ : Measure Bool) :
    ⨅ y, ∫⁻ θ, zeroOneLoss θ y ∂ζ = min (ζ {false}) (ζ {true}) := by
  rw [iInf_bool_eq]
  simp [lintegral_fintype]

/-- The function `x ↦ 𝕀{π₀ * ∂μ/∂(boolKernel μ ν ∘ₘ π) x ≤ π₁ * ∂ν/∂(boolKernel μ ν ∘ₘ π) x}`.
It is an argmin estimator for the simple binary hypothesis testing problem. -/
noncomputable
def binaryArgminEstimator (μ ν : Measure 𝒳) (π : Measure Bool) : 𝒳 → Bool :=
  let E : Set 𝒳 := {x | π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x
    ≤ π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x}
  fun x ↦ Bool.ofNat (E.indicator 1 x)

/-- `binaryArgminEstimator μ ν π` maximizes the posterior weight
`z ↦ π {z} * ∂(boolKernel μ ν z)/∂(boolKernel μ ν ∘ₘ π)`, hence is an argmin estimator, and a
Bayes estimator, for simple binary hypothesis testing. -/
lemma isArgminEstimator_binaryArgminEstimator (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    IsArgminEstimator zeroOneLoss (Kernel.boolKernel μ ν) π
      (binaryArgminEstimator μ ν π) := by
  refine isArgminEstimator_zeroOneLoss ?_ (ae_of_all _ fun x z ↦ ?_)
  · simp_rw [binaryArgminEstimator]
    refine Measurable.of_discrete.fun_comp (measurable_one.indicator (measurableSet_le ?_ ?_))
      <;> fun_prop
  · have hf : binaryArgminEstimator μ ν π x = decide (π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x
        ≤ π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x) := by
      simp [binaryArgminEstimator, Bool.ofNat, Set.indicator_apply]
    rw [hf]
    by_cases h : π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x
        ≤ π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x
    · cases z <;> simp [h]
    · cases z <;> simp [h, (not_le.mp h).le]

end SimpleBinaryHypTest

/-- The Bayes risk of simple binary hypothesis testing with respect to a prior. -/
noncomputable
def bayesBinaryRisk (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  bayesRisk zeroOneLoss (Kernel.boolKernel μ ν) π

lemma bayesBinaryRisk_eq_iInf_kernel (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = ⨅ (κ : Kernel 𝒳 Bool) (_ : IsMarkovKernel κ),
        π {true} * (κ ∘ₘ ν) {false} + π {false} * (κ ∘ₘ μ) {true} := by
  rw [bayesBinaryRisk, bayesRisk]
  congr with κ
  congr with _
  simp only [avgRisk, lintegral_bool, Kernel.comp_boolKernel, Kernel.boolKernel_apply,
    Bool.false_eq_true, ↓reduceIte, zeroOneLoss_self, zeroOneLoss_true_false,
    zeroOneLoss_false_true, zero_mul, one_mul, zero_add, add_zero]
  ring

variable {π : Measure Bool}

/-- `B (a•μ, b•ν; π) = B (μ, ν; (a*π₀, b*π₁)).` -/
lemma bayesBinaryRisk_smul_smul (μ ν : Measure 𝒳) (π : Measure Bool) (a b : ℝ≥0∞) :
    bayesBinaryRisk (a • μ) (b • ν) π
      = bayesBinaryRisk μ ν (π.withDensity (fun x ↦ bif x then b else a)) := by
  simp [bayesBinaryRisk_eq_iInf_kernel, lintegral_dirac, mul_assoc]

/-- The Bayes binary risk is positively homogeneous in the prior: scaling the prior by a finite
factor scales the Bayes binary risk by the same factor. -/
lemma bayesBinaryRisk_smul_prior (μ ν : Measure 𝒳) (π : Measure Bool) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    bayesBinaryRisk μ ν (c • π) = c * bayesBinaryRisk μ ν π :=
  bayesRisk_smul_prior _ _ _ hc

lemma bayesBinaryRisk_eq_bayesBinaryRisk_one_one (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = bayesBinaryRisk (π {false} • μ) (π {true} • ν) (Measure.boolMeasure 1 1) := by
  rw [bayesBinaryRisk_smul_smul, Measure.eq_boolMeasure π, Measure.withDensity_eq_boolMeasure]
  simp

/-- **Data processing inequality** for the Bayes binary risk. -/
lemma bayesBinaryRisk_le_bayesBinaryRisk_comp (μ ν : Measure 𝒳) (π : Measure Bool)
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    bayesBinaryRisk μ ν π ≤ bayesBinaryRisk (η ∘ₘ μ) (η ∘ₘ ν) π :=
  (bayesRisk_le_bayesRisk_comp _ _ _ η).trans_eq (by simp [bayesBinaryRisk, Kernel.comp_boolKernel])

@[simp]
lemma bayesBinaryRisk_self (μ : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ μ π = min (π {false}) (π {true}) * μ .univ := by
  rw [bayesBinaryRisk_eq_iInf_kernel]
  refine le_antisymm ?_ ?_
  · let η : Kernel 𝒳 Bool :=
      if π {true} ≤ π {false} then (Kernel.const 𝒳 (Measure.dirac false))
        else (Kernel.const 𝒳 (Measure.dirac true))
    refine iInf_le_of_le η ?_
    simp_rw [η]
    convert iInf_le _ ?_ using 1
    · split_ifs with h <;> simp [le_of_not_ge, h]
    · split_ifs <;> infer_instance
  · calc
      _ ≥ ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * (κ ∘ₘ μ) {false}
          + min (π {false}) (π {true}) * (κ ∘ₘ μ) {true} := by
        gcongr <;> simp
      _ = ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * μ .univ := by
        simp_rw [← mul_add, ← measure_union (show Disjoint {false} {true} from by simp)
          (by trivial), (set_fintype_card_eq_univ_iff ({false} ∪ {true})).mp rfl,
          Measure.comp_apply_univ]
        rfl
      _ = _ := by
        rw [iInf_subtype']
        convert iInf_const
        infer_instance

lemma bayesBinaryRisk_dirac (a b : ℝ≥0∞) (x : 𝒳) (π : Measure Bool) :
    bayesBinaryRisk (a • Measure.dirac x) (b • Measure.dirac x) π
      = min (π {false} * a) (π {true} * b) := by
  rw [bayesBinaryRisk_smul_smul, bayesBinaryRisk_self]
  simp [lintegral_dirac]

lemma bayesBinaryRisk_le_min (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π ≤ min (π {false} * μ .univ) (π {true} * ν .univ) := by
  convert bayesBinaryRisk_le_bayesBinaryRisk_comp μ ν π (Kernel.discard 𝒳)
  rw [Measure.discard_comp, Measure.discard_comp, bayesBinaryRisk_dirac]

/-- For a probability measure `μ`, the Bayes binary risk for a prior with mass `α` at `false` (for
example the prior `(α, 1 - α)`) is at most `α`. -/
lemma toReal_bayesBinaryRisk_boolMeasure_le (μ ν : Measure 𝒳) [IsProbabilityMeasure μ] (α : ℝ≥0)
    (b : ℝ≥0∞) :
    (bayesBinaryRisk μ ν (Measure.boolMeasure α b)).toReal ≤ α := by
  have h := (bayesBinaryRisk_le_min μ ν (Measure.boolMeasure α b)).trans (min_le_left _ _)
  rw [Measure.boolMeasure_apply_false, measure_univ, mul_one] at h
  exact ENNReal.toReal_le_coe_of_le_coe h

@[simp] lemma bayesBinaryRisk_zero_left : bayesBinaryRisk 0 ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le

@[simp] lemma bayesBinaryRisk_zero_right : bayesBinaryRisk μ 0 π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le

@[simp] lemma bayesBinaryRisk_zero_prior : bayesBinaryRisk μ ν 0 = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le

lemma bayesBinaryRisk_ne_top (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π ≠ ∞ := by
  refine lt_top_iff_ne_top.mp ((bayesBinaryRisk_le_min μ ν π).trans_lt ?_)
  exact min_lt_iff.mpr <| Or.inl <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)

lemma bayesBinaryRisk_of_measure_true_eq_zero (μ ν : Measure 𝒳) (hπ : π {true} = 0) :
    bayesBinaryRisk μ ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp [hπ])) zero_le

lemma bayesBinaryRisk_of_measure_false_eq_zero (μ ν : Measure 𝒳) (hπ : π {false} = 0) :
    bayesBinaryRisk μ ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp [hπ])) zero_le

lemma bayesBinaryRisk_symm (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π = bayesBinaryRisk ν μ (π.map Bool.not) := by
  have : (Bool.not ⁻¹' {true}) = {false} := by ext x; simp
  have h1 : (π.map Bool.not) {true} = π {false} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  have : (Bool.not ⁻¹' {false}) = {true} := by ext x; simp
  have h2 : (π.map Bool.not) {false} = π {true} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  simp_rw [bayesBinaryRisk_eq_iInf_kernel, h1, h2, add_comm, iInf_subtype']
  -- from this point on the proof is basically a change of variable inside the iInf,
  -- to do this I define an equivalence between `Subtype IsMarkovKernel` and itself through
  -- the `Bool.not` operation, maybe it can be shortened or something can be separated as
  -- a different lemma, but I'm not sure how useful this would be
  let e : (Kernel 𝒳 Bool) ≃ (Kernel 𝒳 Bool) := by
    have h_id : (Kernel.deterministic Bool.not .of_discrete).comap Bool.not .of_discrete
        = Kernel.id := by
      ext x : 1
      simp_rw [Kernel.comap_apply, Kernel.deterministic_apply, Kernel.id_apply, Bool.not_not]
    refine ⟨fun κ ↦ (Kernel.deterministic Bool.not .of_discrete) ∘ₖ κ,
      fun κ ↦ (Kernel.deterministic Bool.not .of_discrete) ∘ₖ κ, fun κ ↦ ?_, fun κ ↦ ?_⟩ <;>
    · dsimp
      ext x : 1
      rw [← Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap, h_id, Kernel.id_comp]
  let e' : (Subtype (@IsMarkovKernel 𝒳 Bool _ _)) ≃ (Subtype (@IsMarkovKernel 𝒳 Bool _ _)) := by
    refine ⟨fun ⟨κ, _⟩ ↦ ⟨e κ, ?_⟩, fun ⟨κ, _⟩ ↦ ⟨e.symm κ, ?_⟩, fun κ ↦ by simp, fun κ ↦ by simp⟩
      <;> simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e] <;> infer_instance
  rw [← Equiv.iInf_comp e']
  congr with κ
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e', e]
  have h3 b : Set.indicator {true} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {false} 1 b := by
    cases b <;> simp
  have h4 b : Set.indicator {false} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {true} 1 b := by
    cases b <;> simp
  congr 2 <;>
  · rw [Measure.bind_apply (by trivial) (Kernel.measurable _).aemeasurable,
      Measure.bind_apply (by trivial) (Kernel.measurable _).aemeasurable]
    congr with x
    rw [Kernel.comp_apply']
    simp only [Measure.dirac_apply' _ (show MeasurableSet {true} by trivial),
      Measure.dirac_apply' _ (show MeasurableSet {false} by trivial), Kernel.deterministic_apply]
    swap; trivial
    simp [h3, h4, lintegral_bool]

lemma avgRisk_binary_of_deterministic_indicator (μ ν : Measure 𝒳) (π : Measure Bool)
    {E : Set 𝒳} (hE : MeasurableSet E) :
    avgRisk zeroOneLoss (Kernel.boolKernel μ ν)
      (Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x))
        (Measurable.of_discrete.fun_comp (measurable_one.indicator hE))) π
      = π {false} * μ E + π {true} * ν Eᶜ := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    Measurable.of_discrete.fun_comp (measurable_one.indicator hE)
  have h1 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext; simp [Bool.ofNat]
  have h2 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext; simp [Bool.ofNat]
  simp only [avgRisk, lintegral_bool, Kernel.comp_boolKernel, Kernel.boolKernel_apply,
    Bool.false_eq_true, ↓reduceIte, zeroOneLoss_self, zeroOneLoss_true_false,
    zeroOneLoss_false_true, zero_mul, one_mul, zero_add, add_zero,
    Measure.deterministic_comp_eq_map, Measure.map_apply h_meas trivial, h1, h2]
  ring

lemma bayesBinaryRisk_eq_iInf_measurableSet (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  apply le_antisymm
  · simp_rw [le_iInf_iff, bayesBinaryRisk, bayesRisk]
    intro E hE
    rw [← avgRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le _ (iInf_le _ (Kernel.isMarkovKernel_deterministic _))
  · let E := {x | π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x
      ≤ π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x}
    have hE : MeasurableSet E := measurableSet_le (by fun_prop) (by fun_prop)
    rw [bayesBinaryRisk, ← (isArgminEstimator_binaryArgminEstimator μ ν π).isBayesEstimator
      measurable_zeroOneLoss, IsArgminEstimator.kernel]
    simp_rw [binaryArgminEstimator]
    rw [avgRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le E (iInf_le _ hE)

lemma bayesBinaryRisk_eq_lintegral_min (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ∫⁻ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  simp_rw [bayesBinaryRisk, bayesRisk_boolKernel_eq_lintegral_iInf measurable_zeroOneLoss μ ν π
    hasArgminEstimator_zeroOneLoss, iInf_bool_eq]
  simp

/-- The Bayes binary risk as an integral with respect to `ν`. The singular part of `μ` with respect
to `ν` does not contribute: the optimal test rejects `μ` on a `ν`-null set carrying it. -/
lemma bayesBinaryRisk_eq_lintegral_min_rnDeriv (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ∫⁻ x, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν := by
  set F := {x | π {false} * (∂μ/∂ν) x ≤ π {true}}
  have hF : MeasurableSet F := measurableSet_le (by fun_prop) measurable_const
  rw [bayesBinaryRisk_eq_iInf_measurableSet]
  refine le_antisymm ?_ (le_iInf₂ fun E hE ↦ ?_)
  · -- the risk of the test with rejection region `F ∩ t`, where `t` is a `ν`-full set on which the
    -- singular part of `μ` vanishes
    obtain ⟨t, ht, hμt, hνt⟩ : ∃ t, MeasurableSet t ∧ μ.singularPart ν t = 0 ∧ ν tᶜ = 0 :=
      let h := μ.mutuallySingular_singularPart ν
      ⟨h.nullSet, h.measurableSet_nullSet, h.measure_nullSet, h.measure_compl_nullSet⟩
    have h_false : μ (F ∩ t) ≤ ∫⁻ x in F, (∂μ/∂ν) x ∂ν := by
      conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
      rw [add_apply, withDensity_apply _ (hF.inter ht),
        measure_mono_null Set.inter_subset_right hμt, zero_add]
      exact lintegral_mono_set Set.inter_subset_left
    have h_true : ν (F ∩ t)ᶜ ≤ ν Fᶜ := by
      rw [Set.compl_inter]
      refine (measure_union_le _ _).trans ?_
      rw [hνt, add_zero]
    refine (iInf₂_le (F ∩ t) (hF.inter ht)).trans ?_
    calc π {false} * μ (F ∩ t) + π {true} * ν (F ∩ t)ᶜ
    _ ≤ π {false} * ∫⁻ x in F, (∂μ/∂ν) x ∂ν + π {true} * ν Fᶜ := by grw [h_false, h_true]
    _ = ∫⁻ x in F, π {false} * (∂μ/∂ν) x ∂ν + ∫⁻ x in Fᶜ, π {true} ∂ν := by
      rw [lintegral_const_mul _ (μ.measurable_rnDeriv ν), setLIntegral_const]
    _ = ∫⁻ x, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν := by
      conv_rhs => rw [← lintegral_add_compl _ hF]
      congr 1
      · exact setLIntegral_congr_fun hF fun x hx ↦ (min_eq_left hx).symm
      · exact setLIntegral_congr_fun hF.compl fun x hx ↦ (min_eq_right (not_le.mp hx).le).symm
  · -- every test has risk at least the integral of the minimum
    calc ∫⁻ x, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν
    _ = ∫⁻ x in E, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν
        + ∫⁻ x in Eᶜ, min (π {false} * (∂μ/∂ν) x) (π {true}) ∂ν := (lintegral_add_compl _ hE).symm
    _ ≤ ∫⁻ x in E, π {false} * (∂μ/∂ν) x ∂ν + ∫⁻ x in Eᶜ, π {true} ∂ν := by
      gcongr with x x
      · exact min_le_left _ _
      · exact min_le_right _ _
    _ = π {false} * ν.withDensity (∂μ/∂ν) E + π {true} * ν Eᶜ := by
      rw [lintegral_const_mul _ (μ.measurable_rnDeriv ν), withDensity_apply _ hE,
        setLIntegral_const]
    _ ≤ π {false} * μ E + π {true} * ν Eᶜ := by
      gcongr
      exact μ.withDensity_rnDeriv_le ν

/-- The Bayes binary risk of two mutually singular measures vanishes: the test with rejection
region a `μ`-null set carrying `ν` makes no error. -/
lemma bayesBinaryRisk_of_mutuallySingular (h : μ ⟂ₘ ν) (π : Measure Bool) :
    bayesBinaryRisk μ ν π = 0 := by
  have h_le := bayesRisk_le_avgRisk zeroOneLoss (Kernel.boolKernel μ ν)
    (Kernel.deterministic (fun x ↦ Bool.ofNat (h.nullSet.indicator 1 x))
      (Measurable.of_discrete.fun_comp (measurable_one.indicator h.measurableSet_nullSet))) π
  rw [avgRisk_binary_of_deterministic_indicator _ _ _ h.measurableSet_nullSet, h.measure_nullSet,
    h.measure_compl_nullSet, mul_zero, mul_zero, add_zero, nonpos_iff_eq_zero] at h_le
  exact h_le

/-- For a prior with positive weights, the Bayes binary risk vanishes if and only if the two
measures are mutually singular. -/
lemma bayesBinaryRisk_eq_zero_iff_mutuallySingular [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h_false : π {false} ≠ 0) (h_true : π {true} ≠ 0) :
    bayesBinaryRisk μ ν π = 0 ↔ μ ⟂ₘ ν := by
  rw [bayesBinaryRisk_eq_lintegral_min_rnDeriv, lintegral_eq_zero_iff (by fun_prop),
    ← Measure.rnDeriv_eq_zero]
  refine Filter.eventually_congr (.of_forall fun x ↦ ?_)
  simp +contextual [min_eq_iff, h_false, h_true]

lemma toReal_bayesBinaryRisk_eq_integral_min (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = ∫ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
        (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [bayesBinaryRisk_eq_lintegral_min, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · filter_upwards with x; positivity
  · refine Measurable.aestronglyMeasurable <| Measurable.min ?_ ?_
      <;> exact Measure.measurable_rnDeriv _ _ |>.const_mul _ |>.ennreal_toNNReal |>.coe_nnreal_real
  congr 1
  apply lintegral_congr_ae
  filter_upwards [μ.rnDeriv_ne_top _, ν.rnDeriv_ne_top _] with x hxμ hxν
  have : (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ≠ ⊤ :=
    (ENNReal.mul_ne_top (measure_ne_top _ _) hxμ)
  have : (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ≠ ⊤ :=
    (ENNReal.mul_ne_top (measure_ne_top _ _) hxν)
  rcases le_total (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
    (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) with h | h
  all_goals
  · have h' := (ENNReal.toReal_le_toReal (by assumption) (by assumption)).mpr h
    simp only [h, h', min_eq_left, min_eq_right]
    exact (ENNReal.ofReal_toReal_eq_iff.mpr (by assumption)).symm

lemma toReal_bayesBinaryRisk_eq_integral_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = 2⁻¹ * (((Kernel.boolKernel μ ν ∘ₘ π) .univ).toReal
        - ∫ x, |(π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal|
            ∂(Kernel.boolKernel μ ν ∘ₘ π)) := by
  simp_rw [toReal_bayesBinaryRisk_eq_integral_min, inf_eq_half_smul_add_sub_abs_sub' ℝ, smul_eq_mul,
    integral_const_mul, abs_sub_comm (π {true} * _).toReal]
  congr
  have hμ_int : Integrable (fun x ↦ (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
      (Kernel.boolKernel μ ν ∘ₘ π) := by
    simp_rw [ENNReal.toReal_mul]
    exact Integrable.const_mul Measure.integrable_toReal_rnDeriv _
  have hν_int : Integrable (fun x ↦ (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
      (Kernel.boolKernel μ ν ∘ₘ π) := by
    simp_rw [ENNReal.toReal_mul]
    exact Integrable.const_mul Measure.integrable_toReal_rnDeriv _
  have h_int_abs : Integrable
      (fun x ↦ |(π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
        - (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal|)
      (Kernel.boolKernel μ ν ∘ₘ π) :=
    hμ_int.sub hν_int |>.abs
  rw [integral_sub (by exact hμ_int.add hν_int) h_int_abs, integral_add hμ_int hν_int]
  simp only [ENNReal.toReal_mul, sub_left_inj, integral_const_mul]
  nth_rw 5 [boolKernel_comp_measure]
  calc
    _ = (π {false}).toReal * (μ .univ).toReal + (π {true}).toReal
        * ∫ (a : 𝒳), ((∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
      by_cases hπ_false : π {false} = 0
      · simp [hπ_false]
      rw [Measure.integral_toReal_rnDeriv
        (absolutelyContinuous_boolKernel_comp_left μ ν hπ_false)]
      rw [measureReal_def]
    _ = (π {false}).toReal * (μ .univ).toReal + (π {true}).toReal * (ν .univ).toReal := by
      by_cases hπ_true : π {true} = 0
      · simp [hπ_true]
      rw [Measure.integral_toReal_rnDeriv
        (absolutelyContinuous_boolKernel_comp_right μ ν hπ_true)]
      rw [measureReal_def]
    _ = _ := by
      simp_rw [add_comm, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _)
        (measure_ne_top _ _)) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
        ENNReal.toReal_mul]

lemma bayesBinaryRisk_eq_lintegral_eNorm (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = 2⁻¹ * (((Kernel.boolKernel μ ν ∘ₘ π) .univ)
        - ∫⁻ x, ‖(π {false} * (∂μ/∂(Kernel.boolKernel μ ν ∘ₘ π)) x).toReal
          - (π {true} * (∂ν/∂(Kernel.boolKernel μ ν ∘ₘ π)) x).toReal‖ₑ
            ∂(Kernel.boolKernel μ ν ∘ₘ π)) := by
  rw [← ENNReal.ofReal_toReal (bayesBinaryRisk_ne_top μ ν π),
    toReal_bayesBinaryRisk_eq_integral_abs, ENNReal.ofReal_mul (inv_nonneg.mpr zero_le_two),
    ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _),
    ofReal_integral_eq_lintegral_ofReal _ (.of_forall fun _ ↦ by positivity)]
  swap
  · simp_rw [ENNReal.toReal_mul]
    exact ((Measure.integrable_toReal_rnDeriv.const_mul _).sub
      (Measure.integrable_toReal_rnDeriv.const_mul _)).abs
  simp_rw [Real.eNorm_eq_ofReal_abs]

end ProbabilityTheory
