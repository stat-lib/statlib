/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Statlib.ForMathlib.ENNReal
public import Statlib.ForMathlib.EReal
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Kernel

/-!
# E-variables

This file defines e-variables and randomized e-variables.

## Main definitions

* `IsEVar X S`: A random variable `X` is an e-variable for a set of measures `S` if it has
  expected value at most 1 under all measures in `S`, that is `∫⁻ ω, X ω ∂μ ≤ 1` for all `μ ∈ S`.
  The measures of `S` are arbitrary measures: the bound is `1` whatever their mass.
* `IsRandEVar κ S`: A kernel `κ` is a randomized e-variable for `S` if its mean function is
  an e-variable.

## Main statements

* `isRandEVar_iff_isEVar`: A kernel is a randomized e-variable iff its mean function is an
  e-variable.
* `isEVar_one_iff`: The constant `1` is an e-variable for `S` iff the measures of `S` have mass at
  most one.
* `convex_isEVar`: The set of e-variables is convex.
* `isEVar_liminf`: The limit inferior of a sequence of e-variables is an e-variable.
* `IsEVar.comp`: The composition of an e-variable with a measurable function is an e-variable.
* `IsRandEVar.comp`: The composition of a randomized e-variable with a transition kernel is
  a randomized e-variable.

-/

@[expose] public section

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace ProbabilityTheory

/-- A random variable `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`: `∫⁻ ω, X ω ∂μ ≤ 1` for all `μ ∈ S`.

The measures of `S` are not required to be probability measures, and the bound is `1` whatever the
mass of `μ`. The constant `1` is thus an e-variable for `S` iff the measures of `S` have mass at
most one (`isEVar_one_iff`). -/
structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X := by fun_prop
  lintegral_le_one ⦃μ : Measure 𝓧⦄ (hμ : μ ∈ S) : ∫⁻ ω, X ω ∂μ ≤ 1

/-- A kernel `κ` is a randomized e-variable for a set of measures `S` if it is a
Markov kernel and the expectation of its mean function is at most 1 under all measures in `S`. -/
structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  [markov : IsMarkovKernel κ]
  lintegral_le_one ⦃μ : Measure 𝓧⦄ (hμ : μ ∈ S) : ∫⁻ ω, ∫⁻ x, x ∂(κ ω) ∂μ ≤ 1

variable {X Y : 𝓧 → ℝ≥0∞} {κ η : Kernel 𝓧 ℝ≥0∞} [IsMarkovKernel κ] {S T : Set (Measure 𝓧)}

/-- A kernel `κ` is a randomized e-variable iff its mean function `x ↦ ∫⁻ y, y ∂κ x` is an
e-variable. -/
lemma isRandEVar_iff_isEVar : IsRandEVar κ S ↔ IsEVar (fun x ↦ ∫⁻ y, y ∂κ x) S :=
  ⟨fun h ↦ ⟨by fun_prop, h.lintegral_le_one⟩, fun h ↦ ⟨h.lintegral_le_one⟩⟩

lemma IsEVar.isRandEVar_deterministic (hX : IsEVar X S) :
    IsRandEVar (Kernel.deterministic X hX.measurable) S where
  lintegral_le_one μ hμ := by
    simp only [Kernel.lintegral_deterministic]
    exact hX.lintegral_le_one hμ

@[simp]
lemma isEVar_empty (hX : Measurable X) :
   IsEVar X (∅ : Set (Measure 𝓧)) where
  measurable := hX
  lintegral_le_one := by simp

lemma isEVar_zero : IsEVar 0 S where
  lintegral_le_one _ _ := by simp

/-- The constant `1` is an e-variable for `S` iff the measures of `S` have mass at most one. -/
lemma isEVar_one_iff : IsEVar 1 S ↔ ∀ μ ∈ S, μ Set.univ ≤ 1 :=
  ⟨fun h μ hμ ↦ by simpa using h.lintegral_le_one hμ,
    fun hS ↦ ⟨measurable_one, fun μ hμ ↦ by simpa using hS μ hμ⟩⟩

lemma isEVar_one (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) : IsEVar 1 S := isEVar_one_iff.mpr hS

lemma isEVar_fun_one (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) : IsEVar (fun _ ↦ 1) S := isEVar_one hS

lemma IsEVar.congr (hX : IsEVar X S) (hY : Measurable Y) (hXY : ∀ μ ∈ S, X =ᵐ[μ] Y) :
    IsEVar Y S where
  measurable := hY
  lintegral_le_one μ hμ := by
    rw [← lintegral_congr_ae (hXY μ hμ)]
    exact hX.lintegral_le_one hμ

lemma IsEVar.ae_lt_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) :
    ∀ᵐ ω ∂μ, X ω < ⊤ :=
  MeasureTheory.ae_lt_top hX.measurable (ne_top_of_le_ne_top ENNReal.one_ne_top
    (hX.lintegral_le_one hμ))

lemma IsEVar.ae_ne_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) :
    ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  filter_upwards [hX.ae_lt_top hμ] with ω hω using hω.ne

lemma _root_.Measurable.measurable_fsupport (hX : Measurable X) :
    MeasurableSet X.fsupport := by
  suffices MeasurableSet {ω | X ω ≠ ⊤} ∧ MeasurableSet {ω | X ω ≠ 0} from this.1.inter this.2
  constructor <;> exact ((measurableSet_singleton _).preimage hX).compl

lemma _root_.AEMeasurable.nullMeasurableSet_fsupport {μ : Measure 𝓧} (hX : AEMeasurable X μ) :
    NullMeasurableSet X.fsupport μ :=
  hX.nullMeasurable ((measurableSet_singleton ⊤).compl.inter (measurableSet_singleton 0).compl)

lemma IsEVar.measurable_fsupport (hX : IsEVar X S) :
    MeasurableSet X.fsupport := hX.measurable.measurable_fsupport

lemma measure_fsupport_eq_zero_of_ae_eq_top {μ : Measure 𝓧} {X : 𝓧 → ℝ≥0∞}
    (hX_top : ∀ᵐ ω ∂μ, X ω = ∞) :
    μ X.fsupport = 0 := by
  suffices μ {x | ¬ x ∈ X.fsupportᶜ} = 0 by simpa
  rw [← ae_iff]
  filter_upwards [hX_top] with x hx
  simp [hx]

/-- The integral of `Y / Y` equals the measure of the finite support of `Y`. -/
lemma lintegral_div_self_eq_measure_fsupport {μ : Measure 𝓧} (hY : AEMeasurable Y μ) :
    ∫⁻ ω, Y ω / Y ω ∂μ = μ Y.fsupport := by
  rw [← lintegral_indicator_one₀ hY.nullMeasurableSet_fsupport]
  congr with ω
  by_cases h0 : Y ω = 0 <;> by_cases h_top : Y ω = ∞ <;> simp [h0, h_top, ENNReal.div_self]

lemma IsEVar.mono (hY : IsEVar Y S) (hX : Measurable X) (hXY : X ≤ Y) : IsEVar X S where
  lintegral_le_one μ hμ := (lintegral_mono hXY).trans (hY.lintegral_le_one hμ)

lemma IsRandEVar.mono (hη : IsRandEVar η S) (hκη : κ ≤ η) : IsRandEVar κ S where
  lintegral_le_one μ hμ := by
    refine le_trans ?_ (hη.lintegral_le_one hμ)
    gcongr with x
    exact hκη x

lemma IsEVar.anti_set (hST : S ⊆ T) (hX : IsEVar X T) : IsEVar X S where
  measurable := hX.measurable
  lintegral_le_one _ hμ := hX.lintegral_le_one (hST hμ)

lemma IsRandEVar.anti_set (hST : S ⊆ T) (hκ : IsRandEVar κ T) : IsRandEVar κ S where
  lintegral_le_one _ hμ := hκ.lintegral_le_one (hST hμ)

lemma IsEVar.union (hXS : IsEVar X S) (hXT : IsEVar X T) : IsEVar X (S ∪ T) where
  measurable := hXS.measurable
  lintegral_le_one _ hμ := hμ.elim (fun h ↦ hXS.lintegral_le_one h) fun h ↦ hXT.lintegral_le_one h

lemma isEVar_union_iff : IsEVar X (S ∪ T) ↔ IsEVar X S ∧ IsEVar X T :=
  ⟨fun h ↦ ⟨h.anti_set Set.subset_union_left, h.anti_set Set.subset_union_right⟩,
    fun ⟨hXS, hXT⟩ ↦ hXS.union hXT⟩

/-- The set of e-variables is convex. -/
lemma convex_isEVar (S : Set (Measure 𝓧)) : Convex ℝ≥0∞ {Z | IsEVar Z S} := by
  intro X hX Y hY a b ha hb hab
  have := hX.measurable
  have := hY.measurable
  refine ⟨by fun_prop, fun μ hμ ↦ ?_⟩
  calc ∫⁻ ω, (a • X + b • Y) ω ∂μ
  _ = a * ∫⁻ ω, X ω ∂μ + b * ∫⁻ ω, Y ω ∂μ := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
      lintegral_const_mul _ (by fun_prop)]
  _ ≤ a * 1 + b * 1 := by
    gcongr
    · exact hX.lintegral_le_one hμ
    · exact hY.lintegral_le_one hμ
  _ = 1 := by rw [mul_one, mul_one, hab]

open Filter in
/-- The limit inferior of a sequence of e-variables is an e-variable. -/
lemma isEVar_liminf {X : ℕ → 𝓧 → ℝ≥0∞} (hX : ∀ n, IsEVar (X n) S) :
    IsEVar (fun ω ↦ liminf (X · ω) atTop) S where
  measurable := Measurable.liminf fun n ↦ (hX n).measurable
  lintegral_le_one μ hμ := by
    calc ∫⁻ ω, (fun ω ↦ liminf (X · ω) atTop) ω ∂μ
    _ ≤ liminf (fun n ↦ ∫⁻ ω, X n ω ∂μ) atTop := lintegral_liminf_le fun n ↦ (hX n).measurable
    _ ≤ 1 := by
      refine liminf_le_of_frequently_le ?_
      exact .of_forall fun n ↦ (hX n).lintegral_le_one hμ

/-- The composition of an e-variable with a measurable function is an e-variable. -/
lemma IsEVar.comp {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)} {φ : 𝓧 → 𝓨}
    (hφ : Measurable φ) (h : IsEVar Y {μ.map φ | μ ∈ S}) :
    IsEVar (Y ∘ φ) S where
  measurable := h.measurable.comp hφ
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one ⟨μ, hμ, rfl⟩
    rwa [lintegral_map h.measurable hφ] at h'

/-- The composition of a randomized e-variable with a transition kernel is
a randomized e-variable. -/
lemma IsRandEVar.comp {ξ : Kernel 𝓨 ℝ≥0∞} {S : Set (Measure 𝓧)}
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] (h : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}) :
    IsRandEVar (ξ ∘ₖ κ) S where
  markov := have := h.markov; inferInstance
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one ⟨μ, hμ, rfl⟩
    rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)] at h'
    refine le_of_eq_of_le (lintegral_congr fun ω ↦ ?_) h'
    rw [Kernel.comp_apply, Measure.lintegral_bind (by fun_prop) (by fun_prop)]

end ProbabilityTheory
