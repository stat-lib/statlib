/-
Copyright (c) 2026 David Sillman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sillman
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Continuity
public import Statlib.Contiguity.Def
public import Statlib.ForMathlib.ENNReal

/-!
# Le Cam's first lemma: `Contiguous1 → Contiguous2`

Direct proof assembled from the portmanteau, likelihood-ratio and quantile lemmas:

* `Contiguous1.contiguous2`: the direct proof of van der Vaart, *Asymptotic Statistics*,
  Lemma 6.4, (i) ⇒ (ii).
(Direct proof only; the contrapositive variant was removed to keep a single proof.)
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open ENNReal Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

-- ============================================================
-- Likelihood-ratio facts
-- ============================================================

/-- The pushforward of `Q` under the Radon–Nikodym derivative `f = P.rnDeriv Q`
gives `Q {f < ε}` for the open down-set `Iio ε`. -/
lemma pushforward_rnDeriv_apply_Iio {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ProbabilityMeasure Ω) (ε : ℝ≥0∞) :
    (Q.map (fun x => (P : Measure Ω).rnDeriv (Q : Measure Ω) x)) (Iio ε) =
      Q {x | (P : Measure Ω).rnDeriv (Q : Measure Ω) x < ε} :=
  ProbabilityMeasure.map_apply Q
    ((Measure.measurable_rnDeriv (P : Measure Ω) (Q : Measure Ω)).aemeasurable)
    (measurableSet_Iio (a := ε))

/-- Neyman–Pearson set, sharp form: for any threshold `c` there is a measurable set `s` with
`μ s ≤ c * ν s` which has the same `ν`-mass as the likelihood-ratio level set
`{dμ/dν ≤ c}`. Only the Lebesgue decomposition of `μ` with respect to `ν` is needed. -/
lemma exists_neymanPearson_set_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [μ.HaveLebesgueDecomposition ν] (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      μ s ≤ c * ν s ∧
      ν s = ν {x | μ.rnDeriv ν x ≤ c} := by
  have hms := μ.mutuallySingular_singularPart ν
  set t := {x | μ.rnDeriv ν x ≤ c} ∩ hms.nullSet
  have ht : MeasurableSet t :=
    (measurableSet_le (μ.measurable_rnDeriv ν) measurable_const).inter hms.measurableSet_nullSet
  refine ⟨t, ht, ?_, measure_inter_conull hms.measure_compl_nullSet⟩
  calc μ t = μ.singularPart ν t + ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
        conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
        rw [Measure.add_apply, withDensity_apply _ ht]
    _ = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
        rw [measure_mono_null inter_subset_right hms.measure_nullSet, zero_add]
    _ ≤ ∫⁻ _ in t, c ∂ν := setLIntegral_mono measurable_const fun _ hx => hx.1
    _ = c * ν t := setLIntegral_const _ _

/-- General version for measures: under `[IsProbabilityMeasure ν]` the sharp bound
`μ s ≤ c * ν s` becomes `μ s ≤ c`. -/
lemma exists_neymanPearson_set {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [μ.HaveLebesgueDecomposition ν] [IsProbabilityMeasure ν]
    (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      μ s ≤ c ∧
      ν s = ν {x | μ.rnDeriv ν x ≤ c} := by
  obtain ⟨s, hs, hμ, hν⟩ := exists_neymanPearson_set_mul μ ν c
  exact ⟨s, hs, hμ.trans (mul_le_of_le_one_right' prob_le_one), hν⟩

-- ============================================================
-- Portmanteau lower bound
-- ============================================================

/-- Weak-limit lower bound on `μs a s` for an open set `s`: if `η < L s`, then eventually
`η < μs a s`.  This is the open-set case of the portmanteau theorem. -/
lemma eventually_gt_measure_open_of_tendsto {X α : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] {h : Filter α}
    (L : ProbabilityMeasure X) (μs : α → ProbabilityMeasure X)
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (s : Set X) (hs : IsOpen s)
    (hη : η < L s) :
    ∀ᶠ a in h, η < μs a s := by
  simp only [ennreal_coeFn_eq_coeFn_toMeasure] at hη ⊢
  exact eventually_lt_of_lt_liminf (hη.trans_le (le_liminf_measure_open_of_tendsto hμs hs))

/-- Weak-limit lower bound on `μ (Iio ε)` for any threshold `ε > 0`. -/
lemma eventually_gt_measure_Iio_of_tendsto {α : Type*} {h : Filter α}
    (L : ProbabilityMeasure (ℝ≥0∞)) (μs : α → ProbabilityMeasure (ℝ≥0∞))
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (hη : η < L {0})
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ a in h, η < μs a (Iio ε) :=
  eventually_gt_measure_open_of_tendsto L μs hμs η (Iio ε) isOpen_Iio <|
    hη.trans_le (ENNReal.coe_le_coe.mpr (L.apply_mono (singleton_subset_iff.2 hε)))

-- ============================================================
-- Quantile threshold
-- ============================================================

/-- Continuity from above for the strict level sets at decreasing thresholds:
`ν {f < c + 1/(n+1)} → ν {f ≤ c}` as `n → ∞`, for `c ≠ ∞`. -/
lemma tendsto_measure_lt_add_one_div_nat {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hf : Measurable f) (hc : c ≠ ∞) :
    Tendsto (fun n : ℕ => ν {x | f x < c + 1 / (n + 1 : ℝ≥0∞)}) atTop
      (𝓝 (ν {x | f x ≤ c})) := by
  have hA_anti : Antitone fun n : ℕ => {x | f x < c + 1 / (n + 1 : ℝ≥0∞)} :=
    fun m n hmn x (hx : f x < _) => hx.trans_le (by gcongr)
  have hinter : (⋂ n : ℕ, {x | f x < c + 1 / (n + 1 : ℝ≥0∞)}) = {x | f x ≤ c} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    exact ⟨fun hx => le_of_le_add_one_div fun n => (hx n).le,
      fun hx n => hx.trans_lt (ENNReal.lt_add_right hc (by simp))⟩
  rw [← hinter]
  exact tendsto_measure_iInter_atTop
    (fun n => (measurableSet_lt hf measurable_const).nullMeasurableSet) hA_anti
    ⟨0, measure_ne_top ν _⟩

/-- Selection of thresholds `e a → 0` "at a sufficiently slow rate".

Suppose that for every fixed `ε > 0` and every `η < b`, eventually `η < ν a {f a < ε}`, i.e.
`b ≤ liminf ν a {f a < ε}` for every `ε > 0`. Then there are thresholds `e a` with `e a → 0`
such that `b ≤ ν a {f a ≤ e a} + e a` for every `a`; in particular
`b ≤ liminf ν a {f a ≤ e a}`.

The thresholds are the quantiles `e a = sInf {ε | b < ν a {f a < ε} + ε}`. -/
lemma exists_tendsto_zero_le_measure_le_add {α : Type*} {Ω : α → Type*}
    [∀ a, MeasurableSpace (Ω a)] {h : Filter α} (ν : ∀ a, Measure (Ω a))
    [∀ a, IsFiniteMeasure (ν a)] (f : ∀ a, Ω a → ℝ≥0∞) (hf : ∀ a, Measurable (f a))
    (b : ℝ≥0∞) (hb : b ≠ ∞)
    (hB : ∀ ε : ℝ≥0∞, 0 < ε → ∀ η < b, ∀ᶠ a in h, η < ν a {x | f a x < ε}) :
    ∃ e : α → ℝ≥0∞, Tendsto e h (𝓝 0) ∧
      ∀ a, b ≤ ν a {x | f a x ≤ e a} + e a := by
  refine ⟨fun a => sInf {ε | b < ν a {x | f a x < ε} + ε}, ?_, fun a => ?_⟩
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rcases eq_or_ne b 0 with rfl | hb0
    · exact Eventually.of_forall fun a => sInf_le (hε.trans_le le_add_self)
    filter_upwards [hB ε hε (b - ε) (ENNReal.sub_lt_self hb hb0 hε.ne')] with a ha
    exact sInf_le (ENNReal.lt_add_of_sub_lt_right (Or.inl hb) ha)
  · set c := sInf {ε | b < ν a {x | f a x < ε} + ε}
    change b ≤ ν a {x | f a x ≤ c} + c
    rcases eq_or_ne c ∞ with hc | hc
    · rw [hc, add_top]
      exact le_top
    have hc_inv :
        Tendsto (fun n : ℕ => c + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 (c + 0)) :=
      tendsto_const_nhds.add <|
        (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
    have hlim := (tendsto_measure_lt_add_one_div_nat (ν a) (f a) c (hf a) hc).add hc_inv
    rw [add_zero] at hlim
    refine ge_of_tendsto' hlim fun n => ?_
    obtain ⟨ε, hεb, hεlt⟩ := sInf_lt_iff.1 (ENNReal.lt_add_right hc (by simp) :
      c < c + 1 / (n + 1 : ℝ≥0∞))
    refine hεb.le.trans (add_le_add (measure_mono fun x (hx : f a x < ε) => ?_) ?_)
    · exact hx.trans (by simpa using hεlt)
    · simpa using hεlt.le

-- ============================================================
-- Le Cam's first lemma
-- ============================================================

/-- `Contiguous1 → Contiguous2` (Le Cam's first lemma), direct proof following
van der Vaart, *Asymptotic Statistics*, Lemma 6.4, (i) ⇒ (ii). -/
theorem Contiguous1.contiguous2 {α : Type*} {Ω : α → Type*}
    [∀ a, MeasurableSpace (Ω a)] (l : Filter α)
    (P Q : ∀ a, ProbabilityMeasure (Ω a)) (hPQ : Contiguous1 l P Q) :
    Contiguous2 l P Q := by
  intro L h hle hne htend
  set f : ∀ a, Ω a → ℝ≥0∞ :=
    fun a => (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a))
  have hB : ∀ ε : ℝ≥0∞, 0 < ε → ∀ η < (L {0} : ℝ≥0∞), ∀ᶠ a in h,
      η < (Q a : Measure (Ω a)) {x | f a x < ε} := by
    intro ε hε η hη
    filter_upwards [eventually_gt_measure_Iio_of_tendsto L _ htend η hη ε hε] with a ha
    rwa [pushforward_rnDeriv_apply_Iio, ennreal_coeFn_eq_coeFn_toMeasure] at ha
  obtain ⟨e, he, hLe⟩ :=
    exists_tendsto_zero_le_measure_le_add (fun a => (Q a : Measure (Ω a))) f
      (fun a => Measure.measurable_rnDeriv _ _) _ ENNReal.coe_ne_top hB
  choose s hs_meas hs_P hs_Q using fun a =>
    exists_neymanPearson_set (P a : Measure (Ω a)) (Q a) (e a)
  have hP_tend : Tendsto (fun a => (P a) (s a)) h (𝓝 0) := by
    rw [← ENNReal.tendsto_coe, ENNReal.coe_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
      (fun a => (bot_le : (0 : ℝ≥0∞) ≤ _)) fun a => ?_
    rw [ennreal_coeFn_eq_coeFn_toMeasure]
    exact hs_P a
  have hQ_tend := hPQ hs_meas hle hP_tend
  rw [← ENNReal.tendsto_coe, ENNReal.coe_zero] at hQ_tend
  simp only [ennreal_coeFn_eq_coeFn_toMeasure, hs_Q] at hQ_tend
  have hL : (L {0} : ℝ≥0∞) ≤ 0 := by
    simpa using ge_of_tendsto' (hQ_tend.add he) hLe
  exact_mod_cast nonpos_iff_eq_zero.mp hL

end Statlib.Contiguity
