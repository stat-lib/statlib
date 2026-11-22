/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.CompProd
public import Statlib.Divergence.FDiv.Conj
public import Statlib.Divergence.FDiv.Convex
public import Statlib.ForMathlib.Probability.Distributions.Bernoulli

/-!
# f-divergences between Bernoulli distributions

We study the binary f-divergence `d_f(p, q) = fDiv f Ber(x, y, p) Ber(x, y, q)` between two
Bernoulli distributions, as a function of the parameters `p q : I`, and we prove that it is a lower
bound for the f-divergence between two probability measures on the unit interval with means `p`
and `q`.

## Main statements

* `fDiv_bernoulliMeasure_le_mul_add_mul`: joint convexity of `(p, q) ↦ d_f(p, q)`.
* `monotoneOn_fDiv_bernoulliMeasure_left`, `antitoneOn_fDiv_bernoulliMeasure_left`: for fixed `q`,
  `p ↦ d_f(p, q)` is antitone on `[0, q]` and monotone on `[q, 1]`. Its minimum is
  `d_f(q, q) = 0` (`fDiv_self`). `monotoneOn_fDiv_bernoulliMeasure_right` and
  `antitoneOn_fDiv_bernoulliMeasure_right` are the analogous statements in the second argument.
* `fDiv_bernoulliMeasure_of_mem_of_notMem`: if a measurable set separates `x` and `y`, then
  `d_f(p, q)` is the binary f-divergence between Bernoulli distributions on `Bool`. Otherwise
  `dirac x = dirac y` and `d_f(p, q) = 0` (`fDiv_bernoulliMeasure_of_dirac_eq`).
* `fDiv_bernoulliMeasure_of_ne_zero_of_ne_one`, `fDiv_bernoulliMeasure_zero_right`,
  `fDiv_bernoulliMeasure_one_right`: explicit formulas.
* `continuous_fDiv_bernoulliMeasure_left`: for `q ∉ {0, 1}`, `p ↦ d_f(p, q)` is continuous.
  `continuousAt_fDiv_bernoulliMeasure_left`: for all `q`, it is continuous at every `p ≠ q`.
* `fDiv_bernoulliMeasure_le_of_integral_eq`: for probability measures `μ, ν` on the unit interval
  with means `p` and `q`, `d_f(p, q) ≤ D_f(μ, ν)`.
* `fDiv_bernoulliMeasure_le_of_integral_comp_eq`, `fDiv_bernoulliMeasure_le_of_lintegral_eq`,
  `fDiv_bernoulliMeasure_le_of_integral_comp_kernel_eq`: the same bound for the means of a
  function with values in `[0, 1]`, or of the image of the measures by a Markov kernel to `I`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology unitInterval

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {x y : 𝓧} {f : DivFunction}

section Convexity

/-- **Joint convexity** of the f-divergence between Bernoulli distributions. -/
lemma fDiv_bernoulliMeasure_le_mul_add_mul {p₁ p₂ q₁ q₂ p q : I} {t : ℝ≥0} (ht : t ≤ 1)
    (hp : (p : ℝ) = t * p₁ + (1 - t) * p₂) (hq : (q : ℝ) = t * q₁ + (1 - t) * q₂) :
    fDiv f Ber(x, y, p) Ber(x, y, q)
      ≤ t * fDiv f Ber(x, y, p₁) Ber(x, y, q₁)
        + (1 - t : ℝ≥0) * fDiv f Ber(x, y, p₂) Ber(x, y, q₂) := by
  rw [bernoulliMeasure_eq_smul_add_smul x y ht hp, bernoulliMeasure_eq_smul_add_smul x y ht hq]
  exact fDiv_smul_add_smul_le _ _ _ _ _ _

/-- Moving the first parameter towards the second one along a segment decreases the binary
f-divergence: `d_f(t p' + (1 - t) q, q) ≤ t d_f(p', q)`. -/
lemma fDiv_bernoulliMeasure_le_mul_left {p p' q : I} {t : ℝ≥0} (ht : t ≤ 1)
    (hp : (p : ℝ) = t * p' + (1 - t) * q) :
    fDiv f Ber(x, y, p) Ber(x, y, q) ≤ t * fDiv f Ber(x, y, p') Ber(x, y, q) := by
  refine (fDiv_bernoulliMeasure_le_mul_add_mul (q₁ := q) (q₂ := q) ht hp (by ring)).trans ?_
  simp [fDiv_self]

/-- If `p` lies between `q` and `p'`, then `d_f(p, q) ≤ d_f(p', q)`. -/
lemma fDiv_bernoulliMeasure_le_of_mem_uIcc_left {p p' q : I} (hp : (p : ℝ) ∈ uIcc (q : ℝ) p') :
    fDiv f Ber(x, y, p) Ber(x, y, q) ≤ fDiv f Ber(x, y, p') Ber(x, y, q) := by
  rw [← segment_eq_uIcc] at hp
  obtain ⟨a, b, ha, hb, hab, h⟩ := hp
  lift b to ℝ≥0 using hb
  have hb1 : b ≤ 1 := by exact_mod_cast (by linarith : (b : ℝ) ≤ 1)
  refine (fDiv_bernoulliMeasure_le_mul_left (t := b) (p' := p') hb1 ?_).trans
    (mul_le_of_le_one_left bot_le (by exact_mod_cast hb1))
  simp only [smul_eq_mul] at h
  linear_combination -h + (q : ℝ) * hab

/-- For fixed `q`, `p ↦ d_f(p, q)` is monotone on `[q, 1]`. -/
lemma monotoneOn_fDiv_bernoulliMeasure_left (q : I) :
    MonotoneOn (fun p ↦ fDiv f Ber(x, y, p) Ber(x, y, q)) (Ici q) :=
  fun _ hp _ _ hpp' ↦ fDiv_bernoulliMeasure_le_of_mem_uIcc_left
    (mem_uIcc.mpr (Or.inl ⟨Subtype.coe_le_coe.mpr hp, Subtype.coe_le_coe.mpr hpp'⟩))

/-- For fixed `q`, `p ↦ d_f(p, q)` is antitone on `[0, q]`. -/
lemma antitoneOn_fDiv_bernoulliMeasure_left (q : I) :
    AntitoneOn (fun p ↦ fDiv f Ber(x, y, p) Ber(x, y, q)) (Iic q) :=
  fun _ _ _ hp' hpp' ↦ fDiv_bernoulliMeasure_le_of_mem_uIcc_left
    (mem_uIcc.mpr (Or.inr ⟨Subtype.coe_le_coe.mpr hpp', Subtype.coe_le_coe.mpr hp'⟩))

/-- For fixed `p`, `q ↦ d_f(p, q)` is monotone on `[p, 1]`. -/
lemma monotoneOn_fDiv_bernoulliMeasure_right (p : I) :
    MonotoneOn (fun q ↦ fDiv f Ber(x, y, p) Ber(x, y, q)) (Ici p) := by
  intro q hq q' hq' hqq'
  simp only [← fDiv_conj (f := f)]
  exact monotoneOn_fDiv_bernoulliMeasure_left p hq hq' hqq'

/-- For fixed `p`, `q ↦ d_f(p, q)` is antitone on `[0, p]`. -/
lemma antitoneOn_fDiv_bernoulliMeasure_right (p : I) :
    AntitoneOn (fun q ↦ fDiv f Ber(x, y, p) Ber(x, y, q)) (Iic p) := by
  intro q hq q' hq' hqq'
  simp only [← fDiv_conj (f := f)]
  exact antitoneOn_fDiv_bernoulliMeasure_left p hq hq' hqq'

end Convexity

section Bool

/-- If a measurable set contains `x` but not `y`, the f-divergence between `Ber(x, y, p)` and
`Ber(x, y, q)` is the f-divergence between the Bernoulli distributions with the same parameters
on `Bool`. -/
lemma fDiv_bernoulliMeasure_of_mem_of_notMem {s : Set 𝓧} (hs : MeasurableSet s) (hx : x ∈ s)
    (hy : y ∉ s) (p q : I) :
    fDiv f Ber(x, y, p) Ber(x, y, q) = fDiv f Ber(true, false, p) Ber(true, false, q) := by
  classical
  have he : Measurable fun b : Bool ↦ if b then x else y := measurable_from_top
  have h_inv : Function.LeftInverse (fun z ↦ decide (z ∈ s)) fun b : Bool ↦ if b then x else y := by
    intro b
    cases b <;> simp [hx, hy]
  rw [← fDiv_map_eq_of_leftInverse he (measurable_decide_mem hs) h_inv,
    map_bernoulliMeasure' _ _ he, map_bernoulliMeasure' _ _ he]
  simp

/-- If no measurable set separates `x` and `y`, that is `dirac x = dirac y`, then
`Ber(x, y, p) = dirac x` for all `p` and the f-divergence between two such distributions is zero.
Otherwise, `fDiv_bernoulliMeasure_of_mem_of_notMem` applies. -/
lemma fDiv_bernoulliMeasure_of_dirac_eq (hxy : Measure.dirac x = Measure.dirac y) (p q : I) :
    fDiv f Ber(x, y, p) Ber(x, y, q) = 0 := by
  rw [bernoulliMeasure_eq_dirac_of_dirac_eq hxy, bernoulliMeasure_eq_dirac_of_dirac_eq hxy,
    fDiv_self]

end Bool

section Formula

variable [MeasurableSingletonClass 𝓧]

/-- The f-divergence between Bernoulli distributions, for a second parameter `q ∉ {0, 1}`. -/
lemma fDiv_bernoulliMeasure_of_ne_zero_of_ne_one (hxy : x ≠ y) (p : I) {q : I} (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    fDiv f Ber(x, y, p) Ber(x, y, q)
      = ENNReal.ofReal q * f (ENNReal.ofReal (p / q))
        + ENNReal.ofReal (1 - q) * f (ENNReal.ofReal ((1 - p) / (1 - q))) := by
  classical
  rw [fDiv_of_absolutelyContinuous (bernoulliMeasure_absolutelyContinuous hxy p hq hq1),
    lintegral_congr_ae ((rnDeriv_bernoulliMeasure hxy p hq hq1).mono fun z hz ↦ by rw [hz]),
    lintegral_bernoulliMeasure]
  simp [hxy.symm]

/-- The f-divergence between a Bernoulli distribution and the Dirac mass `Ber(x, y, 1)`. -/
lemma fDiv_bernoulliMeasure_one_right (hxy : x ≠ y) (p : I) :
    fDiv f Ber(x, y, p) Ber(x, y, 1)
      = f (ENNReal.ofReal p) + f.derivAtTop * ENNReal.ofReal (1 - p) := by
  have h_ms : Measure.dirac y ⟂ₘ Measure.dirac x :=
    ⟨{x}, measurableSet_singleton x, by simp [hxy.symm], by simp⟩
  rw [bernoulliMeasure_one, bernoulliMeasure_def,
    fDiv_absolutelyContinuous_add_mutuallySingular
      (Measure.AbsolutelyContinuous.rfl.smul_left (toNNReal p)) (h_ms.smul_nnreal _),
    fDiv_of_absolutelyContinuous (Measure.AbsolutelyContinuous.rfl.smul_left (toNNReal p))]
  have h_rn : (toNNReal p • Measure.dirac x).rnDeriv (Measure.dirac x)
      =ᵐ[Measure.dirac x] fun _ ↦ ENNReal.ofReal p := by
    filter_upwards [Measure.rnDeriv_smul_left' (Measure.dirac x) (Measure.dirac x) (toNNReal p),
      Measure.rnDeriv_self (Measure.dirac x)] with z hz h_self
    rw [hz, Pi.smul_apply, h_self, ENNReal.smul_def, smul_eq_mul, mul_one,
      coe_toNNReal_eq_ofReal]
  rw [lintegral_congr_ae (h_rn.mono fun z hz ↦ by rw [hz])]
  simp [coe_toNNReal_symm_eq_ofReal]

/-- The f-divergence between a Bernoulli distribution and the Dirac mass `Ber(x, y, 0)`. -/
lemma fDiv_bernoulliMeasure_zero_right (hxy : x ≠ y) (p : I) :
    fDiv f Ber(x, y, p) Ber(x, y, 0)
      = f (ENNReal.ofReal (1 - p)) + f.derivAtTop * ENNReal.ofReal p := by
  rw [← bernoulliMeasure_swap x y p, ← bernoulliMeasure_swap x y 0, symm_zero,
    fDiv_bernoulliMeasure_one_right hxy.symm, coe_symm_eq, sub_sub_cancel]

end Formula

section Continuity

/-- For `q ∉ {0, 1}`, the binary f-divergence `p ↦ d_f(p, q)` is continuous. -/
lemma continuous_fDiv_bernoulliMeasure_left {q : I} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    Continuous (fun p ↦ fDiv f Ber(x, y, p) Ber(x, y, q)) := by
  rcases eq_or_ne (Measure.dirac x) (Measure.dirac y) with hxy | hxy
  · simp_rw [fDiv_bernoulliMeasure_of_dirac_eq hxy]
    exact continuous_const
  obtain ⟨s, hs, hx, hy⟩ := dirac_ne_dirac_iff_exists_measurableSet.mp hxy
  simp_rw [fDiv_bernoulliMeasure_of_mem_of_notMem hs hx hy,
    fDiv_bernoulliMeasure_of_ne_zero_of_ne_one Bool.false_ne_true.symm _ hq0 hq1]
  refine Continuous.add ?_ ?_
  · exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (f.continuous.comp (ENNReal.continuous_ofReal.comp (continuous_subtypeVal.div_const _)))
  · exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (f.continuous.comp (ENNReal.continuous_ofReal.comp
        ((continuous_const.sub continuous_subtypeVal).div_const _)))

/-- For `p ≠ q`, the binary f-divergence `p' ↦ d_f(p', q)` is continuous at `p`. For `q ∉ {0, 1}`,
it is continuous everywhere (`continuous_fDiv_bernoulliMeasure_left`), but for `q ∈ {0, 1}` and
`f.derivAtTop = ∞` it is discontinuous at `q`. -/
lemma continuousAt_fDiv_bernoulliMeasure_left {p q : I} (hpq : p ≠ q) :
    ContinuousAt (fun p' ↦ fDiv f Ber(x, y, p') Ber(x, y, q)) p := by
  rcases eq_or_ne (Measure.dirac x) (Measure.dirac y) with hxy | hxy
  · simp_rw [fDiv_bernoulliMeasure_of_dirac_eq hxy]
    exact continuousAt_const
  obtain ⟨s, hs, hx, hy⟩ := dirac_ne_dirac_iff_exists_measurableSet.mp hxy
  simp_rw [fDiv_bernoulliMeasure_of_mem_of_notMem hs hx hy]
  have h_ofReal : Continuous fun p : I ↦ ENNReal.ofReal p :=
    ENNReal.continuous_ofReal.comp continuous_subtypeVal
  have h_ofReal_sub : Continuous fun p : I ↦ ENNReal.ofReal (1 - p) :=
    ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_subtypeVal)
  rcases eq_or_ne q 0 with rfl | hq0
  · simp_rw [fDiv_bernoulliMeasure_zero_right Bool.false_ne_true.symm]
    refine (f.continuous.comp h_ofReal_sub).continuousAt.add
      (ENNReal.Tendsto.const_mul (h_ofReal.tendsto p) (Or.inl ?_))
    rw [ENNReal.ofReal_ne_zero_iff]
    exact lt_of_le_of_ne p.property.1 (coe_ne_zero.mpr hpq).symm
  rcases eq_or_ne q 1 with rfl | hq1
  · simp_rw [fDiv_bernoulliMeasure_one_right Bool.false_ne_true.symm]
    refine (f.continuous.comp h_ofReal).continuousAt.add
      (ENNReal.Tendsto.const_mul (h_ofReal_sub.tendsto p) (Or.inl ?_))
    rw [ENNReal.ofReal_ne_zero_iff, sub_pos]
    exact lt_of_le_of_ne p.property.2 (coe_ne_one.mpr hpq)
  exact (continuous_fDiv_bernoulliMeasure_left hq0 hq1).continuousAt

/-- Let `r₁ ≤ r₂`. If there are pairs `(a, b)` with `a ≥ r₁` arbitrarily close to `r₁`, `b ≥ r₂`
and `d_f(a, b) ≤ D`, then `d_f(r₁, r₂) ≤ D`. -/
lemma fDiv_bernoulliMeasure_le_of_forall_exists {D : ℝ≥0∞} {r₁ r₂ : I} (h₁₂ : r₁ ≤ r₂)
    (h : ∀ ε : ℝ, 0 < ε → ∃ a b : I, r₁ ≤ a ∧ (a : ℝ) ≤ r₁ + ε ∧ r₂ ≤ b
      ∧ fDiv f Ber(x, y, a) Ber(x, y, b) ≤ D) :
    fDiv f Ber(x, y, r₁) Ber(x, y, r₂) ≤ D := by
  rcases eq_or_lt_of_le h₁₂ with h_eq | h_lt
  · simp [h_eq, fDiv_self]
  by_contra h_lt_D
  rw [not_le] at h_lt_D
  have h_ev : ∀ᶠ a in 𝓝 r₁, D < fDiv f Ber(x, y, a) Ber(x, y, r₂) :=
    (continuousAt_fDiv_bernoulliMeasure_left h_lt.ne).eventually (lt_mem_nhds h_lt_D)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h_ev
  have h_lt' : (0 : ℝ) < r₂ - r₁ := sub_pos.mpr h_lt
  obtain ⟨a, b, ha₁, ha₂, hb, hab⟩ :=
    h (min (δ / 2) ((r₂ - r₁) / 2)) (lt_min (half_pos hδ) (half_pos h_lt'))
  have ha₁' : (r₁ : ℝ) ≤ a := Subtype.coe_le_coe.mpr ha₁
  have ha_lt : (a : ℝ) < r₂ := by linarith [min_le_right (δ / 2) (((r₂ : ℝ) - r₁) / 2)]
  have h_dist : dist a r₁ < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith [min_le_left (δ / 2) (((r₂ : ℝ) - r₁) / 2)]
  have h_mono : fDiv f Ber(x, y, a) Ber(x, y, r₂) ≤ fDiv f Ber(x, y, a) Ber(x, y, b) :=
    monotoneOn_fDiv_bernoulliMeasure_right a ha_lt.le
      (ha_lt.le.trans (Subtype.coe_le_coe.mpr hb)) hb
  exact absurd ((hball h_dist).trans_le (h_mono.trans hab)) (lt_irrefl _)

end Continuity

section DataProcessing

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}

/-- **Data processing for the mean**: for probability measures `μ, ν` on the unit interval with
means `p` and `q`, the f-divergence between the Bernoulli distributions with parameters `p` and `q`
is at most `fDiv f μ ν`. -/
theorem fDiv_bernoulliMeasure_le_of_integral_eq (μ ν : Measure I) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {p q : I} (hp : (p : ℝ) = ∫ t, (t : ℝ) ∂μ)
    (hq : (q : ℝ) = ∫ t, (t : ℝ) ∂ν) :
    fDiv f Ber(x, y, p) Ber(x, y, q) ≤ fDiv f μ ν := by
  rw [← bernoulliKernel_comp_eq_bernoulliMeasure _ _ μ hp,
    ← bernoulliKernel_comp_eq_bernoulliMeasure _ _ ν hq]
  exact fDiv_comp_right_le μ ν _

/-- **Data processing for the mean of a function**: if `g : 𝓨 → I` has means `p` and `q` under the
probability measures `μ` and `ν`, then `d_f(p, q) ≤ D_f(μ, ν)`. -/
theorem fDiv_bernoulliMeasure_le_of_integral_comp_eq (μ ν : Measure 𝓨) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : 𝓨 → I} (hg : Measurable g) {p q : I}
    (hp : (p : ℝ) = ∫ z, (g z : ℝ) ∂μ) (hq : (q : ℝ) = ∫ z, (g z : ℝ) ∂ν) :
    fDiv f Ber(x, y, p) Ber(x, y, q) ≤ fDiv f μ ν := by
  refine (fDiv_bernoulliMeasure_le_of_integral_eq (μ.map g) (ν.map g) ?_ ?_).trans
    (fDiv_map_le hg)
  · rw [integral_map hg.aemeasurable (by fun_prop), hp]
  · rw [integral_map hg.aemeasurable (by fun_prop), hq]

/-- **Data processing for the mean of a function**, version for a function with values in
`ℝ≥0∞` bounded by `1`: if `g` has integrals `p` and `q` under the probability measures `μ` and `ν`,
then `d_f(p, q) ≤ D_f(μ, ν)`. -/
theorem fDiv_bernoulliMeasure_le_of_lintegral_eq (μ ν : Measure 𝓨) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : 𝓨 → ℝ≥0∞} (hg : Measurable g) (hg1 : ∀ z, g z ≤ 1) {p q : I}
    (hp : ENNReal.ofReal p = ∫⁻ z, g z ∂μ) (hq : ENNReal.ofReal q = ∫⁻ z, g z ∂ν) :
    fDiv f Ber(x, y, p) Ber(x, y, q) ≤ fDiv f μ ν := by
  let g' : 𝓨 → I := fun z ↦ ⟨(g z).toReal, ENNReal.toReal_mem_unitInterval (hg1 z)⟩
  have hg' : Measurable g' := hg.ennreal_toReal.subtype_mk
  have h_lt (ρ : Measure 𝓨) : ∀ᵐ z ∂ρ, g z < ∞ :=
    ae_of_all _ fun z ↦ (hg1 z).trans_lt ENNReal.one_lt_top
  refine fDiv_bernoulliMeasure_le_of_integral_comp_eq μ ν hg' ?_ ?_
  · rw [integral_toReal hg.aemeasurable (h_lt μ), ← hp, ENNReal.toReal_ofReal p.property.1]
  · rw [integral_toReal hg.aemeasurable (h_lt ν), ← hq, ENNReal.toReal_ofReal q.property.1]

/-- **Data processing for the mean through a kernel**: for a Markov kernel `κ` to the unit
interval such that `κ ∘ₘ μ` and `κ ∘ₘ ν` have means `p` and `q`, `d_f(p, q) ≤ D_f(μ, ν)`. -/
theorem fDiv_bernoulliMeasure_le_of_integral_comp_kernel_eq (μ ν : Measure 𝓨)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (κ : Kernel 𝓨 I) [IsMarkovKernel κ]
    {p q : I} (hp : (p : ℝ) = ∫ t, (t : ℝ) ∂(κ ∘ₘ μ)) (hq : (q : ℝ) = ∫ t, (t : ℝ) ∂(κ ∘ₘ ν)) :
    fDiv f Ber(x, y, p) Ber(x, y, q) ≤ fDiv f μ ν :=
  (fDiv_bernoulliMeasure_le_of_integral_eq _ _ hp hq).trans (fDiv_comp_right_le μ ν κ)

end DataProcessing

end ProbabilityTheory
