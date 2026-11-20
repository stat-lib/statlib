/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import Statlib.EValues.Divergence
public import Statlib.Divergence.Renyi.Bernoulli
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli
public import Statlib.ForMathlib.Probability.Distributions.Bernoulli

/-!
# E-variables for Bernoulli distributions

We compute the numeraire, the maximal logarithmic utility and the e-divergences for the sets of
Bernoulli distributions `Ber(true, false, q)` on `Bool` with parameter `q` at most `δ`, or at least
`η`.

For `δ ≤ p`, the numeraire of `Ber(true, false, p)` for the distributions with parameter at most
`δ` is the likelihood ratio of `Ber(true, false, p)` with respect to `Ber(true, false, δ)`: the
expectation of the ratio of any e-variable to it is the expectation of that e-variable under
`Ber(true, false, δ)`, which is at most one. The maximal logarithmic utility is then the
Kullback-Leibler divergence `klBerReal p δ`. Negation exchanges the parameters at most `1 - η` with
those at least `η`.

For `δ ≤ η`, the e-Rényi divergence of order `α` between the two sets is the Rényi divergence
between `Ber(true, false, δ)` and `Ber(true, false, η)`, and for `δ < η` their e-Chernoff divergence
is the Chernoff information. Both are computed with a saddle point: a Bernoulli distribution
`Ber(true, false, r)` with `δ ≤ r ≤ η` whose likelihood ratios with respect to `Ber(true, false, δ)`
and `Ber(true, false, η)` certify both the lower bound (they are e-variables) and the upper bound
(they are the numeraires at `Ber(true, false, r)`). The same saddle point computes the e-Chernoff
divergence between the singletons `{Ber(true, false, δ)}` and `{Ber(true, false, η)}`, which is the
Chernoff information `chernoffDiv 1` (`echernoffDiv_singleton`).

## Main statements

* `isEVar_bernoulli_iff`: characterization of the e-variables for the Bernoulli distributions with
  parameter at most `δ`.
* `isNumeraire_bernoulli`: the numeraire is the likelihood ratio.
* `maxUtility_bernoulli`, `maxUtility_bernoulli_ge`: the maximal logarithmic utility is the
  Kullback-Leibler divergence. For `p ≤ δ`, `Ber(true, false, p)` belongs to the set and its
  maximal logarithmic utility is zero (`maxUtility_eq_zero_of_mem`).
* `maxUtility_bernoulli_singleton`: for the singleton `{Ber(true, false, δ)}`, the maximal
  logarithmic utility of `Ber(true, false, s)` is the Kullback-Leibler divergence `klBerReal s δ`
  for every `s`.
* `erenyiDiv_bernoulli`: the e-Rényi divergence of order `α` between the Bernoulli distributions
  with parameter at most `δ` and those with parameter at least `η` is the Rényi divergence
  `renyiDiv α Ber(true, false, δ) Ber(true, false, η)`, which is
  `(α - 1)⁻¹ * log (δ ^ α * η ^ (1 - α) + (1 - δ) ^ α * (1 - η) ^ (1 - α))`
  (`renyiDiv_bernoulliMeasure`).
* `echernoffDiv_bernoulli`: their e-Chernoff divergence is the Chernoff information
  `chernoffDiv 1 Ber(true, false, δ) Ber(true, false, η)`.
* `chernoffDiv_one_bernoulliMeasure`: the Chernoff information between `Ber(true, false, δ)` and
  `Ber(true, false, η)` is `klBerReal r δ = klBerReal r η` for an explicit `r ∈ [δ, η]`.
* `erenyiDiv_inv_two_bernoulli_one_sub`, `echernoffDiv_bernoulli_one_sub`: for `η = 1 - δ`, the
  divergences are `log (1 / (4 * δ * (1 - δ)))` (order `1/2`) and half of it.
-/

@[expose] public section

open InformationTheory MeasureTheory unitInterval
open scoped ENNReal

namespace ProbabilityTheory

lemma eintegral_bernoulliMeasure {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    [MeasurableSingletonClass 𝓧] (x y : 𝓧) (p : I) (f : 𝓧 → EReal) :
    ∫ᵉ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, eintegral_add_measure, ENNReal.smul_def, ENNReal.smul_def,
    eintegral_smul_measure (by simp), eintegral_smul_measure (by simp), eintegral_dirac,
    eintegral_dirac, coe_toNNReal_eq_ofReal, coe_toNNReal_symm_eq_ofReal]

/-- Version of `eintegral_bernoulliMeasure` for a measurable function, without
`MeasurableSingletonClass`. -/
lemma eintegral_bernoulliMeasure' {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} (x y : 𝓧) (p : I)
    {f : 𝓧 → EReal} (hf : Measurable f) :
    ∫ᵉ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, eintegral_add_measure, ENNReal.smul_def, ENNReal.smul_def,
    eintegral_smul_measure (by simp), eintegral_smul_measure (by simp), eintegral_dirac' _ hf,
    eintegral_dirac' _ hf, coe_toNNReal_eq_ofReal, coe_toNNReal_symm_eq_ofReal]

/-! ### E-variables and numeraire -/

variable {δ η : I} {X : Bool → ℝ≥0∞}

/-- A function is an e-variable for the Bernoulli distributions with parameter at most `δ` iff its
expectations under the parameters `0` and `δ` are at most one: the expectation is affine in the
parameter. -/
lemma isEVar_bernoulli_iff :
    IsEVar X {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)} ↔
      X false ≤ 1 ∧ ENNReal.ofReal δ * X true + ENNReal.ofReal (1 - δ) * X false ≤ 1 := by
  have h_iff : IsEVar X {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)} ↔ ∀ q : I, (q : ℝ) ≤ δ →
      ENNReal.ofReal q * X true + ENNReal.ofReal (1 - q) * X false ≤ 1 := by
    refine ⟨fun hX q hq ↦ ?_, fun h ↦ ⟨.of_discrete, ?_⟩⟩
    · simpa [lintegral_bernoulliMeasure] using hX.lintegral_le_one ⟨q, hq, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      simpa [lintegral_bernoulliMeasure] using h q hq
  rw [h_iff]
  refine ⟨fun h ↦ ⟨by simpa using h 0 δ.2.1, h δ le_rfl⟩, fun ⟨h0, hδ⟩ q hq ↦ ?_⟩
  rcases eq_or_ne δ 0 with rfl | hδ0
  · obtain rfl : q = 0 := Subtype.ext (le_antisymm hq q.2.1)
    simpa using h0
  have hδ_pos : (0 : ℝ) < δ := coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hδ0)
  have hδ_le : (δ : ℝ) ≤ 1 := δ.2.2
  -- the distribution with parameter `q` is a mixture of those with parameters `δ` and `0`
  set t := (q : ℝ) / δ
  have ht_nonneg : 0 ≤ t := div_nonneg q.2.1 hδ_pos.le
  have ht_le : t ≤ 1 := (div_le_one hδ_pos).mpr hq
  calc ENNReal.ofReal q * X true + ENNReal.ofReal (1 - q) * X false
  _ = ENNReal.ofReal t * (ENNReal.ofReal δ * X true + ENNReal.ofReal (1 - δ) * X false)
      + ENNReal.ofReal (1 - t) * X false := by
    rw [show (q : ℝ) = t * δ from (div_mul_cancel₀ _ hδ_pos.ne').symm,
      show 1 - t * (δ : ℝ) = t * (1 - δ) + (1 - t) by ring,
      ENNReal.ofReal_mul ht_nonneg, ENNReal.ofReal_add (by nlinarith) (by linarith),
      ENNReal.ofReal_mul ht_nonneg]
    ring
  _ ≤ ENNReal.ofReal t * 1 + ENNReal.ofReal (1 - t) * 1 := by gcongr
  _ = 1 := by
    rw [mul_one, mul_one, ← ENNReal.ofReal_add ht_nonneg (by linarith), add_sub_cancel,
      ENNReal.ofReal_one]

private lemma ofReal_mul_div_ofReal_div {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (y : ℝ≥0∞) :
    ENNReal.ofReal a * (y / ENNReal.ofReal (a / c)) = ENNReal.ofReal c * y := by
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div, mul_comm y,
    ← mul_assoc, ← ENNReal.ofReal_mul ha.le]
  congr 2
  field_simp

/-- For `δ ≤ p`, the numeraire of `Ber(true, false, p)` for the Bernoulli distributions with
parameter at most `δ` is the likelihood ratio of `Ber(true, false, p)` with respect to
`Ber(true, false, δ)`. -/
theorem isNumeraire_bernoulli {p : I} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hδp : δ ≤ p) :
    IsNumeraire
      (fun b ↦ if b then ENNReal.ofReal (p / δ) else ENNReal.ofReal ((1 - p) / (1 - δ)))
      {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)} Ber(true, false, p) := by
  set X : Bool → ℝ≥0∞ :=
    fun b ↦ if b then ENNReal.ofReal (p / δ) else ENNReal.ofReal ((1 - p) / (1 - δ))
  replace hδ_pos : (0 : ℝ) < δ := coe_pos.mpr hδ_pos
  replace hδ_lt : (δ : ℝ) < 1 := coe_lt_one.mpr hδ_lt
  replace hδp : (δ : ℝ) ≤ p := hδp
  have hp_pos : 0 < (p : ℝ) := hδ_pos.trans_le hδp
  have hδ_one : 0 < 1 - (δ : ℝ) := by linarith
  have hX : IsEVar X {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)} := by
    rw [isEVar_bernoulli_iff]
    simp only [X, ↓reduceIte, Bool.false_eq_true]
    refine ⟨?_, ?_⟩
    · rw [ENNReal.ofReal_le_one, div_le_one hδ_one]
      linarith
    · rw [← ENNReal.ofReal_mul hδ_pos.le, ← ENNReal.ofReal_mul hδ_one.le,
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hδ_one.le (div_nonneg
          (by linarith [p.2.2]) hδ_one.le)), ENNReal.ofReal_le_one]
      field_simp
      linarith
  -- the finite support of `X` has full measure
  have h_fsupport : Ber(true, false, p) X.fsupport = 1 := by
    rcases eq_or_lt_of_le p.2.2 with hp1 | hp1
    · obtain rfl : p = 1 := Subtype.ext hp1
      rw [bernoulliMeasure_one, Measure.dirac_apply_of_mem]
      simp [X, hδ_pos]
    · have : X.fsupport = Set.univ := by
        ext b
        cases b <;> simp [X, ENNReal.ofReal_eq_zero, div_pos hp_pos hδ_pos,
          div_pos (sub_pos.mpr hp1) hδ_one]
      simp [this]
  refine isNumeraire_of_lintegral_div_le hX (by simp [h_fsupport]) fun Y hY ↦ ?_
  -- the expectation of `Y / X` under `Ber(true, false, p)` is at most that of `Y` under
  -- `Ber(true, false, δ)`
  have hYδ := hY.lintegral_le_one ⟨δ, le_rfl, rfl⟩
  rw [lintegral_bernoulliMeasure] at hYδ
  rw [h_fsupport, lintegral_bernoulliMeasure]
  refine le_trans ?_ hYδ
  simp only [X, ↓reduceIte, Bool.false_eq_true]
  gcongr ?_ + ?_
  · rw [ofReal_mul_div_ofReal_div hp_pos hδ_pos]
  · rcases eq_or_lt_of_le p.2.2 with hp1 | hp1
    · simp [hp1]
    · rw [ofReal_mul_div_ofReal_div (sub_pos.mpr hp1) hδ_one]

/-- For `δ ≤ p`, the maximal logarithmic utility of `Ber(true, false, p)` for the Bernoulli
distributions with parameter at most `δ` is the Kullback-Leibler divergence between
`Ber(true, false, p)` and `Ber(true, false, δ)`. For `p ≤ δ`, it is zero by
`maxUtility_eq_zero_of_mem`. -/
theorem maxUtility_bernoulli {p : I} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hδp : δ ≤ p) :
    maxUtility Ber(true, false, p) {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)} logUtility
      = klBerReal p δ := by
  rw [(isNumeraire_bernoulli hδ_pos hδ_lt hδp).maxUtility_eq_eintegral,
    eintegral_bernoulliMeasure, klBerReal_apply]
  replace hδ_pos : (0 : ℝ) < δ := coe_pos.mpr hδ_pos
  replace hδ_lt : (δ : ℝ) < 1 := coe_lt_one.mpr hδ_lt
  have hp_pos : 0 < (p : ℝ) := hδ_pos.trans_le hδp
  have hδ_one : 0 < 1 - (δ : ℝ) := by linarith
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [ENNReal.log_ofReal_of_pos (div_pos hp_pos hδ_pos), EReal.coe_ennreal_ofReal,
    max_eq_left hp_pos.le]
  rcases eq_or_lt_of_le p.2.2 with hp1 | hp1
  · simp [hp1]
  rw [ENNReal.log_ofReal_of_pos (div_pos (sub_pos.mpr hp1) hδ_one), EReal.coe_ennreal_ofReal,
    max_eq_left (sub_pos.mpr hp1).le]
  norm_cast

/-- For `δ ∈ (0, 1)`, the maximal logarithmic utility of `Ber(true, false, s)` for the singleton
`{Ber(true, false, δ)}` is the Kullback-Leibler divergence `klBerReal s δ`, for every `s`. For the
Bernoulli distributions with parameter at most `δ`, see `maxUtility_bernoulli`. -/
theorem maxUtility_bernoulli_singleton (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (s : I) :
    maxUtility Ber(true, false, s) {Ber(true, false, δ)} logUtility = klBerReal s δ := by
  rw [maxUtility_singleton_eq_klDiv,
    klDiv_bernoulliMeasure_eq_klBerReal (by decide) s hδ_pos.ne' hδ_lt.ne,
    EReal.coe_ennreal_ofReal, max_eq_left (klBerReal_nonneg s.2.1 s.2.2 (coe_pos.mpr hδ_pos)
      (coe_lt_one.mpr hδ_lt))]

/-- The likelihood ratio of `Ber(true, false, p)` with respect to `Ber(true, false, δ)` is an
e-variable for the Bernoulli distributions with parameter at most `δ`: its expected logarithm
under `Ber(true, false, s)`, an affine function of `s`, bounds the maximal logarithmic utility of
`Ber(true, false, s)`. It is equal to it at `s = p`. -/
private lemma le_maxUtility_bernoulli {p : I} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hδp : δ ≤ p)
    (hp : p < 1) (s : I) :
    ((s * Real.log (p / δ) + (1 - s) * Real.log ((1 - p) / (1 - δ)) : ℝ) : EReal)
      ≤ maxUtility Ber(true, false, s) {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)}
        logUtility := by
  refine le_of_eq_of_le ?_
    ((isNumeraire_bernoulli hδ_pos hδ_lt hδp).isEVar.eintegral_le_maxUtility _ logUtility)
  replace hδ_pos : (0 : ℝ) < δ := coe_pos.mpr hδ_pos
  replace hδ_lt : (δ : ℝ) < 1 := coe_lt_one.mpr hδ_lt
  replace hp : (p : ℝ) < 1 := coe_lt_one.mpr hp
  have hp_pos : 0 < (p : ℝ) := hδ_pos.trans_le hδp
  have hδ_one : 0 < 1 - (δ : ℝ) := by linarith
  rw [eintegral_bernoulliMeasure]
  simp only [Function.comp_apply, ↓reduceIte, Bool.false_eq_true, logUtility_apply]
  rw [ENNReal.log_ofReal_of_pos (div_pos hp_pos hδ_pos),
    ENNReal.log_ofReal_of_pos (div_pos (by linarith) hδ_one), EReal.coe_ennreal_ofReal,
    EReal.coe_ennreal_ofReal, max_eq_left s.2.1, max_eq_left (by linarith [s.2.2])]
  norm_cast

/-! ### Bernoulli distributions with parameter at least `η`

Negation maps the Bernoulli distributions with parameter at most `1 - η` to those with parameter
at least `η`, which reduces the maximal logarithmic utility for the latter to the former. -/

lemma map_not_bernoulliMeasure (q : I) : Ber(true, false, q).map not = Ber(true, false, σ q) := by
  rw [map_bernoulliMeasure, Bool.not_true, Bool.not_false, ← bernoulliMeasure_swap]

lemma image_map_not_bernoulli (δ : I) :
    {μ.map not | μ ∈ {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)}}
      = {Ber(true, false, q) | (q : I) (_ : (σ δ : ℝ) ≤ q)} := by
  ext μ
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨σ q, by rw [coe_symm_eq, coe_symm_eq]; linarith, (map_not_bernoulliMeasure q).symm⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨Ber(true, false, σ q), ⟨σ q, by rw [coe_symm_eq] at hq ⊢; linarith, rfl⟩, ?_⟩
    rw [map_not_bernoulliMeasure, symm_symm]

private lemma maxUtility_bernoulli_ge_eq (η p : I) :
    maxUtility Ber(true, false, p) {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)} logUtility
      = maxUtility Ber(true, false, σ p) {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ σ η)}
        logUtility := by
  have h := image_map_not_bernoulli (σ η)
  rw [symm_symm] at h
  rw [← h, maxUtility_involutive _ _ .of_discrete Bool.not_not, map_not_bernoulliMeasure]

/-- For `p ≤ η`, the maximal logarithmic utility of `Ber(true, false, p)` for the Bernoulli
distributions with parameter at least `η` is the Kullback-Leibler divergence between
`Ber(true, false, p)` and `Ber(true, false, η)`. -/
theorem maxUtility_bernoulli_ge {p : I} (hη_pos : 0 < η) (hη_lt : η < 1) (hpη : p ≤ η) :
    maxUtility Ber(true, false, p) {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)} logUtility
      = klBerReal p η := by
  rw [maxUtility_bernoulli_ge_eq, maxUtility_bernoulli (by rwa [← symm_one, symm_lt_symm])
    (by rwa [← symm_zero, symm_lt_symm]) (symm_le_symm.mpr hpη), coe_symm_eq, coe_symm_eq,
    klBerReal_one_sub]

/-- Version of `le_maxUtility_bernoulli` for the Bernoulli distributions with parameter at least
`η`, with the likelihood ratio of `Ber(true, false, p)` with respect to `Ber(true, false, η)`. -/
private lemma le_maxUtility_bernoulli_ge {p : I} (hη_pos : 0 < η) (hη_lt : η < 1)
    (hpη : p ≤ η) (hp : 0 < p) (s : I) :
    ((s * Real.log (p / η) + (1 - s) * Real.log ((1 - p) / (1 - η)) : ℝ) : EReal)
      ≤ maxUtility Ber(true, false, s) {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)}
        logUtility := by
  rw [maxUtility_bernoulli_ge_eq]
  refine le_of_eq_of_le ?_ (le_maxUtility_bernoulli (p := σ p) (δ := σ η)
    (by rwa [← symm_one, symm_lt_symm]) (by rwa [← symm_zero, symm_lt_symm])
    (symm_le_symm.mpr hpη) (by rwa [← symm_zero, symm_lt_symm]) (σ s))
  simp only [coe_symm_eq, sub_sub_cancel]
  norm_cast
  ring

/-! ### Divergences between Bernoulli distributions -/

/-- The parameter `δ ^ a * η ^ (1 - a) / Z` of the normalized geometric mixture of
`Ber(true, false, δ)` and `Ber(true, false, η)` is at least `δ`. -/
private lemma le_geomMix {δ η a : ℝ} (ha1 : a ≤ 1) (hδ_pos : 0 < δ) (hδη : δ ≤ η) (hη : η < 1) :
    δ * ((1 - δ) ^ a * (1 - η) ^ (1 - a)) ≤ (1 - δ) * (δ ^ a * η ^ (1 - a)) := by
  have hη_pos : 0 < η := hδ_pos.trans_le hδη
  have hδ1 : 0 < 1 - δ := by linarith
  have hη1 : 0 < 1 - η := by linarith
  calc δ * ((1 - δ) ^ a * (1 - η) ^ (1 - a))
  _ = δ ^ a * (1 - δ) ^ a * (δ * (1 - η)) ^ (1 - a) := by
    rw [Real.mul_rpow hδ_pos.le hη1.le, show δ ^ a * (1 - δ) ^ a * (δ ^ (1 - a) * (1 - η) ^ (1 - a))
      = (δ ^ a * δ ^ (1 - a)) * ((1 - δ) ^ a * (1 - η) ^ (1 - a)) by ring,
      ← Real.rpow_add hδ_pos, add_sub_cancel, Real.rpow_one]
  _ ≤ δ ^ a * (1 - δ) ^ a * ((1 - δ) * η) ^ (1 - a) := by
    gcongr δ ^ a * (1 - δ) ^ a * ?_
    exact Real.rpow_le_rpow (mul_nonneg hδ_pos.le hη1.le) (by nlinarith) (by linarith)
  _ = (1 - δ) * (δ ^ a * η ^ (1 - a)) := by
    rw [Real.mul_rpow hδ1.le hη_pos.le, show δ ^ a * (1 - δ) ^ a * ((1 - δ) ^ (1 - a) * η ^ (1 - a))
      = ((1 - δ) ^ a * (1 - δ) ^ (1 - a)) * (δ ^ a * η ^ (1 - a)) by ring,
      ← Real.rpow_add hδ1, add_sub_cancel, Real.rpow_one]

/-- The parameter `δ ^ a * η ^ (1 - a) / Z` of the normalized geometric mixture of
`Ber(true, false, δ)` and `Ber(true, false, η)` is at most `η`. -/
private lemma geomMix_le {δ η a : ℝ} (ha0 : 0 ≤ a) (hδ_pos : 0 < δ) (hδη : δ ≤ η) (hη : η < 1) :
    (1 - η) * (δ ^ a * η ^ (1 - a)) ≤ η * ((1 - δ) ^ a * (1 - η) ^ (1 - a)) := by
  have hη_pos : 0 < η := hδ_pos.trans_le hδη
  have hδ1 : 0 < 1 - δ := by linarith
  have hη1 : 0 < 1 - η := by linarith
  calc (1 - η) * (δ ^ a * η ^ (1 - a))
  _ = (δ * (1 - η)) ^ a * (η ^ (1 - a) * (1 - η) ^ (1 - a)) := by
    rw [Real.mul_rpow hδ_pos.le hη1.le, show δ ^ a * (1 - η) ^ a * (η ^ (1 - a) * (1 - η) ^ (1 - a))
      = ((1 - η) ^ a * (1 - η) ^ (1 - a)) * (δ ^ a * η ^ (1 - a)) by ring,
      ← Real.rpow_add hη1, add_sub_cancel, Real.rpow_one]
  _ ≤ ((1 - δ) * η) ^ a * (η ^ (1 - a) * (1 - η) ^ (1 - a)) := by
    gcongr ?_ * (η ^ (1 - a) * (1 - η) ^ (1 - a))
    exact Real.rpow_le_rpow (mul_nonneg hδ_pos.le hη1.le) (by nlinarith) ha0
  _ = η * ((1 - δ) ^ a * (1 - η) ^ (1 - a)) := by
    rw [Real.mul_rpow hδ1.le hη_pos.le, show (1 - δ) ^ a * η ^ a * (η ^ (1 - a) * (1 - η) ^ (1 - a))
      = (η ^ a * η ^ (1 - a)) * ((1 - δ) ^ a * (1 - η) ^ (1 - a)) by ring,
      ← Real.rpow_add hη_pos, add_sub_cancel, Real.rpow_one]

/-- For `δ ≤ η`, the e-Rényi divergence of order `α < 1` between the Bernoulli distributions with
parameter at most `δ` and those with parameter at least `η` is
`(α - 1)⁻¹ * log (δ ^ α * η ^ (1 - α) + (1 - δ) ^ α * (1 - η) ^ (1 - α))`.

The normalized geometric mixture `Ber(true, false, r)` of `Ber(true, false, δ)` and
`Ber(true, false, η)` with weights `α` and `1 - α` is a saddle point: `δ ≤ r ≤ η`, the likelihood
ratios of `Ber(true, false, r)` with respect to `Ber(true, false, δ)` and `Ber(true, false, η)` are
e-variables for the two sets and their numeraires at `Ber(true, false, r)`, and the mixture of
their logarithms with weights `α` and `1 - α` is constant. -/
private theorem erenyiDiv_bernoulli_eq_ofReal {α : ℝ≥0∞} (hα : α < 1) (hδ_pos : 0 < δ)
    (hδη : δ ≤ η) (hη : η < 1) :
    erenyiDiv α {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)}
        {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)}
      = ENNReal.ofReal ((α.toReal - 1)⁻¹ * Real.log ((δ : ℝ) ^ α.toReal * (η : ℝ) ^ (1 - α.toReal)
        + (1 - (δ : ℝ)) ^ α.toReal * (1 - (η : ℝ)) ^ (1 - α.toReal))) := by
  obtain ⟨a, ha0, rfl⟩ : ∃ a : ℝ, 0 ≤ a ∧ α = ENNReal.ofReal a :=
    ⟨α.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hα.ne_top).symm⟩
  have ha1 : a < 1 := ENNReal.ofReal_lt_one.mp hα
  have h1α : 1 - ENNReal.ofReal a = ENNReal.ofReal (1 - a) := by
    rw [ENNReal.ofReal_sub _ ha0, ENNReal.ofReal_one]
  rw [ENNReal.toReal_ofReal ha0]
  have hδ' : (0 : ℝ) < δ := coe_pos.mpr hδ_pos
  have hδη' : (δ : ℝ) ≤ η := hδη
  have hη' : (η : ℝ) < 1 := coe_lt_one.mpr hη
  have hη_pos : (0 : ℝ) < η := hδ'.trans_le hδη'
  have hδ1 : 0 < 1 - (δ : ℝ) := by linarith
  have hη1 : 0 < 1 - (η : ℝ) := by linarith
  -- the normalized geometric mixture `Ber(true, false, r)`
  set u := (δ : ℝ) ^ a * (η : ℝ) ^ (1 - a) with hu_def
  set v := (1 - (δ : ℝ)) ^ a * (1 - (η : ℝ)) ^ (1 - a) with hv_def
  have hu : 0 < u := by positivity
  have hv : 0 < v := mul_pos (Real.rpow_pos_of_pos hδ1 _) (Real.rpow_pos_of_pos hη1 _)
  have hZ : 0 < u + v := add_pos hu hv
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = u / (u + v) := ⟨_, rfl⟩
  have h1r : 1 - r = v / (u + v) := by rw [hr]; field_simp; ring
  have hr0 : 0 < r := hr ▸ div_pos hu hZ
  have hr1 : 0 < 1 - r := h1r ▸ div_pos hv hZ
  have hδr : (δ : ℝ) ≤ r := by
    rw [hr, le_div_iff₀ hZ]
    linarith [le_geomMix ha1.le hδ' hδη' hη']
  have hrη : r ≤ (η : ℝ) := by
    rw [hr, div_le_iff₀ hZ]
    linarith [geomMix_le ha0 hδ' hδη' hη']
  -- the mixture of the logarithms of the likelihood ratios is constant
  have h_true : a * Real.log (r / δ) + (1 - a) * Real.log (r / η) = -Real.log (u + v) := by
    rw [Real.log_div hr0.ne' hδ'.ne', Real.log_div hr0.ne' hη_pos.ne', hr,
      Real.log_div hu.ne' hZ.ne', hu_def, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hδ', Real.log_rpow hη_pos]
    ring
  have h_false : a * Real.log ((1 - r) / (1 - δ)) + (1 - a) * Real.log ((1 - r) / (1 - η))
      = -Real.log (u + v) := by
    rw [Real.log_div hr1.ne' hδ1.ne', Real.log_div hr1.ne' hη1.ne', h1r,
      Real.log_div hv.ne' hZ.ne', hv_def,
      Real.log_mul (Real.rpow_pos_of_pos hδ1 _).ne' (Real.rpow_pos_of_pos hη1 _).ne',
      Real.log_rpow hδ1, Real.log_rpow hη1]
    ring
  have h_comb (s : ℝ) : a * (s * Real.log (r / δ) + (1 - s) * Real.log ((1 - r) / (1 - δ)))
      + (1 - a) * (s * Real.log (r / η) + (1 - s) * Real.log ((1 - r) / (1 - η)))
      = -Real.log (u + v) := by
    linear_combination s * h_true + (1 - s) * h_false
  set r' : I := ⟨r, hr0.le, by linarith⟩
  have hδr' : δ ≤ r' := hδr
  have hr'η : r' ≤ η := hrη
  have hr'0 : 0 < r' := coe_pos.mp hr0
  have hr'1 : r' < 1 := coe_lt_one.mp (by simp only [r']; linarith)
  have h_inf : ⨅ (R : Measure Bool) (_ : IsProbabilityMeasure R),
      ENNReal.ofReal a
          * (maxUtility R {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)} logUtility).toENNReal
        + (1 - ENNReal.ofReal a)
          * (maxUtility R {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)} logUtility).toENNReal
      = ENNReal.ofReal (-Real.log (u + v)) := by
    refine le_antisymm (iInf₂_le_of_le Ber(true, false, r') inferInstance (le_of_eq ?_))
      (le_iInf₂ fun R _ ↦ ?_)
    · -- the geometric mixture attains the bound
      rw [maxUtility_bernoulli hδ_pos (hδη.trans_lt hη) hδr',
        maxUtility_bernoulli_ge (hδ_pos.trans_le hδη) hη hr'η,
        EReal.real_coe_toENNReal, EReal.real_coe_toENNReal, h1α, ← ENNReal.ofReal_mul ha0,
        ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add
          (mul_nonneg ha0 (klBerReal_nonneg hr0.le (by linarith) hδ' (by linarith)))
          (mul_nonneg (by linarith) (klBerReal_nonneg hr0.le (by linarith) hη_pos hη'))]
      exact congrArg ENNReal.ofReal (h_comb r)
    · -- every probability measure on `Bool` is a Bernoulli distribution
      obtain ⟨s, rfl⟩ : ∃ s : I, Ber(true, false, s) = R :=
        ⟨_, (eq_bernoulliMeasure_real_true R).symm⟩
      rw [← h_comb s, h1α]
      refine ENNReal.ofReal_add_le.trans ?_
      rw [ENNReal.ofReal_mul ha0, ENNReal.ofReal_mul (by linarith)]
      gcongr <;> rw [← EReal.real_coe_toENNReal] <;> refine EReal.toENNReal_le_toENNReal ?_
      · exact le_maxUtility_bernoulli hδ_pos (hδη.trans_lt hη) hδr' hr'1 s
      · exact le_maxUtility_bernoulli_ge (hδ_pos.trans_le hδη) hη hr'η hr'0 s
  rw [erenyiDiv, h_inf, h1α, ← ENNReal.ofReal_inv_of_pos (by linarith),
    ← ENNReal.ofReal_mul (by simp [ha1.le])]
  congr 1
  rw [show a - 1 = -(1 - a) by ring, inv_neg]
  ring

/-- For `δ < η`, the e-Chernoff divergence between sets `S` and `T` of Bernoulli distributions
with parameters at most `δ`, respectively at least `η`, is `klBerReal r δ = klBerReal r η`, where
`r` is the parameter at which the two Kullback-Leibler divergences are equal, provided that the
maximal logarithmic utilities of `Ber(true, false, s)` for `S` and `T` are at most the
Kullback-Leibler divergences to `Ber(true, false, δ)` and `Ber(true, false, η)`. This holds for the
sets of all such Bernoulli distributions and for the singletons `{Ber(true, false, δ)}` and
`{Ber(true, false, η)}`.

The lower bounds given by the likelihood ratios of `Ber(true, false, r)` with respect to
`Ber(true, false, δ)` and `Ber(true, false, η)` are affine in the parameter, one nondecreasing and
one nonincreasing, and they are equal at `r`. -/
private theorem echernoffDiv_bernoulli_eq_ofReal (hδ_pos : 0 < δ) (hδη : δ < η) (hη : η < 1)
    {r : ℝ}
    (hr : r = Real.log ((1 - δ) / (1 - η)) / (Real.log (η / δ) + Real.log ((1 - δ) / (1 - η))))
    {S T : Set (Measure Bool)} (hS : S ⊆ {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)})
    (hT : T ⊆ {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)})
    (hS_le : ∀ s : I, δ ≤ s → maxUtility Ber(true, false, s) S logUtility ≤ klBerReal s δ)
    (hT_le : ∀ s : I, s ≤ η → maxUtility Ber(true, false, s) T logUtility ≤ klBerReal s η) :
    echernoffDiv S T = ENNReal.ofReal (klBerReal r δ) := by
  have hδ' : (0 : ℝ) < δ := coe_pos.mpr hδ_pos
  have hδη' : (δ : ℝ) < η := hδη
  have hη' : (η : ℝ) < 1 := coe_lt_one.mpr hη
  have hη_pos : (0 : ℝ) < η := hδ'.trans hδη'
  have hδ1 : 0 < 1 - (δ : ℝ) := by linarith
  have hη1 : 0 < 1 - (η : ℝ) := by linarith
  set A := Real.log ((1 - δ) / (1 - η)) with hA_def
  set B := Real.log (η / δ) with hB_def
  have hA : 0 < A := Real.log_pos ((one_lt_div hη1).mpr (by linarith))
  have hB : 0 < B := Real.log_pos ((one_lt_div hδ').mpr hδη')
  have hr0 : 0 < r := hr ▸ div_pos hA (add_pos hB hA)
  have hr1 : 0 < 1 - r := by
    rw [hr, sub_pos, div_lt_one (add_pos hB hA)]
    linarith
  -- Gibbs' inequality locates `r` between `δ` and `η`
  have h_gibbs₁ := klBerReal_nonneg hδ'.le (by linarith) hη_pos hη'
  have h_gibbs₂ := klBerReal_nonneg hη_pos.le hη'.le hδ' (by linarith)
  rw [klBerReal_apply, ← inv_div (η : ℝ) δ, Real.log_inv, ← hB_def, ← hA_def] at h_gibbs₁
  rw [klBerReal_apply, ← hB_def, ← inv_div (1 - (δ : ℝ)) (1 - η), Real.log_inv,
    ← hA_def] at h_gibbs₂
  have hδr : (δ : ℝ) ≤ r := by
    rw [hr, le_div_iff₀ (add_pos hB hA)]
    linarith
  have hrη : r ≤ (η : ℝ) := by
    rw [hr, div_le_iff₀ (add_pos hB hA)]
    linarith
  -- at `r`, the divergences to `δ` and to `η` are equal
  have h_eq : klBerReal r δ = klBerReal r η := by
    rw [klBerReal_eq_of_ne hδ'.ne' (by linarith), klBerReal_eq_of_ne hη_pos.ne' (by linarith)]
    have hA' : A = Real.log (1 - δ) - Real.log (1 - η) := Real.log_div hδ1.ne' hη1.ne'
    have hB' : B = Real.log η - Real.log δ := Real.log_div hη_pos.ne' hδ'.ne'
    have hrBA : r * (B + A) = A := by rw [hr]; field_simp
    linear_combination (-r) * hB' + (1 - r) * hA' + hrBA
  have hlogδ : 0 ≤ Real.log (r / δ) := Real.log_nonneg ((one_le_div hδ').mpr hδr)
  have hlogδ' : Real.log ((1 - r) / (1 - δ)) ≤ 0 :=
    Real.log_nonpos (div_nonneg hr1.le hδ1.le) ((div_le_one hδ1).mpr (by linarith))
  have hlogη : Real.log (r / η) ≤ 0 :=
    Real.log_nonpos (div_nonneg hr0.le hη_pos.le) ((div_le_one hη_pos).mpr hrη)
  have hlogη' : 0 ≤ Real.log ((1 - r) / (1 - η)) :=
    Real.log_nonneg ((one_le_div hη1).mpr (by linarith))
  set r' : I := ⟨r, hr0.le, by linarith⟩
  have hδr' : δ ≤ r' := hδr
  have hr'η : r' ≤ η := hrη
  have hr'0 : 0 < r' := coe_pos.mp hr0
  have hr'1 : r' < 1 := coe_lt_one.mp (by simp only [r']; linarith)
  refine le_antisymm (iInf₂_le_of_le Ber(true, false, r') inferInstance ?_)
    (le_iInf₂ fun R _ ↦ ?_)
  · -- `Ber(true, false, r)` attains the bound
    calc max (maxUtility Ber(true, false, r') S logUtility).toENNReal
          (maxUtility Ber(true, false, r') T logUtility).toENNReal
    _ ≤ max (klBerReal r δ : EReal).toENNReal (klBerReal r η : EReal).toENNReal :=
      max_le_max (EReal.toENNReal_le_toENNReal (hS_le r' hδr'))
        (EReal.toENNReal_le_toENNReal (hT_le r' hr'η))
    _ = ENNReal.ofReal (klBerReal r δ) := by
      rw [EReal.real_coe_toENNReal, EReal.real_coe_toENNReal, ← h_eq, max_self]
  -- every probability measure on `Bool` is a Bernoulli distribution
  obtain ⟨s, rfl⟩ : ∃ s : I, Ber(true, false, s) = R := ⟨_, (eq_bernoulliMeasure_real_true R).symm⟩
  rcases le_total r (s : ℝ) with hrs | hsr
  · refine le_max_of_le_left ?_
    rw [← EReal.real_coe_toENNReal]
    refine EReal.toENNReal_le_toENNReal ((EReal.coe_le_coe_iff.mpr ?_).trans
      ((le_maxUtility_bernoulli hδ_pos (hδη.trans hη) hδr' hr'1 s).trans
        (maxUtility_anti hS)))
    rw [klBerReal_apply]
    nlinarith [mul_nonneg (sub_nonneg.mpr hrs) (sub_nonneg.mpr (hlogδ'.trans hlogδ))]
  · refine le_max_of_le_right ?_
    rw [h_eq, ← EReal.real_coe_toENNReal]
    refine EReal.toENNReal_le_toENNReal ((EReal.coe_le_coe_iff.mpr ?_).trans
      ((le_maxUtility_bernoulli_ge (hδ_pos.trans hδη) hη hr'η hr'0 s).trans
        (maxUtility_anti hT)))
    rw [klBerReal_apply]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (sub_nonneg.mpr (hlogη.trans hlogη'))]

/-! ### Identification with the classical divergences -/

/-- For `0 < δ ≤ η < 1`, the e-Rényi divergence of order `α < 1` between the Bernoulli
distributions with parameter at most `δ` and those with parameter at least `η` is the Rényi
divergence of order `α` between `Ber(true, false, δ)` and `Ber(true, false, η)`, whose value is
given by `renyiDiv_bernoulliMeasure`. -/
theorem erenyiDiv_bernoulli {α : ℝ≥0∞} (hα : α < 1) (hδ_pos : 0 < δ) (hδη : δ ≤ η)
    (hη : η < 1) :
    erenyiDiv α {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)}
        {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)}
      = renyiDiv α.toReal Ber(true, false, δ) Ber(true, false, η) := by
  rw [erenyiDiv_bernoulli_eq_ofReal hα hδ_pos hδη hη]
  rcases eq_or_ne α 0 with rfl | hα0
  · rw [ENNReal.toReal_zero, renyiDiv_zero_bernoulliMeasure (by decide) hδ_pos.ne'
      (hδη.trans_lt hη).ne (hδ_pos.trans_le hδη).ne' hη.ne]
    simp
  · rw [renyiDiv_bernoulliMeasure (ENNReal.toReal_pos hα0 hα.ne_top)
      (by simpa using (ENNReal.toReal_lt_toReal hα.ne_top ENNReal.one_ne_top).mpr hα) (by decide)
      _ (hδ_pos.trans_le hδη).ne' hη.ne]

/-- For `0 < δ < η < 1`, the Chernoff information between `Ber(true, false, δ)` and
`Ber(true, false, η)` is `klBerReal r δ = klBerReal r η`, where `r` is the parameter at which the
two Kullback-Leibler divergences are equal. -/
theorem chernoffDiv_one_bernoulliMeasure (hδ_pos : 0 < δ) (hδη : δ < η) (hη : η < 1) {r : ℝ}
    (hr : r = Real.log ((1 - δ) / (1 - η)) / (Real.log (η / δ) + Real.log ((1 - δ) / (1 - η)))) :
    chernoffDiv 1 Ber(true, false, δ) Ber(true, false, η) = ENNReal.ofReal (klBerReal r δ) := by
  rw [← echernoffDiv_singleton, echernoffDiv_bernoulli_eq_ofReal hδ_pos hδη hη hr
    (Set.singleton_subset_iff.mpr ⟨δ, le_rfl, rfl⟩) (Set.singleton_subset_iff.mpr ⟨η, le_rfl, rfl⟩)]
  · exact fun s _ ↦ (maxUtility_bernoulli_singleton hδ_pos (hδη.trans hη) s).le
  · exact fun s _ ↦ (maxUtility_bernoulli_singleton (hδ_pos.trans hδη) hη s).le

/-- For `0 < δ < η < 1`, the e-Chernoff divergence between the Bernoulli distributions with
parameter at most `δ` and those with parameter at least `η` is the Chernoff information between
`Ber(true, false, δ)` and `Ber(true, false, η)`, whose value is given by
`chernoffDiv_one_bernoulliMeasure`. -/
theorem echernoffDiv_bernoulli (hδ_pos : 0 < δ) (hδη : δ < η) (hη : η < 1) :
    echernoffDiv {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)}
        {Ber(true, false, q) | (q : I) (_ : (η : ℝ) ≤ q)}
      = chernoffDiv 1 Ber(true, false, δ) Ber(true, false, η) := by
  rw [chernoffDiv_one_bernoulliMeasure hδ_pos hδη hη rfl,
    echernoffDiv_bernoulli_eq_ofReal hδ_pos hδη hη rfl subset_rfl subset_rfl]
  · exact fun s hs ↦ (maxUtility_bernoulli hδ_pos (hδη.trans hη) hs).le
  · exact fun s hs ↦ (maxUtility_bernoulli_ge (hδ_pos.trans hδη) hη hs).le

/-- The e-Rényi divergence of order `1/2` between the Bernoulli distributions with parameter at
most `δ` and those with parameter at least `1 - δ` is `log (1 / (4 * δ * (1 - δ)))`. -/
theorem erenyiDiv_inv_two_bernoulli_one_sub (hδ_pos : 0 < δ) (hδ : (δ : ℝ) ≤ 2⁻¹) :
    erenyiDiv 2⁻¹ {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)}
        {Ber(true, false, q) | (q : I) (_ : (σ δ : ℝ) ≤ q)}
      = ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  have hδ' : (0 : ℝ) < δ := coe_pos.mpr hδ_pos
  have hδ1 : 0 < 1 - (δ : ℝ) := by linarith
  have hδσ : δ ≤ σ δ := show (δ : ℝ) ≤ σ δ by rw [coe_symm_eq]; linarith
  rw [erenyiDiv_bernoulli_eq_ofReal (by norm_num) hδ_pos hδσ (by rwa [← symm_zero, symm_lt_symm]),
    coe_symm_eq, sub_sub_cancel]
  congr 1
  rw [show (2⁻¹ : ℝ≥0∞).toReal = 2⁻¹ by norm_num, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num,
    mul_comm ((1 - (δ : ℝ)) ^ (2⁻¹ : ℝ)), ← two_mul,
    Real.log_mul two_ne_zero (mul_pos (Real.rpow_pos_of_pos hδ' _)
      (Real.rpow_pos_of_pos hδ1 _)).ne',
    Real.log_mul (Real.rpow_pos_of_pos hδ' _).ne' (Real.rpow_pos_of_pos hδ1 _).ne',
    Real.log_rpow hδ', Real.log_rpow hδ1, one_div, Real.log_inv,
    Real.log_mul (by positivity) hδ1.ne', Real.log_mul (by norm_num) hδ'.ne',
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, show ((2⁻¹ : ℝ) - 1)⁻¹ = -2 by norm_num]
  push_cast
  ring

/-- The e-Chernoff divergence between the Bernoulli distributions with parameter at most `δ` and
those with parameter at least `1 - δ` is `2⁻¹ * log (1 / (4 * δ * (1 - δ)))`. Negation exchanges
the two sets, so this is half their e-Rényi divergence of order `1/2`. -/
theorem echernoffDiv_bernoulli_one_sub (hδ_pos : 0 < δ) (hδ : (δ : ℝ) ≤ 2⁻¹) :
    echernoffDiv {Ber(true, false, q) | (q : I) (_ : (q : ℝ) ≤ δ)}
        {Ber(true, false, q) | (q : I) (_ : (σ δ : ℝ) ≤ q)}
      = 2⁻¹ * ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  rw [← erenyiDiv_inv_two_bernoulli_one_sub hδ_pos hδ,
    erenyiDiv_eq_two_mul_echernoffDiv_of_involutive (φ := not) .of_discrete Bool.not_not
      (image_map_not_bernoulli δ), ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    one_mul]

end ProbabilityTheory
