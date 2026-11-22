/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.Chernoff
public import Statlib.Divergence.Renyi.Order

/-!
# Properties of the Chernoff divergence

We prove that the Chernoff divergence is monotone in its order and that for finite measures `μ`
and `ν`, `C₁(μ, ν) = ⨆ a ∈ [0, 1], (1 - a) * Rₐ(μ, ν)`. By scale invariance
(`chernoffDiv_eq_chernoffDiv_inv_smul`), it suffices to prove the latter for probability
measures.

The inequality `≥` follows from the variational formula for the Rényi divergence,
`(1 - a) * Rₐ(μ, ν) = ⨅ ξ, (a * KL(ξ, μ) + (1 - a) * KL(ξ, ν))`. The other inequality is usually
obtained from a minimax theorem. We prove it instead with the tilted measures
`ξₐ = renyiMeasure a μ ν`, for `a ∈ (0, 1)`. By the variational formula, for all `b ∈ (0, 1)`,
`b * KL(ξₐ, μ) + (1 - b) * KL(ξₐ, ν) ≥ (1 - b) * R_b(μ, ν)`, with equality for `b = a`.
That is, the affine function `b ↦ b * KL(ξₐ, μ) + (1 - b) * KL(ξₐ, ν)` is a supporting line at `a`
of the concave function `b ↦ (1 - b) * R_b(μ, ν)`, and its slope `KL(ξₐ, μ) - KL(ξₐ, ν)` is
antitone in `a`. If that slope changes sign, a convex combination of two tilted measures with
close parameters on both sides of the sign change has both Kullback-Leibler divergences close to
the supremum (by convexity of the Kullback-Leibler divergence). Otherwise, a tilted measure with
parameter close to `0` or `1` does the job.

## Main statements

* `chernoffDiv_le_chernoffDiv_of_le`, `monotoneOn_chernoffDiv`: for finite measures,
  `a ↦ Cₐ(μ, ν)` is monotone on `[0, ∞)`.
* `chernoffDiv_one_eq_iSup_mul_renyiDiv`: for finite measures,
  `C₁(μ, ν) = ⨆ a ∈ [0, 1], (1 - a) * Rₐ(μ, ν)`. The supremum is not attained in general.

## References

* T. van Erven, P. Harremoës, *Rényi divergence and Kullback-Leibler divergence*, IEEE
  Transactions on Information Theory 60(7) (2014).
-/

@[expose] public section

open MeasureTheory Set InformationTheory unitInterval

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a b : ℝ}

/-- For finite measures, `a ↦ Cₐ(μ, ν)` is monotone on `[0, ∞)`. -/
@[gcongr]
lemma chernoffDiv_le_chernoffDiv_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 0 ≤ a) (hab : a ≤ b) :
    chernoffDiv a μ ν ≤ chernoffDiv b μ ν :=
  iInf₂_mono fun _ _ ↦ max_le_max (renyiDiv_le_renyiDiv_of_le ha hab)
    (renyiDiv_le_renyiDiv_of_le ha hab)

/-- For finite measures, `a ↦ Cₐ(μ, ν)` is monotone on `[0, ∞)`. -/
lemma monotoneOn_chernoffDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    MonotoneOn (fun a ↦ chernoffDiv a μ ν) (Ici 0) :=
  fun _ ha _ _ hab ↦ chernoffDiv_le_chernoffDiv_of_le ha hab

/-! ### The Chernoff divergence as a supremum of Rényi divergences -/

/-- For probability measures, `⨆ a ∈ [0, 1], (1 - a) * Rₐ(μ, ν) ≤ C₁(μ, ν)`, by the variational
formula for the Rényi divergence. -/
private lemma iSup_mul_renyiDiv_le_chernoffDiv_one_of_isProbabilityMeasure [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ⨆ a ∈ Icc (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν ≤ chernoffDiv 1 μ ν := by
  rw [← iSup_Ioo_mul_renyiDiv_eq_iSup_Icc, chernoffDiv_one]
  refine iSup₂_le fun a ha ↦ le_iInf₂ fun ξ _ ↦
    (mul_renyiDiv_le_mul_klDiv_add_mul_klDiv μ ν ξ ha.1 ha.2).trans ?_
  calc ENNReal.ofReal a * klDiv ξ μ + ENNReal.ofReal (1 - a) * klDiv ξ ν
      ≤ ENNReal.ofReal a * max (klDiv ξ μ) (klDiv ξ ν)
        + ENNReal.ofReal (1 - a) * max (klDiv ξ μ) (klDiv ξ ν) := by gcongr <;> simp
    _ = max (klDiv ξ μ) (klDiv ξ ν) := by
      rw [← add_mul, ← ENNReal.ofReal_add ha.1.le (by linarith [ha.2])]
      simp

/-- Real-valued core of `chernoffDiv_one_le_iSup_mul_renyiDiv_of_isProbabilityMeasure`. Suppose
that for all `a, b ∈ (0, 1)`, `g b ≤ b * A a + (1 - b) * B a`, with equality for `b = a` (the line
`b ↦ b * A a + (1 - b) * B a` supports `g` at `a`), and that `g ≤ S` on `(0, 1)`. Then for all
`ε > 0`, there exist `a₁, a₂ ∈ (0, 1)` and `t ∈ [0, 1]` such that both convex combinations
`t * A a₁ + (1 - t) * A a₂` and `t * B a₁ + (1 - t) * B a₂` are at most `S + ε`. -/
private lemma exists_convex_combination_le {A B g : ℝ → ℝ} {S ε : ℝ} (hε : 0 < ε)
    (hg_le : ∀ a ∈ Ioo (0 : ℝ) 1, g a ≤ S)
    (h_supp : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, g b ≤ b * A a + (1 - b) * B a)
    (h_eq : ∀ a ∈ Ioo (0 : ℝ) 1, g a = a * A a + (1 - a) * B a) :
    ∃ a₁ ∈ Ioo (0 : ℝ) 1, ∃ a₂ ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      t * A a₁ + (1 - t) * A a₂ ≤ S + ε ∧ t * B a₁ + (1 - t) * B a₂ ≤ S + ε := by
  -- the slopes `A a - B a` of the supporting lines are antitone
  have hφ : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, a ≤ b → A b - B b ≤ A a - B a := by
    intro a ha b hb hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    have h1 := h_supp a ha b hb
    have h2 := h_supp b hb a ha
    rw [h_eq b hb] at h1
    rw [h_eq a ha] at h2
    have key : 0 ≤ (b - a) * ((A a - B a) - (A b - B b)) := by nlinarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sub_pos.mpr hab)).mp key)
  -- a single parameter `a` is a convex combination with `t = 1`
  have h_single : ∀ a ∈ Ioo (0 : ℝ) 1, A a ≤ S + ε → B a ≤ S + ε →
      ∃ a₁ ∈ Ioo (0 : ℝ) 1, ∃ a₂ ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        t * A a₁ + (1 - t) * A a₂ ≤ S + ε ∧ t * B a₁ + (1 - t) * B a₂ ≤ S + ε :=
    fun a ha hA hB ↦ ⟨a, ha, a, ha, 1, ⟨zero_le_one, le_rfl⟩, by simpa using hA, by simpa using hB⟩
  have h_half : (2⁻¹ : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hεd : ∀ d : ℝ, 0 ≤ d → ε / (d + 1) * d ≤ ε := by
    intro d hd
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  by_cases h1 : ∀ a ∈ Ioo (0 : ℝ) 1, 0 ≤ A a - B a
  · -- all slopes are nonnegative: parameter close to `1`
    set d := A 2⁻¹ - B 2⁻¹ with hd_def
    have hd : 0 ≤ d := h1 2⁻¹ h_half
    set a₀ := max 2⁻¹ (1 - ε / (d + 1)) with ha₀_def
    have ha₀_ge : 2⁻¹ ≤ a₀ := le_max_left _ _
    have ha₀ : a₀ ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith, max_lt (by norm_num) (by linarith [div_pos hε (by linarith : 0 < d + 1)])⟩
    have h1a : 1 - a₀ ≤ ε / (d + 1) := by linarith [le_max_right 2⁻¹ (1 - ε / (d + 1))]
    have hA_eq : A a₀ = g a₀ + (1 - a₀) * (A a₀ - B a₀) := by rw [h_eq a₀ ha₀]; ring
    have hprod : (1 - a₀) * (A a₀ - B a₀) ≤ ε / (d + 1) * d :=
      mul_le_mul h1a (hφ 2⁻¹ h_half a₀ ha₀ ha₀_ge) (h1 a₀ ha₀) (by positivity)
    have hA_le : A a₀ ≤ S + ε := by linarith [hg_le a₀ ha₀, hεd d hd]
    exact h_single a₀ ha₀ hA_le (by linarith [h1 a₀ ha₀])
  simp only [not_forall, not_le] at h1
  obtain ⟨a₂, ha₂, hφ₂⟩ := h1
  by_cases h3 : ∃ a₁ ∈ Ioo (0 : ℝ) 1, 0 ≤ A a₁ - B a₁
  swap
  · -- all slopes are negative: parameter close to `0`
    simp only [not_exists, not_and, not_le] at h3
    set d := B 2⁻¹ - A 2⁻¹ with hd_def
    have hd : 0 ≤ d := by linarith [h3 2⁻¹ h_half]
    set a₀ := min 2⁻¹ (ε / (d + 1)) with ha₀_def
    have ha₀_pos : 0 < a₀ := lt_min (by norm_num) (div_pos hε (by linarith))
    have ha₀_le : a₀ ≤ 2⁻¹ := min_le_left _ _
    have ha₀ : a₀ ∈ Ioo (0 : ℝ) 1 := ⟨ha₀_pos, by linarith⟩
    have hB_eq : B a₀ = g a₀ + a₀ * (B a₀ - A a₀) := by rw [h_eq a₀ ha₀]; ring
    have hprod : a₀ * (B a₀ - A a₀) ≤ ε / (d + 1) * d :=
      mul_le_mul (min_le_right _ _) (by linarith [hφ a₀ ha₀ 2⁻¹ h_half ha₀_le])
        (by linarith [h3 a₀ ha₀]) (by positivity)
    have hB_le : B a₀ ≤ S + ε := by linarith [hg_le a₀ ha₀, hεd d hd]
    exact h_single a₀ ha₀ (by linarith [h3 a₀ ha₀]) hB_le
  -- the slopes change sign at `c`: convex combination of two parameters close to `c`
  obtain ⟨a₁, ha₁, hφ₁⟩ := h3
  set T := {a ∈ Ioo (0 : ℝ) 1 | 0 ≤ A a - B a} with hT
  have hT_ne : T.Nonempty := ⟨a₁, ha₁, hφ₁⟩
  have hT_bdd : BddAbove T := ⟨1, fun a ha ↦ ha.1.2.le⟩
  set c := sSup T with hc_def
  have hT_lt : ∀ a ∈ T, a < a₂ := by
    intro a ha
    by_contra h
    have := hφ a₂ ha₂ a ha.1 (not_lt.mp h)
    linarith [ha.2]
  have hc_ge : a₁ ≤ c := le_csSup hT_bdd ⟨ha₁, hφ₁⟩
  set D := B a₂ - A a₂ with hD_def
  have hD : 0 < D := by linarith
  set η := ε / D with hη_def
  have hη : 0 < η := div_pos hε hD
  obtain ⟨a₁', ha₁'T, ha₁'gt⟩ := exists_lt_of_lt_csSup hT_ne (show c - η / 2 < c by linarith)
  have ha₁' : a₁' ∈ Ioo (0 : ℝ) 1 := ha₁'T.1
  set a₂' := min (c + η / 2) a₂ with ha₂'_def
  have ha₂'_le : a₂' ≤ a₂ := min_le_right _ _
  have ha₂'_le' : a₂' ≤ c + η / 2 := min_le_left _ _
  have ha₂' : a₂' ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by linarith [ha₁.1]) ha₂.1, ha₂'_le.trans_lt ha₂.2⟩
  have hφ₂' : A a₂' - B a₂' < 0 := by
    by_contra h
    have h_mem : a₂' ∈ T := ⟨ha₂', not_lt.mp h⟩
    have h_lt := hT_lt a₂' h_mem
    have h_eq' : a₂' = c + η / 2 := by
      rcases min_choice (c + η / 2) a₂ with h' | h'
      · exact h'
      · exact absurd h' h_lt.ne
    linarith [le_csSup hT_bdd h_mem]
  have hφ₁' : 0 ≤ A a₁' - B a₁' := ha₁'T.2
  have hgap : a₂' - a₁' ≤ η := by linarith
  have hφ₂'_le : B a₂' - A a₂' ≤ D := by linarith [hφ a₂' ha₂' a₂ ha₂ ha₂'_le]
  have ha₁₂ : a₁' ≤ a₂' := by
    by_contra h
    linarith [hφ a₂' ha₂' a₁' ha₁' (not_le.mp h).le]
  -- weight of the convex combination, chosen so that the two combinations are equal
  set t := (B a₂' - A a₂') / ((A a₁' - B a₁') - (A a₂' - B a₂')) with ht_def
  have h_den : 0 < (A a₁' - B a₁') - (A a₂' - B a₂') := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) h_den.le
  have ht1 : t ≤ 1 := (div_le_one h_den).mpr (by linarith)
  have ht_eq : t * (A a₁' - B a₁') + (1 - t) * (A a₂' - B a₂') = 0 := by
    rw [ht_def]
    field_simp
    ring
  have hT_le : t * A a₁' + (1 - t) * A a₂' ≤ S + ε := by
    have e1 := h_eq a₁' ha₁'
    have e2 := h_eq a₂' ha₂'
    have hTA : t * A a₁' + (1 - t) * A a₂'
        = t * g a₁' + (1 - t) * g a₂' + (1 - t) * ((a₂' - a₁') * (B a₂' - A a₂')) := by
      rw [e1, e2]
      linear_combination (1 - a₁') * ht_eq
    have hg_comb : t * g a₁' + (1 - t) * g a₂' ≤ S := by
      have := hg_le a₁' ha₁'
      have := hg_le a₂' ha₂'
      nlinarith
    have hprod : (a₂' - a₁') * (B a₂' - A a₂') ≤ η * D :=
      mul_le_mul hgap hφ₂'_le (by linarith) hη.le
    have hηD : η * D = ε := div_mul_cancel₀ _ hD.ne'
    have hprod' : (1 - t) * ((a₂' - a₁') * (B a₂' - A a₂')) ≤ (a₂' - a₁') * (B a₂' - A a₂') :=
      mul_le_of_le_one_left (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith
  have hTB : t * B a₁' + (1 - t) * B a₂' = t * A a₁' + (1 - t) * A a₂' := by
    linear_combination -ht_eq
  exact ⟨a₁', ha₁', a₂', ha₂', t, ⟨ht0, ht1⟩, hT_le, hTB ▸ hT_le⟩

/-- For probability measures, `C₁(μ, ν) ≤ ⨆ a ∈ [0, 1], (1 - a) * Rₐ(μ, ν)`, with convex
combinations of tilted measures. -/
private lemma chernoffDiv_one_le_iSup_mul_renyiDiv_of_isProbabilityMeasure [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    chernoffDiv 1 μ ν ≤ ⨆ a ∈ Icc (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν := by
  rw [← iSup_Ioo_mul_renyiDiv_eq_iSup_Icc]
  set s := ⨆ a ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν with hs
  have h_le_s : ∀ a ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν ≤ s :=
    fun a ha ↦ le_iSup₂ (f := fun a (_ : a ∈ Ioo (0 : ℝ) 1) ↦
      ENNReal.ofReal (1 - a) * renyiDiv a μ ν) a ha
  by_cases hs_top : s = ∞
  · simp [hs_top]
  have h_ms : ¬ μ ⟂ₘ ν := by
    refine fun h_ms ↦ hs_top (top_le_iff.mp ((h_le_s 2⁻¹ ⟨by norm_num, by norm_num⟩).trans' ?_))
    rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)).mpr h_ms,
      ENNReal.mul_top (by norm_num)]
  -- real-valued notation: `g a = (1 - a) * Rₐ(μ, ν)`, and the Kullback-Leibler divergences
  -- `A a = KL(ξₐ, μ)` and `B a = KL(ξₐ, ν)` of the tilted measures
  set g : ℝ → ℝ := fun a ↦ (1 - a) * (renyiDiv a μ ν).toReal with hg_def
  set A : ℝ → ℝ := fun a ↦ (klDiv (renyiMeasure a μ ν) μ).toReal with hA_def
  set B : ℝ → ℝ := fun a ↦ (klDiv (renyiMeasure a μ ν) ν).toReal with hB_def
  have hg : ∀ a ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 - a) * renyiDiv a μ ν = ENNReal.ofReal (g a) := by
    intro a ha
    rw [hg_def, ENNReal.ofReal_mul (by linarith [ha.2]), ENNReal.ofReal_toReal
      (mt (renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha.1.le ha.2).mp h_ms)]
  have hAB_nonneg : ∀ a, ∀ b ∈ Icc (0 : ℝ) 1, 0 ≤ b * A a + (1 - b) * B a := fun a b hb ↦
    add_nonneg (mul_nonneg hb.1 ENNReal.toReal_nonneg)
      (mul_nonneg (sub_nonneg.mpr hb.2) ENNReal.toReal_nonneg)
  have hAB : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal b * klDiv (renyiMeasure a μ ν) μ
        + ENNReal.ofReal (1 - b) * klDiv (renyiMeasure a μ ν) ν
      = ENNReal.ofReal (b * A a + (1 - b) * B a) := by
    intro a ha b hb
    rw [ENNReal.ofReal_add (mul_nonneg hb.1 ENNReal.toReal_nonneg)
      (mul_nonneg (sub_nonneg.mpr hb.2) ENNReal.toReal_nonneg), ENNReal.ofReal_mul hb.1,
      ENNReal.ofReal_mul (sub_nonneg.mpr hb.2),
      ENNReal.ofReal_toReal (klDiv_renyiMeasure_left_ne_top ha.1 ha.2 h_ms),
      ENNReal.ofReal_toReal (klDiv_renyiMeasure_right_ne_top ha.1 ha.2 h_ms)]
  have hg_le : ∀ a ∈ Ioo (0 : ℝ) 1, g a ≤ s.toReal := fun a ha ↦
    (ENNReal.ofReal_le_iff_le_toReal hs_top).mp (hg a ha ▸ h_le_s a ha)
  have h_supp : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, g b ≤ b * A a + (1 - b) * B a := by
    intro a ha b hb
    have := isProbabilityMeasure_renyiMeasure ha.1 ha.2 h_ms
    have h := mul_renyiDiv_le_mul_klDiv_add_mul_klDiv μ ν (renyiMeasure a μ ν) hb.1 hb.2
    rw [hg b hb, hAB a ha b ⟨hb.1.le, hb.2.le⟩] at h
    exact (ENNReal.ofReal_le_ofReal_iff (hAB_nonneg a b ⟨hb.1.le, hb.2.le⟩)).mp h
  have h_eq : ∀ a ∈ Ioo (0 : ℝ) 1, g a = a * A a + (1 - a) * B a := by
    intro a ha
    have h := mul_renyiDiv_eq_mul_klDiv_renyiMeasure ha.1 ha.2 h_ms
    rw [hg a ha, hAB a ha a ⟨ha.1.le, ha.2.le⟩] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (by linarith [ha.2]) ENNReal.toReal_nonneg)
      (hAB_nonneg a a ⟨ha.1.le, ha.2.le⟩)).mp h
  -- it suffices to find, for all `ε > 0`, a probability measure with both divergences
  -- at most `s + ε`: a convex combination of two tilted measures
  rw [chernoffDiv_one]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨a₁, ha₁, a₂, ha₂, t, ht, hA, hB⟩ :=
    exists_convex_combination_le (NNReal.coe_pos.mpr hε) hg_le h_supp h_eq
  have := isProbabilityMeasure_renyiMeasure ha₁.1 ha₁.2 h_ms
  have := isProbabilityMeasure_renyiMeasure ha₂.1 ha₂.2 h_ms
  obtain ⟨p, rfl⟩ : ∃ p : I, (p : ℝ) = t := ⟨⟨t, ht⟩, rfl⟩
  have h_mix : ∀ (ρ : Measure α) [IsFiniteMeasure ρ],
      klDiv (toNNReal p • renyiMeasure a₁ μ ν + toNNReal (σ p) • renyiMeasure a₂ μ ν) ρ
        ≤ ENNReal.ofReal p * klDiv (renyiMeasure a₁ μ ν) ρ
          + ENNReal.ofReal (1 - p) * klDiv (renyiMeasure a₂ μ ν) ρ := by
    intro ρ _
    have h := klDiv_smul_add_smul_le (renyiMeasure a₁ μ ν) (renyiMeasure a₂ μ ν) ρ ρ
      (toNNReal p) (toNNReal (σ p))
    rwa [← add_smul, toNNReal_add_toNNReal_symm, one_smul, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_coe_nnreal (p := toNNReal (σ p)), coe_toNNReal, coe_toNNReal,
      coe_symm_eq] at h
  have h_bound : ∀ x y : ℝ≥0∞, x ≠ ∞ → y ≠ ∞ → p * x.toReal + (1 - p) * y.toReal ≤ s.toReal + ε →
      ENNReal.ofReal p * x + ENNReal.ofReal (1 - p) * y ≤ s + ε := by
    intro x y hx hy h
    rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy, ← ENNReal.ofReal_mul p.property.1,
      ← ENNReal.ofReal_mul (sub_nonneg.mpr p.property.2), ← ENNReal.ofReal_add
        (mul_nonneg p.property.1 ENNReal.toReal_nonneg)
        (mul_nonneg (sub_nonneg.mpr p.property.2) ENNReal.toReal_nonneg),
      ← ENNReal.ofReal_toReal hs_top, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal h
  have hζ : IsProbabilityMeasure
      (toNNReal p • renyiMeasure a₁ μ ν + toNNReal (σ p) • renyiMeasure a₂ μ ν) := inferInstance
  refine (iInf₂_le _ hζ).trans (max_le ((h_mix μ).trans ?_) ((h_mix ν).trans ?_))
  · exact h_bound _ _ (klDiv_renyiMeasure_left_ne_top ha₁.1 ha₁.2 h_ms)
      (klDiv_renyiMeasure_left_ne_top ha₂.1 ha₂.2 h_ms) hA
  · exact h_bound _ _ (klDiv_renyiMeasure_right_ne_top ha₁.1 ha₁.2 h_ms)
      (klDiv_renyiMeasure_right_ne_top ha₂.1 ha₂.2 h_ms) hB

/-- For finite measures, `C₁(μ, ν) = ⨆ a ∈ [0, 1], (1 - a) * Rₐ(μ, ν)`. The supremum is not
attained in general. -/
theorem chernoffDiv_one_eq_iSup_mul_renyiDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    chernoffDiv 1 μ ν = ⨆ a ∈ Icc (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν := by
  -- if `μ = 0` or `ν = 0`, both sides are infinite
  have h_top : μ ⟂ₘ ν → ⨆ a ∈ Icc (0 : ℝ) 1, ENNReal.ofReal (1 - a) * renyiDiv a μ ν = ∞ := by
    refine fun h_ms ↦ top_le_iff.mp (le_iSup₂_of_le (f := fun a (_ : a ∈ Icc (0 : ℝ) 1) ↦
      ENNReal.ofReal (1 - a) * renyiDiv a μ ν) 2⁻¹ ⟨by norm_num, by norm_num⟩ ?_)
    rw [(renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (by norm_num) (by norm_num)).mpr h_ms,
      ENNReal.mul_top (by norm_num)]
  rcases eq_zero_or_neZero μ with rfl | _
  · rw [chernoffDiv_zero_measure_left zero_le_one, h_top Measure.MutuallySingular.zero_left]
  rcases eq_zero_or_neZero ν with rfl | _
  · rw [chernoffDiv_zero_measure_right zero_le_one, h_top Measure.MutuallySingular.zero_right]
  -- otherwise, both sides are invariant under normalization of the measures
  rw [chernoffDiv_eq_chernoffDiv_inv_smul zero_le_one,
    le_antisymm chernoffDiv_one_le_iSup_mul_renyiDiv_of_isProbabilityMeasure
      iSup_mul_renyiDiv_le_chernoffDiv_one_of_isProbabilityMeasure]
  exact iSup_congr fun a ↦ iSup_congr fun ha ↦ by rw [← renyiDiv_eq_renyiDiv_inv_smul ha.1]

/-- For finite measures and `0 ≤ a`, `(1 - a) * Rₐ(μ, ν) ≤ C₁(μ, ν)`, where `1 - a` is truncated
at `0`. -/
lemma mul_renyiDiv_le_chernoffDiv_one [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha : 0 ≤ a) :
    ENNReal.ofReal (1 - a) * renyiDiv a μ ν ≤ chernoffDiv 1 μ ν := by
  rcases le_or_gt a 1 with ha1 | ha1
  · exact (le_iSup₂ (f := fun a (_ : a ∈ Icc (0 : ℝ) 1) ↦ ENNReal.ofReal (1 - a) * renyiDiv a μ ν)
      a ⟨ha, ha1⟩).trans chernoffDiv_one_eq_iSup_mul_renyiDiv.ge
  · simp [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr ha1.le)]

end ProbabilityTheory
