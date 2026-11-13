/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import Statlib.EValues.Numeraire
public import Statlib.ForMathlib.MeasureTheory.Komlos

/-!
# Existence of the numeraire

We prove that a class of e-variables `𝓔` (an `IsEVarClass`) has a numeraire under a finite measure
`P`, for every bounded utility function and for the logarithmic utility.

The proof uses only that the class consists of measurable functions, contains `1`, is convex and
is closed under `liminf` of sequences (`IsEVarClass`). The e-variables for a set of finite measures
are an example (`isEVarClass_isEVar`).

The steps are:

* `IsEVarClass.exists_max_eintegral_utility`: a maximizer of a bounded, concave and upper
  semicontinuous utility exists in the class, by a maximizing sequence, a Komlós-type lemma and
  Fatou.
* `IsEVarClass.exists_max_eintegral_utility_ae_lt_top`: the maximizer can moreover be taken infinite
  wherever any element of the class is, by boosting it with an infinitesimal amount of the maximal
  element of `IsEVarClass.exists_forall_ae_eq_top`.
* `IsEVarClass.exists_isNumeraireFor`: for a bounded utility, that maximizer satisfies the first
  order optimality condition, hence is a numeraire.
* `IsEVarClass.exists_isLogNumeraireFor`: a numeraire for the logarithmic utility, obtained from
  the numeraires of the bounded approximations `boundedLogUtility` of the logarithm by letting the
  bound tend to infinity, using again a Komlós-type lemma and Fatou.

The Komlós-type lemma is `MeasureTheory.komlos_ennreal`.

## Main definitions

* `logNumeraire P 𝓔`: a numeraire for the logarithmic utility in the class `𝓔`.
* `numeraire P S`: the numeraire of the e-variables for the set of measures `S`.

## Main statements

* `IsEVarClass.exists_isNumeraireFor`: existence of the numeraire for a bounded utility.
* `IsEVarClass.exists_isLogNumeraireFor`: existence of the numeraire for the logarithmic utility.
* `exists_isNumeraire`: existence of the numeraire of the e-variables for a set of finite measures.
* `isLogNumeraireFor_logNumeraire`, `isNumeraire_numeraire`: `logNumeraire P 𝓔` and
  `numeraire P S` are numeraires.

## References

* M. Larsson, A. Ramdas, J. Ruf, *The numeraire e-variable and reverse information projection*
  (2025). The existence proof follows its Lemmas 2.9 and 2.10.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : Measure 𝓧} {S : Set (Measure 𝓧)}
  {𝓔 : Set (𝓧 → ℝ≥0∞)} {X : 𝓧 → ℝ≥0∞}

/-! ### Maximizers of a bounded utility -/

section

variable {U : ℝ≥0∞ → EReal}

lemma convex_eintegral_utility_ge [IsFiniteMeasure P] (u : EReal)
    (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    (hU_meas : Measurable U) {B : EReal} (hU_le : ∀ x : ℝ≥0∞, U x ≤ B) (hB : B ≠ ⊤) :
    Convex ℝ≥0∞ {Z | Measurable Z ∧ u ≤ ∫ᵉ ω, U (Z ω) ∂P} := by
  intro Y ⟨hY_meas, hY⟩ Z ⟨hZ_meas, hZ⟩ a b ha hb hab
  refine ⟨by fun_prop, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hY hZ ⊢
  have ha_ne_top : a ≠ ∞ := fun ha_top ↦ by simp [ha_top] at hab
  have hb_ne_top : b ≠ ∞ := fun hb_top ↦ by simp [hb_top] at hab
  have h_int (Y : 𝓧 → ℝ≥0∞) : EIntegrable (fun ω ↦ U (Y ω)) P :=
    eintegrable_of_le (ae_of_all _ fun _ ↦ hU_le _) hB
  have h_ne_top (c : ℝ≥0∞) (hc : c ≠ ∞) (Y : 𝓧 → ℝ≥0∞) :
      ∫ᵉ ω, (c : EReal) * U (Y ω) ∂P ≠ ⊤ := by
    refine (eintegral_lt_top_of_le (b := c * B) (ae_of_all _ fun ω ↦ ?_) ?_).ne
    · gcongr
      exact hU_le _
    · simp [EReal.mul_eq_top, hc, hB, not_lt.mpr (EReal.coe_ennreal_nonneg c)]
  calc u
  _ = a * u + b * u := by
    conv_lhs => rw [← one_mul u]
    have : (1 : EReal) = (1 : ℝ≥0∞) := rfl
    rw [this, ← hab]
    simp only [EReal.coe_ennreal_add]
    exact EReal.distrib_ennreal _ _ _
  _ ≤ a * ∫ᵉ ω, U (Y ω) ∂P + b * ∫ᵉ ω, U (Z ω) ∂P := by gcongr
  _ = ∫ᵉ ω, a • U (Y ω) + b • U (Z ω) ∂P := by
    simp only [EReal.smul_ennreal_eq_mul]
    rw [eintegral_add (by fun_prop) (by fun_prop) ((h_int _).const_mul (by simp) (by simpa))
        (.inr (h_ne_top b hb_ne_top Z)) (.inl (h_ne_top a ha_ne_top Y)),
      eintegral_const_mul (by simp) (by simpa) (h_int _),
      eintegral_const_mul (by simp) (by simpa) (h_int _)]
  _ ≤ ∫ᵉ ω, U (a * Y ω + b * Z ω) ∂P := by
    refine eintegral_mono fun ω ↦ ?_
    lift a to ℝ≥0 using ha_ne_top
    lift b to ℝ≥0 using hb_ne_top
    norm_cast at ha hb hab
    exact hU_ccv.2 (by simp : Y ω ∈ Set.univ) (by simp) ha hb hab

/-- **Existence of a utility maximizer in an abstract class of e-variables.** For a bounded,
upper semicontinuous and concave utility `U`, some element of `𝓔` maximizes `∫ᵉ U ∘ X ∂P` over
`𝓔`. -/
theorem IsEVarClass.exists_max_eintegral_utility (h𝓔 : IsEVarClass 𝓔)
    (hU_ccv : ConcaveOn ℝ≥0 Set.univ U) {B : ℝ} (hU_usc : UpperSemicontinuous U)
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ B) (P : Measure 𝓧) [IsFiniteMeasure P] :
    ∃ Y ∈ 𝓔, ∀ X ∈ 𝓔, ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P := by
  -- the set of achievable utilities, and a sequence attaining its supremum
  let V := {y | ∃ X ∈ 𝓔, y = ∫ᵉ x, U (X x) ∂P}
  have hV : V.Nonempty := ⟨∫ᵉ x, U ((1 : 𝓧 → ℝ≥0∞) x) ∂P, ⟨1, h𝓔.one_mem, rfl⟩⟩
  have hV_bdd : BddAbove V := ⟨⊤, by simp [mem_upperBounds]⟩
  obtain ⟨u, hu_mono, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sSup hV hV_bdd
  simp only [Set.mem_ofPred_eq, V] at hu_mem
  choose X hX_mem hu_eq using hu_mem
  -- convex combinations of the tails of the maximizing sequence, converging almost everywhere
  obtain ⟨Y, Ylim, hY_mem, hY_lim_meas, hY_tendsto⟩ :=
    komlos_ennreal (fun n ↦ h𝓔.measurable (hX_mem n)) P
  have hY_class n : Y n ∈ 𝓔 := by
    specialize hY_mem n
    rw [mem_convexHull_iff] at hY_mem
    refine hY_mem 𝓔 ?_ h𝓔.convex
    rintro _ ⟨m, rfl⟩
    exact hX_mem (n + m)
  let Yliminf := fun x ↦ liminf (fun n ↦ Y n x) atTop
  refine ⟨Yliminf, h𝓔.liminf_mem Y hY_class, ?_⟩
  suffices ⨆ n, ∫ᵉ x, U (X n x) ∂P ≤ ∫ᵉ x, U (Ylim x) ∂P by
    intro Z hZ_mem
    refine le_trans ?_ (this.trans_eq ?_)
    · simp_rw [← hu_eq]
      rw [iSup_eq_of_tendsto hu_mono hu_tendsto]
      exact le_sSup ⟨Z, hZ_mem, rfl⟩
    · refine eintegral_congr_ae ?_
      filter_upwards [hY_tendsto] with x hx
      congr
      unfold Yliminf
      rwa [Tendsto.liminf_eq]
  calc ⨆ n, ∫ᵉ x, U (X n x) ∂P
  _ = limsup (fun n ↦ ∫ᵉ x, U (X n x) ∂P) atTop := by
    simp_rw [← hu_eq]
    rw [Tendsto.limsup_eq hu_tendsto, iSup_eq_of_tendsto hu_mono hu_tendsto]
  _ ≤ limsup (fun n ↦ ∫ᵉ x, U (Y n x) ∂P) atTop := by
    refine limsup_le_limsup (.of_forall fun n ↦ ?_)
    specialize hY_mem n
    simp only [mem_convexHull_iff] at hY_mem
    refine (hY_mem {Z | Measurable Z ∧ ∫ᵉ ω, U (X n ω) ∂P ≤ ∫ᵉ ω, U (Z ω) ∂P} ?_ ?_).2
    · rintro _ ⟨m, rfl⟩
      simp only [Set.mem_ofPred_eq]
      simp_rw [← hu_eq]
      exact ⟨h𝓔.measurable (hX_mem _), hu_mono (by grind)⟩
    · exact convex_eintegral_utility_ge _ hU_ccv hU_usc.measurable hU_le (by simp)
  _ ≤ ∫ᵉ x, limsup (fun n ↦ U (Y n x)) atTop ∂P := by
    refine limsup_eintegral_le (g := fun _ ↦ .ofReal B) ?_ ?_ ?_ ?_
    · intro n
      have := h𝓔.measurable (hY_class n)
      have := hU_usc.measurable
      fun_prop
    · intro n
      refine ae_of_all _ fun x ↦ ?_
      simp only [Function.comp_apply]
      have : ENNReal.ofReal B = B.toEReal.toENNReal := by simp
      rw [this]
      exact EReal.toENNReal_le_toENNReal <| hU_le (Y n x)
    · simp only [lintegral_const]
      exact ENNReal.mul_ne_top (by simp) (by simp)
    · left
      rw [EReal.ne_top_exists_finite_iff]
      by_cases hB : B < 0
      · refine ⟨0, by simp, ?_⟩
        rw [Filter.limsup_le_iff']
        intro y hy
        refine .of_forall fun n ↦ LT.lt.le <| lt_of_le_of_lt (Eq.le ?_) hy
        suffices ∀ x, (U (Y n x)).toENNReal = 0 by simp [this]
        intro x
        replace hB : B.toEReal < 0 := by simp [hB]
        replace hU_le := (lt_of_le_of_lt (hU_le (Y n x)) hB).le
        simp [hU_le]
      · refine ⟨B * P .univ, (EReal.mul_ne_top _ _).mpr (by simp), ?_⟩
        rw [Filter.limsup_le_iff']
        intro y hy
        refine .of_forall fun n ↦ LT.lt.le <| lt_of_le_of_lt ?_ hy
        have hBc : B.toEReal = (ENNReal.ofReal B).toEReal := by
          push Not at hB
          simp only [EReal.coe_ennreal_ofReal, hB, sup_of_le_left]
        rw [hBc]
        norm_cast
        suffices ∀ x, (U (Y n x)).toENNReal ≤ ENNReal.ofReal B by
          calc
          _ ≤ ∫⁻ x, ENNReal.ofReal B ∂P := lintegral_mono this
          _ = ENNReal.ofReal B * P .univ := by simp [lintegral_const]
        intro x
        have : ENNReal.ofReal B = B.toEReal.toENNReal := by simp
        rw [this]
        exact EReal.toENNReal_le_toENNReal (hU_le (Y n x))
  _ ≤ ∫ᵉ x, U (Ylim x) ∂P := by
    refine eintegral_mono_ae ?_
    filter_upwards [hY_tendsto] with x hx
    calc limsup (fun n ↦ U (Y n x)) atTop
    _ = limsup U (map (Y · x) atTop) := limsup_comp U (Y · x) atTop
    _ ≤ limsup U (𝓝 (Ylim x)) := limsup_le_limsup_of_le hx
    _ ≤ U (Ylim x) := upperSemicontinuousAt_iff_limsup_le.mp (hU_usc (Ylim x))

/-- **Existence of a utility maximizer of the class which is infinite wherever any element of the
class is.** The maximizer of `IsEVarClass.exists_max_eintegral_utility` is boosted by an
infinitesimal amount of the maximal element of `IsEVarClass.exists_forall_ae_eq_top`: the utility
does not see the boost in the limit, but the infinities do.

Compared to `IsEVarClass.exists_max_eintegral_utility` this needs `U` to be monotone. -/
theorem IsEVarClass.exists_max_eintegral_utility_ae_lt_top (h𝓔 : IsEVarClass 𝓔)
    (hU_ccv : ConcaveOn ℝ≥0 Set.univ U) {b : ℝ} (hU_usc : UpperSemicontinuous U)
    (hU_mono : Monotone U)
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) (P : Measure 𝓧) [IsFiniteMeasure P] :
    ∃ Y ∈ 𝓔, ∀ X ∈ 𝓔,
      (∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P) ∧ (∀ᵐ x ∂P, Y x < ∞ → X x < ∞) := by
  obtain ⟨Y, hY_mem, h_opt⟩ := h𝓔.exists_max_eintegral_utility hU_ccv hU_usc hU_le P
  obtain ⟨Z, hZ_mem, hZ_top⟩ := h𝓔.exists_forall_ae_eq_top P
  -- the weights of the boost
  set a : ℕ → ℝ≥0∞ := fun k ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ with ha_def
  have ha_le_one (k : ℕ) : a k ≤ 1 := by
    rw [ha_def, ENNReal.inv_le_one]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
  have ha_ne_zero (k : ℕ) : a k ≠ 0 := by simp [ha_def]
  have ha_tendsto : Tendsto a atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hb_tendsto : Tendsto (fun k ↦ 1 - a k) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞)) (f := atTop (α := ℕ)))
      ha_tendsto (.inl (by simp))
    simpa using this
  -- the boosted sequence and its `liminf`
  set W : ℕ → 𝓧 → ℝ≥0∞ := fun k ↦ (1 - a k) • Y + a k • Z with hW_def
  have hW_mem (k : ℕ) : W k ∈ 𝓔 :=
    h𝓔.convex hY_mem hZ_mem (by simp) (by simp) (tsub_add_cancel_of_le (ha_le_one k))
  set Y' : 𝓧 → ℝ≥0∞ := fun x ↦ liminf (fun k ↦ W k x) atTop with hY'_def
  have hW_apply (k : ℕ) (x : 𝓧) : W k x = (1 - a k) * Y x + a k * Z x := rfl
  -- the boost only increases the function
  have hY_le (x : 𝓧) : Y x ≤ Y' x := by
    have h1 : Tendsto (fun k ↦ (1 - a k) * Y x) atTop (𝓝 (Y x)) := by
      simpa using ENNReal.Tendsto.mul_const hb_tendsto (.inl one_ne_zero)
    rw [hY'_def, ← h1.liminf_eq]
    exact liminf_le_liminf (.of_forall fun k ↦ by rw [hW_apply]; exact le_self_add)
  -- and it is infinite where `Z` is
  have hZ_le (x : 𝓧) (hx : Z x = ∞) : Y' x = ∞ := by
    have h_ev : ∀ᶠ k in atTop, W k x = ∞ := by
      filter_upwards with k
      rw [hW_apply, hx, ENNReal.mul_top (ha_ne_zero k), add_top]
    simp only [hY'_def]
    rw [liminf_congr h_ev]
    simp
  refine ⟨Y', h𝓔.liminf_mem W hW_mem, fun X hX_mem ↦ ⟨?_, ?_⟩⟩
  · exact (h_opt X hX_mem).trans (eintegral_mono fun x ↦ hU_mono (hY_le x))
  · filter_upwards [hZ_top X hX_mem] with x hx h_lt_top
    by_contra! h_eq_top
    simp only [top_le_iff] at h_eq_top
    exact h_lt_top.ne (hZ_le x (hx h_eq_top))

end

/-! ### The numeraire of a bounded utility -/

private lemma exists_max_eintegral_utility_of_le (h𝓔 : IsEVarClass 𝓔) {U : Utility} {b : ℝ}
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) (P : Measure 𝓧) [IsFiniteMeasure P] :
    ∃ Y ∈ 𝓔, ∀ X ∈ 𝓔,
      (∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P) ∧ (∀ᵐ x ∂P, Y x < ∞ → X x < ∞) :=
  h𝓔.exists_max_eintegral_utility_ae_lt_top U.concave U.continuous.upperSemicontinuous U.monotone
    hU_le P

/-- A maximizer of a bounded utility function, which is infinite wherever any element of the
class is (see `isNumeraireFor_numeraireOfBounded`). -/
private noncomputable def numeraireOfBounded {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔) :
    𝓧 → ℝ≥0∞ :=
  (exists_max_eintegral_utility_of_le h𝓔 hU_le P).choose

private lemma mem_numeraireOfBounded {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔) :
    numeraireOfBounded hU_le P h𝓔 ∈ 𝓔 :=
  (Classical.choose_spec
    (exists_max_eintegral_utility_of_le h𝓔 hU_le P)).1

private lemma eintegral_le_numeraireOfBounded {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : X ∈ 𝓔) :
    ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (numeraireOfBounded hU_le P h𝓔 x) ∂P :=
  ((Classical.choose_spec (exists_max_eintegral_utility_of_le h𝓔 hU_le P)).2 X hX_evar).1

private lemma eintegral_numeraireOfBounded_ge {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔) :
    U 1 * P .univ ≤ ∫ᵉ x, U (numeraireOfBounded hU_le P h𝓔 x) ∂P := calc
  U 1 * P .univ
  _ = ∫ᵉ x, U 1 ∂P := by simp
  _ ≤ ∫ᵉ x, U (numeraireOfBounded hU_le P h𝓔 x) ∂P :=
    eintegral_le_numeraireOfBounded hU_le P h𝓔 (h𝓔.one_mem)

private lemma eintegral_numeraireOfBounded_ne_bot {U : Utility} {b : ℝ}
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔) :
    ∫ᵉ x, U (numeraireOfBounded hU_le P h𝓔 x) ∂P ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot ?_ (eintegral_numeraireOfBounded_ge hU_le P h𝓔)
  rw [EReal.mul_ne_bot]
  have h : U 1 ≠ ⊥ ∧ U 1 ≠ ⊤ := U.eq_coe (by simp) (by simp)
  simp [h.1, h.2]

private lemma lt_top_of_numeraireOfBounded_lt_top {U : Utility} {b : ℝ}
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : X ∈ 𝓔) :
    ∀ᵐ x ∂P, (numeraireOfBounded hU_le P h𝓔 x) < ∞ → X x < ∞ :=
  ((Classical.choose_spec (exists_max_eintegral_utility_of_le h𝓔 hU_le P)).2 X hX_evar).2

section FirstOrderCondition

/-- **First order optimality condition**, for e-variables bounded below by a positive constant.
This is the main step in the proof of `eintegral_deriv_mul_le`. -/
private lemma eintegral_deriv_mul_le_of_ge (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔)
    {Y : 𝓧 → ℝ≥0∞} (hY : Y ∈ 𝓔) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcY : ∀ x, c ≤ Y x) :
    ∫ᵉ x, U.deriv (numeraireOfBounded hU_le P h𝓔 x)
        * ((Y x : EReal) - numeraireOfBounded hU_le P h𝓔 x) ∂P ≤ 0
      ∧ ∫ᵉ x, U.deriv (numeraireOfBounded hU_le P h𝓔 x)
        * ((Y x : EReal) - numeraireOfBounded hU_le P h𝓔 x) ∂P ≠ ⊥ := by
  set X := numeraireOfBounded hU_le P h𝓔 with hX_def
  have hX_evar : X ∈ 𝓔 := mem_numeraireOfBounded hU_le P h𝓔
  have hX_meas : Measurable X := h𝓔.measurable hX_evar
  have hY_meas : Measurable Y := h𝓔.measurable hY
  have hY0 (x : 𝓧) : Y x ≠ 0 := fun h ↦ hc0 (le_antisymm (h ▸ hcY x) (by positivity))
  have hb_top : (b : EReal) ≠ ⊤ := by simp
  -- `k` is a finite lower bound for all the difference quotients below
  set k : EReal := U c - (b : EReal) with hk_def
  have hk_bot : k ≠ ⊥ := by
    rw [hk_def, ne_eq, EReal.sub_eq_bot]
    simp [U.ne_bot hc0]
  have hk_int {f : 𝓧 → EReal} (h : ∀ᵐ x ∂P, k ≤ f x) : ∫⁻ x, (-f x).toENNReal ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (-k).toENNReal ∂P) ?_ (lintegral_mono_ae ?_)
    swap
    · filter_upwards [h] with x hx
      exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hx)
    simp only [lintegral_const]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
    simp [hk_bot]
  -- the sequence of interpolation parameters
  set t : ℕ → ℝ := fun n ↦ 1 / (n + 2) with ht_def
  have ht0 (n : ℕ) : 0 < t n := by
    rw [ht_def]
    positivity
  have ht1 (n : ℕ) : t n < 1 := by
    rw [ht_def, div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have ht_tendsto : Tendsto t atTop (𝓝 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ 1
    exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  -- the interpolating e-variables and the difference quotients
  set Z : ℕ → 𝓧 → ℝ≥0∞ :=
    fun n x ↦ ENNReal.ofReal (t n) * Y x + ENNReal.ofReal (1 - t n) * X x with hZ_def
  have hZ_evar (n : ℕ) : Z n ∈ 𝓔 :=
    h𝓔.convex hY hX_evar (by positivity) (by positivity)
      (by rw [← ENNReal.ofReal_add (ht0 n).le (by linarith [ht1 n])]; simp)
  have hZ_meas (n : ℕ) : Measurable (Z n) := h𝓔.measurable (hZ_evar n)
  set F : ℕ → 𝓧 → EReal := fun n x ↦ ((t n : ℝ) : EReal)⁻¹ * (U (Z n x) - U (X x)) with hF_def
  have hF_meas (n : ℕ) : Measurable (F n) := by
    have := hZ_meas n
    fun_prop
  -- the difference quotients are bounded below by the constant `k`
  have hF_lb (n : ℕ) (x : 𝓧) : k ≤ F n x := by
    refine le_trans ?_ (U.sub_le_inv_mul_sub (α := X x) (β := Y x) (hY0 x) (ht0 n) (ht1 n).le)
    exact EReal.sub_le_sub (U.monotone (hcY x)) (hU_le (X x))
  -- each difference quotient has nonpositive integral
  have hdiff_lb (n : ℕ) (x : 𝓧) :
      U (ENNReal.ofReal (t n) * c) - (b : EReal) ≤ U (Z n x) - U (X x) := by
    refine EReal.sub_le_sub (U.monotone ?_) (hU_le (X x))
    rw [hZ_def]
    exact le_add_right (by gcongr; exact hcY x)
  have hdiff_int (n : ℕ) : EIntegrable (fun x ↦ U (Z n x) - U (X x)) P := by
    refine .inr ?_
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x ↦
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hdiff_lb n x)))
    simp only [lintegral_const]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
    rw [ne_eq, EReal.toENNReal_eq_top_iff, EReal.neg_eq_top_iff, EReal.sub_eq_bot]
    simp only [not_or]
    refine ⟨U.ne_bot ?_, hb_top⟩
    simp only [ne_eq, mul_eq_zero, not_or, ENNReal.ofReal_eq_zero, not_le]
    exact ⟨ht0 n, hc0⟩
  have hF_nonpos (n : ℕ) : ∫ᵉ x, F n x ∂P ≤ 0 := by
    have h_sub : ∫ᵉ x, (U (Z n x) - U (X x)) ∂P ≤ 0 := by
      rw [eintegral_sub (f := fun x ↦ U (Z n x)) (g := fun x ↦ U (X x))
          (U.measurable.comp (hZ_meas n)).aemeasurable (U.measurable.comp hX_meas).aemeasurable
          (eintegrable_of_le (b := (b : EReal)) (ae_of_all _ fun x ↦ hU_le _) hb_top)
          (.inl (eintegral_lt_top_of_le (ae_of_all _ fun x ↦ hU_le (Z n x)) hb_top).ne)
          (.inr (eintegral_numeraireOfBounded_ne_bot hU_le P h𝓔)),
        EReal.sub_nonpos]
      exact eintegral_le_numeraireOfBounded hU_le P h𝓔 (hZ_evar n)
    have ht_ne : ((t n : ℝ) : EReal)⁻¹ ≠ ⊥ ∧ ((t n : ℝ) : EReal)⁻¹ ≠ ⊤ := by
      simp [← EReal.coe_inv]
    rw [hF_def]
    simp only
    rw [eintegral_const_mul ht_ne.1 ht_ne.2 (hdiff_int n), ← mul_zero ((t n : ℝ) : EReal)⁻¹]
    gcongr
  -- the pointwise liminf bound
  set g : 𝓧 → EReal := fun x ↦ U.deriv (X x) * ((Y x : EReal) - X x) with hg_def
  have h_ptwise : ∀ᵐ x ∂P, g x ≤ liminf (fun n ↦ F n x) atTop := by
    filter_upwards [lt_top_of_numeraireOfBounded_lt_top hU_le P h𝓔 hY] with x hx
    exact U.deriv_mul_sub_le_liminf hU_le (hY0 x)
      (fun hX_top ↦ (hx (lt_top_iff_ne_top.mpr hX_top)).ne) ht0 ht1 ht_tendsto
  -- `g` is also bounded below by `k`
  have hg_lb : ∀ᵐ x ∂P, k ≤ g x := by
    filter_upwards [lt_top_of_numeraireOfBounded_lt_top hU_le P h𝓔 hY] with x hx
    by_cases hX0 : X x = 0
    · have hk_nonpos : k ≤ 0 := by
        rw [hk_def, EReal.sub_nonpos]
        exact hU_le c
      refine hk_nonpos.trans ?_
      simp only [hg_def]
      refine mul_nonneg (U.deriv_nonneg _) ?_
      rw [hX0]
      simpa using EReal.coe_ennreal_nonneg (Y x)
    · refine le_trans ?_ (U.sub_le_deriv_mul_sub hU_le hX0
        (fun hX_top ↦ (hx (lt_top_iff_ne_top.mpr hX_top)).ne))
      exact EReal.sub_le_sub (U.monotone (hcY x)) (hU_le (X x))
  refine ⟨?_, ?_⟩
  swap
  · rw [eintegral_ne_bot_iff_lintegral_ne_top]
    exact hk_int hg_lb
  rw [eintegral_nonpos_iff_lintegral_le]
  calc ∫⁻ x, (g x).toENNReal ∂P
  _ ≤ ∫⁻ x, liminf (fun n ↦ (F n x).toENNReal) atTop ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [h_ptwise] with x hx
    rw [← EReal.liminf_coe_ennreal]
    exact EReal.toENNReal_le_toENNReal hx
  _ ≤ liminf (fun n ↦ ∫⁻ x, (F n x).toENNReal ∂P) atTop :=
    lintegral_liminf_le fun n ↦ EReal.continuous_toENNReal.measurable.comp (hF_meas n)
  _ ≤ liminf (fun n ↦ ∫⁻ x, (-(F n x)).toENNReal ∂P) atTop :=
    liminf_le_liminf (.of_forall fun n ↦ eintegral_nonpos_iff_lintegral_le.mp (hF_nonpos n))
  _ ≤ limsup (fun n ↦ ∫⁻ x, (-(F n x)).toENNReal ∂P) atTop := liminf_le_limsup
  _ ≤ ∫⁻ x, limsup (fun n ↦ (-(F n x)).toENNReal) atTop ∂P := by
    refine limsup_lintegral_le (fun _ ↦ (-k).toENNReal)
      (fun n ↦ (EReal.continuous_toENNReal.measurable.comp (hF_meas n).neg))
      (fun n ↦ .of_forall fun x ↦
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hF_lb n x))) ?_
    simp only [lintegral_const]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
    simp [hk_bot]
  _ ≤ ∫⁻ x, (-g x).toENNReal ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [h_ptwise] with x hx
    rw [← EReal.limsup_coe_ennreal]
    refine EReal.toENNReal_le_toENNReal ?_
    have h_neg : limsup (fun n ↦ -(F n x)) atTop = -liminf (fun n ↦ F n x) atTop :=
      (EReal.neg_strictAnti.antitone.map_liminf_of_continuousAt _
        (continuous_neg (G := EReal)).continuousAt).symm
    rw [h_neg]
    exact EReal.neg_le_neg_iff.mpr hx

/-- **First order optimality condition** for a bounded utility: the maximizer
`numeraireOfBounded` satisfies `∫ U'(X) (Y - X) ≤ 0`, and that integral is not `⊥`. -/
private lemma eintegral_deriv_mul_numeraireOfBounded (U : Utility) {b : ℝ}
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔)
    {Y : 𝓧 → ℝ≥0∞} (hY : Y ∈ 𝓔) :
    ∫ᵉ x, U.deriv (numeraireOfBounded hU_le P h𝓔 x)
        * (Y x - numeraireOfBounded hU_le P h𝓔 x) ∂P ≤ 0
      ∧ ∫ᵉ x, U.deriv (numeraireOfBounded hU_le P h𝓔 x)
        * (Y x - numeraireOfBounded hU_le P h𝓔 x) ∂P ≠ ⊥ := by
  -- Lemma 2.9 of _Larsson et al._ (2025). We know the result for e-variables that are bounded
  -- below by a positive constant (`eintegral_deriv_mul_le_of_ge`); we apply it to the
  -- e-variables `Yδ n = δ n + (1 - δ n) * Y` and let `δ n` tend to `0`.
  set X := numeraireOfBounded hU_le P h𝓔 with hX_def
  set g : 𝓧 → EReal := fun x ↦ U.deriv (X x) * ((Y x : EReal) - X x) with hg_def
  have hg_meas : AEMeasurable g P := by
    have := h𝓔.measurable (mem_numeraireOfBounded hU_le P h𝓔)
    have := h𝓔.measurable hY
    fun_prop
  -- the first order condition for the constant e-variable `1`
  have h1_evar : (1 : 𝓧 → ℝ≥0∞) ∈ 𝓔 := h𝓔.one_mem
  obtain ⟨hg1_nonpos, hg1_bot⟩ :=
    eintegral_deriv_mul_le_of_ge U hU_le P h𝓔 h1_evar (c := 1) one_ne_zero fun _ ↦ le_rfl
  simp only [Pi.one_apply, EReal.coe_ennreal_one] at hg1_nonpos hg1_bot
  set g1 : 𝓧 → EReal := fun x ↦ U.deriv (X x) * ((1 : EReal) - X x) with hg1_def
  have hg1_int : EIntegrable g1 P := eintegrable_of_eintegral_ne_bot hg1_bot
  have hg1_meas : AEMeasurable g1 P := by
    have := h𝓔.measurable (mem_numeraireOfBounded hU_le P h𝓔)
    fun_prop
  have hg1_top : ∫ᵉ x, g1 x ∂P ≠ ⊤ := ne_top_of_le_ne_top (by simp) hg1_nonpos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, ∫ᵉ x, g1 x ∂P = (m : EReal) :=
    ⟨_, (EReal.coe_toReal hg1_top hg1_bot).symm⟩
  -- the sequence of e-variables `Yδ n`
  set δ : ℕ → ℝ := fun n ↦ 1 / (n + 2) with hδ_def
  have hδ0 (n : ℕ) : 0 < δ n := by
    rw [hδ_def]
    positivity
  have hδ1 (n : ℕ) : δ n < 1 := by
    rw [hδ_def, div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hδ_tendsto : Tendsto δ atTop (𝓝 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ 1
    exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  set Yδ : ℕ → 𝓧 → ℝ≥0∞ :=
    fun n ↦ ENNReal.ofReal (δ n) • (1 : 𝓧 → ℝ≥0∞) + ENNReal.ofReal (1 - δ n) • Y with hYδ_def
  have hYδ_evar (n : ℕ) : Yδ n ∈ 𝓔 :=
    h𝓔.convex h1_evar hY (by positivity) (by positivity)
      (by rw [← ENNReal.ofReal_add (hδ0 n).le (by linarith [hδ1 n])]; simp)
  have hYδ_ge (n : ℕ) (x : 𝓧) : ENNReal.ofReal (δ n) ≤ Yδ n x := by
    simp only [hYδ_def, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact le_add_right le_rfl
  -- the first order term for `Yδ n` is a convex combination of those for `Y` and `1`
  have hδg1_eq (n : ℕ) : ∫ᵉ x, ((δ n : ℝ) : EReal) * g1 x ∂P = ((δ n * m : ℝ) : EReal) := by
    rw [eintegral_const_mul (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hg1_int, hm,
      ← EReal.coe_mul]
  have h_comb (n : ℕ) : ∫ᵉ x, U.deriv (X x) * ((Yδ n x : EReal) - X x) ∂P
      = ((1 - δ n : ℝ) : EReal) * ∫ᵉ x, g x ∂P + ((δ n * m : ℝ) : EReal) := by
    have h_eq : ∀ᵐ x ∂P, U.deriv (X x) * ((Yδ n x : EReal) - X x)
        = ((1 - δ n : ℝ) : EReal) * g x + ((δ n : ℝ) : EReal) * g1 x := by
      filter_upwards [lt_top_of_numeraireOfBounded_lt_top hU_le P h𝓔 hY] with x hx
      exact U.deriv_mul_sub_convex hU_le
        (fun hXt ↦ (hx (lt_top_iff_ne_top.mpr hXt)).ne) (hδ0 n) (hδ1 n)
    rw [eintegral_congr_ae h_eq, eintegral_add' (hg_meas.const_mul _) (hg1_meas.const_mul _)
        (by rw [hδg1_eq]; exact EReal.coe_ne_top _) (by rw [hδg1_eq]; exact EReal.coe_ne_bot _),
      eintegral_real_const_mul_of_nonneg (by linarith [hδ1 n]), hδg1_eq]
  have key (n : ℕ) :
      ((1 - δ n : ℝ) : EReal) * ∫ᵉ x, g x ∂P + ((δ n * m : ℝ) : EReal) ≤ 0
        ∧ ((1 - δ n : ℝ) : EReal) * ∫ᵉ x, g x ∂P + ((δ n * m : ℝ) : EReal) ≠ ⊥ := by
    rw [← h_comb n]
    exact eintegral_deriv_mul_le_of_ge U hU_le P h𝓔 (hYδ_evar n)
      (c := ENNReal.ofReal (δ n)) (by simp [hδ0 n]) (hYδ_ge n)
  -- the integral of `g` is finite
  have hg_bot : ∫ᵉ x, g x ∂P ≠ ⊥ := by
    intro hG
    have h0 := (key 0).2
    rw [hG, EReal.coe_mul_bot_of_pos (by linarith [hδ1 0]), EReal.bot_add] at h0
    exact h0 rfl
  have hg_top : ∫ᵉ x, g x ∂P ≠ ⊤ := by
    intro hG
    have h0 := (key 0).1
    rw [hG, EReal.coe_mul_top_of_pos (x := 1 - δ 0) (by linarith [hδ1 0]),
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at h0
    simp at h0
  refine ⟨?_, hg_bot⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, ∫ᵉ x, g x ∂P = (G : EReal) :=
    ⟨_, (EReal.coe_toReal hg_top hg_bot).symm⟩
  rw [hG]
  have key' (n : ℕ) : (1 - δ n) * G + δ n * m ≤ 0 := by
    have h := (key n).1
    rw [hG] at h
    exact_mod_cast h
  have h_tendsto : Tendsto (fun n ↦ (1 - δ n) * G + δ n * m) atTop (𝓝 ((1 - 0) * G + 0 * m)) :=
    ((tendsto_const_nhds.sub hδ_tendsto).mul_const G).add (hδ_tendsto.mul_const m)
  have hG_nonpos : G ≤ 0 := by simpa using le_of_tendsto h_tendsto (.of_forall key')
  exact_mod_cast hG_nonpos

/-- **The maximizer of a bounded utility is a numeraire** for that utility. -/
private theorem isNumeraireFor_numeraireOfBounded (U : Utility) {b : ℝ}
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔) :
    IsNumeraireFor U (numeraireOfBounded hU_le P h𝓔) 𝓔 P where
  mem := mem_numeraireOfBounded hU_le P h𝓔
  eintegral_deriv_mul_ne_bot _ hY := (eintegral_deriv_mul_numeraireOfBounded U hU_le P h𝓔 hY).2
  eintegral_deriv_mul_le _ hY := (eintegral_deriv_mul_numeraireOfBounded U hU_le P h𝓔 hY).1

/-- **Existence of the numeraire for a bounded utility** in a class of e-variables, under a finite
measure. -/
theorem IsEVarClass.exists_isNumeraireFor (h𝓔 : IsEVarClass 𝓔) {U : Utility} {b : ℝ}
    (hU_le : ∀ x : ℝ≥0∞, U x ≤ b) (P : Measure 𝓧) [IsFiniteMeasure P] :
    ∃ X, IsNumeraireFor U X 𝓔 P :=
  ⟨_, isNumeraireFor_numeraireOfBounded U hU_le P h𝓔⟩

end FirstOrderCondition

/-! ### Existence of the numeraire for the logarithmic utility -/

/-- The first order optimality condition for `boundedLogUtility`, in `ℝ≥0∞` form. -/
private lemma lintegral_harmonicDeriv_mul_le {N : ℝ} (hN : 0 < N)
    (P : Measure 𝓧) [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔)
    {Y : 𝓧 → ℝ≥0∞} (hY : Y ∈ 𝓔) :
    ∫⁻ x, harmonicDeriv N (numeraireOfBounded (boundedLogUtility_le hN) P h𝓔 x) * Y x ∂P
      ≤ P {x | numeraireOfBounded (boundedLogUtility_le hN) P h𝓔 x ≠ ∞} := by
  set X := numeraireOfBounded (boundedLogUtility_le hN) P h𝓔 with hX_def
  have hX_meas : Measurable X :=
    h𝓔.measurable (mem_numeraireOfBounded (boundedLogUtility_le hN) P h𝓔)
  have hA_meas : MeasurableSet {x | X x ≠ ∞} := (hX_meas (measurableSet_singleton ∞)).compl
  -- the integral of `harmonicDeriv N (X x) * X x` is at most `P {X ≠ ∞}`
  have h_bound : ∫⁻ x, harmonicDeriv N (X x) * X x ∂P ≤ P {x | X x ≠ ∞} := by
    rw [← lintegral_indicator_one hA_meas]
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : X x = ∞
    · simp [hx]
    · rw [Set.indicator_of_mem hx]
      exact harmonicDeriv_mul_le_one N (X x)
  refine le_trans ?_ h_bound
  simpa [deriv_boundedLogUtility hN] using
    (isNumeraireFor_numeraireOfBounded (boundedLogUtility hN) (boundedLogUtility_le hN) P
      h𝓔).lintegral_deriv_mul_le hY hX_meas.aemeasurable (h𝓔.measurable hY).aemeasurable

/-- **Existence of the numeraire for the logarithmic utility** in a class of e-variables, under a
finite measure. It is obtained from the numeraires of the bounded approximations
`boundedLogUtility` of the logarithm, by a Komlós-type lemma and Fatou. -/
theorem IsEVarClass.exists_isLogNumeraireFor (h𝓔 : IsEVarClass 𝓔) (P : Measure 𝓧)
    [IsFiniteMeasure P] :
    ∃ Y, IsLogNumeraireFor Y 𝓔 P := by
  -- Lemma 2.10 of _Larsson et al._ (2025).
  -- the bounded approximations of the logarithm and their optimal e-variables
  have hN (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set Xo : ℕ → 𝓧 → ℝ≥0∞ :=
    fun n ↦ numeraireOfBounded (boundedLogUtility_le (hN n)) P h𝓔 with hXo_def
  have hXo_evar (n : ℕ) : Xo n ∈ 𝓔 := mem_numeraireOfBounded _ P h𝓔
  have hXo_meas (n : ℕ) : Measurable (Xo n) := h𝓔.measurable (hXo_evar n)
  -- all the sets `{Xo n ≠ ∞}` agree up to null sets
  set A : Set 𝓧 := {x | Xo 0 x ≠ ∞} with hA_def
  have hA (n : ℕ) : P {x | Xo n x ≠ ∞} = P A := by
    refine measure_congr (Filter.EventuallyEqSet.symm ?_)
    filter_upwards [lt_top_of_numeraireOfBounded_lt_top (boundedLogUtility_le (hN n)) P h𝓔
        (hXo_evar 0), lt_top_of_numeraireOfBounded_lt_top (boundedLogUtility_le (hN 0)) P h𝓔
        (hXo_evar n)] with x h1 h2
    exact ⟨fun h ↦ (h2 (lt_top_iff_ne_top.mpr h)).ne, fun h ↦ (h1 (lt_top_iff_ne_top.mpr h)).ne⟩
  have hPA : P A ≠ ∞ := measure_ne_top _ _
  -- the first order condition, in `ℝ≥0∞` form
  have hfoc (n : ℕ) {Y : 𝓧 → ℝ≥0∞} (hY : Y ∈ 𝓔) :
      ∫⁻ x, harmonicDeriv ((n : ℝ) + 1) (Xo n x) * Y x ∂P ≤ P A := by
    rw [← hA n]
    exact lintegral_harmonicDeriv_mul_le (hN n) P h𝓔 hY
  -- the Komlós lemma applied to the sequence `Xo`
  obtain ⟨W, W_lim, hW_mem, hW_lim_meas, hW_tendsto⟩ := komlos_ennreal hXo_meas P
  have hW_evar (n : ℕ) : W n ∈ 𝓔 := by
    have h := hW_mem n
    rw [mem_convexHull_iff] at h
    refine h 𝓔 ?_ (h𝓔.convex)
    rintro _ ⟨m, rfl⟩
    exact hXo_evar (n + m)
  set Xstar : 𝓧 → ℝ≥0∞ := fun x ↦ liminf (fun n ↦ W n x) atTop with hXstar_def
  have hXstar_evar : Xstar ∈ 𝓔 := h𝓔.liminf_mem _ hW_evar
  have hXstar_meas : Measurable Xstar := h𝓔.measurable hXstar_evar
  have hXstar_eq : ∀ᵐ x ∂P, Xstar x = W_lim x := by
    filter_upwards [hW_tendsto] with x hx
    exact hx.liminf_eq
  -- the sequence of error terms
  have h_err : Tendsto (fun n : ℕ ↦ (ENNReal.ofReal ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun n ↦ by positivity) (fun n ↦ ?_)
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the key estimate, for an integrable function `Y` dominated by an element `Z` of the class
  have key : ∀ Y Z : 𝓧 → ℝ≥0∞, Measurable Y → Z ∈ 𝓔 → Y ≤ Z → ∫⁻ x, Y x ∂P ≠ ∞ →
      ∫⁻ x, Y x * (Xstar x)⁻¹ ∂P ≤ P A := by
    intro Y Z hY_meas hZ hYZ hY_int
    have h5 (i : ℕ) : ∫⁻ x, Y x * (Xo i x)⁻¹ ∂P
        ≤ P A + (ENNReal.ofReal ((i : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
      calc ∫⁻ x, Y x * (Xo i x)⁻¹ ∂P
      _ ≤ ∫⁻ x, (harmonicDeriv ((i : ℝ) + 1) (Xo i x) * Y x
            + (ENNReal.ofReal ((i : ℝ) + 1))⁻¹ * Y x) ∂P := by
        refine lintegral_mono fun x ↦ ?_
        rw [← add_mul, mul_comm (Y x)]
        gcongr
        exact inv_le_harmonicDeriv_add _ _
      _ = ∫⁻ x, harmonicDeriv ((i : ℝ) + 1) (Xo i x) * Y x ∂P
            + (ENNReal.ofReal ((i : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
        rw [lintegral_add_left (by have := measurable_harmonicDeriv ((i : ℝ) + 1); fun_prop),
          lintegral_const_mul _ hY_meas]
      _ ≤ _ := by
        gcongr
        refine (lintegral_mono fun x ↦ ?_).trans (hfoc i hZ)
        gcongr
        exact hYZ x
    have h7 (n : ℕ) : ∫⁻ x, Y x * (W n x)⁻¹ ∂P
        ≤ P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
      have h := hW_mem n
      rw [mem_convexHull_iff] at h
      refine (h {Z | Measurable Z ∧ ∫⁻ x, Y x * (Z x)⁻¹ ∂P
          ≤ P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P} ?_ ?_).2
      · rintro _ ⟨m, rfl⟩
        refine ⟨hXo_meas _, (h5 (n + m)).trans ?_⟩
        have hcoef : (ENNReal.ofReal (((n + m : ℕ) : ℝ) + 1))⁻¹
            ≤ (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ := by
          rw [ENNReal.inv_le_inv]
          exact ENNReal.ofReal_le_ofReal (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) m])
        exact add_le_add le_rfl (by gcongr)
      · rintro Z1 ⟨h1m, h1⟩ Z2 ⟨h2m, h2⟩ a b ha hb hab
        refine ⟨by fun_prop, ?_⟩
        calc ∫⁻ x, Y x * ((a • Z1 + b • Z2) x)⁻¹ ∂P
        _ ≤ ∫⁻ x, (a * (Y x * (Z1 x)⁻¹) + b * (Y x * (Z2 x)⁻¹)) ∂P := by
          refine lintegral_mono fun x ↦ ?_
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          calc Y x * (a * Z1 x + b * Z2 x)⁻¹
          _ ≤ Y x * (a * (Z1 x)⁻¹ + b * (Z2 x)⁻¹) := by
            gcongr
            exact convexOn_inv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
          _ = a * (Y x * (Z1 x)⁻¹) + b * (Y x * (Z2 x)⁻¹) := by ring
        _ = a * ∫⁻ x, Y x * (Z1 x)⁻¹ ∂P + b * ∫⁻ x, Y x * (Z2 x)⁻¹ ∂P := by
          rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lintegral_const_mul _ (by fun_prop)]
        _ ≤ a * (P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P)
              + b * (P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P) := by gcongr
        _ = P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
          rw [← add_mul, hab, one_mul]
    -- Fatou
    calc ∫⁻ x, Y x * (Xstar x)⁻¹ ∂P
    _ ≤ ∫⁻ x, liminf (fun n ↦ Y x * (W n x)⁻¹) atTop ∂P := by
      refine lintegral_mono_ae ?_
      filter_upwards [hW_tendsto, hXstar_eq] with x hx hx_eq
      rw [hx_eq]
      exact ENNReal.const_mul_le_liminf ((continuous_inv.tendsto _).comp hx)
    _ ≤ liminf (fun n ↦ ∫⁻ x, Y x * (W n x)⁻¹ ∂P) atTop := by
      refine lintegral_liminf_le fun n ↦ ?_
      have := h𝓔.measurable (hW_evar n)
      fun_prop
    _ ≤ liminf (fun n : ℕ ↦ P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P) atTop :=
      liminf_le_liminf (.of_forall h7)
    _ = P A := by
      refine Tendsto.liminf_eq ?_
      have h0 : Tendsto (fun n : ℕ ↦ (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P)
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const h_err (Or.inr hY_int)
      simpa using (tendsto_const_nhds (x := P A) (f := atTop (α := ℕ))).add h0
  -- `Xstar` is almost everywhere nonzero
  have hXstar_ne_zero : ∀ᵐ x ∂P, Xstar x ≠ 0 := by
    have h := key 1 1 measurable_one h𝓔.one_mem le_rfl (by simp)
    simp only [Pi.one_apply, one_mul] at h
    have h_lt := ae_lt_top' (by fun_prop) (ne_top_of_le_ne_top hPA h)
    filter_upwards [h_lt] with x hx
    intro h0
    rw [h0] at hx
    simp at hx
  -- `Xstar` is almost everywhere finite on `A`
  have hXstar_ne_top : ∀ᵐ x ∂P, x ∈ A → Xstar x ≠ ∞ := by
    have h : ∫⁻ x, harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * Xstar x ∂P ≤ P A := by
      calc ∫⁻ x, harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * Xstar x ∂P
      _ ≤ ∫⁻ x, liminf (fun n ↦ harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * W n x) atTop ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hW_tendsto, hXstar_eq] with x hx hx_eq
        rw [hx_eq]
        exact ENNReal.const_mul_le_liminf hx
      _ ≤ liminf (fun n ↦ ∫⁻ x, harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * W n x ∂P) atTop := by
        refine lintegral_liminf_le fun n ↦ ?_
        have := h𝓔.measurable (hW_evar n)
        have := measurable_harmonicDeriv ((0 : ℝ) + 1)
        fun_prop
      _ ≤ P A := by
        refine liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_)
        simpa using hfoc 0 (hW_evar n)
    have h_lt := ae_lt_top' (by
      have := measurable_harmonicDeriv ((0 : ℝ) + 1); fun_prop) (ne_top_of_le_ne_top hPA h)
    filter_upwards [h_lt] with x hx hxA
    intro h_top
    rw [h_top, ENNReal.mul_top (harmonicDeriv_ne_zero (by norm_num) hxA)] at hx
    simp at hx
  -- conclusion
  refine ⟨Xstar, isLogNumeraireFor_of_lintegral_div_le hXstar_evar
    (fun _ hX ↦ (h𝓔.measurable hX).aemeasurable) (measure_ne_top _ _) fun X hX ↦ ?_⟩
  have hA_le : P A ≤ P Xstar.fsupport := by
    refine measure_mono_ae ?_
    filter_upwards [hXstar_ne_zero, hXstar_ne_top] with x h0 h_top hxA
    exact ⟨h_top hxA, h0⟩
  refine le_trans ?_ hA_le
  -- reduce to the truncations of `X`, which are integrable
  have h_trunc (k : ℕ) : ∫⁻ x, (min (X x) k) / Xstar x ∂P ≤ P A := by
    have hk_int : ∫⁻ x, min (X x) (k : ℝ≥0∞) ∂P ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x ↦ min_le_right _ _)
      simp only [lintegral_const]
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have := key _ X ((h𝓔.measurable hX).min measurable_const) hX (fun x ↦ min_le_left _ _)
      hk_int
    simpa only [ENNReal.div_eq_inv_mul, mul_comm] using this
  have h_mono : Monotone fun k : ℕ ↦ fun x ↦ (min (X x) (k : ℝ≥0∞)) / Xstar x := by
    intro j k hjk x
    simp only
    refine ENNReal.div_le_div_right (min_le_min le_rfl ?_) _
    exact_mod_cast hjk
  have h_sup_min (a : ℝ≥0∞) : ⨆ k : ℕ, min a (k : ℝ≥0∞) = a := by
    refine le_antisymm (iSup_le fun k ↦ min_le_left _ _) ?_
    rcases eq_or_ne a ∞ with rfl | ha
    · calc (∞ : ℝ≥0∞) = ⨆ k : ℕ, (k : ℝ≥0∞) := ENNReal.iSup_natCast.symm
        _ ≤ ⨆ k : ℕ, min (∞ : ℝ≥0∞) (k : ℝ≥0∞) := by
          refine iSup_mono fun k ↦ ?_
          rw [min_eq_right le_top]
    · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt ha
      exact le_iSup_of_le k (by simp [min_eq_left hk.le])
  have h_sup : ∀ x, ⨆ k : ℕ, (min (X x) (k : ℝ≥0∞)) / Xstar x = X x / Xstar x := by
    intro x
    rw [← ENNReal.iSup_div, h_sup_min]
  calc ∫⁻ x, X x / Xstar x ∂P
  _ = ∫⁻ x, ⨆ k : ℕ, (min (X x) (k : ℝ≥0∞)) / Xstar x ∂P := by simp_rw [h_sup]
  _ = ⨆ k : ℕ, ∫⁻ x, (min (X x) (k : ℝ≥0∞)) / Xstar x ∂P := by
    refine lintegral_iSup (fun k ↦ ?_) h_mono
    have := h𝓔.measurable hX
    fun_prop
  _ ≤ P A := iSup_le h_trunc

/-! ### The numeraire for the logarithmic utility -/

open Classical in
/-- A numeraire for the logarithmic utility in the class `𝓔`, under `P`
(see `isLogNumeraireFor_logNumeraire`). It is defined as `1` if `𝓔` is not an `IsEVarClass` or
`P` is not a finite measure. -/
noncomputable
def logNumeraire (P : Measure 𝓧) (𝓔 : Set (𝓧 → ℝ≥0∞)) : 𝓧 → ℝ≥0∞ :=
  if h : IsEVarClass 𝓔 ∧ IsFiniteMeasure P then
    have := h.2
    (h.1.exists_isLogNumeraireFor P).choose
  else 1

lemma isLogNumeraireFor_logNumeraire (h𝓔 : IsEVarClass 𝓔) (P : Measure 𝓧) [IsFiniteMeasure P] :
    IsLogNumeraireFor (logNumeraire P 𝓔) 𝓔 P := by
  unfold logNumeraire
  split_ifs with h
  · exact (h𝓔.exists_isLogNumeraireFor P).choose_spec
  · exact absurd ⟨h𝓔, inferInstance⟩ h

lemma logNumeraire_mem (P : Measure 𝓧) (h_one : 1 ∈ 𝓔) : logNumeraire P 𝓔 ∈ 𝓔 := by
  unfold logNumeraire
  split_ifs with h
  · have := h.2
    exact (h.1.exists_isLogNumeraireFor P).choose_spec.mem
  · exact h_one

lemma measurable_logNumeraire (P : Measure 𝓧) (h𝓔 : IsEVarClass 𝓔) :
    Measurable (logNumeraire P 𝓔) :=
  h𝓔.measurable (logNumeraire_mem P h𝓔.one_mem)

lemma lintegral_div_logNumeraire_le_measure_fsupport (P : Measure 𝓧) (h𝓔 : IsEVarClass 𝓔)
    (hX : X ∈ 𝓔) :
    ∫⁻ x, X x / logNumeraire P 𝓔 x ∂P ≤ P (logNumeraire P 𝓔).fsupport := by
  by_cases hP : IsFiniteMeasure P
  · exact (isLogNumeraireFor_logNumeraire h𝓔 P).lintegral_div_le_measure_fsupport
      (measurable_logNumeraire P h𝓔).aemeasurable hX (h𝓔.measurable hX).aemeasurable
  · have h_univ : P .univ = ∞ := by rwa [not_isFiniteMeasure_iff] at hP
    have h_one : logNumeraire P 𝓔 = 1 := by
      unfold logNumeraire
      split_ifs with h
      · exact absurd h.2 hP
      · rfl
    simp [h_one, h_univ]

lemma lintegral_div_logNumeraire_le (P : Measure 𝓧) (h𝓔 : IsEVarClass 𝓔) (hX : X ∈ 𝓔) :
    ∫⁻ x, X x / logNumeraire P 𝓔 x ∂P
      ≤ ∫⁻ x, logNumeraire P 𝓔 x / logNumeraire P 𝓔 x ∂P := by
  rw [lintegral_div_self_eq_measure_fsupport (measurable_logNumeraire P h𝓔).aemeasurable]
  exact lintegral_div_logNumeraire_le_measure_fsupport P h𝓔 hX

lemma lintegral_div_logNumeraire_le_measure_univ (P : Measure 𝓧) (h𝓔 : IsEVarClass 𝓔)
    (hX : X ∈ 𝓔) :
    ∫⁻ x, X x / logNumeraire P 𝓔 x ∂P ≤ P .univ :=
  (lintegral_div_logNumeraire_le_measure_fsupport P h𝓔 hX).trans (measure_mono (by simp))

lemma lintegral_div_logNumeraire_le_one (P : Measure 𝓧) [IsProbabilityMeasure P]
    (h𝓔 : IsEVarClass 𝓔) (hX : X ∈ 𝓔) :
    ∫⁻ x, X x / logNumeraire P 𝓔 x ∂P ≤ 1 := by
  simpa using lintegral_div_logNumeraire_le_measure_univ P h𝓔 hX

lemma IsLogNumeraireFor.ae_eq_logNumeraire [IsFiniteMeasure P] (h𝓔 : IsEVarClass 𝓔)
    (hX : IsLogNumeraireFor X 𝓔 P) :
    X =ᵐ[P] logNumeraire P 𝓔 :=
  hX.ae_unique (isLogNumeraireFor_logNumeraire h𝓔 P) strictAntiOn_deriv_logUtility
    (h𝓔.measurable hX.mem).aemeasurable (measurable_logNumeraire P h𝓔).aemeasurable

/-! ### The numeraire of the e-variables for a set of measures -/

/-- **Existence of the numeraire** of the e-variables for a set of finite measures. -/
theorem exists_isNumeraire (P : Measure 𝓧) [IsFiniteMeasure P]
    (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ X, IsNumeraire X S P :=
  (isEVarClass_isEVar S hS).exists_isLogNumeraireFor P

/-- The numeraire of the e-variables for `S`, under `P` (see `isNumeraire_numeraire`). -/
noncomputable
def numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) : 𝓧 → ℝ≥0∞ :=
  logNumeraire P {X | IsEVar X S}

lemma isEVar_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    IsEVar (numeraire P S) S :=
  logNumeraire_mem (𝓔 := {X | IsEVar X S}) P (isEVar_one S)

@[fun_prop]
lemma measurable_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Measurable (numeraire P S) := (isEVar_numeraire P S).measurable

/-- The numeraire `numeraire P S` is indeed a numeraire for `S` and `P`. -/
lemma isNumeraire_numeraire (P : Measure 𝓧) [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    IsNumeraire (numeraire P S) S P :=
  isLogNumeraireFor_logNumeraire (isEVarClass_isEVar S hS) P

/-- The numeraire `numeraire P S` attains the maximum logarithmic utility. -/
lemma maxUtility_eq_eintegral_numeraire (P : Measure 𝓧) [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    maxUtility P S logUtility = ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P :=
  (isNumeraire_numeraire P hS).maxUtility_eq_eintegral

lemma lintegral_div_numeraire_le (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (hX : IsEVar X S) :
    ∫⁻ x, X x / numeraire P S x ∂P ≤ ∫⁻ x, numeraire P S x / numeraire P S x ∂P :=
  lintegral_div_logNumeraire_le P (isEVarClass_isEVar S hS) hX

lemma lintegral_div_numeraire_le_measure_univ (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (hX : IsEVar X S) :
    ∫⁻ x, X x / numeraire P S x ∂P ≤ P .univ :=
  lintegral_div_logNumeraire_le_measure_univ P (isEVarClass_isEVar S hS) hX

lemma lintegral_div_numeraire_le_one (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (hX : IsEVar X S) :
    ∫⁻ x, X x / numeraire P S x ∂P ≤ 1 :=
  (isNumeraire_numeraire P hS).lintegral_div_le_one hX

lemma IsNumeraire.ae_eq_numeraire [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (hX : IsNumeraire X S P) :
    X =ᵐ[P] numeraire P S :=
  hX.ae_unique (isNumeraire_numeraire P hS)

lemma eintegrable_log_numeraire [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    EIntegrable (fun x ↦ ENNReal.log (numeraire P S x)) P :=
  (isNumeraire_numeraire P hS).eintegrable_log

end ProbabilityTheory
