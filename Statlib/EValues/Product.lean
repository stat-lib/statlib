/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Statlib.EValues.NumeraireExistence

/-!
# Numeraire of a product

The product of e-variables for two sets of measures `S` and `T` is an e-variable for the set of
product measures `Set.image2 Measure.prod S T`, and the product of the numeraires is the numeraire
for the product measure. As a consequence, the maximal logarithmic utility is additive on products
of probability measures. The statements about numeraires and maximal utilities are for sets of
measures of mass at most one, for which the numeraire exists.

## Main statements

* `IsEVar.prod`: the product of two e-variables is an e-variable for the product measures.
* `IsNumeraire.prod`: the product of two numeraires is a numeraire for the product measure.
* `eintegral_log_numeraire_prod`: the expected logarithm of the numeraire of a product.
* `maxUtility_prod`: the maximal logarithmic utility of a product is a weighted sum of the maximal
  logarithmic utilities, and `maxUtility_prod_eq_add` is the case of probability measures.
* `isNumeraire_pi_numeraire`: the product of the numeraires is the numeraire for a finite product
  of finite measures.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

namespace MeasureTheory

/-- The integral of `(x, y) ↦ f x + g y` against a measure on a product is the sum of the integrals
of `f` and `g` against the marginals, if those are not `⊥`. -/
lemma eintegral_add_fst_snd {R : Measure (𝓧 × 𝓨)} {f : 𝓧 → EReal} {g : 𝓨 → EReal}
    (hf : AEMeasurable f R.fst) (hg : AEMeasurable g R.snd) (hf_bot : ∫ᵉ x, f x ∂R.fst ≠ ⊥)
    (hg_bot : ∫ᵉ y, g y ∂R.snd ≠ ⊥) :
    ∫ᵉ p, f p.1 + g p.2 ∂R = ∫ᵉ x, f x ∂R.fst + ∫ᵉ y, g y ∂R.snd := by
  rw [Measure.fst, eintegral_map' hf measurable_fst.aemeasurable] at hf_bot ⊢
  rw [Measure.snd, eintegral_map' hg measurable_snd.aemeasurable] at hg_bot ⊢
  exact eintegral_add (hf.comp_aemeasurable measurable_fst.aemeasurable)
    (hg.comp_aemeasurable measurable_snd.aemeasurable) (eintegrable_of_eintegral_ne_bot hg_bot)
    (.inl hf_bot) (.inr hg_bot)

end MeasureTheory

namespace ProbabilityTheory

variable {P : Measure 𝓧} {Q : Measure 𝓨} {S : Set (Measure 𝓧)} {T : Set (Measure 𝓨)}

/-- The product of two e-variables is an e-variable for the product measures. This needs no
assumption on the measures, since `lintegral_prod_le` holds without s-finiteness. -/
lemma IsEVar.prod {X : 𝓧 → ℝ≥0∞} {Y : 𝓨 → ℝ≥0∞} (hX : IsEVar X S) (hY : IsEVar Y T) :
    IsEVar (fun (x : 𝓧 × 𝓨) ↦ X x.1 * Y x.2) (Set.image2 Measure.prod S T) := by
  have hX_meas := hX.measurable
  have hY_meas := hY.measurable
  refine ⟨by fun_prop, ?_⟩
  rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
  calc ∫⁻ x, X x.1 * Y x.2 ∂μ.prod ν
  _ ≤ ∫⁻ x, ∫⁻ y, X x * Y y ∂ν ∂μ := lintegral_prod_le _
  _ = (∫⁻ x, X x ∂μ) * ∫⁻ y, Y y ∂ν := lintegral_lintegral_mul (by fun_prop) (by fun_prop)
  _ ≤ 1 := mul_le_one' (hX.lintegral_le_one hμS) (hY.lintegral_le_one hνT)

/-- Products of measures of mass at most one have mass at most one. -/
private lemma measure_univ_le_one_of_mem_image2_prod (hS : ∀ μ ∈ S, μ Set.univ ≤ 1)
    (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    ∀ ρ ∈ Set.image2 Measure.prod S T, ρ Set.univ ≤ 1 := by
  rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
  have : IsFiniteMeasure ν := ⟨(hT ν hνT).trans_lt ENNReal.one_lt_top⟩
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  exact mul_le_one' (hS μ hμS) (hT ν hνT)

/-- The product of two numeraires is a numeraire for the product measure, with respect to the set
of product measures. -/
theorem IsNumeraire.prod [IsFiniteMeasure P] [IsFiniteMeasure Q] {X : 𝓧 → ℝ≥0∞}
    {Y : 𝓨 → ℝ≥0∞} (hX : IsNumeraire X S P) (hY : IsNumeraire Y T Q)
    (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ X x.1 * Y x.2) (Set.image2 Measure.prod S T) (P.prod Q) := by
  have hX_meas := hX.measurable
  have hY_meas := hY.measurable
  refine isNumeraire_of_lintegral_div_le (hX.isEVar.prod hY.isEVar) (measure_ne_top _ _)
    fun Z hZ_evar ↦ ?_
  have hZ_meas := hZ_evar.measurable
  rw [Function.fsupport_mul_prod, Measure.prod_prod, lintegral_prod _ (by fun_prop)]
  simp_rw [mul_comm (X _)]
  -- integrate first over `y`
  have h_eq : ∫⁻ x, ∫⁻ y, Z (x, y) / (Y y * X x) ∂Q ∂P
      = ∫⁻ x, (∫⁻ y, Z (x, y) / Y y ∂Q) / X x ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hX.ae_ne_zero hS] with x hx
    simp_rw [div_eq_mul_inv]
    rw [← lintegral_mul_const _ (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [hY.ae_ne_zero hT] with y hy
    rw [ENNReal.mul_inv (.inl hy) (.inr hx), mul_assoc]
  rw [h_eq]
  -- if `Y` is almost everywhere infinite, both sides vanish
  by_cases hY_top : Y =ᵐ[Q] fun _ ↦ ∞
  · have hQY : Q Y.fsupport = 0 := measure_fsupport_eq_zero_of_ae_eq_top hY_top
    refine le_of_eq ?_
    calc ∫⁻ x, (∫⁻ y, Z (x, y) / Y y ∂Q) / X x ∂P
    _ = ∫⁻ x, 0 / X x ∂P := by
      congr with x
      congr
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hY_top] with y hy
      simp [hy]
    _ = 0 := by simp
    _ = P X.fsupport * Q Y.fsupport := by simp [hQY]
  -- otherwise, `x ↦ (Q Y.fsupport)⁻¹ * ∫⁻ y, Z (x, y) / Y y ∂Q` is an e-variable for `S`, and we
  -- conclude with the numeraire property of `X`
  suffices IsEVar (fun x ↦ (Q Y.fsupport)⁻¹ * ∫⁻ y, Z (x, y) / Y y ∂Q) S by
    have h_le := hX.lintegral_div_le_measure_fsupport this
    simp_rw [mul_div_assoc] at h_le
    rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ (by simp), mul_comm] at h_le
    swap; · simpa [hY_top] using hY.measure_fsupport_ne_zero_or_ae_top hT
    exact h_le
  refine ⟨by fun_prop, fun μ hμS ↦ ?_⟩
  have : IsFiniteMeasure μ := ⟨(hS μ hμS).trans_lt ENNReal.one_lt_top⟩
  -- this follows from the numeraire property of `Y`, applied to the e-variable
  -- `y ↦ ∫⁻ x, Z (x, y) ∂μ` for `T`
  suffices IsEVar (fun y ↦ ∫⁻ x, Z (x, y) ∂μ) T by
    have hY' := hY.lintegral_div_le_measure_fsupport this
    rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ (by simp), mul_one]
    swap; · simpa [hY_top] using hY.measure_fsupport_ne_zero_or_ae_top hT
    refine le_trans (le_of_eq ?_) hY'
    rw [lintegral_lintegral_swap (by fun_prop)]
    congr with y
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const _ (by fun_prop)]
  refine ⟨by fun_prop, fun ν hνT ↦ ?_⟩
  have : IsFiniteMeasure ν := ⟨(hT ν hνT).trans_lt ENNReal.one_lt_top⟩
  rw [lintegral_lintegral_symm (by fun_prop)]
  exact hZ_evar.lintegral_le_one ⟨μ, hμS, ν, hνT, rfl⟩

/-- The product of the numeraires is the numeraire for the product measure. -/
theorem isNumeraire_prod_numeraire (P : Measure 𝓧) [IsFiniteMeasure P] (Q : Measure 𝓨)
    [IsFiniteMeasure Q] (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ numeraire P S x.1 * numeraire Q T x.2)
      (Set.image2 Measure.prod S T) (P.prod Q) :=
  (isNumeraire_numeraire P hS).prod (isNumeraire_numeraire Q hT) hS hT

/-- The expected logarithm of the numeraire of a product is a weighted sum of the expected
logarithms of the numeraires of the factors. -/
theorem eintegral_log_numeraire_prod [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    ∫ᵉ x, ENNReal.log (numeraire (P.prod Q) (Set.image2 Measure.prod S T) x) ∂(P.prod Q)
      = Q .univ * ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P +
        P .univ * ∫ᵉ x, ENNReal.log (numeraire Q T x) ∂Q := by
  have hX := isNumeraire_numeraire P hS
  have hY := isNumeraire_numeraire Q hT
  have h_fst : (P.prod Q).fst = Q .univ • P := Measure.map_fst_prod
  have h_snd : (P.prod Q).snd = P .univ • Q := Measure.map_snd_prod
  -- the numeraire of the product is the product of the numeraires
  have h_ae_eq : numeraire (P.prod Q) (Set.image2 Measure.prod S T)
      =ᵐ[P.prod Q] (fun x ↦ numeraire P S x.1 * numeraire Q T x.2) :=
    ((hX.prod hY hS hT).ae_eq_numeraire (measure_univ_le_one_of_mem_image2_prod hS hT)).symm
  rw [eintegral_congr_ae (h_ae_eq.mono fun p hp ↦ by rw [hp])]
  simp_rw [ENNReal.log_mul_add]
  rw [eintegral_add_fst_snd (f := fun x ↦ ENNReal.log (numeraire P S x))
      (g := fun y ↦ ENNReal.log (numeraire Q T y)) (by fun_prop) (by fun_prop), h_fst, h_snd,
    eintegral_smul_measure (by simp), eintegral_smul_measure (by simp)]
  · rw [h_fst, eintegral_smul_measure (by simp)]
    have := hX.eintegral_log_nonneg hS
    exact EReal.ne_bot_of_nonneg (by positivity)
  · rw [h_snd, eintegral_smul_measure (by simp)]
    have := hY.eintegral_log_nonneg hT
    exact EReal.ne_bot_of_nonneg (by positivity)

/-- The maximal logarithmic utility of a product is a weighted sum of the maximal logarithmic
utilities of the factors. -/
lemma maxUtility_prod (P : Measure 𝓧) (Q : Measure 𝓨) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    maxUtility (P.prod Q) (Set.image2 Measure.prod S T) logUtility =
      Q .univ * maxUtility P S logUtility + P .univ * maxUtility Q T logUtility := by
  rw [maxUtility_eq_eintegral_numeraire (P.prod Q) (measure_univ_le_one_of_mem_image2_prod hS hT),
    maxUtility_eq_eintegral_numeraire _ hS, maxUtility_eq_eintegral_numeraire _ hT]
  exact eintegral_log_numeraire_prod hS hT

/-- The maximal logarithmic utility of a product of probability measures is the sum of the maximal
logarithmic utilities of the factors. -/
lemma maxUtility_prod_eq_add (P : Measure 𝓧) (Q : Measure 𝓨) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    maxUtility (P.prod Q) (Set.image2 Measure.prod S T) logUtility =
      maxUtility P S logUtility + maxUtility Q T logUtility := by
  simpa using maxUtility_prod P Q hS hT

/-- The maximal logarithmic utility of a finite measure on a product is at least the sum of the
maximal logarithmic utilities of its marginals. The two are equal for a product measure of
probability measures (`maxUtility_prod_eq_add`). -/
lemma maxUtility_fst_add_maxUtility_snd_le (R : Measure (𝓧 × 𝓨)) [IsFiniteMeasure R]
    (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) (hT : ∀ μ ∈ T, μ Set.univ ≤ 1) :
    maxUtility R.fst S logUtility + maxUtility R.snd T logUtility
      ≤ maxUtility R (Set.image2 Measure.prod S T) logUtility := by
  have hX := isNumeraire_numeraire R.fst hS
  have hY := isNumeraire_numeraire R.snd hT
  -- the product of the numeraires of the marginals is an e-variable for the product sets
  calc maxUtility R.fst S logUtility + maxUtility R.snd T logUtility
  _ = ∫ᵉ p, (logUtility ∘ fun p : 𝓧 × 𝓨 ↦ numeraire R.fst S p.1 * numeraire R.snd T p.2) p ∂R := by
    simp_rw [Function.comp_apply, logUtility_apply, ENNReal.log_mul_add]
    rw [eintegral_add_fst_snd (f := fun x ↦ ENNReal.log (numeraire R.fst S x))
      (g := fun y ↦ ENNReal.log (numeraire R.snd T y)) (by fun_prop) (by fun_prop)
      (hX.eintegral_log_ne_bot hS) (hY.eintegral_log_ne_bot hT), hX.maxUtility_eq_eintegral,
      hY.maxUtility_eq_eintegral]
  _ ≤ maxUtility R (Set.image2 Measure.prod S T) logUtility :=
    (hX.isEVar.prod hY.isEVar).eintegral_le_maxUtility R logUtility

/-- The product of the numeraires is a numeraire for the product measure, for a family indexed
by `Fin n`. This is the induction that underlies `isNumeraire_pi_numeraire`. -/
private lemma isNumeraire_pi_numeraire_fin : ∀ (n : ℕ) {𝓧 : Fin n → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] (P : (i : Fin n) → Measure (𝓧 i))
    [∀ i, IsFiniteMeasure (P i)] (S : (i : Fin n) → Set (Measure (𝓧 i))),
    (∀ i, ∀ μ ∈ S i, μ Set.univ ≤ 1) →
    IsNumeraire (fun x ↦ ∏ i, numeraire (P i) (S i) (x i))
      (Measure.pi '' (Set.pi Set.univ S)) (Measure.pi P) := by
  intro n
  induction n with
  | zero =>
    intro 𝓧 _ P _ S _
    have h1 : (fun x : ∀ i : Fin 0, 𝓧 i ↦ ∏ i, numeraire (P i) (S i) (x i)) = 1 := by
      ext x
      simp
    rw [h1]
    have : IsProbabilityMeasure (Measure.pi P) := by
      rw [Measure.pi_of_empty]
      infer_instance
    refine isNumeraire_one ?_ ⟨P, fun i _ ↦ i.elim0, rfl⟩
    rintro _ ⟨ν, -, rfl⟩
    simp
  | succ n ih =>
    intro 𝓧 _ P _ S hS
    -- split off the first coordinate
    set e := MeasurableEquiv.piFinSuccAbove 𝓧 0 with he
    set S' : (j : Fin n) → Set (Measure (𝓧 ((0 : Fin (n + 1)).succAbove j))) :=
      fun j ↦ S ((0 : Fin (n + 1)).succAbove j) with hS'
    set P' : (j : Fin n) → Measure (𝓧 ((0 : Fin (n + 1)).succAbove j)) :=
      fun j ↦ P ((0 : Fin (n + 1)).succAbove j) with hP'
    have hS_fin (i : Fin (n + 1)) {μ : Measure (𝓧 i)} (hμ : μ ∈ S i) : IsFiniteMeasure μ :=
      ⟨(hS i μ hμ).trans_lt ENNReal.one_lt_top⟩
    have hS0 : ∀ μ ∈ S 0, μ Set.univ ≤ 1 := hS 0
    have hT : ∀ ρ ∈ Measure.pi '' (Set.pi Set.univ S'), ρ Set.univ ≤ 1 := by
      rintro _ ⟨ν, hν, rfl⟩
      have : ∀ j, IsFiniteMeasure (ν j) := fun j ↦ hS_fin _ (hν j (Set.mem_univ _))
      rw [Measure.pi_univ]
      exact Finset.prod_le_one fun j _ ↦ hS _ _ (hν j (Set.mem_univ _))
    have h_prod := (isNumeraire_numeraire (P 0) hS0).prod (ih P' S' fun j ↦ hS _) hS0 hT
    -- the images of the two sets of measures agree
    have h_map (ν : (i : Fin (n + 1)) → Measure (𝓧 i)) [∀ i, SigmaFinite (ν i)] :
        (Measure.pi ν).map e = (ν 0).prod (Measure.pi fun j ↦ ν ((0 : Fin (n + 1)).succAbove j)) :=
      (measurePreserving_piFinSuccAbove ν 0).map_eq
    have h_eq_set : Measure.map e '' (Measure.pi '' (Set.pi Set.univ S))
        = Set.image2 Measure.prod (S 0) (Measure.pi '' (Set.pi Set.univ S')) := by
      ext ρ
      simp only [Set.mem_image, Set.mem_image2]
      constructor
      · rintro ⟨_, ⟨ν, hν, rfl⟩, rfl⟩
        have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS_fin _ (hν i (Set.mem_univ _))
        exact ⟨ν 0, hν 0 (Set.mem_univ _), _,
          ⟨fun j ↦ ν ((0 : Fin (n + 1)).succAbove j), fun j _ ↦ hν _ (Set.mem_univ _), rfl⟩,
          (h_map ν).symm⟩
      · rintro ⟨μ, hμ, _, ⟨ν', hν', rfl⟩, rfl⟩
        set ν : (i : Fin (n + 1)) → Measure (𝓧 i) :=
          Fin.insertNth (α := fun i ↦ Measure (𝓧 i)) 0 μ ν' with hν_def
        have hν0 : ν 0 = μ := Fin.insertNth_apply_same _ _ _
        have hνs (j : Fin n) : ν ((0 : Fin (n + 1)).succAbove j) = ν' j :=
          Fin.insertNth_apply_succAbove _ _ _ _
        have hν_mem : ∀ i, ν i ∈ S i := by
          refine Fin.succAboveCases 0 ?_ ?_
          · rw [hν0]; exact hμ
          · intro j
            rw [hνs]
            exact hν' j (Set.mem_univ _)
        have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS_fin i (hν_mem i)
        refine ⟨Measure.pi ν, ⟨ν, fun i _ ↦ hν_mem i, rfl⟩, ?_⟩
        rw [h_map ν, hν0]
        congr 1
    rw [← h_eq_set, ← h_map P] at h_prod
    have h := h_prod.comp_measurableEquiv e
    convert h using 1
    ext x
    rw [Fin.prod_univ_succAbove _ 0]
    rfl

/-- The product of the numeraires is the numeraire for a finite product of finite measures. -/
lemma isNumeraire_pi_numeraire {ι : Type*} {𝓧 : ι → Type*} [Fintype ι]
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {P : (i : ι) → Measure (𝓧 i)}
    {S : (i : ι) → Set (Measure (𝓧 i))} [∀ i, IsFiniteMeasure (P i)]
    (hS : ∀ i, ∀ μ ∈ S i, μ Set.univ ≤ 1) :
    IsNumeraire (fun x ↦ ∏ i, numeraire (P i) (S i) (x i))
      (Measure.pi '' (Set.pi Set.univ S)) (Measure.pi P) := by
  have hS_fin (i : ι) {μ : Measure (𝓧 i)} (hμ : μ ∈ S i) : IsFiniteMeasure μ :=
    ⟨(hS i μ hμ).trans_lt ENNReal.one_lt_top⟩
  -- reindex the family by `Fin (card ι)`
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let e : ((i : ι) → 𝓧 i) ≃ᵐ ((j : Fin (Fintype.card ι)) → 𝓧 (f j)) :=
    (MeasurableEquiv.piCongrLeft 𝓧 f).symm
  have h_map (ν : (i : ι) → Measure (𝓧 i)) [∀ i, SigmaFinite (ν i)] :
      (Measure.pi ν).map e = Measure.pi fun j ↦ ν (f j) :=
    (MeasurePreserving.symm _ (measurePreserving_piCongrLeft ν f)).map_eq
  have h_fin := isNumeraire_pi_numeraire_fin _ (fun j ↦ P (f j)) (fun j ↦ S (f j))
    fun j ↦ hS (f j)
  have h_set : Measure.map e '' (Measure.pi '' (Set.pi Set.univ S))
      = Measure.pi '' (Set.pi Set.univ fun j ↦ S (f j)) := by
    ext ρ
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨ν, hν, rfl⟩, rfl⟩
      have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS_fin _ (hν i (Set.mem_univ _))
      exact ⟨fun j ↦ ν (f j), fun j _ ↦ hν _ (Set.mem_univ _), (h_map ν).symm⟩
    · rintro ⟨ν', hν', rfl⟩
      set ν : (i : ι) → Measure (𝓧 i) :=
        Equiv.piCongrLeft (fun i ↦ Measure (𝓧 i)) f ν' with hν_def
      have hν_apply (j : Fin (Fintype.card ι)) : ν (f j) = ν' j :=
        Equiv.piCongrLeft_apply_apply (fun i ↦ Measure (𝓧 i)) f ν' j
      have hν_mem (i : ι) : ν i ∈ S i := by
        obtain ⟨j, rfl⟩ := f.surjective i
        rw [hν_apply]
        exact hν' j (Set.mem_univ _)
      have : ∀ i, IsFiniteMeasure (ν i) := fun i ↦ hS_fin i (hν_mem i)
      refine ⟨Measure.pi ν, ⟨ν, fun i _ ↦ hν_mem i, rfl⟩, ?_⟩
      rw [h_map ν]
      congr 1
      funext j
      exact hν_apply j
  rw [← h_set, ← h_map P] at h_fin
  have h := h_fin.comp_measurableEquiv e
  convert h using 1
  ext x
  rw [← f.prod_comp fun i ↦ numeraire (P i) (S i) (x i)]
  rfl

/-- The product of the numeraires is the numeraire for the product of finite measures indexed by
a finset. -/
lemma isNumeraire_pi_numeraire_finset {ι : Type*} {𝓧 : ι → Type*} {s : Finset ι}
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {P : (i : ι) → Measure (𝓧 i)}
    {S : (i : ι) → Set (Measure (𝓧 i))} [∀ i : s, IsFiniteMeasure (P i)]
    (hS : ∀ i ∈ s, ∀ μ ∈ S i, μ Set.univ ≤ 1) :
    IsNumeraire (fun x ↦ ∏ i : s, numeraire (P i) (S i) (x i))
      (Measure.pi '' (Set.pi Set.univ fun i : s ↦ S i)) (Measure.pi fun i : s ↦ P i) :=
  isNumeraire_pi_numeraire fun i ↦ hS i i.2

end ProbabilityTheory
