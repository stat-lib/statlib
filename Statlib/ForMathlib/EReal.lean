/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Lemmas about EReal
-/

@[expose] public section

open ENNReal NNReal

lemma EReal.le_of_toReal_le {a b : EReal} (h1 : a ≠ ⊤) (h2 : b ≠ ⊤) (h3 : a ≠ ⊥) (h4 : b ≠ ⊥)
    (h5 : b.toReal ≤ a.toReal) : b ≤ a := by
  lift a to ℝ using ⟨h1, h3⟩
  lift b to ℝ using ⟨h2, h4⟩
  exact EReal.coe_le_coe_iff.mpr h5

lemma EReal.toReal_log {x : ℝ≥0∞} (hx₀ : x ≠ 0) (hxₜ : x ≠ ⊤) :
    (log x).toReal = Real.log x.toReal := by
  simp_all [log]

lemma EReal.mul_add_ENNReal {a : ℝ≥0∞} {b c : EReal} (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c) :
    a * (b + c).toENNReal = a * b.toENNReal + a * c.toENNReal := by
  by_cases hₜ : b + c = ⊤
  · rw [hₜ]
    by_cases ha₀ : a = 0
    · simp [ha₀]
    · simp_all only [toENNReal_top, ne_eq, not_false_eq_true, mul_top]
      have : b = ⊤ ∨ c = ⊤ := by
        by_contra! h
        exact add_ne_top h.1 h.2 hₜ
      cases this with
      | inl hbₜ =>
        rw [hbₜ]
        simp_all
      | inr hcₜ =>
        rw [hcₜ]
        simp_all
  · push Not at hₜ
    rw [toENNReal_of_ne_top hₜ]
    suffices ENNReal.ofReal (b + c).toReal = b.toENNReal + c.toENNReal by
      rw [this]
      ring
    have hb_bot : b ≠ ⊥ := by
      rintro rfl
      simp_all
    have hc_bot : c ≠ ⊥ := by
      rintro rfl
      simp_all
    obtain ⟨hbₜ, hcₜ⟩ := (add_ne_top_iff_ne_top₂ hb_bot hc_bot).mp hₜ
    rw [EReal.toReal_add, toENNReal_of_ne_top hbₜ, toENNReal_of_ne_top hcₜ, ← ENNReal.ofReal_add]
    · exact toReal_nonneg hb₀
    · exact toReal_nonneg hc₀
    · exact hbₜ
    · exact hb_bot
    · exact hcₜ
    · exact hc_bot

lemma EReal.toReal_inv (r : EReal) : (r⁻¹).toReal = (r.toReal)⁻¹ := by
    cases r with
    | bot => simp
    | coe a => rw [← EReal.coe_inv, EReal.toReal_coe, EReal.toReal_coe]
    | top => simp

lemma EReal.inv_ne_top {r : EReal} : r⁻¹ ≠ ⊤ := by
    cases r with
    | bot => simp
    | coe a => rw [← EReal.coe_inv]; simp
    | top => simp

lemma EReal.toENNReal_inv {r : EReal} (hr : 0 < r) :
    (r⁻¹).toENNReal = (r.toENNReal)⁻¹ := by
    cases r with
    | bot => simp at hr
    | coe a =>
      simp only [EReal.toENNReal, EReal.coe_ne_top, ↓reduceIte, EReal.toReal_coe]
      rw [ite_eq_right EReal.inv_ne_top, EReal.toReal_inv, ENNReal.ofReal_inv_of_pos,
        EReal.toReal_coe]
      simpa using hr
    | top => simp

lemma EReal.iSup_coe_mul_of_nonneg {α : Type*} [Nonempty α] {f : α → EReal} {a : ℝ} (ha : 0 ≤ a) :
    a * (⨆ x, f x) = ⨆ x, a * f x := by
  by_cases ha' : a = 0
  · simp [ha']
  refine le_antisymm ?_ ?_
  · calc a * ⨆ x, f x
    _ ≤ a * (a⁻¹ * ⨆ x, a * f x) := by
      gcongr
      simp only [iSup_le_iff]
      intro x
      suffices a * f x ≤ ⨆ x, a * f x by
        calc f x
        _ = a⁻¹ * (a * f x) := by rw [← mul_assoc]; norm_cast; rw [inv_mul_cancel₀ ha']; simp
        _ ≤ a⁻¹ * ⨆ x, a * f x := by gcongr
      exact le_iSup (fun x ↦ a * f x) x
    _ = ⨆ x, a * f x := by rw [← mul_assoc]; norm_cast; rw [mul_inv_cancel₀ ha']; simp
  · simp only [iSup_le_iff]
    intro x
    gcongr
    exact le_iSup f x

lemma EReal.iSup_ennreal_mul {α : Type*} [Nonempty α] {f : α → EReal} {a : ℝ≥0∞} (ha : a ≠ ∞) :
    a * (⨆ x, f x) = ⨆ x, a * f x := by
  by_cases ha' : a = 0
  · simp [ha']
  refine le_antisymm ?_ ?_
  · calc a * ⨆ x, f x
    _ ≤ a * (a⁻¹ * ⨆ x, a * f x) := by
      gcongr
      simp only [iSup_le_iff]
      intro x
      suffices a * f x ≤ ⨆ x, a * f x by
        calc f x
        _ = a⁻¹ * (a * f x) := by
          rw [← mul_assoc]; norm_cast; rw [ENNReal.inv_mul_cancel ha' ha]; simp
        _ ≤ a⁻¹ * ⨆ x, a * f x := by gcongr
      exact le_iSup (fun x ↦ a * f x) x
    _ = ⨆ x, a * f x := by rw [← mul_assoc]; norm_cast; rw [ENNReal.mul_inv_cancel ha' ha]; simp
  · simp only [iSup_le_iff]
    intro x
    gcongr
    exact le_iSup f x

lemma EReal.inv_coe_ennreal {x : ℝ≥0∞} (hx : x ≠ 0) :
    (x : EReal)⁻¹ = (x⁻¹ : ℝ≥0∞) := by
  by_cases hx_top : x = ⊤
  · simp [hx_top]
  have hx_eq : x = ENNReal.ofReal x.toReal := by rw [ENNReal.ofReal_toReal hx_top]
  rw [hx_eq]
  simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
  rw [← ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hx hx_top)]
  simp only [EReal.coe_ennreal_ofReal, inv_nonneg, ENNReal.toReal_nonneg, sup_of_le_left]
  rw [EReal.coe_inv]

lemma EReal.add_sub_add (a b : EReal) {c d : EReal} (hc : c ≠ ⊥) (hd : d ≠ ⊥) :
    a + b - (c + d) = (a - c) + (b - d) := by
  cases a <;> cases b <;> cases c <;> cases d
  -- 81 goals :)
  any_goals simp [hc, hd]
  all_goals simp at hc
  all_goals simp at hd
  · norm_cast
    ring
  · norm_cast
  · norm_cast

lemma EReal.mul_sub_of_eq_zero {a b c : EReal} (h : b = 0 ∨ c = 0) :
    a * (b - c) = a * b - a * c := by
  cases h with
  | inl hb => simp [hb]
  | inr hc => simp [hc]

lemma EReal.ne_bot_of_nonneg {a : EReal} (ha : 0 ≤ a) : a ≠ ⊥ := by
  intro h_false
  simp [h_false] at ha

lemma EReal.neg_div (a b : EReal) : - a / b = - (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, EReal.neg_mul]

@[simp]
lemma EReal.toENNReal_one : (1 : EReal).toENNReal = 1 := by
  have : (1 : EReal) = (1 : ℝ≥0∞) := rfl
  rw [this, EReal.toENNReal_coe]

lemma EReal.coe_ennreal_div {a b : ℝ≥0∞} (hb_zero : b ≠ 0) :
    ((a / b : ℝ≥0∞) : EReal) = (a : EReal) / (b : EReal) := by
  by_cases hb_top : b = ∞
  · simp [hb_top]
  by_cases ha_top : a = ∞
  · simp only [ha_top, EReal.coe_ennreal_top]
    rw [EReal.top_div_of_pos_ne_top, ENNReal.top_div_of_ne_top]
    · simp
    · exact hb_top
    · simpa [pos_iff_ne_zero] using hb_zero
    · simpa
  have ha : a = ENNReal.ofReal a.toReal := by rw [ENNReal.ofReal_toReal ha_top]
  have hb : b = ENNReal.ofReal b.toReal := by rw [ENNReal.ofReal_toReal hb_top]
  rw [ha, hb]
  rw [← ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hb_zero hb_top)]
  simp only [EReal.coe_ennreal_ofReal]
  rw [max_eq_left (by positivity), max_eq_left (by positivity), max_eq_left (by positivity),
    EReal.coe_div]

lemma EReal.coe_ennreal_inv {a : ℝ≥0∞} (ha : a ≠ 0) : ((a⁻¹ : ℝ≥0∞) : EReal) = (a : EReal)⁻¹ := by
  by_cases ha_top : a = ⊤
  · simp [ha_top]
  have ha_eq : a = ENNReal.ofReal a.toReal := by rw [ENNReal.ofReal_toReal ha_top]
  have ha_pos : 0 < a.toReal := ENNReal.toReal_pos ha ha_top
  rw [ha_eq, EReal.coe_ennreal_ofReal, ← ENNReal.ofReal_inv_of_pos ha_pos, EReal.coe_ennreal_ofReal]
  simp only [inv_nonneg, ENNReal.toReal_nonneg, sup_of_le_left]
  rw [EReal.coe_inv]

instance : MeasurableInv EReal where
  measurable_inv := by
    refine EReal.measurable_of_measurable_real ?_
    simp_rw [← EReal.coe_inv]
    change Measurable (Real.toEReal ∘ _)
    exact Measurable.comp measurable_coe_real_ereal (by fun_prop)

lemma EReal.sub_lt_sub_of_le_of_lt {x y z t : EReal} (h : x ≤ y) (h' : z < t)
  (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) : x - t < y - z := by
  refine sub_lt_of_lt_add' ?_
  rw [add_sub_assoc', add_comm, add_sub_assoc]
  by_cases hxy : x = y
  · rw [hxy]
    lift y to ℝ using ⟨hy_top, hy_bot⟩
    by_cases htz_top : t - z = ⊤
    · simp_all
    rw [← coe_toReal htz_top <| ne_bot_of_nonneg (sub_pos.mpr h').le]
    norm_cast
    refine lt_add_of_pos_right y ?_
    exact EReal.toReal_pos (sub_pos.mpr h') htz_top
  · rw [← add_zero x]
    refine add_lt_add ?_ ?_
    · grind
    · exact sub_pos.mpr h'

lemma EReal.top_sub_eq_top_or_bot {a : EReal} : ⊤ - a = ⊤ ∨ ⊤ - a = ⊥ := by
  cases a with
  | bot => simp
  | coe a => simp
  | top => simp

-- In newer versions of Mathlib
lemma EReal.sub_eq_bot {a b : EReal} : a - b = ⊥ ↔ a = ⊥ ∨ b = ⊤ := by
  cases a <;> cases b <;> simp_all
  norm_cast
  simp [-coe_sub]

lemma EReal.coe_ennreal_sub_toENNReal (a b : ℝ≥0∞) :
    ((a : EReal) - (b : EReal)).toENNReal = a - b := by
  cases a <;> cases b <;> aesop

lemma EReal.ne_top_exists_finite_iff {a : EReal} : a ≠ ⊤ ↔ ∃ b, b ≠ ⊤ ∧ a ≤ b := by
  constructor
  · intro ha
    exact ⟨a, ha, le_refl _⟩
  · rintro ⟨b, hb_top, hab⟩
    rw [← lt_top_iff_ne_top]
    exact lt_of_le_of_lt hab hb_top.lt_top

noncomputable
instance : ENorm EReal where
  eNorm x := (max x 0).toENNReal + (- min x 0).toENNReal

noncomputable instance : SMul ℝ≥0 EReal where smul c x := c * x
noncomputable instance : SMul ℝ≥0∞ EReal where smul c x := c * x

@[simp] lemma EReal.smul_nnreal_eq_mul (c : ℝ≥0) (x : EReal) : c • x = (c : ℝ) * x := rfl
@[simp] lemma EReal.smul_ennreal_eq_mul (c : ℝ≥0∞) (x : EReal) : c • x = c * x := rfl

section limsup_liminf

open Filter

lemma EReal.coe_ennreal_limsup {α : Type} (F : Filter α) [F.NeBot] (g : α → ℝ≥0∞) :
    (limsup g F).toEReal = limsup (fun x => (g x).toEReal) F := by
  refine Monotone.map_limsup_of_continuousAt ?_ _ ?_
  · intro x y hxy
    simp [hxy]
  · exact continuous_coe_ennreal_ereal.continuousAt

lemma EReal.limsup_coe_ennreal {α : Type} (F : Filter α) [F.NeBot] (g : α → EReal) :
    (limsup g F).toENNReal = limsup (fun x => (g x).toENNReal) F := by
  refine Monotone.map_limsup_of_continuousAt ?_ _ ?_
  · intro x y hxy
    exact EReal.toENNReal_le_toENNReal hxy
  · exact EReal.continuous_toENNReal.continuousAt

lemma EReal.coe_ennreal_liminf {α : Type} (F : Filter α) [F.NeBot] (g : α → ℝ≥0∞) :
    (liminf g F).toEReal = liminf (fun x => (g x).toEReal) F := by
  refine Monotone.map_liminf_of_continuousAt ?_ _ ?_
  · intro x y hxy
    simp [hxy]
  · exact continuous_coe_ennreal_ereal.continuousAt

lemma EReal.liminf_coe_ennreal {α : Type} (F : Filter α) [F.NeBot] (g : α → EReal) :
    (liminf g F).toENNReal = liminf (fun x => (g x).toENNReal) F := by
  refine Monotone.map_liminf_of_continuousAt ?_ _ ?_
  · intro x y hxy
    exact EReal.toENNReal_le_toENNReal hxy
  · exact EReal.continuous_toENNReal.continuousAt

end limsup_liminf

lemma EReal.distrib_real {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u : EReal) :
    (a + b) * u = a * u + b * u := by
  cases u with
  | bot =>
    by_cases ha_zero : a = 0
    · simp [ha_zero]
    rw [EReal.mul_bot_of_pos (by positivity), EReal.mul_bot_of_pos (by positivity)]
    simp
  | coe u => norm_cast; ring
  | top =>
    by_cases ha_zero : a = 0
    · simp [ha_zero]
    rw [EReal.mul_top_of_pos (by positivity), EReal.mul_top_of_pos (by positivity)]
    by_cases hb_zero : b = 0
    · simp [hb_zero]
    rw [EReal.mul_top_of_pos (by positivity)]
    simp

lemma EReal.distrib_ennreal (a b : ℝ≥0∞) (u : EReal) : (a + b) * u = a * u + b * u := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha_pos : 0 < a := by positivity
  have hb_pos : 0 < b := by positivity
  by_cases ha_top : a = ∞
  · simp only [ha_top, EReal.coe_ennreal_top, ne_eq, EReal.coe_ennreal_ne_bot, not_false_eq_true,
      EReal.top_add_of_ne_bot]
    rcases lt_trichotomy u 0 with (hu_neg | rfl | hu_pos)
    · rw [EReal.top_mul_of_neg (by simpa)]; simp
    · simp
    · rw [EReal.top_mul_of_pos (by simpa), EReal.top_add_of_ne_bot]
      simp only [ne_eq, EReal.mul_eq_bot, EReal.coe_ennreal_ne_bot, false_and,
        EReal.coe_ennreal_pos, hb_pos, true_and, EReal.coe_ennreal_eq_top_iff, false_or, not_or,
        not_and, not_lt, hu_pos.le, implies_true]
      refine ⟨fun h ↦ by simp [h] at hu_pos, fun h ↦ ?_⟩
      norm_cast at h
      exact absurd hb_pos.le (not_le.mpr h)
  by_cases hb_top : b = ∞
  · simp only [hb_top, EReal.coe_ennreal_top, ne_eq, EReal.coe_ennreal_ne_bot, not_false_eq_true,
      EReal.add_top_of_ne_bot]
    rcases lt_trichotomy u 0 with (hu_neg | rfl | hu_pos)
    · rw [EReal.top_mul_of_neg (by simpa)]; simp
    · simp
    · rw [EReal.top_mul_of_pos (by simpa), EReal.add_top_of_ne_bot]
      simp only [ne_eq, EReal.mul_eq_bot, EReal.coe_ennreal_ne_bot, false_and,
        EReal.coe_ennreal_pos, ha_pos, true_and, EReal.coe_ennreal_eq_top_iff, false_or, not_or,
        not_and, not_lt, hu_pos.le, implies_true]
      refine ⟨fun h ↦ by simp [h] at hu_pos, fun h ↦ ?_⟩
      norm_cast at h
      exact absurd ha_pos.le (not_le.mpr h)
  have ha_real : (a : EReal) = a.toReal := by rw [EReal.coe_ennreal_toReal ha_top]
  have hb_real : (b : EReal) = b.toReal := by rw [EReal.coe_ennreal_toReal hb_top]
  rw [ha_real, hb_real, EReal.distrib_real (by simp) (by simp)]

/-- Distributing an `ℝ≥0∞` factor over a difference of `ℝ≥0∞` values. The hypothesis rules out
the bad case `∞ * (β - α) = ∞` versus `∞ * β - ∞ * α = ⊥` with `0 < α < β`. -/
lemma EReal.coe_ennreal_mul_sub {c α β : ℝ≥0∞} (h : c = ∞ → α = 0) :
    (c : EReal) * ((β : EReal) - (α : EReal))
      = ((c * β : ℝ≥0∞) : EReal) - ((c * α : ℝ≥0∞) : EReal) := by
  rcases eq_or_ne c ∞ with rfl | hc_top
  · rw [h rfl, mul_zero]
    simp only [EReal.coe_ennreal_zero, sub_zero, EReal.coe_ennreal_top]
    rcases eq_or_ne β 0 with rfl | hβ0
    · simp
    · rw [ENNReal.top_mul hβ0, EReal.top_mul_of_pos]
      · simp
      · simpa [EReal.coe_ennreal_pos] using pos_iff_ne_zero.mpr hβ0
  · rw [EReal.mul_sub_of_nonneg_of_ne_top (by positivity) (by simp [hc_top]),
      ← EReal.coe_ennreal_mul, ← EReal.coe_ennreal_mul]

namespace EReal

/-! ### Positive and negative parts -/

@[simp]
lemma toENNReal_posPart (x : EReal) : x⁺.toENNReal = x.toENNReal := by
  rcases le_total 0 x with h | h <;> simp [h]

@[simp]
lemma toENNReal_negPart (x : EReal) : x⁻.toENNReal = (-x).toENNReal := by
  rcases le_total 0 x with h | h <;> simp [negPart_def, h]

/-- An extended real is the difference of its positive and negative parts, seen as elements
of `ℝ≥0∞`. -/
lemma coe_toENNReal_sub_coe_toENNReal_neg (x : EReal) :
    (x.toENNReal : EReal) - (-x).toENNReal = x := by
  rcases le_total x 0 with h | h <;> simp [h]

lemma toReal_toENNReal_sub_toReal_toENNReal_neg (x : EReal) :
    x.toENNReal.toReal - (-x).toENNReal.toReal = x.toReal := by
  induction x with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← coe_neg, toENNReal_of_ne_top (coe_ne_top _), toENNReal_of_ne_top (coe_ne_top _),
      toReal_coe, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    rcases le_total 0 x with h | h <;> simp [h]

lemma toENNReal_neg_le_toENNReal_neg_add_add_toENNReal (x y : EReal) :
    (-x).toENNReal ≤ (-(x + y)).toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp}
  rename_i a b
  simp only [← coe_add, ← coe_neg, toENNReal_of_ne_top (coe_ne_top _), toReal_coe]
  calc ENNReal.ofReal (-a) = ENNReal.ofReal (-(a + b) + b) := by ring_nf
  _ ≤ ENNReal.ofReal (-(a + b)) + ENNReal.ofReal b := ENNReal.ofReal_add_le

lemma neg_coe_ennreal_sub {u v : ℝ≥0∞} (h : u ≠ ⊤ ∨ v ≠ ⊤) :
    -((u : EReal) - v) = v - u := by
  rw [EReal.neg_sub (.inl (by simp)) (by simpa using h), add_comm, ← sub_eq_add_neg]

lemma toENNReal_coe_ennreal_sub_le (u v : ℝ≥0∞) : ((u : EReal) - v).toENNReal ≤ u := by
  rw [toENNReal_sub (coe_ennreal_nonneg _)]
  simp

lemma toENNReal_neg_coe_ennreal_sub_le (u v : ℝ≥0∞) : (-((u : EReal) - v)).toENNReal ≤ v := by
  by_cases h : u = ⊤ ∧ v = ⊤
  · obtain ⟨rfl, rfl⟩ := h
    simp
  rw [neg_coe_ennreal_sub (by tauto), toENNReal_sub (coe_ennreal_nonneg _)]
  simp

/-- For `u v : ℝ≥0∞`, the positive and negative parts of `u - v` satisfy
`(u - v)⁺ + v = (u - v)⁻ + u`. -/
lemma toENNReal_coe_ennreal_sub_add (u v : ℝ≥0∞) :
    ((u : EReal) - v).toENNReal + v = (-((u : EReal) - v)).toENNReal + u := by
  by_cases h : u = ⊤ ∧ v = ⊤
  · obtain ⟨rfl, rfl⟩ := h
    simp
  rw [neg_coe_ennreal_sub (by tauto), toENNReal_sub (coe_ennreal_nonneg _),
    toENNReal_sub (coe_ennreal_nonneg _)]
  simp [tsub_add_eq_max, max_comm]

/-- If `a + d = c + b` in `ℝ≥0∞` with `c` and `d` finite, then `a - c = b - d` in `EReal`.
See also `EReal.coe_ennreal_sub_eq_of_add_eq'` for finite `a` and `b`. -/
lemma coe_ennreal_sub_eq_of_add_eq {a b c d : ℝ≥0∞} (h : a + d = c + b) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) :
    (a : EReal) - c = b - d := by
  lift c to NNReal using hc
  lift d to NNReal using hd
  induction a with
  | top =>
    obtain rfl : b = ⊤ := by simpa [eq_comm] using h
    simp [top_sub]
  | coe a =>
    induction b with
    | top => simp at h
    | coe b =>
      norm_cast at h
      simp only [coe_nnreal_eq_coe_real, ← coe_sub]
      have := congrArg (fun x : NNReal ↦ (x : ℝ)) h
      push_cast at this
      exact_mod_cast (by linarith : (a : ℝ) - c = b - d)

/-- If `a + d = c + b` in `ℝ≥0∞` with `a` and `b` finite, then `a - c = b - d` in `EReal`.
See also `EReal.coe_ennreal_sub_eq_of_add_eq` for finite `c` and `d`. -/
lemma coe_ennreal_sub_eq_of_add_eq' {a b c d : ℝ≥0∞} (h : a + d = c + b) (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) :
    (a : EReal) - c = b - d := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  induction c with
  | top =>
    obtain rfl : d = ⊤ := by simpa using h
    simp [sub_top]
  | coe c =>
    induction d with
    | top =>
      simp at h
      exact absurd h.symm (by simp)
    | coe d =>
      norm_cast at h
      simp only [coe_nnreal_eq_coe_real, ← coe_sub]
      have := congrArg (fun x : NNReal ↦ (x : ℝ)) h
      push_cast at this
      exact_mod_cast (by linarith : (a : ℝ) - c = b - d)

end EReal

namespace EReal

/-! ### Subtraction, `toENNReal` and continuity

These lemmas are adapted from the testing-lower-bounds project of Rémy Degenne and Lorenzo Luccioli
(https://github.com/RemyDegenne/testing-lower-bounds). -/

open Filter Set

lemma sub_add_sub_cancel (b a : EReal) (c : ℝ) :
    b - c + (c - a) = b - a := by
  induction a <;> induction b
  · simp
  · simp only [coe_sub_bot]
    rw [← coe_sub, coe_add_top]
  · simp
  · simp
  · norm_cast
    ring
  · simp only [top_sub_coe]
    rw [← coe_sub, top_add_coe]
  · simp
  · simp
  · simp

lemma toENNReal_sub_le_add (b a c : EReal) :
    (b - a).toENNReal ≤ (b - c).toENNReal + (c - a).toENNReal := by
  by_cases hc_top : c = ⊤
  · simp only [hc_top, sub_top, ne_eq, bot_ne_top, not_false_eq_true,
      toENNReal_of_ne_top, toReal_bot, ENNReal.ofReal_zero, zero_add]
    by_cases ha : a = ⊤
    · simp [ha]
    · simp [top_sub ha]
  by_cases hc_bot : c = ⊥
  · simp [hc_bot, sub_eq_add_neg]
    by_cases hb_bot : b = ⊥
    · simp [hb_bot]
    · simp [add_top_of_ne_bot hb_bot]
  refine (toENNReal_le_toENNReal ?_).trans toENNReal_add_le
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  rw [sub_add_sub_cancel]

lemma toENNReal_sub_add_cancel {b a c : EReal} (hac : a ≤ c) (hcb : c ≤ b) :
    (b - c).toENNReal + (c - a).toENNReal = (b - a).toENNReal := by
  induction c
  · have ha : a = ⊥ := eq_bot_iff.mpr hac
    simp [ha]
  · rw [← toENNReal_add, sub_add_sub_cancel]
    · rwa [sub_nonneg (.inr <| coe_ne_top _) (.inr <| coe_ne_bot _)]
    · by_cases ha : a = ⊥
      · simp [ha]
      rwa [sub_nonneg _ (.inr ha)]
      exact .inr (hac.trans_lt (coe_lt_top _)).ne
  · have hb : b = ⊤ := eq_top_iff.mpr hcb
    simp [hb]

lemma continuousAt_sub {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊤) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊥) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 - p.2) p := by
  simp_rw [sub_eq_add_neg]
  refine ContinuousAt.comp (g := fun p : EReal × EReal ↦ p.1 + p.2)
    (f := fun p : EReal × EReal ↦ (p.1, -p.2)) ?_ ?_
  · refine EReal.continuousAt_add ?_ ?_
    · simp [h]
    · simp [h']
  · fun_prop

lemma continuousAt_const_sub {c x : EReal} (h' : x ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousAt (fun x : EReal ↦ c - x) x := by
  by_cases hc_top : c = ⊥
  · simp only [hc_top, bot_sub]
    exact continuous_const.continuousAt
  exact (EReal.continuousAt_sub h'.symm (Or.inl hc_top)).comp (f := fun x ↦ (c, x))
    (by fun_prop)

lemma continuousAt_sub_const {c x : EReal} (h' : x ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousAt (fun x : EReal ↦ x - c) x := by
  by_cases hc_top : c = ⊤
  · simp only [hc_top, sub_top]
    exact continuous_const.continuousAt
  exact (EReal.continuousAt_sub (Or.inr hc_top) h').comp (f := fun x ↦ (x, c)) (by fun_prop)

lemma continuous_coe_add (c : ℝ) : Continuous (fun x : EReal ↦ c + x) :=
  continuous_iff_continuousAt.2 fun x ↦ (EReal.continuousAt_add (p := (c, x))
    (.inl (EReal.coe_ne_top c)) (.inl (EReal.coe_ne_bot c))).comp
    (continuous_const.prodMk continuous_id).continuousAt

lemma continuous_coe_mul (c : ℝ) : Continuous (fun x : EReal ↦ c * x) := by
  by_cases hc0 : c = 0
  · simp only [hc0, EReal.coe_zero, zero_mul]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  have h_cont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (c, x) := by
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_ <;> exact Or.inl (by simp [hc0])
  refine h_cont.comp ?_
  fun_prop

lemma toENNReal_coe_mul_sub {c : ℝ≥0∞} (hc : c ≠ ∞) (x y : EReal) :
    ((c : EReal) * x - c * y).toENNReal = c * (x - y).toENNReal := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← mul_neg, ← left_distrib_of_nonneg_of_ne_top
    (coe_ennreal_nonneg c) fun h ↦ hc (coe_ennreal_eq_top_iff.mp h),
    toENNReal_mul (coe_ennreal_nonneg c), toENNReal_coe]

end EReal
