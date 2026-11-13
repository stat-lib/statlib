/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Order.CompletePartialOrder

/-! # ENNReal lemmas
-/

@[expose] public section

open ENNReal

namespace Function

/-- The finite support of a function `X : α → β` with top and zero elements is the set of points
where `X` is neither `⊤` nor `0`. -/
abbrev fsupport {α β : Type*} [Top β] [Zero β] (f : α → β) := {x | f x ≠ ⊤} ∩ {x | f x ≠ 0}

lemma fsupport_compl {α β : Type*} [Top β] [Zero β] (X : α → β) :
    X.fsupportᶜ = {ω | X ω = ⊤} ∪ {ω | X ω = 0} := by
  ext ω
  simp [-not_and]

lemma fsupport_compl_disjoint {α β : Type*} [Top β] [Zero β] (X : α → β) (h : (0 : β) ≠ ⊤) :
    Disjoint {ω | X ω = ⊤} {ω | X ω = 0} := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and_or]
  by_contra! h'
  rw [h'.1] at h'
  exact h.symm h'.2

lemma not_mem_fsupport_iff {α β : Type*} [Top β] [Zero β] (X : α → β) (ω : α) :
    ω ∉ X.fsupport ↔ X ω = ⊤ ∨ X ω = 0 := by
  rw [← Set.mem_compl_iff, fsupport_compl]
  simp

/-- The finite support of `(x, y) ↦ X x * Y y` is the product of the finite supports. -/
lemma fsupport_mul_prod {α β : Type*} (X : α → ℝ≥0∞) (Y : β → ℝ≥0∞) :
    (fun x : α × β ↦ X x.1 * Y x.2).fsupport = X.fsupport ×ˢ Y.fsupport := by
  ext x
  simp only [fsupport, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, ne_eq,
    ENNReal.mul_eq_top, mul_eq_zero, not_or]
  tauto

end Function

namespace ENNReal

lemma eq_of_div_eq_one {a b : ℝ≥0∞} (h : a / b = 1) : a = b := by
  by_cases hb_zero : b = 0
  · simp only [hb_zero] at h ⊢
    by_cases ha_zero : a = 0
    · exact ha_zero
    · simp [ENNReal.div_zero ha_zero] at h
  by_cases hb_top : b = ⊤
  · simp [hb_top] at h
  rwa [ENNReal.div_eq_one_iff hb_zero hb_top] at h

lemma inv_div_fsupport {α : Type*} (f g : α → ℝ≥0∞) :
    ∀ x ∈ g.fsupport, ((f / g) x)⁻¹ = g x / f x := by
  intro x hx
  simp only [Pi.div_apply]
  rw [ENNReal.inv_div]
  · exact Or.inl hx.1
  · exact Or.inl hx.2

lemma log_div (a b : ℝ≥0∞) : ENNReal.log (a / b) = ENNReal.log a - ENNReal.log b := by
  simp_rw [div_eq_mul_inv, ENNReal.log_mul_add, ENNReal.log_inv, sub_eq_add_neg]

/-- An extended nonnegative real number bounded by `1` gives an element of the unit interval. -/
lemma toReal_mem_unitInterval {r : ℝ≥0∞} (hr : r ≤ 1) : r.toReal ∈ unitInterval :=
  ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hr)⟩

section Ioo

open Set
open scoped NNReal

lemma toReal_image_Ioo {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    ENNReal.toReal '' (Ioo x y) = Ioo x.toReal y.toReal := by
  ext a
  refine
    ⟨fun ⟨a', ⟨hxa, hay⟩, ha⟩ ↦ ha ▸ ⟨toReal_strict_mono hay.ne_top hxa, toReal_strict_mono hy hay⟩,
    fun ⟨hxa, hay⟩ ↦ ⟨.ofReal a, ⟨?_, ?_⟩, toReal_ofReal (toReal_nonneg.trans_lt hxa).le⟩⟩
  · rw [← ofReal_toReal hx, ofReal_lt_ofReal_iff']
    exact ⟨hxa, toReal_nonneg.trans_lt hxa⟩
  · rw [← ofReal_toReal hy, ofReal_lt_ofReal_iff']
    exact ⟨hay, (toReal_nonneg.trans_lt hxa).trans hay⟩

@[simp]
lemma toReal_image_Ioo_top {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ENNReal.toReal '' (Ioo x ∞) = Ioi x.toReal := by
  ext a
  refine ⟨fun ⟨a', ⟨hxa, hay⟩, ha⟩ ↦ ha ▸ toReal_strict_mono hay.ne_top hxa,
    fun hxa ↦ ⟨.ofReal a, ⟨?_, ofReal_lt_top⟩, toReal_ofReal (toReal_nonneg.trans_lt hxa).le⟩⟩
  rw [← ofReal_toReal hx, ofReal_lt_ofReal_iff']
  exact ⟨hxa, toReal_nonneg.trans_lt hxa⟩

/-- A point of `[x, y]` (with `y ≠ ∞`) is a convex combination of `x` and `y` with `ℝ≥0` weights. -/
lemma exists_nnreal_smul_add_eq {x y z : ℝ≥0∞} (hy : y ≠ ∞) (hxz : x ≤ z) (hzy : z ≤ y) :
    ∃ u v : ℝ≥0, u + v = 1 ∧ u • x + v • y = z := by
  have hz : z ≠ ∞ := ne_top_of_le_ne_top hy hzy
  have hx : x ≠ ∞ := ne_top_of_le_ne_top hz hxz
  rcases eq_or_lt_of_le (hxz.trans hzy) with rfl | hxy
  · obtain rfl := le_antisymm hxz hzy
    exact ⟨1, 0, by simp, by simp⟩
  have hxy' : x.toReal < y.toReal := toReal_strict_mono hy hxy
  have hxy_ne : y.toReal - x.toReal ≠ 0 := (sub_pos.mpr hxy').ne'
  set v : ℝ := (z.toReal - x.toReal) / (y.toReal - x.toReal) with hv
  have hv0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr (toReal_mono hz hxz)) (sub_nonneg.mpr hxy'.le)
  have hv1 : v ≤ 1 :=
    (div_le_one (sub_pos.mpr hxy')).mpr (sub_le_sub_right (toReal_mono hy hzy) _)
  refine ⟨(1 - v).toNNReal, v.toNNReal, ?_, ?_⟩
  · rw [← Real.toNNReal_add (sub_nonneg.mpr hv1) hv0, sub_add_cancel, Real.toNNReal_one]
  · rw [← toReal_eq_toReal_iff' (by simp [smul_def, mul_ne_top, hx, hy]) hz]
    simp only [smul_def, smul_eq_mul, toReal_add (mul_ne_top coe_ne_top hx)
        (mul_ne_top coe_ne_top hy), toReal_mul, coe_toReal,
      Real.coe_toNNReal _ (sub_nonneg.mpr hv1), Real.coe_toNNReal _ hv0]
    rw [hv]
    field_simp
    ring

lemma preimage_toReal_Ioc {a b : ℝ} (h : 0 ≤ a) :
    ENNReal.toReal ⁻¹' Ioc a b = Ioc (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  ext x
  rcases lt_or_ge b a with hb | hb
  · rw [Ioc_eq_empty (not_lt.mpr hb.le), Ioc_eq_empty]
    · simp
    · rw [not_lt, ENNReal.ofReal_le_ofReal_iff h]
      exact hb.le
  simp only [mem_preimage, mem_Ioc]
  by_cases hx_top : x = ∞
  · simp [hx_top, not_lt.mpr h]
  rw [ENNReal.le_ofReal_iff_toReal_le hx_top (h.trans hb),
    ENNReal.ofReal_lt_iff_lt_toReal h hx_top]

end Ioo

/-- The truncated subtraction of finite extended nonnegative reals, as a real number. -/
lemma toReal_sub_eq_max_zero {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (a - b).toReal = max 0 (a.toReal - b.toReal) := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, toReal_zero, max_eq_left (sub_nonpos.2 (toReal_mono hb h))]
  · rw [toReal_sub_of_le h ha, max_eq_right (sub_nonneg.2 (toReal_mono ha h))]

section Topology

open Filter Topology

instance : (𝓝[<] ∞).NeBot := by
  have : NeZero ∞ := by constructor; simp
  exact ENNReal.nhdsLT_neBot

lemma tendsto_toReal_atTop : Tendsto (fun x : ℝ≥0∞ ↦ x.toReal) (𝓝[<] ∞) atTop := by
  rw [tendsto_atTop]
  intro y
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_Iio]
  have h_ge : ∀ᶠ (x : ℝ≥0∞) in 𝓝 ⊤, ENNReal.ofReal y ≤ x := eventually_ge_nhds (by simp)
  filter_upwards [h_ge] with x hx hx_lt_top
  rwa [← ENNReal.ofReal_le_iff_le_toReal hx_lt_top.ne]

lemma eventually_toReal_pos_nhdsGT_zero : ∀ᶠ (x : ℝ≥0∞) in 𝓝[>] 0, 0 < x.toReal := by
  have h_ne_top : ∀ᶠ x in 𝓝[>] (0 : ℝ≥0∞), x ≠ ∞ := eventually_ne_nhdsWithin (by simp)
  have h_pos : ∀ᶠ x in 𝓝[>] (0 : ℝ≥0∞), 0 < x := eventually_nhdsWithin_of_forall fun x hx ↦ hx
  filter_upwards [h_ne_top, h_pos] with x hx_ne_top hx_pos
  simp [ENNReal.toReal_pos_iff, hx_pos, hx_ne_top.lt_top]

lemma eventually_toReal_pos_nhdsLT_top : ∀ᶠ (x : ℝ≥0∞) in 𝓝[<] ∞, 0 < x.toReal := by
  have h_ne_top : ∀ᶠ x in 𝓝[<] (∞ : ℝ≥0∞), x ≠ ∞ :=
    eventually_nhdsWithin_of_forall fun x hx ↦ (Set.mem_Iio.mp hx).ne
  have h_pos : ∀ᶠ x in 𝓝[<] (∞ : ℝ≥0∞), 0 < x := by
    simp only [pos_iff_ne_zero, ne_eq]
    exact eventually_ne_nhdsWithin (by simp)
  filter_upwards [h_ne_top, h_pos] with x hx_ne_top hx_pos
  simp [ENNReal.toReal_pos_iff, hx_pos, hx_ne_top.lt_top]

lemma const_mul_le_liminf {c a : ℝ≥0∞} {u : ℕ → ℝ≥0∞}
    (h : Tendsto u atTop (𝓝 a)) : c * a ≤ liminf (fun n ↦ c * u n) atTop := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  exact (ENNReal.Tendsto.const_mul h (Or.inl ha0)).liminf_eq.ge

end Topology

end ENNReal
