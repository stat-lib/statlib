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
  simp [-not_and, not_and_or]

lemma fsupport_compl_disjoint {α β : Type*} [Top β] [Zero β] (X : α → β) (h : (0 : β) ≠ ⊤) :
    Disjoint {ω | X ω = ⊤} {ω | X ω = 0} := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and_or]
  by_contra! h'
  rw [h'.1] at h'
  exact h.symm h'.2

lemma not_mem_fsupport_iff {α β : Type*} [Top β] [Zero β] (X : α → β) (ω : α) :
    ω ∉ X.fsupport ↔ X ω = ⊤ ∨ X ω = 0 := by
  rw [← Set.mem_compl_iff, fsupport_compl]
  simp

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
