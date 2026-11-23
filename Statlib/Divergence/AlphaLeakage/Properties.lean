/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.AlphaLeakage.Maximal
public import Statlib.Divergence.MaximalLeakage.Properties

/-!
# Properties of maximal α-leakage

We prove the properties of maximal α-leakage listed in Theorem 3, eq. (44) and Theorem 4 of
Liao, Kosut, Sankar and Calmon (*Tunable measures for information leakage and applications to
privacy-utility tradeoffs*, IEEE Trans. Inf. Theory 65(12), 2019, arXiv:1809.09231), for
`a ∈ (1, ∞)` and finite alphabets, together with the limit `a → ∞`. All of them go through the
closed form of Theorem 2 (`maxAlphaLeakageRatio_eq_sibsonCapacitySum`).

## Main statements

* `maxAlphaLeakage_nonneg`: eq. (42), `L^max_a(X → Y) ≥ 0`.
* `maxAlphaLeakage_eq_zero_of_forall_eq`, `maxAlphaLeakage_eq_zero_of_compProd_eq_prod`: the
  "if" direction of the equality case of eq. (42), no leakage under independence.
* `maxAlphaLeakage_le_maxLeakage`: eq. (44), `L^max_a(X → Y) ≤ L_MaxL(X → Y)`.
* `maxAlphaLeakage_le_log_card_input`, `maxAlphaLeakage_le_log_card_support`: eq. (43) for
  `a > 1`, `L^max_a(X → Y) ≤ log |X|` (indeed `≤ log |supp P_X|`).
* `maxAlphaLeakage_le_log_card`: Remark 1, `L^max_a(X → Y) ≤ log |Y|`.
* `maxAlphaLeakage_comp_le`: eq. (41a), the post-processing inequality.
* `maxAlphaLeakage_comp_le_comp`: eq. (41b), the linkage inequality.
* `log_sum_rpow_div_le_maxAlphaLeakage`: Theorem 4, the lower bound by the uniform input
  (without its equality condition).
* `sibsonMI_le_maxAlphaLeakage`, `alphaLeakage_le_maxAlphaLeakage`: `I^S_a(X̃; Y)` for
  `P_X̃ ≪ P_X`, and `L_a(X → Y)`, are lower bounds.
* `tendsto_maxAlphaLeakage_atTop`: `L^max_a(X → Y) → L_MaxL(X → Y)` as `a → ∞`, the case
  `α = ∞` of Theorem 2 (eq. (93)).

Not formalized: quasi-convexity (Theorem 3.1), monotonicity in `a` (Theorem 3.2; eq. (44) is proved
directly instead), the "only if" directions of the equality cases in Theorem 3.4, both
directions of the equality characterization accompanying eq. (43) (only the inequality is
proved), and Theorems 5 and 6 (sub-additivity and additivity).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ ν : Measure α} {κ : Kernel α β} {a : ℝ}

omit [MeasurableSpace α] in
/-- `r ↦ a / (a - 1) · log r` is monotone on `[1, ∞)` for `a > 1`. -/
lemma mul_log_toReal_le_mul_log_toReal (ha : 1 < a) {r s : ℝ≥0∞} (hr : 1 ≤ r) (hs : s ≠ ∞)
    (hrs : r ≤ s) : a / (a - 1) * Real.log r.toReal ≤ a / (a - 1) * Real.log s.toReal := by
  have hr' : 1 ≤ r.toReal := by
    simpa using ENNReal.toReal_mono (ne_top_of_le_ne_top hs hrs) hr
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (ENNReal.toReal_mono hs hrs))
    (div_nonneg (by linarith) (by linarith))

section Bounds

variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- Every `I^S_a(X̃; Y)` with `P_X̃ ≪ P_X` is a lower bound for `L^max_a(X → Y)`. -/
lemma sibsonMI_le_maxAlphaLeakage [Fintype α] [Fintype β] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) :
    sibsonMI a ν κ ≤ maxAlphaLeakage a μ κ :=
  mul_log_toReal_le_mul_log_toReal ha (one_le_sibsonSum ha.le) (maxAlphaLeakageRatio_ne_top ha)
    (sibsonSum_le_maxAlphaLeakageRatio ha hνμ)

/-- α-leakage is at most maximal α-leakage: `L_a(X → Y) ≤ L^max_a(X → Y)`. -/
lemma alphaLeakage_le_maxAlphaLeakage [Finite α] [Finite β] (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] : alphaLeakage a (μ ⊗ₘ κ) ≤ maxAlphaLeakage a μ κ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have ha0 : 0 < a := zero_lt_one.trans ha
  have := isProbabilityMeasure_escort (μ := μ) ha0 (IsProbabilityMeasure.ne_zero μ)
  rw [alphaLeakage_eq_arimotoMI ha, arimotoMI_compProd ha0.le]
  exact sibsonMI_le_maxAlphaLeakage ha (escort_absolutelyContinuous ha0)

lemma one_le_maxAlphaLeakageRatio [Finite α] [Finite β] (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] : 1 ≤ maxAlphaLeakageRatio a μ κ :=
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  (one_le_sibsonSum ha.le).trans
    (sibsonSum_le_maxAlphaLeakageRatio ha Measure.AbsolutelyContinuous.rfl)

/-- **Nonnegativity of maximal α-leakage**, eq. (42) of Liao–Kosut–Sankar–Calmon. -/
lemma maxAlphaLeakage_nonneg [Finite α] [Finite β] (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] : 0 ≤ maxAlphaLeakage a μ κ :=
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  (sibsonMI_nonneg ha).trans (sibsonMI_le_maxAlphaLeakage ha Measure.AbsolutelyContinuous.rfl)

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma maxLeakageSum_mono_of_absolutelyContinuous [Fintype β] (hνμ : ν ≪ μ) :
    maxLeakageSum ν κ ≤ maxLeakageSum μ κ :=
  Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x hx ↦
    le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y}) x fun h ↦ hx (hνμ h)

/-- Multiplicative form of `maxAlphaLeakage_le_maxLeakage`. -/
lemma maxAlphaLeakageRatio_le_maxLeakageSum_rpow [Finite α] [Fintype β] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    maxAlphaLeakageRatio a μ κ ≤ maxLeakageSum μ κ ^ (1 - a⁻¹) := by
  have := Fintype.ofFinite α
  have hb : 0 ≤ 1 - a⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ ha.le)
  rw [maxAlphaLeakageRatio_eq_sibsonCapacitySum ha]
  refine iSup₂_le fun ν _ ↦ iSup_le fun hνμ ↦ ?_
  exact (sibsonSum_le_maxLeakageSum_rpow ha).trans
    (ENNReal.rpow_le_rpow (maxLeakageSum_mono_of_absolutelyContinuous hνμ) hb)

/-- **Maximal α-leakage is at most maximal leakage**, eq. (44) of Liao–Kosut–Sankar–Calmon:
`L^max_a(X → Y) ≤ L_MaxL(X → Y) = I^S_∞(X; Y)` for `a ∈ (1, ∞)`. The paper derives it from the
monotonicity of `L^max_a` in `a`; here it follows from Hölder's inequality
(`sibsonSum_le_maxLeakageSum_rpow`). -/
theorem maxAlphaLeakage_le_maxLeakage [Finite α] [Fintype β] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] : maxAlphaLeakage a μ κ ≤ maxLeakage μ κ := by
  have := Fintype.ofFinite α
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb : 0 < 1 - a⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ ha)
  obtain ⟨x, hx⟩ : ∃ x, μ {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := μ) (s := Finset.univ)
    simp [h] at this
  have hL := one_le_toReal_maxLeakageSum (κ := κ) hx
  have h_le : (maxAlphaLeakageRatio a μ κ).toReal ≤ (maxLeakageSum μ κ).toReal ^ (1 - a⁻¹) := by
    rw [ENNReal.toReal_rpow]
    exact ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hb.le maxLeakageSum_ne_top)
      (maxAlphaLeakageRatio_le_maxLeakageSum_rpow ha)
  have h1 : 1 ≤ (maxAlphaLeakageRatio a μ κ).toReal := by
    simpa using ENNReal.toReal_mono (maxAlphaLeakageRatio_ne_top ha)
      (one_le_maxAlphaLeakageRatio (μ := μ) (κ := κ) ha)
  have h_log := Real.log_le_log (by linarith) h_le
  rw [Real.log_rpow (by linarith)] at h_log
  calc maxAlphaLeakage a μ κ ≤ a / (a - 1) * ((1 - a⁻¹) * Real.log (maxLeakageSum μ κ).toReal) :=
        mul_le_mul_of_nonneg_left h_log (div_nonneg ha0.le (by linarith))
    _ = maxLeakage μ κ := by
        rw [maxLeakage, ← mul_assoc]
        convert one_mul _ using 2
        field_simp

/-- `L^max_a(X → Y) ≤ log |Y|` (Remark 1 of Liao–Kosut–Sankar–Calmon). -/
lemma maxAlphaLeakage_le_log_card [Finite α] [Fintype β] (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] : maxAlphaLeakage a μ κ ≤ Real.log (Fintype.card β) := by
  have := Fintype.ofFinite α
  obtain ⟨x, hx⟩ : ∃ x, μ {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := μ) (s := Finset.univ)
    simp [h] at this
  exact (maxAlphaLeakage_le_maxLeakage ha).trans (maxLeakage_le_log_card hx)

/-- `L^max_a(X → Y) ≤ log |supp P_X|`, the inequality of eq. (43) of Liao–Kosut–Sankar–Calmon
for `a > 1`; its equality characterization is not formalized (the paper
states it with `|X|` for a fully supported `P_X`; see `maxAlphaLeakage_le_log_card_input`). -/
theorem maxAlphaLeakage_le_log_card_support [Fintype α] [Finite β] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] [DecidablePred fun x : α ↦ μ {x} ≠ 0] :
    maxAlphaLeakage a μ κ ≤ Real.log (Finset.univ.filter fun x : α ↦ μ {x} ≠ 0).card := by
  have := Fintype.ofFinite β
  obtain ⟨x, hx⟩ : ∃ x, μ {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := μ) (s := Finset.univ)
    simp [h] at this
  refine (maxAlphaLeakage_le_maxLeakage ha).trans
    (Real.log_le_log (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx]) ?_)
  simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top _) maxLeakageSum_le_card_support

/-- `L^max_a(X → Y) ≤ log |X|`, eq. (43) of Liao–Kosut–Sankar–Calmon for `a > 1`. -/
theorem maxAlphaLeakage_le_log_card_input [Fintype α] [Finite β] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    maxAlphaLeakage a μ κ ≤ Real.log (Fintype.card α) := by
  classical
  refine (maxAlphaLeakage_le_log_card_support ha).trans (Real.log_le_log ?_ ?_)
  · obtain ⟨x, hx⟩ : ∃ x, μ {x} ≠ 0 := by
      by_contra! h
      have := sum_measure_singleton (μ := μ) (s := Finset.univ)
      simp [h] at this
    exact_mod_cast Finset.card_pos.2 ⟨x, by simpa using hx⟩
  · exact_mod_cast Finset.card_filter_le _ _

/-- **Theorem 4 of Liao–Kosut–Sankar–Calmon** (lower bound, without its equality condition): for a
fully supported `P_X` and `a ∈ (1, ∞)`,
`L^max_a(X → Y) ≥ a / (a - 1) · log (∑_y ‖P_{Y|X}(y | ·)‖_a / |X| ^ (1 / a))`,
the Sibson mutual information at the uniform input. -/
theorem log_sum_rpow_div_le_maxAlphaLeakage [Fintype α] [Fintype β] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] (hμ : ∀ x, μ {x} ≠ 0) :
    a / (a - 1) * Real.log ((∑ y, (∑ x, κ x {y} ^ a) ^ a⁻¹) /
      (Fintype.card α : ℝ≥0∞) ^ a⁻¹).toReal ≤ maxAlphaLeakage a μ κ := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  set N : ℝ≥0∞ := (Fintype.card α : ℝ≥0∞)
  have hN0 : N ≠ 0 := by simp [N]
  have hNtop : N ≠ ∞ := ENNReal.natCast_ne_top _
  set ν : Measure α := ∑ x, N⁻¹ • Measure.dirac x
  have hν (x : α) : ν {x} = N⁻¹ := sum_smul_dirac_apply_singleton (fun _ ↦ N⁻¹) x
  have : IsProbabilityMeasure ν := ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hν, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hN0 hNtop⟩
  have hνμ : ν ≪ μ := fun s hs ↦ (measure_null_iff_singleton s.to_countable).2 fun x hx ↦
    absurd ((measure_null_iff_singleton s.to_countable).1 hs x hx) (hμ x)
  have h_eq : sibsonSum a ν κ = (∑ y, (∑ x, κ x {y} ^ a) ^ a⁻¹) / N ^ a⁻¹ := by
    simp_rw [sibsonSum, hν, ← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 ha0.le),
      ENNReal.inv_rpow, ← Finset.mul_sum, ENNReal.div_eq_inv_mul]
  rw [← h_eq]
  exact sibsonMI_le_maxAlphaLeakage ha hνμ

end Bounds

section DataProcessing

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [Finite γ] [MeasurableSingletonClass γ]

/-- Multiplicative form of `maxAlphaLeakage_comp_le`. -/
lemma maxAlphaLeakageRatio_comp_le (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] :
    maxAlphaLeakageRatio a μ (η ∘ₖ κ) ≤ maxAlphaLeakageRatio a μ κ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  rw [maxAlphaLeakageRatio_eq_sibsonCapacitySum ha, maxAlphaLeakageRatio_eq_sibsonCapacitySum ha]
  exact iSup₂_le fun ν hν ↦ iSup_le fun hνμ ↦
    (sibsonSum_comp_le ha.le η).trans (le_iSup₂_of_le ν hν (le_iSup_of_le hνμ le_rfl))

/-- **Post-processing inequality**, eq. (41a) of Liao–Kosut–Sankar–Calmon (Theorem 3.3): for a
Markov chain `X - Y - Z`, `L^max_a(X → Z) ≤ L^max_a(X → Y)`. -/
theorem maxAlphaLeakage_comp_le (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] :
    maxAlphaLeakage a μ (η ∘ₖ κ) ≤ maxAlphaLeakage a μ κ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  exact mul_log_toReal_le_mul_log_toReal ha (one_le_maxAlphaLeakageRatio ha)
    (maxAlphaLeakageRatio_ne_top ha) (maxAlphaLeakageRatio_comp_le ha η)

/-- Multiplicative form of `maxAlphaLeakage_comp_le_comp`. -/
lemma maxAlphaLeakageRatio_comp_le_comp (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] :
    maxAlphaLeakageRatio a μ (η ∘ₖ κ) ≤ maxAlphaLeakageRatio a (κ ∘ₘ μ) η := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  rw [maxAlphaLeakageRatio_eq_sibsonCapacitySum ha, maxAlphaLeakageRatio_eq_sibsonCapacitySum ha]
  refine iSup₂_le fun ν hν ↦ iSup_le fun hνμ ↦ (sibsonSum_comp_le_comp ha.le η).trans ?_
  exact le_iSup₂_of_le (κ ∘ₘ ν) inferInstance (le_iSup_of_le
    (hνμ.comp (ae_of_all _ fun _ ↦ Measure.AbsolutelyContinuous.rfl)) le_rfl)

/-- **Linkage inequality**, eq. (41b) of Liao–Kosut–Sankar–Calmon (Theorem 3.3): for a Markov
chain `X - Y - Z`, `L^max_a(X → Z) ≤ L^max_a(Y → Z)`, where `Y ∼ κ ∘ₘ μ`. -/
theorem maxAlphaLeakage_comp_le_comp (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] :
    maxAlphaLeakage a μ (η ∘ₖ κ) ≤ maxAlphaLeakage a (κ ∘ₘ μ) η := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  exact mul_log_toReal_le_mul_log_toReal ha (one_le_maxAlphaLeakageRatio ha)
    (maxAlphaLeakageRatio_ne_top ha) (maxAlphaLeakageRatio_comp_le_comp ha η)

end DataProcessing

section Limit

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- **Maximal α-leakage of order `∞` is maximal leakage**: as `a → ∞`, `L^max_a(X → Y)` tends to
`L_MaxL(X → Y) = log ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`. This is the case `α = ∞` of Theorem 2
of Liao–Kosut–Sankar–Calmon (eqs. (31a) and (93)), where `L^max_∞` is defined by continuous
extension. -/
theorem tendsto_maxAlphaLeakage_atTop [Fintype β] [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    Tendsto (fun a ↦ maxAlphaLeakage a μ κ) atTop (𝓝 (maxLeakage μ κ)) := by
  have := Fintype.ofFinite α
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_sibsonMI_atTop tendsto_const_nhds
    ((eventually_gt_atTop 1).mono fun _ ha ↦
      sibsonMI_le_maxAlphaLeakage ha Measure.AbsolutelyContinuous.rfl)
    ((eventually_gt_atTop 1).mono fun _ ha ↦ maxAlphaLeakage_le_maxLeakage ha)

/-- **No leakage under independence** (the "if" direction of the equality case of eq. (42) of
Liao–Kosut–Sankar–Calmon): if the rows of the channel coincide on the support of `P_X`, i.e. `X`
and `Y` are independent, then `L^max_a(X → Y) = 0`. The converse is not formalized here. -/
theorem maxAlphaLeakage_eq_zero_of_forall_eq [Finite β] (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] (h : ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → κ x = κ x') :
    maxAlphaLeakage a μ κ = 0 := by
  have := Fintype.ofFinite β
  exact le_antisymm ((maxAlphaLeakage_le_maxLeakage ha).trans (maxLeakage_eq_zero_iff.2 h).le)
    (maxAlphaLeakage_nonneg ha)

/-- **No leakage under independence**: if `μ ⊗ₘ κ = μ × (κ ∘ₘ μ)`, then `L^max_a(X → Y) = 0`. -/
theorem maxAlphaLeakage_eq_zero_of_compProd_eq_prod [Finite β] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] (h : μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ)) :
    maxAlphaLeakage a μ κ = 0 := by
  have := Fintype.ofFinite β
  exact maxAlphaLeakage_eq_zero_of_forall_eq ha
    (maxLeakage_eq_zero_iff.1 (maxLeakage_eq_zero_iff_compProd_eq_prod.2 h))

end Limit

end InformationTheory
