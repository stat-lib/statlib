/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.AlphaLeakage.Operational
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Maximal α-leakage and the Arimoto–Sibson capacity

Liao, Kosut, Sankar and Calmon (*Tunable measures for information leakage and applications to
privacy-utility tradeoffs*, IEEE Trans. Inf. Theory 65(12), 2019, arXiv:1809.09231; journal
version of *A tunable measure for information leakage*, ISIT 2018, arXiv:1806.03332) define the
**maximal α-leakage** (their Definition 6) as the largest α-leakage about any randomized function
of the data: `L^max_a(X → Y) = sup_{U - X - Y} L_a(U → Y)`, the supremum ranging over all random
variables `U` on finite alphabets forming a Markov chain `U - X - Y`. Their Theorem 2 evaluates it
for `a ∈ (1, ∞)` as a channel capacity:
`L^max_a(X → Y) = sup_{P_X̃ ≪ P_X} I^S_a(X̃; Y) = sup_{P_X̃ ≪ P_X} I^A_a(X̃; Y)`.

We formalize the definition, with `U` ranging over the alphabets `Fin n` (any finite alphabet
reduces to these, `alphaLeakageRatio_le_maxAlphaLeakageRatio`), and prove Theorem 2 for
`a ∈ (1, ∞)` and finite alphabets.

* **Converse** (`arimotoSum_joint_le`). By Theorem 1, `L_a(U → Y) = I^A_a(U; Y)`; a weighted
  Hölder inequality bounds `I^A_a(U; Y)` by `I^S_a(X̃; Y)` for an explicit `P_X̃ ≪ P_X`.
* **Achievability** (`exists_arimotoSum_joint_eq`, `sibsonSum_le_maxAlphaLeakageRatio`). For
  `P_X̃` charging every atom of `P_X`, the paper's construction `U = (X, J)` (eqs. (104)–(109))
  attains `I^S_a(X̃; Y)` exactly; the conditional law of the label `J` is found with the
  intermediate value theorem, a step the paper leaves implicit. A general `P_X̃ ≪ P_X` is reached
  by mixing it with `P_X`, which is why the supremum need not be attained.

## Main definitions

* `maxAlphaLeakageRatio a μ κ`, `maxAlphaLeakage a μ κ`: maximal α-leakage (Definition 6), in
  multiplicative form and in nats.
* `sibsonCapacitySum a μ κ`: `sup_{ν ≪ μ} sibsonSum a ν κ`.

## Main statements

* `maxAlphaLeakageRatio_eq_sibsonCapacitySum`, `isLUB_sibsonMI`: **Theorem 2**, Sibson form of
  eq. (31a), `L^max_a(X → Y) = sup_{P_X̃ ≪ P_X} I^S_a(X̃; Y)`.
* `maxAlphaLeakageRatio_eq_iSup_arimotoSum`: **Theorem 2**, Arimoto form of eq. (31a),
  `L^max_a(X → Y) = sup_{P_X̃ ≪ P_X} I^A_a(X̃; Y)`.
* `isLUB_alphaLeakage`: Definition 6 in its original form, `maxAlphaLeakage a μ κ` is the least
  upper bound of the α-leakages `L_a(U → Y)`.
* `escort_escort_inv`: the escort operations of orders `a` and `1 / a` are inverse to each other.

The case `a = 1` of Theorem 2 (eq. (31b), mutual information) is not formalized; the case
`a = ∞` is `tendsto_maxAlphaLeakage_atTop` in `Statlib.Divergence.AlphaLeakage.Properties`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ ν : Measure α} {κ : Kernel α β} {ρ : Kernel α γ} {a : ℝ}

/-- The multiplicative form of the maximal α-leakage of Definition 6 of
Liao–Kosut–Sankar–Calmon: the supremum of `alphaLeakageRatio a P_{U,Y}` over all randomized
functions `U` of `X ∼ μ` (Markov kernels `ρ : α → Fin n`, for every `n`), where `U` and the output
`Y` of the channel `κ` are conditionally independent given `X`. -/
noncomputable def maxAlphaLeakageRatio (a : ℝ) (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ), alphaLeakageRatio a ((ρ ×ₖ κ) ∘ₘ μ)

/-- The **maximal α-leakage** `L^max_a(X → Y)` of Definition 6 of Liao–Kosut–Sankar–Calmon, for
`a ∈ (1, ∞)`, in nats: `a / (a - 1) · log` of `maxAlphaLeakageRatio a μ κ`, that is, the
supremum of the α-leakages `L_a(U → Y)` over all Markov chains `U - X - Y` with `U` on a finite
alphabet (see `isLUB_alphaLeakage` for this form). -/
noncomputable def maxAlphaLeakage (a : ℝ) (μ : Measure α) (κ : Kernel α β) : ℝ :=
  a / (a - 1) * Real.log (maxAlphaLeakageRatio a μ κ).toReal

/-- `sup_{P_X̃ ≪ P_X} ∑_y (∑_x P_X̃(x) P_{Y|X}(y | x) ^ a) ^ (1 / a)`, the multiplicative form of
the Sibson capacity of order `a` of the channel `κ` with inputs supported in the support of `μ`. -/
noncomputable def sibsonCapacitySum [Fintype α] [Fintype β] (a : ℝ) (μ : Measure α)
    (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ (ν : Measure α) (_ : IsProbabilityMeasure ν) (_ : ν ≪ μ), sibsonSum a ν κ

section Joint

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

omit [Fintype β] [Fintype γ] in
/-- The joint law of `(U, Y)` when `X ∼ μ`, `U ∼ ρ(X)` and `Y ∼ κ(X)`. -/
lemma kernelProd_bind_singleton [IsMarkovKernel ρ] [IsMarkovKernel κ] (u : γ) (y : β) :
    ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} = ∑ x, ρ x {u} * κ x {y} * μ {x} := by
  rw [Measure.bind_apply (measurableSet_singleton _) (ρ ×ₖ κ).aemeasurable, lintegral_fintype]
  simp_rw [Kernel.prod_apply, ← Set.singleton_prod_singleton, Measure.prod_prod]

omit [Fintype β] [Fintype γ] in
lemma kernelProd_bind_fst_singleton [Finite β] [IsMarkovKernel ρ] [IsMarkovKernel κ] (u : γ) :
    ((ρ ×ₖ κ) ∘ₘ μ).fst {u} = ∑ x, ρ x {u} * μ {x} := by
  have := Fintype.ofFinite β
  rw [fst_singleton_eq_sum]
  simp_rw [kernelProd_bind_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ,
    mul_one]

omit [Fintype β] [MeasurableSingletonClass β] in
lemma sum_joint_fst_singleton [IsProbabilityMeasure μ] [IsMarkovKernel ρ] :
    ∑ u, ∑ x, ρ x {u} * μ {x} = 1 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]
  simp [sum_measure_singleton]

omit [Fintype β] [MeasurableSingletonClass β] in
lemma sum_rpow_joint_fst_ne_zero (ha : 0 < a) [IsProbabilityMeasure μ] [IsMarkovKernel ρ] :
    ∑ u, (∑ x, ρ x {u} * μ {x}) ^ a ≠ 0 := by
  obtain ⟨u, hu⟩ : ∃ u, ∑ x, ρ x {u} * μ {x} ≠ 0 := by
    by_contra! h
    have h1 := sum_joint_fst_singleton (μ := μ) (ρ := ρ)
    simp [h] at h1
  exact ne_of_gt <| (pos_iff_ne_zero.2 ((ENNReal.rpow_eq_zero_iff_of_pos ha).not.2 hu)).trans_le
    (Finset.single_le_sum (f := fun u ↦ (∑ x, ρ x {u} * μ {x}) ^ a) (fun _ _ ↦ zero_le)
      (Finset.mem_univ u))

end Joint

section UpperBound

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

/-- **Converse half of Theorem 2** of Liao–Kosut–Sankar–Calmon: for a Markov chain `U - X - Y`,
`I^A_a(U; Y) ≤ sup_{P_X̃ ≪ P_X} I^S_a(X̃; Y)`. Writing `P_U(u) = ∑_x ρ x {u} μ {x}`, the weighted
Hölder inequality gives `P_{U,Y}(u, y) ^ a ≤ P_U(u) ^ (a - 1) ∑_x ρ x {u} μ {x} κ x {y} ^ a`, and
the right-hand side summed over `u` is `(∑_u P_U(u) ^ a) ∑_x P_X̃(x) κ x {y} ^ a` for the input law
`P_X̃(x) ∝ μ {x} ∑_u P_U(u) ^ (a - 1) ρ x {u}`, which is supported in the support of `μ`. This
replaces the escort change of variables and data-processing argument of eqs. (94)–(103). -/
lemma arimotoSum_joint_le (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (ρ : Kernel α γ) [IsMarkovKernel ρ] :
    arimotoSum a ((ρ ×ₖ κ) ∘ₘ μ) ≤ sibsonCapacitySum a μ κ := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hinv : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  set P : γ → ℝ≥0∞ := fun u ↦ ∑ x, ρ x {u} * μ {x}
  set c := ∑ u, P u ^ a
  have hP_le (u : γ) : P u ≤ 1 :=
    (Finset.single_le_sum (f := P) (fun _ _ ↦ zero_le) (Finset.mem_univ u)).trans
      (sum_joint_fst_singleton (μ := μ) (ρ := ρ)).le
  have hc0 : c ≠ 0 := sum_rpow_joint_fst_ne_zero ha0
  have hctop : c ≠ ∞ := ENNReal.sum_ne_top.2 fun u _ ↦
    ENNReal.rpow_ne_top_of_nonneg ha0.le (ne_top_of_le_ne_top ENNReal.one_ne_top (hP_le u))
  -- The input law `P_X̃`.
  set m : α → ℝ≥0∞ := fun x ↦ μ {x} * ∑ u, P u ^ (a - 1) * ρ x {u}
  set ν : Measure α := ∑ x, (c⁻¹ * m x) • Measure.dirac x
  have hν (x : α) : ν {x} = c⁻¹ * m x := sum_smul_dirac_apply_singleton _ _
  have hPa (u : γ) : P u ^ (a - 1) * P u = P u ^ a := by
    conv_rhs => rw [← sub_add_cancel a 1]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
  have hm_sum : ∑ x, m x = c := by
    simp_rw [m, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [← hPa u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  have hν_prob : IsProbabilityMeasure ν := ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hν, ← Finset.mul_sum, hm_sum]
    exact ENNReal.inv_mul_cancel hc0 hctop⟩
  have hν_ac : ν ≪ μ := by
    refine fun s hs ↦ (measure_null_iff_singleton s.to_countable).2 fun x hx ↦ ?_
    rw [hν]
    simp [m, (measure_null_iff_singleton s.to_countable).1 hs x hx]
  -- The weighted Hölder inequality, column by column.
  have h_y (y : β) : ∑ u, ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} ^ a ≤ c * ∑ x, ν {x} * κ x {y} ^ a := by
    have h_u (u : γ) : ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} ^ a ≤
        P u ^ (a - 1) * ∑ x, ρ x {u} * μ {x} * κ x {y} ^ a := by
      have h := ENNReal.inner_le_weight_mul_Lp_of_nonneg Finset.univ ha.le
        (fun x ↦ ρ x {u} * μ {x}) (fun x ↦ κ x {y})
      calc ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} ^ a
          = (∑ x, ρ x {u} * μ {x} * κ x {y}) ^ a := by
            rw [kernelProd_bind_singleton]
            congr 1
            exact Finset.sum_congr rfl fun x _ ↦ by ring
        _ ≤ (P u ^ (1 - a⁻¹) * (∑ x, ρ x {u} * μ {x} * κ x {y} ^ a) ^ a⁻¹) ^ a :=
            ENNReal.rpow_le_rpow h ha0.le
        _ = P u ^ (a - 1) * ∑ x, ρ x {u} * μ {x} * κ x {y} ^ a := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
              inv_mul_cancel₀ ha0.ne', ENNReal.rpow_one]
            congr 2
            field_simp
    calc ∑ u, ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} ^ a
        ≤ ∑ u, P u ^ (a - 1) * ∑ x, ρ x {u} * μ {x} * κ x {y} ^ a :=
          Finset.sum_le_sum fun u _ ↦ h_u u
      _ = ∑ x, m x * κ x {y} ^ a := by
          simp_rw [m, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun u _ ↦ by ring
      _ = c * ∑ x, ν {x} * κ x {y} ^ a := by
          simp_rw [hν, Finset.mul_sum, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
  have hc_rpow0 : c ^ a⁻¹ ≠ 0 := (ENNReal.rpow_eq_zero_iff_of_pos (inv_pos.2 ha0)).not.2 hc0
  have hc_rpow_top : c ^ a⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hinv hctop
  calc arimotoSum a ((ρ ×ₖ κ) ∘ₘ μ)
      = (∑ y, (∑ u, ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} ^ a) ^ a⁻¹) / c ^ a⁻¹ := by
        simp_rw [arimotoSum, kernelProd_bind_fst_singleton]
        rfl
    _ ≤ (∑ y, (c * ∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹) / c ^ a⁻¹ := by
        gcongr with y
        exact h_y y
    _ = sibsonSum a ν κ := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hinv, ← Finset.mul_sum, mul_comm (c ^ a⁻¹)]
        exact ENNReal.mul_div_cancel_right hc_rpow0 hc_rpow_top
    _ ≤ sibsonCapacitySum a μ κ := le_iSup₂_of_le ν hν_prob (le_iSup_of_le hν_ac le_rfl)

end UpperBound

section LowerBound

omit [MeasurableSpace α] in
/-- For `a > 1`, every value `t ∈ [(n + 1) ^ (1 - a), 1]` is the sum `∑_j w_j ^ a` of a probability
vector `w` on `n + 1` points: by the intermediate value theorem along the segment from the uniform
vector to a point mass. -/
lemma exists_sum_rpow_eq (ha : 1 < a) (n : ℕ) {t : ℝ} (ht₀ : ((n : ℝ) + 1) ^ (1 - a) ≤ t)
    (ht₁ : t ≤ 1) :
    ∃ w : Fin (n + 1) → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ ∑ j, w j ^ a = t := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  set w : ℝ → Fin (n + 1) → ℝ := fun s j ↦ (if j = 0 then s else 0) + (1 - s) / (n + 1)
  set f : ℝ → ℝ := fun s ↦ ∑ j, w s j ^ a
  have hw (j : Fin (n + 1)) : Continuous fun s ↦ w s j := by
    by_cases hj : j = 0 <;> simp only [w, hj, ite_true, ite_false] <;> fun_prop
  have hf : Continuous f := continuous_finsetSum _ fun j _ ↦
    (hw j).rpow_const fun _ ↦ Or.inr (by linarith)
  have hf0 : f 0 = ((n : ℝ) + 1) ^ (1 - a) := by
    simp only [f, w, ite_self, zero_add, sub_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.div_rpow zero_le_one hn.le, Real.one_rpow, Real.rpow_sub hn, Real.rpow_one]
    field_simp
  have hf1 : f 1 = 1 := by
    simp only [f, w, sub_self, zero_div, add_zero]
    rw [Fin.sum_univ_succ]
    simp [Real.zero_rpow (by linarith : a ≠ 0)]
  have ht : t ∈ Icc (f 0) (f 1) := by
    rw [hf0, hf1]
    exact ⟨ht₀, ht₁⟩
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hf.continuousOn ht
  refine ⟨w s, fun j ↦ add_nonneg (by split_ifs <;> linarith) (by
    have : 0 ≤ 1 - s := by linarith
    positivity), ?_, hs⟩
  simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp
  ring

omit [MeasurableSpace α] in
/-- `ℝ≥0∞` version of `exists_sum_rpow_eq`. -/
lemma exists_sum_rpow_eq_of_le (ha : 1 < a) (n : ℕ) {t : ℝ≥0∞}
    (ht₀ : ((n : ℝ≥0∞) + 1) ^ (1 - a) ≤ t) (ht₁ : t ≤ 1) :
    ∃ w : Fin (n + 1) → ℝ≥0∞, ∑ j, w j = 1 ∧ ∑ j, w j ^ a = t := by
  have ht : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ht₁
  have h₀ : ((n : ℝ) + 1) ^ (1 - a) ≤ t.toReal := by
    have := ENNReal.toReal_mono ht ht₀
    rwa [← ENNReal.toReal_rpow, ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one] at this
  have h₁ : t.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top ht₁
  obtain ⟨w, hw0, hw1, hwa⟩ := exists_sum_rpow_eq ha n h₀ h₁
  refine ⟨fun j ↦ ENNReal.ofReal (w j), ?_, ?_⟩
  · rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hw0 j, hw1, ENNReal.ofReal_one]
  · simp_rw [ENNReal.ofReal_rpow_of_nonneg (hw0 _) (by linarith : (0 : ℝ) ≤ a)]
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ Real.rpow_nonneg (hw0 j) _, hwa,
      ENNReal.ofReal_toReal ht]

omit [MeasurableSpace α] in
lemma exists_nat_rpow_le (ha : 1 < a) {t : ℝ≥0∞} (ht : t ≠ 0) :
    ∃ n : ℕ, ((n : ℝ≥0∞) + 1) ^ (1 - a) ≤ t := by
  have hb : 0 < a - 1 := by linarith
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hb.le) (ENNReal.inv_ne_top.2 ht) :
      t⁻¹ ^ (a - 1)⁻¹ ≠ ∞)
  refine ⟨n, ?_⟩
  have h : t⁻¹ ≤ ((n : ℝ≥0∞) + 1) ^ (a - 1) :=
    calc t⁻¹ = (t⁻¹ ^ (a - 1)⁻¹) ^ (a - 1) := (ENNReal.rpow_inv_rpow hb.ne' _).symm
      _ ≤ ((n : ℝ≥0∞) + 1) ^ (a - 1) :=
          ENNReal.rpow_le_rpow (hn.le.trans le_self_add) hb.le
  rw [show 1 - a = -(a - 1) by ring, ENNReal.rpow_neg]
  simpa using ENNReal.inv_le_inv.2 h

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

/-- **Achievability half of Theorem 2** of Liao–Kosut–Sankar–Calmon, for an input law `ν ≪ μ` that
charges every atom of `μ`: some randomized function `U = (X, J)` of `X` with `J ∈ Fin (n + 1)`
has `I^A_a(U; Y) = I^S_a(X̃; Y)` with `X̃ ∼ ν`. Given `X = x`, the label `J` is drawn from a
probability vector `w_x` with `∑_j w_x(j) ^ a ∝ ν {x} / μ {x} ^ a`, so that the escort
distribution of `U`, pushed to `X`, is `ν` (eqs. (104)–(109) of the paper; the paper leaves the
existence of `w_x` implicit, here it comes from the intermediate value theorem). -/
lemma exists_arimotoSum_joint_eq (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (hμν : ∀ x, μ {x} ≠ 0 → ν {x} ≠ 0) :
    ∃ (n : ℕ) (ρ : Kernel α (α × Fin (n + 1))), IsMarkovKernel ρ ∧
      arimotoSum a ((ρ ×ₖ κ) ∘ₘ μ) = sibsonSum a ν κ := by
  classical
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hinv : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  set S := Finset.univ.filter fun x : α ↦ μ {x} ≠ 0
  have hmem (x : α) : x ∈ S ↔ μ {x} ≠ 0 := by simp [S]
  have hS : S.Nonempty := by
    by_contra h
    have h0 : ∀ x, μ {x} = 0 := fun x ↦ by
      by_contra hx
      exact h ⟨x, (hmem x).2 hx⟩
    have := sum_measure_singleton (μ := μ) (s := Finset.univ)
    simp [h0] at this
  have hμa0 (x : α) (hx : μ {x} ≠ 0) : μ {x} ^ a ≠ 0 :=
    (ENNReal.rpow_eq_zero_iff_of_pos ha0).not.2 hx
  have hμatop (x : α) : μ {x} ^ a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha0.le (measure_ne_top _ _)
  -- The normalization `λ = min_{x ∈ supp μ} μ {x} ^ a / ν {x}` and the targets `t x ≤ 1`.
  set lam := S.inf' hS fun x ↦ μ {x} ^ a / ν {x}
  obtain ⟨x₁, hx₁S, hx₁⟩ := Finset.exists_mem_eq_inf' hS fun x ↦ μ {x} ^ a / ν {x}
  have hx₁ : lam = μ {x₁} ^ a / ν {x₁} := hx₁
  have hlam0 : lam ≠ 0 := by
    rw [hx₁]
    exact ENNReal.div_ne_zero.2 ⟨hμa0 x₁ ((hmem x₁).1 hx₁S), measure_ne_top ν _⟩
  set t : α → ℝ≥0∞ := fun x ↦ lam * ν {x} / μ {x} ^ a
  have ht_le (x : α) (hx : μ {x} ≠ 0) : t x ≤ 1 := by
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hμν x hx)) (Or.inl (measure_ne_top ν _))).1
      (Finset.inf'_le _ ((hmem x).2 hx))
  set tmin := S.inf' hS t
  have htmin0 : tmin ≠ 0 := by
    obtain ⟨x, hxS, hx⟩ := Finset.exists_mem_eq_inf' hS t
    have hx' : tmin = t x := hx
    rw [hx']
    exact ENNReal.div_ne_zero.2 ⟨mul_ne_zero hlam0 (hμν x ((hmem x).1 hxS)), hμatop x⟩
  obtain ⟨n, hn⟩ := exists_nat_rpow_le ha htmin0
  -- The conditional laws `w x` of the label `J`.
  have hw : ∀ x, ∃ w : Fin (n + 1) → ℝ≥0∞, ∑ j, w j = 1 ∧ (μ {x} ≠ 0 → ∑ j, w j ^ a = t x) := by
    intro x
    by_cases hx : μ {x} = 0
    · exact ⟨fun j ↦ if j = 0 then 1 else 0, by simp, fun h ↦ absurd hx h⟩
    · obtain ⟨w, hw1, hwa⟩ := exists_sum_rpow_eq_of_le ha n
        (hn.trans (Finset.inf'_le _ ((hmem x).2 hx))) (ht_le x hx)
      exact ⟨w, hw1, fun _ ↦ hwa⟩
  choose w hw1 hwa using hw
  have hkey (x : α) : (∑ j, w x j ^ a) * μ {x} ^ a = lam * ν {x} := by
    by_cases hx : μ {x} = 0
    · have hνx : ν {x} = 0 := hνμ hx
      rw [hx, hνx, ENNReal.zero_rpow_of_pos ha0, mul_zero, mul_zero]
    · rw [hwa x hx, ENNReal.div_mul_cancel (hμa0 x hx) (hμatop x)]
  -- The randomized function `U = (X, J)`.
  set W : α → α × Fin (n + 1) → ℝ≥0∞ := fun x p ↦ if p.1 = x then w x p.2 else 0
  set ρ : Kernel α (α × Fin (n + 1)) :=
    Kernel.ofFunOfCountable fun x ↦ ∑ p, W x p • Measure.dirac p
  have hρ (x : α) (p : α × Fin (n + 1)) : ρ x {p} = W x p := sum_smul_dirac_apply_singleton _ _
  have hρM : IsMarkovKernel ρ := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hρ]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x (fun x' _ hx' ↦ by simp [W, hx'])
      (by simp)]
    simpa [W] using hw1 x⟩⟩
  have hJ (x' : α) (j : Fin (n + 1)) (y : β) :
      ((ρ ×ₖ κ) ∘ₘ μ) {((x', j), y)} = w x' j * κ x' {y} * μ {x'} := by
    rw [kernelProd_bind_singleton,
      Finset.sum_eq_single x' (fun x _ hx ↦ by simp [hρ, W, Ne.symm hx]) (by simp)]
    simp [hρ, W]
  have hP (x' : α) (j : Fin (n + 1)) : ∑ x, ρ x {(x', j)} * μ {x} = w x' j * μ {x'} := by
    rw [Finset.sum_eq_single x' (fun x _ hx ↦ by simp [hρ, W, Ne.symm hx]) (by simp)]
    simp [hρ, W]
  have hnum (y : β) : ∑ u, ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} ^ a = lam * ∑ x, ν {x} * κ x {y} ^ a := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp_rw [hJ, ENNReal.mul_rpow_of_nonneg _ _ ha0.le]
    rw [← Finset.sum_mul, ← Finset.sum_mul, mul_right_comm, hkey, mul_assoc]
  have hden : ∑ u, (∑ x, ρ x {u} * μ {x}) ^ a = lam := by
    rw [Fintype.sum_prod_type]
    simp_rw [hP, ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ← Finset.sum_mul, hkey, ← Finset.mul_sum,
      sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
  have hlam_rpow0 : lam ^ a⁻¹ ≠ 0 := (ENNReal.rpow_eq_zero_iff_of_pos (inv_pos.2 ha0)).not.2 hlam0
  have hlam_rpow_top : lam ^ a⁻¹ ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg hinv ?_
    rw [hx₁]
    exact ENNReal.div_ne_top (hμatop x₁) (hμν x₁ ((hmem x₁).1 hx₁S))
  refine ⟨n, ρ, hρM, ?_⟩
  simp_rw [arimotoSum, kernelProd_bind_fst_singleton, hden, hnum,
    ENNReal.mul_rpow_of_nonneg _ _ hinv, ← Finset.mul_sum, mul_comm (lam ^ a⁻¹)]
  exact ENNReal.mul_div_cancel_right hlam_rpow0 hlam_rpow_top

end LowerBound

section MainTheorem

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Relabelling the alphabet `γ` of `U` as `Fin (card γ)` shows that every randomized function
`U` of `X` on a finite alphabet is covered by the supremum defining `maxAlphaLeakageRatio`. -/
lemma alphaLeakageRatio_le_maxAlphaLeakageRatio [Finite α] [Finite β] [Finite γ] (ha : 1 < a)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] (ρ : Kernel α γ) [IsMarkovKernel ρ] :
    alphaLeakageRatio a ((ρ ×ₖ κ) ∘ₘ μ) ≤ maxAlphaLeakageRatio a μ κ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  set e := Fintype.equivFin γ
  have he : Measurable e := measurable_of_finite _
  have hmap (x : α) (u : γ) : ρ.map e x {e u} = ρ x {u} := by
    rw [Kernel.map_apply' _ he _ (measurableSet_singleton _)]
    congr 1
    ext v
    simp
  have := Kernel.IsMarkovKernel.map ρ he
  have h1 (y : β) : ∑ v, ((ρ.map e ×ₖ κ) ∘ₘ μ) {(v, y)} ^ a =
      ∑ u, ((ρ ×ₖ κ) ∘ₘ μ) {(u, y)} ^ a := by
    rw [← e.sum_comp (fun v ↦ ((ρ.map e ×ₖ κ) ∘ₘ μ) {(v, y)} ^ a)]
    simp_rw [kernelProd_bind_singleton, hmap]
  have h2 : ∑ v, ((ρ.map e ×ₖ κ) ∘ₘ μ).fst {v} ^ a = ∑ u, ((ρ ×ₖ κ) ∘ₘ μ).fst {u} ^ a := by
    rw [← e.sum_comp (fun v ↦ ((ρ.map e ×ₖ κ) ∘ₘ μ).fst {v} ^ a)]
    simp_rw [kernelProd_bind_fst_singleton, hmap]
  have h_eq : arimotoSum a ((ρ.map e ×ₖ κ) ∘ₘ μ) = arimotoSum a ((ρ ×ₖ κ) ∘ₘ μ) := by
    simp_rw [arimotoSum, h1, h2]
  rw [alphaLeakageRatio_eq_arimotoSum ha, ← h_eq, ← alphaLeakageRatio_eq_arimotoSum ha]
  exact le_iSup_of_le (Fintype.card γ) <| le_iSup₂_of_le (ρ.map e) this le_rfl

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Fintype γ]
  [MeasurableSingletonClass γ] in
/-- `ν ↦ ∑_y (∑_x ν {x} κ x {y} ^ a) ^ (1 / a)` grows at least like `s ^ (1 / a)` when `ν` is
replaced by `s • ν + (1 - s) • μ`. -/
lemma rpow_inv_mul_sibsonSum_le (ha : 0 < a) (s : ℝ≥0∞) :
    s ^ a⁻¹ * sibsonSum a ν κ ≤ sibsonSum a (s • ν + (1 - s) • μ) κ := by
  rw [sibsonSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 ha.le), Finset.mul_sum]
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun x _ ↦ ?_) (inv_nonneg.2 ha.le)
  rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, add_mul, mul_assoc]
  exact le_self_add

/-- **Achievability half of Theorem 2** of Liao–Kosut–Sankar–Calmon: every `I^S_a(X̃; Y)` with
`P_X̃ ≪ P_X` is approached by α-leakages `L_a(U → Y)` of randomized functions `U` of `X`. We mix
`P_X̃` with `P_X` so that it charges every atom of `P_X`, and apply
`exists_arimotoSum_joint_eq`. -/
lemma sibsonSum_le_maxAlphaLeakageRatio (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) :
    sibsonSum a ν κ ≤ maxAlphaLeakageRatio a μ κ := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  refine ENNReal.le_of_forall_lt_one_mul_le fun s hs ↦ ?_
  have hs1 : 1 - s ≠ 0 := (tsub_pos_of_lt hs).ne'
  set ν' := s • ν + (1 - s) • μ
  have hν' (x : α) : ν' {x} = s * ν {x} + (1 - s) * μ {x} := by
    simp [ν']
  have : IsProbabilityMeasure ν' := ⟨by
    simp [ν', add_tsub_cancel_of_le hs.le]⟩
  have hν'μ : ν' ≪ μ := by
    refine fun t ht ↦ (measure_null_iff_singleton t.to_countable).2 fun x hx ↦ ?_
    have hμx := (measure_null_iff_singleton t.to_countable).1 ht x hx
    rw [hν', hμx, hνμ hμx]
    simp
  have hμν' (x : α) (hx : μ {x} ≠ 0) : ν' {x} ≠ 0 := by
    rw [hν']
    exact fun h ↦ mul_ne_zero hs1 hx (add_eq_zero.1 h).2
  obtain ⟨n, ρ, hρ, h_eq⟩ := exists_arimotoSum_joint_eq (κ := κ) ha hν'μ hμν'
  calc s * sibsonSum a ν κ ≤ s ^ a⁻¹ * sibsonSum a ν κ := by
        gcongr
        simpa using ENNReal.rpow_le_rpow_of_exponent_ge hs.le (inv_le_one_of_one_le₀ ha.le)
    _ ≤ sibsonSum a ν' κ := rpow_inv_mul_sibsonSum_le ha0 s
    _ = alphaLeakageRatio a ((ρ ×ₖ κ) ∘ₘ μ) := by rw [alphaLeakageRatio_eq_arimotoSum ha, h_eq]
    _ ≤ maxAlphaLeakageRatio a μ κ := alphaLeakageRatio_le_maxAlphaLeakageRatio ha ρ

omit [Fintype γ] [MeasurableSingletonClass γ] in
/-- **Theorem 2 of Liao–Kosut–Sankar–Calmon** (eq. (31a), Sibson form), multiplicative form: for
`a ∈ (1, ∞)` the maximal α-leakage is the Sibson capacity of order `a` of the channel over inputs
supported in the support of `P_X`:
`L^max_a(X → Y) = sup_{P_X̃ ≪ P_X} I^S_a(X̃; Y)`. -/
theorem maxAlphaLeakageRatio_eq_sibsonCapacitySum (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] : maxAlphaLeakageRatio a μ κ = sibsonCapacitySum a μ κ := by
  refine le_antisymm (iSup_le fun n ↦ iSup₂_le fun ρ _ ↦ ?_) (iSup₂_le fun ν _ ↦ iSup_le
    fun hνμ ↦ sibsonSum_le_maxAlphaLeakageRatio ha hνμ)
  rw [alphaLeakageRatio_eq_arimotoSum ha]
  exact arimotoSum_joint_le ha ρ

end MainTheorem

section Arimoto

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [Fintype β] [MeasurableSingletonClass β] in
/-- The escort operation of order `a` inverts the escort operation of order `1 / a`. -/
lemma escort_escort_inv (ha : 0 < a) [IsProbabilityMeasure ν] : escort a (escort a⁻¹ ν) = ν := by
  set T := ∑ x, ν {x} ^ a⁻¹
  have hT0 : T ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x, ν {x} ≠ 0 := by
      by_contra! h
      have := sum_measure_singleton (μ := ν) (s := Finset.univ)
      simp [h] at this
    exact ne_of_gt <| (pos_iff_ne_zero.2 ((ENNReal.rpow_eq_zero_iff_of_pos (inv_pos.2 ha)).not.2
      hx)).trans_le (Finset.single_le_sum (f := fun x ↦ ν {x} ^ a⁻¹) (fun _ _ ↦ zero_le)
        (Finset.mem_univ x))
  have hTtop : T ≠ ∞ := ENNReal.sum_ne_top.2 fun x _ ↦
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ha.le) (measure_ne_top ν _)
  have hc0 : T⁻¹ ^ a ≠ 0 := (ENNReal.rpow_eq_zero_iff_of_pos ha).not.2 (ENNReal.inv_ne_zero.2 hTtop)
  have hctop : T⁻¹ ^ a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha.le (ENNReal.inv_ne_top.2 hT0)
  have h_pow (x : α) : escort a⁻¹ ν {x} ^ a = T⁻¹ ^ a * ν {x} := by
    rw [escort_singleton, ENNReal.mul_rpow_of_nonneg _ _ ha.le, ENNReal.rpow_inv_rpow ha.ne']
  refine Measure.ext_iff_singleton.2 fun x ↦ ?_
  rw [escort_singleton]
  simp_rw [h_pow, ← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one,
    ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]

/-- **Theorem 2 of Liao–Kosut–Sankar–Calmon** (eq. (31a), Arimoto form), multiplicative form:
`L^max_a(X → Y) = sup_{P_X̃ ≪ P_X} I^A_a(X̃; Y)` for `a ∈ (1, ∞)`. The Sibson and Arimoto
suprema agree because the escort operation is a bijection of the input laws supported in the
support of `P_X` (Csiszár's observation, [43, Thm. 5] in the paper). -/
theorem maxAlphaLeakageRatio_eq_iSup_arimotoSum (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] : maxAlphaLeakageRatio a μ κ =
      ⨆ (ν : Measure α) (_ : IsProbabilityMeasure ν) (_ : ν ≪ μ), arimotoSum a (ν ⊗ₘ κ) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  rw [maxAlphaLeakageRatio_eq_sibsonCapacitySum ha]
  refine le_antisymm (iSup₂_le fun ν hν ↦ iSup_le fun hνμ ↦ ?_)
    (iSup₂_le fun ν hν ↦ iSup_le fun hνμ ↦ ?_)
  · have := isProbabilityMeasure_escort (μ := ν) (inv_pos.2 ha0) (IsProbabilityMeasure.ne_zero ν)
    refine le_iSup₂_of_le (escort a⁻¹ ν) this <| le_iSup_of_le
      ((escort_absolutelyContinuous (inv_pos.2 ha0)).trans hνμ) (le_of_eq ?_)
    rw [arimotoSum_compProd ha0.le, escort_escort_inv ha0]
  · have := isProbabilityMeasure_escort (μ := ν) ha0 (IsProbabilityMeasure.ne_zero ν)
    rw [arimotoSum_compProd ha0.le]
    exact le_iSup₂_of_le (escort a ν) this <| le_iSup_of_le
      ((escort_absolutelyContinuous ha0).trans hνμ) le_rfl

end Arimoto

section LogForm

omit [MeasurableSpace α] in
/-- Transfers a supremum in `ℝ≥0∞` of quantities `≥ 1` through `r ↦ a / (a - 1) · log r`. -/
lemma isLUB_image_mul_log_toReal (ha : 1 < a) {A : Set ℝ≥0∞} (hA : ∀ r ∈ A, 1 ≤ r)
    (hne : A.Nonempty) (htop : sSup A ≠ ∞) :
    IsLUB ((fun r : ℝ≥0∞ ↦ a / (a - 1) * Real.log r.toReal) '' A)
      (a / (a - 1) * Real.log (sSup A).toReal) := by
  have hc : 0 < a / (a - 1) := div_pos (by linarith) (by linarith)
  have h_one (r : ℝ≥0∞) (hr : r ∈ A) : 1 ≤ r.toReal := by
    have hrtop : r ≠ ∞ := ne_top_of_le_ne_top htop (le_sSup hr)
    simpa using ENNReal.toReal_mono hrtop (hA r hr)
  obtain ⟨r₀, hr₀⟩ := hne
  have hS1 : 1 ≤ (sSup A).toReal :=
    (h_one r₀ hr₀).trans (ENNReal.toReal_mono htop (le_sSup hr₀))
  refine ⟨?_, fun b hb ↦ ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [h_one r hr])
      (ENNReal.toReal_mono htop (le_sSup hr))) hc.le
  by_contra! hlt
  set q := Real.exp (b / (a / (a - 1)))
  have hq : q < (sSup A).toReal := by
    rw [← Real.exp_log (by linarith : 0 < (sSup A).toReal)]
    exact Real.exp_lt_exp.2 ((div_lt_iff₀' hc).2 hlt)
  have hqS : ENNReal.ofReal q < sSup A :=
    (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le htop).2 hq
  obtain ⟨r, hr, hqr⟩ := lt_sSup_iff.1 hqS
  have hrtop : r ≠ ∞ := ne_top_of_le_ne_top htop (le_sSup hr)
  have hqr' : q < r.toReal := (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le hrtop).1 hqr
  have hbr : b < a / (a - 1) * Real.log r.toReal := by
    rw [← div_lt_iff₀' hc, ← Real.exp_lt_exp, Real.exp_log (by linarith [h_one r hr])]
    exact hqr'
  exact absurd (hb ⟨r, hr, rfl⟩) (not_le.2 hbr)

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass β] in
lemma sibsonCapacitySum_le_card (ha : 0 < a) [IsMarkovKernel κ] :
    sibsonCapacitySum a μ κ ≤ Fintype.card β :=
  iSup₂_le fun _ _ ↦ iSup_le fun _ ↦ sibsonSum_le_card ha

omit [Fintype α] [Fintype β] in
lemma maxAlphaLeakageRatio_ne_top [Finite α] [Finite β] (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] : maxAlphaLeakageRatio a μ κ ≠ ∞ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [maxAlphaLeakageRatio_eq_sibsonCapacitySum ha]
  exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (sibsonCapacitySum_le_card (zero_lt_one.trans ha))

/-- **Theorem 2 of Liao–Kosut–Sankar–Calmon** (eq. (31a), Sibson form): for `a ∈ (1, ∞)`,
`L^max_a(X → Y) = sup_{P_X̃ ≪ P_X} I^S_a(X̃; Y)`, as a least upper bound of real numbers. -/
theorem isLUB_sibsonMI (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    IsLUB {r | ∃ ν : Measure α, IsProbabilityMeasure ν ∧ ν ≪ μ ∧ r = sibsonMI a ν κ}
      (maxAlphaLeakage a μ κ) := by
  set A := {r : ℝ≥0∞ | ∃ ν : Measure α, IsProbabilityMeasure ν ∧ ν ≪ μ ∧ r = sibsonSum a ν κ}
  have hA : sSup A = maxAlphaLeakageRatio a μ κ := by
    rw [maxAlphaLeakageRatio_eq_sibsonCapacitySum ha]
    refine le_antisymm (sSup_le ?_)
      (iSup₂_le fun ν hν ↦ iSup_le fun hνμ ↦ le_sSup ⟨ν, hν, hνμ, rfl⟩)
    rintro _ ⟨ν, hν, hνμ, rfl⟩
    exact le_iSup₂_of_le ν hν (le_iSup_of_le hνμ le_rfl)
  have hset : {r | ∃ ν : Measure α, IsProbabilityMeasure ν ∧ ν ≪ μ ∧ r = sibsonMI a ν κ} =
      (fun r : ℝ≥0∞ ↦ a / (a - 1) * Real.log r.toReal) '' A := by
    ext r
    constructor
    · rintro ⟨ν, hν, hνμ, rfl⟩
      exact ⟨_, ⟨ν, hν, hνμ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨ν, hν, hνμ, rfl⟩, rfl⟩
      exact ⟨ν, hν, hνμ, rfl⟩
  rw [hset, maxAlphaLeakage, ← hA]
  refine isLUB_image_mul_log_toReal ha ?_ ⟨_, μ, inferInstance, Measure.AbsolutelyContinuous.rfl,
    rfl⟩ (hA ▸ maxAlphaLeakageRatio_ne_top ha)
  rintro _ ⟨ν, hν, -, rfl⟩
  exact one_le_sibsonSum ha.le

omit [Fintype α] [Fintype β] in
/-- **Definition 6 of Liao–Kosut–Sankar–Calmon**, in its original form: for `a ∈ (1, ∞)`,
`maxAlphaLeakage a μ κ` is the supremum of the α-leakages `L_a(U → Y)` over all randomized
functions `U` of `X` on finite alphabets, `U - X - Y`. -/
theorem isLUB_alphaLeakage [Finite α] [Finite β] (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] :
    IsLUB {r | ∃ (n : ℕ) (ρ : Kernel α (Fin n)), IsMarkovKernel ρ ∧
      r = alphaLeakage a ((ρ ×ₖ κ) ∘ₘ μ)} (maxAlphaLeakage a μ κ) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  set A := {r : ℝ≥0∞ | ∃ (n : ℕ) (ρ : Kernel α (Fin n)), IsMarkovKernel ρ ∧
    r = alphaLeakageRatio a ((ρ ×ₖ κ) ∘ₘ μ)}
  have hA : sSup A = maxAlphaLeakageRatio a μ κ := by
    refine le_antisymm (sSup_le ?_)
      (iSup_le fun n ↦ iSup₂_le fun ρ hρ ↦ le_sSup ⟨n, ρ, hρ, rfl⟩)
    rintro _ ⟨n, ρ, hρ, rfl⟩
    exact le_iSup_of_le n (le_iSup₂_of_le ρ hρ le_rfl)
  have hset : {r | ∃ (n : ℕ) (ρ : Kernel α (Fin n)), IsMarkovKernel ρ ∧
      r = alphaLeakage a ((ρ ×ₖ κ) ∘ₘ μ)} =
      (fun r : ℝ≥0∞ ↦ a / (a - 1) * Real.log r.toReal) '' A := by
    ext r
    constructor
    · rintro ⟨n, ρ, hρ, rfl⟩
      exact ⟨_, ⟨n, ρ, hρ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨n, ρ, hρ, rfl⟩, rfl⟩
      exact ⟨n, ρ, hρ, rfl⟩
  rw [hset, maxAlphaLeakage, ← hA]
  refine isLUB_image_mul_log_toReal ha ?_ ⟨_, 1, Kernel.deterministic (fun _ ↦ 0) measurable_const,
    inferInstance, rfl⟩ (hA ▸ maxAlphaLeakageRatio_ne_top ha)
  rintro _ ⟨n, ρ, hρ, rfl⟩
  rw [alphaLeakageRatio_eq_arimotoSum ha]
  exact one_le_arimotoSum ha.le

end LogForm

end InformationTheory
