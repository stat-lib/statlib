/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Sibson and Arimoto mutual information on finite alphabets

Liao, Kosut, Sankar and Calmon (*Tunable measures for information leakage and applications to
privacy-utility tradeoffs*, IEEE Trans. Inf. Theory 65(12), 2019, arXiv:1809.09231) express their
tunable leakage measures through two Rényi-type generalizations of mutual information. For an
order `a ∈ (1, ∞)`, an input law `P_X` and a channel `P_{Y|X}` on finite alphabets,

* the **Sibson mutual information** (their eq. (7)) is
  `I^S_a(X; Y) = a / (a - 1) · log ∑_y (∑_x P_X(x) P_{Y|X}(y | x) ^ a) ^ (1 / a)`;
* the **Arimoto mutual information** (their eq. (9)) of a joint law `P_{X,Y}` is
  `I^A_a(X; Y) = a / (a - 1) · log (∑_y ‖P_{X,Y}(·, y)‖_a / ‖P_X‖_a)`.

We take these closed forms as definitions; the variational characterization
`I^S_a(X; Y) = min_{Q_Y} D_a(P_{X,Y} ‖ P_X × Q_Y)` of their eq. (6) and the decomposition
`I^A_a = H_a(X) - H^A_a(X | Y)` of their eq. (8) are not formalized. As in
`Statlib.Divergence.MaximalLeakage.Basic`, the definitions come in an `ℝ≥0∞`-valued
multiplicative form (`sibsonSum`, `arimotoSum`) and a real logarithmic form in nats
(`sibsonMI`, `arimotoMI`).

## Main definitions

* `sibsonSum a μ κ = ∑_y (∑_x μ {x} * κ x {y} ^ a) ^ a⁻¹` and `sibsonMI a μ κ`, its logarithm
  scaled by `a / (a - 1)`.
* `arimotoSum a π` and `arimotoMI a π` for a joint law `π` on `α × β`.
* `escort a μ`: the escort distribution `μ {x} ^ a / ∑_x' μ {x'} ^ a`.

## Main statements

* `arimotoSum_compProd`: Arimoto's quantity of `(X, Y)` is Sibson's quantity of the escort
  distribution of `X` (the change of variables in eqs. (100)–(103) of the paper).
* `one_le_sibsonSum`, `sibsonMI_nonneg`: Sibson mutual information is nonnegative.
* `sibsonSum_le_maxLeakageSum_rpow`, `sibsonMI_le_maxLeakage`: `I^S_a(X; Y) ≤ L(X → Y)`, which
  with Theorem 2 of the paper gives eq. (44).
* `sibsonSum_comp_le`, `sibsonSum_comp_le_comp`: data processing for Sibson mutual information
  under post- and pre-processing (used in Theorem 3 of the paper).
* `one_le_arimotoSum`, `arimotoMI_nonneg`: Arimoto mutual information is nonnegative (by
  Minkowski's inequality).
* `arimotoMI_compProd_comp_le`: the post-processing inequality for Arimoto mutual information
  (footnote 4 of the paper).
* `tendsto_sibsonSum_atTop`, `tendsto_sibsonMI_atTop`: as `a → ∞`, Sibson mutual information
  tends to the maximal leakage `maxLeakage μ κ` (eq. (12) of the paper, where `I^S_∞` is defined
  by continuous extension). This connects to `Statlib.Divergence.MaximalLeakage`.
* `ENNReal.Lp_finsetSum_le`: Minkowski's inequality for finite sums of vectors in `ℝ≥0∞`.

## Mapping to Liao–Kosut–Sankar–Calmon

* eq. (7) (Sibson MI), eq. (9) (Arimoto MI): `sibsonMI`, `arimotoMI` (definitions, `a ∈ (1, ∞)`).
* eq. (12): `tendsto_sibsonMI_atTop`.
* eqs. (100)–(103): `arimotoSum_compProd`.
* Definition 5 and Theorem 1: `Statlib.Divergence.AlphaLeakage.Operational`.
* Definition 6 and Theorem 2: `Statlib.Divergence.AlphaLeakage.Maximal`.
* Theorem 3, eq. (44), Theorem 4: `Statlib.Divergence.AlphaLeakage.Properties`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ ν : Measure α} {κ : Kernel α β} {π : Measure (α × β)} {a : ℝ}

/-- The sum `∑_y (∑_x P_X(x) P_{Y|X}(y | x) ^ a) ^ (1 / a)` whose logarithm, scaled by
`a / (a - 1)`, is the Sibson mutual information `sibsonMI a μ κ`. -/
noncomputable def sibsonSum [Fintype α] [Fintype β] (a : ℝ) (μ : Measure α) (κ : Kernel α β) :
    ℝ≥0∞ :=
  ∑ y, (∑ x, μ {x} * κ x {y} ^ a) ^ a⁻¹

/-- The **Sibson mutual information** of order `a` between an input `X ∼ μ` and the output `Y` of
the channel `κ`, in nats, in the closed form of eq. (7) of Liao–Kosut–Sankar–Calmon:
`I^S_a(X; Y) = a / (a - 1) · log ∑_y (∑_x P_X(x) P_{Y|X}(y | x) ^ a) ^ (1 / a)`.
It is meaningful for `a ∈ (0, 1) ∪ (1, ∞)`; the results of this library are for `a > 1`. -/
noncomputable def sibsonMI [Fintype α] [Fintype β] (a : ℝ) (μ : Measure α) (κ : Kernel α β) :
    ℝ :=
  a / (a - 1) * Real.log (sibsonSum a μ κ).toReal

/-- The ratio `∑_y ‖P_{X,Y}(·, y)‖_a / ‖P_X‖_a` whose logarithm, scaled by `a / (a - 1)`, is the
Arimoto mutual information `arimotoMI a π` of a joint law `π = P_{X,Y}`. -/
noncomputable def arimotoSum [Fintype α] [Fintype β] (a : ℝ) (π : Measure (α × β)) : ℝ≥0∞ :=
  (∑ y, (∑ x, π {(x, y)} ^ a) ^ a⁻¹) / (∑ x, π.fst {x} ^ a) ^ a⁻¹

/-- The **Arimoto mutual information** of order `a` of a joint law `π = P_{X,Y}`, in nats, in the
closed form of eq. (9) of Liao–Kosut–Sankar–Calmon:
`I^A_a(X; Y) = a / (a - 1) · log (∑_y (∑_x P_{X,Y}(x, y) ^ a) ^ (1 / a) / ‖P_X‖_a)`,
where `‖P_X‖_a = (∑_x P_X(x) ^ a) ^ (1 / a)`.
It is meaningful for `a ∈ (0, 1) ∪ (1, ∞)`; the results of this library are for `a > 1`. -/
noncomputable def arimotoMI [Fintype α] [Fintype β] (a : ℝ) (π : Measure (α × β)) : ℝ :=
  a / (a - 1) * Real.log (arimotoSum a π).toReal

/-- The **escort distribution** of order `a` of `μ`, with masses `μ {x} ^ a / ∑_x' μ {x'} ^ a`.
Liao–Kosut–Sankar–Calmon use it (eqs. (100)–(103)) to turn Arimoto into Sibson mutual
information. -/
noncomputable def escort [Fintype α] (a : ℝ) (μ : Measure α) : Measure α :=
  (∑ x, μ {x} ^ a)⁻¹ • ∑ x, μ {x} ^ a • Measure.dirac x

section Singletons

variable [Fintype α] [MeasurableSingletonClass α]

lemma sum_smul_dirac_apply_singleton (f : α → ℝ≥0∞) (x : α) :
    (∑ x', f x' • Measure.dirac x') {x} = f x := by
  simp only [sum_apply, smul_apply, MeasurableSet.singleton, Measure.dirac_apply', smul_eq_mul]
  rw [Finset.sum_eq_single x (fun b _ hb ↦ by
    simp [Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 hb)]) (by simp)]
  simp

lemma escort_singleton (a : ℝ) (μ : Measure α) (x : α) :
    escort a μ {x} = (∑ x', μ {x'} ^ a)⁻¹ * μ {x} ^ a := by
  rw [escort, smul_apply, sum_smul_dirac_apply_singleton, smul_eq_mul]

lemma isProbabilityMeasure_escort (ha : 0 < a) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    IsProbabilityMeasure (escort a μ) := by
  have h_ne : ∑ x, μ {x} ^ a ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x, μ {x} ≠ 0 := by
      by_contra! h
      exact hμ (Measure.ext_iff_singleton.2 fun x ↦ by simp [h x])
    exact ne_of_gt <| (ENNReal.rpow_pos (pos_iff_ne_zero.2 hx) (measure_ne_top μ _)).trans_le <|
      Finset.single_le_sum (f := fun x ↦ μ {x} ^ a) (fun _ _ ↦ zero_le) (Finset.mem_univ x)
  have h_top : ∑ x, μ {x} ^ a ≠ ∞ := ENNReal.sum_ne_top.2 fun x _ ↦
    ENNReal.rpow_ne_top_of_nonneg ha.le (measure_ne_top μ _)
  constructor
  rw [← Finset.coe_univ, ← sum_measure_singleton]
  simp_rw [escort_singleton, ← Finset.mul_sum]
  exact ENNReal.inv_mul_cancel h_ne h_top

lemma escort_absolutelyContinuous (ha : 0 < a) : escort a μ ≪ μ := by
  refine fun s hs ↦ (measure_null_iff_singleton s.to_countable).2 fun x hx ↦ ?_
  rw [escort_singleton, (measure_null_iff_singleton s.to_countable).1 hs x hx,
    ENNReal.zero_rpow_of_pos ha, mul_zero]

end Singletons

section Formulas

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [Fintype α] [Fintype β] in
lemma compProd_singleton_eq_mul [SFinite μ] [IsSFiniteKernel κ] (x : α) (y : β) :
    (μ ⊗ₘ κ) {(x, y)} = μ {x} * κ x {y} := by
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod (measurableSet_singleton x)
    (measurableSet_singleton y), lintegral_singleton, mul_comm]

/-- **Arimoto mutual information is Sibson mutual information at the escort input**:
`I^A_a(X; Y) = I^S_a(X_a; Y)` where `X_a` follows the escort distribution `escort a μ` of `X ∼ μ`.
This is the change of variables in eqs. (100)–(103) of Liao–Kosut–Sankar–Calmon. -/
lemma arimotoSum_compProd [SFinite μ] [IsMarkovKernel κ] (ha : 0 ≤ a) :
    arimotoSum a (μ ⊗ₘ κ) = sibsonSum a (escort a μ) κ := by
  have ha' : 0 ≤ a⁻¹ := inv_nonneg.2 ha
  simp_rw [arimotoSum, sibsonSum, Measure.fst_compProd, compProd_singleton_eq_mul, escort_singleton,
    ENNReal.mul_rpow_of_nonneg _ _ ha, mul_assoc, ← Finset.mul_sum,
    ENNReal.mul_rpow_of_nonneg _ _ ha', ENNReal.inv_rpow, ← Finset.mul_sum, div_eq_mul_inv,
    mul_comm]

/-- **Arimoto mutual information is Sibson mutual information at the escort input**, eqs.
(100)–(103) of Liao–Kosut–Sankar–Calmon. -/
lemma arimotoMI_compProd [SFinite μ] [IsMarkovKernel κ] (ha : 0 ≤ a) :
    arimotoMI a (μ ⊗ₘ κ) = sibsonMI a (escort a μ) κ := by
  rw [arimotoMI, sibsonMI, arimotoSum_compProd ha]

end Formulas

section Bounds

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass β] in
lemma sibsonSum_le_card (ha : 0 < a) [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    sibsonSum a ν κ ≤ Fintype.card β := by
  have h_y (y : β) : (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹ ≤ 1 := by
    refine ENNReal.rpow_le_one ?_ (inv_nonneg.2 ha.le)
    calc ∑ x, ν {x} * κ x {y} ^ a ≤ ∑ x, ν {x} :=
          Finset.sum_le_sum fun x _ ↦
            mul_le_of_le_one_right' (ENNReal.rpow_le_one prob_le_one ha.le)
      _ = 1 := by simp [sum_measure_singleton]
  calc sibsonSum a ν κ ≤ ∑ _y : β, (1 : ℝ≥0∞) := Finset.sum_le_sum fun y _ ↦ h_y y
    _ = Fintype.card β := by simp

omit [MeasurableSingletonClass β] in
lemma sibsonSum_ne_top (ha : 0 < a) [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    sibsonSum a ν κ ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (sibsonSum_le_card ha)

/-- Jensen's inequality gives `∑_y (∑_x P(x) W(y | x) ^ a) ^ (1 / a) ≥ ∑_y ∑_x P(x) W(y | x) = 1`
for `a ≥ 1`. -/
lemma one_le_sibsonSum (ha : 1 ≤ a) [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    1 ≤ sibsonSum a ν κ := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have h_y (y : β) : ∑ x, ν {x} * κ x {y} ≤ (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹ := by
    have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun x ↦ ν {x})
      (fun x ↦ κ x {y}) (by simp [sum_measure_singleton]) ha
    calc ∑ x, ν {x} * κ x {y} = ((∑ x, ν {x} * κ x {y}) ^ a) ^ a⁻¹ :=
          (ENNReal.rpow_rpow_inv ha0.ne' _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow h (inv_nonneg.2 ha0.le)
  calc (1 : ℝ≥0∞) = ∑ y, ∑ x, ν {x} * κ x {y} := by
        rw [Finset.sum_comm]
        simp [← Finset.mul_sum, sum_measure_singleton]
    _ ≤ sibsonSum a ν κ := Finset.sum_le_sum fun y _ ↦ h_y y

lemma one_le_toReal_sibsonSum (ha : 1 ≤ a) [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    1 ≤ (sibsonSum a ν κ).toReal := by
  simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top
    (sibsonSum_ne_top (zero_lt_one.trans_le ha))).2 (one_le_sibsonSum ha)

/-- **Nonnegativity of Sibson mutual information** for `a > 1`. -/
lemma sibsonMI_nonneg (ha : 1 < a) [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    0 ≤ sibsonMI a ν κ :=
  mul_nonneg (div_nonneg (by linarith) (by linarith))
    (Real.log_nonneg (one_le_toReal_sibsonSum ha.le))

/-- Multiplicative form of `I^S_a(X; Y) ≤ L(X → Y)`: by Hölder's inequality,
`∑_y (∑_x P(x) W(y | x) ^ a) ^ (1 / a) ≤ (∑_y max_{x ∈ supp P} W(y | x)) ^ (1 - 1 / a)`. -/
lemma sibsonSum_le_maxLeakageSum_rpow (ha : 1 < a) [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    sibsonSum a ν κ ≤ maxLeakageSum ν κ ^ (1 - a⁻¹) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 ≤ 1 - a⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ ha.le)
  set M : β → ℝ≥0∞ := fun y ↦ ⨆ (x) (_ : ν {x} ≠ 0), κ x {y}
  set P : β → ℝ≥0∞ := fun y ↦ ∑ x, ν {x} * κ x {y}
  -- Each column: `∑_x P(x) W(y | x) ^ a ≤ M_y ^ (a - 1) * P_Y(y)`.
  have h_col (y : β) : ∑ x, ν {x} * κ x {y} ^ a ≤ M y ^ (a - 1) * P y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    by_cases hx : ν {x} = 0
    · simp [hx]
    have hle : κ x {y} ≤ M y := le_iSup₂ (f := fun x (_ : ν {x} ≠ 0) ↦ κ x {y}) x hx
    calc ν {x} * κ x {y} ^ a = ν {x} * (κ x {y} ^ (a - 1) * κ x {y}) := by
          conv_lhs => rw [← sub_add_cancel a 1]
          rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
      _ ≤ ν {x} * (M y ^ (a - 1) * κ x {y}) := by gcongr
      _ = M y ^ (a - 1) * (ν {x} * κ x {y}) := by ring
  have h_term (y : β) : (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹ ≤ P y ^ a⁻¹ * M y ^ (1 - a⁻¹) := by
    calc (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹ ≤ (M y ^ (a - 1) * P y) ^ a⁻¹ :=
          ENNReal.rpow_le_rpow (h_col y) (inv_nonneg.2 ha0.le)
      _ = P y ^ a⁻¹ * M y ^ (1 - a⁻¹) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 ha0.le), ← ENNReal.rpow_mul, mul_comm]
          congr 2
          field_simp
  -- Hölder's inequality with the conjugate exponents `a` and `(1 - 1 / a)⁻¹`.
  have hpq : a.HolderConjugate (1 - a⁻¹)⁻¹ := by
    simpa using Real.HolderConjugate.inv_one_sub_inv (inv_pos.2 ha0) (inv_lt_one_of_one_lt₀ ha)
  have hP : ∑ y, P y = 1 := by
    simp only [P]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, sum_measure_singleton]
  calc sibsonSum a ν κ ≤ ∑ y, P y ^ a⁻¹ * M y ^ (1 - a⁻¹) := Finset.sum_le_sum fun y _ ↦ h_term y
    _ ≤ (∑ y, (P y ^ a⁻¹) ^ a) ^ (1 / a) *
          (∑ y, (M y ^ (1 - a⁻¹)) ^ (1 - a⁻¹)⁻¹) ^ (1 / (1 - a⁻¹)⁻¹) :=
        ENNReal.inner_le_Lp_mul_Lq _ _ _ hpq
    _ = maxLeakageSum ν κ ^ (1 - a⁻¹) := by
        have hb : 1 - a⁻¹ ≠ 0 := (sub_pos.2 (inv_lt_one_of_one_lt₀ ha)).ne'
        simp_rw [ENNReal.rpow_inv_rpow ha0.ne', ← ENNReal.rpow_mul, mul_inv_cancel₀ hb,
          ENNReal.rpow_one, hP, one_div, inv_inv, ENNReal.one_rpow, one_mul]
        rfl

/-- **Sibson mutual information is at most maximal leakage**: `I^S_a(X; Y) ≤ L(X → Y)` for
`a > 1`. Together with Theorem 2 this gives eq. (44) of Liao–Kosut–Sankar–Calmon. -/
lemma sibsonMI_le_maxLeakage (ha : 1 < a) [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    sibsonMI a ν κ ≤ maxLeakage ν κ := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb : 0 < 1 - a⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ ha)
  obtain ⟨x, hx⟩ : ∃ x, ν {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := ν) (s := Finset.univ)
    simp [h] at this
  have hL := one_le_toReal_maxLeakageSum (κ := κ) hx
  have h_le : (sibsonSum a ν κ).toReal ≤ (maxLeakageSum ν κ).toReal ^ (1 - a⁻¹) := by
    rw [ENNReal.toReal_rpow]
    exact ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hb.le maxLeakageSum_ne_top)
      (sibsonSum_le_maxLeakageSum_rpow ha)
  have h_log := Real.log_le_log (by linarith [one_le_toReal_sibsonSum (ν := ν) (κ := κ) ha.le])
    h_le
  rw [Real.log_rpow (by linarith)] at h_log
  calc sibsonMI a ν κ ≤ a / (a - 1) * ((1 - a⁻¹) * Real.log (maxLeakageSum ν κ).toReal) :=
        mul_le_mul_of_nonneg_left h_log (div_nonneg ha0.le (by linarith))
    _ = maxLeakage ν κ := by
        rw [maxLeakage, ← mul_assoc]
        convert one_mul _ using 2
        field_simp

end Bounds

section DataProcessing

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] [Fintype γ]
  [MeasurableSingletonClass γ] in
/-- **Minkowski's inequality** for a finite sum of nonnegative vectors:
`‖∑_i f_i‖_p ≤ ∑_i ‖f_i‖_p` for `p ≥ 1`. -/
lemma _root_.ENNReal.Lp_finsetSum_le {ι ι' : Type*} (s : Finset ι) (t : Finset ι')
    (f : ι → ι' → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑ j ∈ t, (∑ i ∈ s, f i j) ^ p) ^ (1 / p) ≤ ∑ i ∈ s, (∑ j ∈ t, f i j ^ p) ^ (1 / p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hp0 : 0 < p := zero_lt_one.trans_le hp
    simp [ENNReal.zero_rpow_of_pos hp0, hp0]
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (ENNReal.Lp_add_le t (fun j ↦ f i j) (fun j ↦ ∑ i ∈ s, f i j) hp).trans
      (add_le_add le_rfl ih)

omit [Fintype α] [MeasurableSingletonClass α] [Fintype γ] in
lemma kernel_comp_singleton_eq_sum (η : Kernel β γ) (x : α) (z : γ) :
    (η ∘ₖ κ) x {z} = ∑ y, η y {z} * κ x {y} := by
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton z), lintegral_fintype]

omit [Fintype β] [Fintype γ] [MeasurableSingletonClass γ] in
lemma measure_bind_singleton_eq_sum (μ : Measure α) (κ : Kernel α β) (y : β) :
    (κ ∘ₘ μ) {y} = ∑ x, κ x {y} * μ {x} := by
  rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable, lintegral_fintype]

omit [MeasurableSingletonClass α] in
/-- **Data processing** for Sibson mutual information, multiplicative form: post-processing the
channel output through a Markov kernel `η` cannot increase `sibsonSum`. This is Minkowski's
inequality for the `a`-norms of the vectors `(P(x) ^ (1 / a) W(y | x))_x`. -/
lemma sibsonSum_comp_le (ha : 1 ≤ a) (η : Kernel β γ) [IsMarkovKernel η] :
    sibsonSum a ν (η ∘ₖ κ) ≤ sibsonSum a ν κ := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hinv : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  set T : β → ℝ≥0∞ := fun y ↦ (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹
  have h_z (z : γ) : (∑ x, ν {x} * (η ∘ₖ κ) x {z} ^ a) ^ a⁻¹ ≤ ∑ y, η y {z} * T y := by
    have h_eq (x : α) : ν {x} * (η ∘ₖ κ) x {z} ^ a =
        (∑ y, ν {x} ^ a⁻¹ * (η y {z} * κ x {y})) ^ a := by
      rw [kernel_comp_singleton_eq_sum, ← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ ha0.le,
        ENNReal.rpow_inv_rpow ha0.ne']
    have h_norm (y : β) : (∑ x, (ν {x} ^ a⁻¹ * (η y {z} * κ x {y})) ^ a) ^ (1 / a) =
        η y {z} * T y := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ENNReal.rpow_inv_rpow ha0.ne']
      have : ∀ x, ν {x} * (η y {z} ^ a * κ x {y} ^ a) = η y {z} ^ a * (ν {x} * κ x {y} ^ a) :=
        fun x ↦ by ring
      simp_rw [this, ← Finset.mul_sum, one_div, ENNReal.mul_rpow_of_nonneg _ _ hinv,
        ENNReal.rpow_rpow_inv ha0.ne']
      rfl
    simp_rw [h_eq]
    calc (∑ x, (∑ y, ν {x} ^ a⁻¹ * (η y {z} * κ x {y})) ^ a) ^ a⁻¹
        = (∑ x, (∑ y, ν {x} ^ a⁻¹ * (η y {z} * κ x {y})) ^ a) ^ (1 / a) := by rw [one_div]
      _ ≤ ∑ y, (∑ x, (ν {x} ^ a⁻¹ * (η y {z} * κ x {y})) ^ a) ^ (1 / a) :=
          ENNReal.Lp_finsetSum_le Finset.univ Finset.univ
            (fun y x ↦ ν {x} ^ a⁻¹ * (η y {z} * κ x {y})) ha
      _ = ∑ y, η y {z} * T y := Finset.sum_congr rfl fun y _ ↦ h_norm y
  calc sibsonSum a ν (η ∘ₖ κ) ≤ ∑ z, ∑ y, η y {z} * T y := Finset.sum_le_sum fun z _ ↦ h_z z
    _ = ∑ y, (∑ z, η y {z}) * T y := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = sibsonSum a ν κ := by simp [sum_measure_singleton, sibsonSum, T]

/-- **Data processing** for Sibson mutual information under pre-processing, multiplicative form:
for a Markov chain `X - Y - Z`, `I^S_a(X; Z) ≤ I^S_a(Y; Z)`, where `Y ∼ κ ∘ₘ ν`. This is Jensen's
inequality for `t ↦ t ^ a`. -/
lemma sibsonSum_comp_le_comp (ha : 1 ≤ a) [IsMarkovKernel κ] (η : Kernel β γ) :
    sibsonSum a ν (η ∘ₖ κ) ≤ sibsonSum a (κ ∘ₘ ν) η := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  refine Finset.sum_le_sum fun z _ ↦ ENNReal.rpow_le_rpow ?_ (inv_nonneg.2 ha0.le)
  calc ∑ x, ν {x} * (η ∘ₖ κ) x {z} ^ a ≤ ∑ x, ν {x} * ∑ y, κ x {y} * η y {z} ^ a := by
        gcongr with x
        rw [kernel_comp_singleton_eq_sum]
        simp_rw [mul_comm (η _ {z})]
        exact ENNReal.rpow_arith_mean_le_arith_mean_rpow _ _ _ (by simp [sum_measure_singleton])
          ha
    _ = ∑ y, (κ ∘ₘ ν) {y} * η y {z} ^ a := by
        simp_rw [measure_bind_singleton_eq_sum, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

end DataProcessing

section Arimoto

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

omit [Fintype α] [Fintype γ] [MeasurableSingletonClass γ] in
lemma fst_singleton_eq_sum (π : Measure (α × β)) (x : α) : π.fst {x} = ∑ y, π {(x, y)} := by
  classical
  have h : Prod.fst ⁻¹' {x} = ((Finset.univ.image fun y : β ↦ (x, y) : Finset (α × β)) :
      Set (α × β)) := by
    ext ⟨x', y⟩
    simp [eq_comm]
  rw [Measure.fst_apply (measurableSet_singleton x), h, ← sum_measure_singleton,
    Finset.sum_image fun y _ y' _ h ↦ (Prod.mk.inj h).2]

omit [Fintype β] [MeasurableSingletonClass β] [Fintype γ] [MeasurableSingletonClass γ] in
lemma sum_rpow_fst_singleton_ne_zero (ha : 0 < a) [IsProbabilityMeasure π] :
    ∑ x, π.fst {x} ^ a ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, π.fst {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := π.fst) (s := Finset.univ)
    simp [h] at this
  exact ne_of_gt <| (pos_iff_ne_zero.2 ((ENNReal.rpow_eq_zero_iff_of_pos ha).not.2 hx)).trans_le
    (Finset.single_le_sum (f := fun x ↦ π.fst {x} ^ a) (fun _ _ ↦ zero_le) (Finset.mem_univ x))

omit [MeasurableSingletonClass β] [Fintype γ] [MeasurableSingletonClass γ] in
lemma arimotoSum_ne_top (ha : 0 < a) [IsProbabilityMeasure π] : arimotoSum a π ≠ ∞ := by
  refine ENNReal.div_ne_top (ENNReal.sum_ne_top.2 fun y _ ↦
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ha.le) (ENNReal.sum_ne_top.2 fun x _ ↦
      ENNReal.rpow_ne_top_of_nonneg ha.le (measure_ne_top _ _))) ?_
  exact (ENNReal.rpow_eq_zero_iff_of_pos (inv_pos.2 ha)).not.2
    (sum_rpow_fst_singleton_ne_zero ha)

omit [Fintype γ] [MeasurableSingletonClass γ] in
/-- By Minkowski's inequality `‖P_X‖_a = ‖∑_y P_{X,Y}(·, y)‖_a ≤ ∑_y ‖P_{X,Y}(·, y)‖_a`, so
`arimotoSum a π ≥ 1`. -/
lemma one_le_arimotoSum (ha : 1 ≤ a) [IsProbabilityMeasure π] : 1 ≤ arimotoSum a π := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hD0 : (∑ x, π.fst {x} ^ a) ^ a⁻¹ ≠ 0 :=
    (ENNReal.rpow_eq_zero_iff_of_pos (inv_pos.2 ha0)).not.2 (sum_rpow_fst_singleton_ne_zero ha0)
  have hDtop : (∑ x, π.fst {x} ^ a) ^ a⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ha0.le) (ENNReal.sum_ne_top.2 fun x _ ↦
      ENNReal.rpow_ne_top_of_nonneg ha0.le (measure_ne_top _ _))
  rw [arimotoSum, ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDtop), one_mul]
  simp_rw [fst_singleton_eq_sum]
  simpa only [one_div] using
    ENNReal.Lp_finsetSum_le Finset.univ Finset.univ (fun y x ↦ π {(x, y)}) ha

omit [Fintype γ] [MeasurableSingletonClass γ] in
lemma one_le_toReal_arimotoSum (ha : 1 ≤ a) [IsProbabilityMeasure π] :
    1 ≤ (arimotoSum a π).toReal := by
  simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top
    (arimotoSum_ne_top (zero_lt_one.trans_le ha))).2 (one_le_arimotoSum ha)

omit [Fintype γ] [MeasurableSingletonClass γ] in
/-- **Nonnegativity of Arimoto mutual information** for `a > 1`. -/
lemma arimotoMI_nonneg (ha : 1 < a) [IsProbabilityMeasure π] : 0 ≤ arimotoMI a π :=
  mul_nonneg (div_nonneg (by linarith) (by linarith))
    (Real.log_nonneg (one_le_toReal_arimotoSum ha.le))

/-- **Post-processing inequality** for Arimoto mutual information, multiplicative form: for a
Markov chain `X - Y - Z`, `I^A_a(X; Z) ≤ I^A_a(X; Y)`. -/
lemma arimotoSum_compProd_comp_le (ha : 1 ≤ a) [SFinite μ] [IsMarkovKernel κ] (η : Kernel β γ)
    [IsMarkovKernel η] : arimotoSum a (μ ⊗ₘ (η ∘ₖ κ)) ≤ arimotoSum a (μ ⊗ₘ κ) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  rw [arimotoSum_compProd ha0, arimotoSum_compProd ha0]
  exact sibsonSum_comp_le ha η

/-- **Post-processing inequality** for Arimoto mutual information (footnote 4 of
Liao–Kosut–Sankar–Calmon): for a Markov chain `X - Y - Z` and `a > 1`, `I^A_a(X; Z) ≤ I^A_a(X; Y)`.
-/
lemma arimotoMI_compProd_comp_le (ha : 1 < a) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] : arimotoMI a (μ ⊗ₘ (η ∘ₖ κ)) ≤ arimotoMI a (μ ⊗ₘ κ) := by
  refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) (div_nonneg (by linarith) (by linarith))
  · linarith [one_le_toReal_arimotoSum (π := μ ⊗ₘ (η ∘ₖ κ)) ha.le]
  · exact ENNReal.toReal_mono (arimotoSum_ne_top (zero_lt_one.trans ha))
      (arimotoSum_compProd_comp_le ha.le η)

end Arimoto

section Limit

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α] [Fintype β]
  [MeasurableSingletonClass β] in
/-- `c ^ (1 / a) → 1` as `a → ∞`, for `0 < c < ∞`. -/
lemma _root_.ENNReal.tendsto_rpow_inv_atTop_nhds_one {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    Tendsto (fun a : ℝ ↦ c ^ a⁻¹) atTop (𝓝 1) := by
  lift c to NNReal using hc
  have hc' : (0 : ℝ) < c := by simpa [pos_iff_ne_zero] using hc0
  have h := ENNReal.tendsto_ofReal
    (((Real.continuousAt_const_rpow hc'.ne').tendsto).comp tendsto_inv_atTop_zero)
  rw [Function.comp_def, Real.rpow_zero, ENNReal.ofReal_one] at h
  refine h.congr fun a ↦ ?_
  rw [← ENNReal.ofReal_rpow_of_pos hc', ENNReal.ofReal_coe_nnreal]

omit [Fintype β] [MeasurableSingletonClass β] in
/-- As `a → ∞`, the `a`-norm `(∑_x P(x) W(y | x) ^ a) ^ (1 / a)` of a column of the channel,
weighted by the input law, tends to the column maximum over the support of the input. -/
lemma tendsto_rpow_inv_sum_atTop [IsProbabilityMeasure ν] (y : β) :
    Tendsto (fun a : ℝ ↦ (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹) atTop
      (𝓝 (⨆ (x) (_ : ν {x} ≠ 0), κ x {y})) := by
  classical
  set S := Finset.univ.filter fun x : α ↦ ν {x} ≠ 0
  have hS : S.Nonempty := by
    by_contra h
    have h0 : ∀ x, ν {x} = 0 := fun x ↦ by
      by_contra hx
      exact h ⟨x, by simpa [S] using hx⟩
    have := sum_measure_singleton (μ := ν) (s := Finset.univ)
    simp [h0] at this
  obtain ⟨x₀, hx₀S, hx₀⟩ := S.exists_max_image (fun x ↦ κ x {y}) hS
  have hx₀' : ν {x₀} ≠ 0 := by simpa [S] using hx₀S
  set M := ⨆ (x) (_ : ν {x} ≠ 0), κ x {y}
  have hM : M = κ x₀ {y} :=
    le_antisymm (iSup₂_le fun x hx ↦ hx₀ x (by simpa [S] using hx))
      (le_iSup₂ (f := fun x (_ : ν {x} ≠ 0) ↦ κ x {y}) x₀ hx₀')
  have h_up (a : ℝ) (ha : 0 < a) : (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹ ≤ M := by
    calc (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹ ≤ (∑ x, ν {x} * M ^ a) ^ a⁻¹ := by
          refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun x _ ↦ ?_) (inv_nonneg.2 ha.le)
          by_cases hx : ν {x} = 0
          · simp [hx]
          · gcongr
            exact le_iSup₂ (f := fun x (_ : ν {x} ≠ 0) ↦ κ x {y}) x hx
      _ = M := by
          rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul,
            ENNReal.rpow_rpow_inv ha.ne']
  have h_low (a : ℝ) (ha : 0 < a) : ν {x₀} ^ a⁻¹ * M ≤ (∑ x, ν {x} * κ x {y} ^ a) ^ a⁻¹ := by
    calc ν {x₀} ^ a⁻¹ * M = (ν {x₀} * κ x₀ {y} ^ a) ^ a⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 ha.le), ENNReal.rpow_rpow_inv ha.ne',
            hM]
      _ ≤ _ := ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun x ↦ ν {x} * κ x {y} ^ a)
          (fun _ _ ↦ zero_le) (Finset.mem_univ x₀)) (inv_nonneg.2 ha.le)
  have h_lim : Tendsto (fun a : ℝ ↦ ν {x₀} ^ a⁻¹ * M) atTop (𝓝 M) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_rpow_inv_atTop_nhds_one hx₀' (measure_ne_top ν _)) (Or.inl one_ne_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim tendsto_const_nhds
    ((eventually_gt_atTop 0).mono h_low) ((eventually_gt_atTop 0).mono h_up)

omit [MeasurableSingletonClass β] in
/-- As `a → ∞`, `sibsonSum a ν κ` tends to `maxLeakageSum ν κ = ∑_y max_{x ∈ supp ν} κ x {y}`. -/
theorem tendsto_sibsonSum_atTop [IsProbabilityMeasure ν] :
    Tendsto (fun a ↦ sibsonSum a ν κ) atTop (𝓝 (maxLeakageSum ν κ)) :=
  tendsto_finsetSum _ fun y _ ↦ tendsto_rpow_inv_sum_atTop y

/-- **Sibson mutual information of order `∞` is maximal leakage**: as `a → ∞`, `I^S_a(X; Y)`
tends to `L(X → Y) = log ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`. This is eq. (12) of
Liao–Kosut–Sankar–Calmon, where `I^S_∞` is defined by continuous extension. -/
theorem tendsto_sibsonMI_atTop [IsProbabilityMeasure ν] [IsMarkovKernel κ] :
    Tendsto (fun a ↦ sibsonMI a ν κ) atTop (𝓝 (maxLeakage ν κ)) := by
  obtain ⟨x, hx⟩ : ∃ x, ν {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := ν) (s := Finset.univ)
    simp [h] at this
  have h1 : Tendsto (fun a : ℝ ↦ a / (a - 1)) atTop (𝓝 1) := by
    have h : Tendsto (fun a : ℝ ↦ 1 + (a - 1)⁻¹) atTop (𝓝 (1 + 0)) :=
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)).const_add 1
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with a ha
    have : a - 1 ≠ 0 := by linarith
    field_simp
    ring
  have h2 : Tendsto (fun a ↦ Real.log (sibsonSum a ν κ).toReal) atTop (𝓝 (maxLeakage ν κ)) :=
    ((ENNReal.tendsto_toReal maxLeakageSum_ne_top).comp tendsto_sibsonSum_atTop).log
      (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx])
  simpa only [sibsonMI, one_mul] using h1.mul h2

end Limit

end InformationTheory
