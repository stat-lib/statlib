/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.Basic
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Operational meaning of maximal leakage

Issa, Wagner and Kamath (*An operational approach to information leakage*, IEEE Trans. Inf.
Theory 66(3), 2020, Definition 1) define the maximal leakage from `X` to `Y` as
`L(X → Y) = sup_{U - X - Y - Û} log (P[U = Û] / max_u P_U(u))`,
the supremum ranging over all random variables `U`, `Û` on a common finite alphabet forming the
Markov chain `U - X - Y - Û`. It measures how much observing `Y` multiplies an adversary's chance
of guessing *some* randomized function `U` of `X`. Their Theorem 1 evaluates it in closed form:
`L(X → Y) = log ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`.

We formalize the definition and prove Theorem 1 for finite alphabets.

## Main definitions

* `guessProb μ ρ κ g`: `P[U = Û]` when `X ∼ μ`, `U` is drawn from `X` through `ρ`, `Y` from `X`
  through `κ` and the guess `Û` from `Y` through `g`.
* `blindGuessProb μ ρ`: `max_u P_U(u)`, the best success probability without observing `Y`.
* `opMaxLeakageSum μ κ`: the supremum of `P[U = Û] / max_u P_U(u)` over all finite alphabets
  `Fin n` and all kernels `ρ`, `g`. Its logarithm is the operational maximal leakage.

## Main statements

* `guessProb_le`: the converse, `P[U = Û] ≤ (∑_y max_x κ x {y}) · max_u P_U(u)`.
* `opMaxLeakageSum_eq_maxLeakageSum`: **Theorem 1 of Issa–Wagner–Kamath**, the operational
  definition equals the closed form `maxLeakageSum`.
* `exists_guessProb_div_eq`: the supremum is attained by an explicit guessing problem.
* `isGreatest_log_guessRatio`: Theorem 1 in the exact form of Definition 1, as the largest
  value of `log (P[U = Û] / max_u P_U(u))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β} {ρ : Kernel α γ} {g : Kernel β γ}

/-- `P[U = Û]` in the Markov chain `U - X - Y - Û`: `X ∼ μ`, `U` is drawn from `X` through `ρ`,
`Y` is drawn from `X` through `κ` (independently of `U` given `X`), and the guess `Û` is drawn
from `Y` through `g`. -/
noncomputable def guessProb (μ : Measure α) (ρ : Kernel α γ) (κ : Kernel α β) (g : Kernel β γ) :
    ℝ≥0∞ :=
  ((ρ ×ₖ (g ∘ₖ κ)) ∘ₘ μ) {p | p.1 = p.2}

/-- `max_u P_U(u)`: the best probability of guessing `U` without any observation. -/
noncomputable def blindGuessProb (μ : Measure α) (ρ : Kernel α γ) : ℝ≥0∞ :=
  ⨆ u, (ρ ∘ₘ μ) {u}

/-- The operational maximal leakage of Issa–Wagner–Kamath, multiplicative form: the supremum of
`P[U = Û] / max_u P_U(u)` over all finite alphabets `Fin n` for `U` and `Û`, all randomized
functions `ρ` of `X`, and all guessing rules `g` from `Y`. -/
noncomputable def opMaxLeakageSum (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ) (g : Kernel β (Fin n))
    (_ : IsMarkovKernel g), guessProb μ ρ κ g / blindGuessProb μ ρ

section Formulas

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

omit [Fintype β] [MeasurableSingletonClass β] [Fintype γ] in
lemma comp_apply_singleton (μ : Measure α) (ρ : Kernel α γ) (u : γ) :
    (ρ ∘ₘ μ) {u} = ∑ x, ρ x {u} * μ {x} := by
  rw [Measure.bind_apply (measurableSet_singleton u) ρ.measurable.aemeasurable,
    lintegral_fintype]

omit [Fintype α] [MeasurableSingletonClass α] [Fintype γ] in
lemma kernel_comp_apply_singleton (κ : Kernel α β) (g : Kernel β γ) (x : α) (u : γ) :
    (g ∘ₖ κ) x {u} = ∑ y, g y {u} * κ x {y} := by
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton u), lintegral_fintype]

/-- `P[U = Û]` as a finite sum. -/
lemma guessProb_eq_sum [IsMarkovKernel ρ] [IsMarkovKernel κ] [IsMarkovKernel g] :
    guessProb μ ρ κ g = ∑ x, ∑ u, ∑ y, g y {u} * κ x {y} * ρ x {u} * μ {x} := by
  have h_diag (x : α) : (ρ ×ₖ (g ∘ₖ κ)) x {p | p.1 = p.2} = ∑ u, (g ∘ₖ κ) x {u} * ρ x {u} := by
    rw [Kernel.prod_apply, Measure.prod_apply (Set.toFinite _).measurableSet, lintegral_fintype]
    congr 1 with u
    congr 2
    ext v
    simp [eq_comm]
  rw [guessProb, Measure.bind_apply (Set.toFinite _).measurableSet
    (ρ ×ₖ (g ∘ₖ κ)).measurable.aemeasurable, lintegral_fintype]
  simp only [h_diag, kernel_comp_apply_singleton, Finset.sum_mul]

end Formulas

section Converse

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Finite γ] [MeasurableSingletonClass γ]

omit [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
/-- On the support of `μ`, each channel entry is at most its column maximum; off the support
the term vanishes. -/
lemma mul_le_iSup_mul (x : α) (y : β) :
    κ x {y} * μ {x} ≤ (⨆ (x') (_ : μ {x'} ≠ 0), κ x' {y}) * μ {x} := by
  by_cases hx : μ {x} = 0
  · simp [hx]
  · gcongr
    exact le_iSup₂ (f := fun x' (_ : μ {x'} ≠ 0) ↦ κ x' {y}) x hx

/-- **Converse half of Theorem 1**: observing `Y` multiplies the chance of guessing any `U` by at
most `∑_y max_x κ x {y}`. -/
lemma guessProb_le [IsMarkovKernel ρ] [IsMarkovKernel κ] [IsMarkovKernel g] :
    guessProb μ ρ κ g ≤ maxLeakageSum μ κ * blindGuessProb μ ρ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite γ
  set M : β → ℝ≥0∞ := fun y ↦ ⨆ (x) (_ : μ {x} ≠ 0), κ x {y}
  calc guessProb μ ρ κ g
      = ∑ x, ∑ u, ∑ y, g y {u} * ρ x {u} * (κ x {y} * μ {x}) := by
        rw [guessProb_eq_sum]
        refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun y _ ↦ by ring
    _ ≤ ∑ x, ∑ u, ∑ y, g y {u} * ρ x {u} * (M y * μ {x}) := by
        exact Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦ Finset.sum_le_sum
          fun y _ ↦ mul_le_mul' le_rfl (mul_le_iSup_mul x y)
    _ = ∑ x, ∑ y, ∑ u, g y {u} * ρ x {u} * (M y * μ {x}) :=
        Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ u, g y {u} * ρ x {u} * (M y * μ {x}) := Finset.sum_comm
    _ = ∑ y, ∑ u, ∑ x, g y {u} * ρ x {u} * (M y * μ {x}) :=
        Finset.sum_congr rfl fun y _ ↦ Finset.sum_comm
    _ = ∑ y, M y * ∑ u, g y {u} * (ρ ∘ₘ μ) {u} := by
        simp_rw [comp_apply_singleton, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun x _ ↦ by ring
    _ ≤ ∑ y, M y * ∑ u, g y {u} * blindGuessProb μ ρ := by
        gcongr with y _ u _
        exact le_iSup (fun u ↦ (ρ ∘ₘ μ) {u}) u
    _ = maxLeakageSum μ κ * blindGuessProb μ ρ := by
        simp_rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]
        rw [maxLeakageSum, Finset.sum_mul]

end Converse

section Relabel

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

/-- Relabelling the common alphabet `γ` of `U` and `Û` as `Fin (card γ)` preserves the
guessing ratio. -/
lemma exists_fin_guessProb_div_eq [IsMarkovKernel ρ] [IsMarkovKernel κ] [IsMarkovKernel g] :
    ∃ (ρ' : Kernel α (Fin (Fintype.card γ))) (_ : IsMarkovKernel ρ')
      (g' : Kernel β (Fin (Fintype.card γ))) (_ : IsMarkovKernel g'),
      guessProb μ ρ' κ g' / blindGuessProb μ ρ' = guessProb μ ρ κ g / blindGuessProb μ ρ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  set e := Fintype.equivFin γ
  have he : Measurable e := measurable_of_finite _
  have h_preimage (u : γ) : e ⁻¹' {e u} = {u} := by
    ext v
    simp
  have h_mapρ (a : α) (u : γ) : ρ.map e a {e u} = ρ a {u} := by
    rw [Kernel.map_apply' _ he _ (measurableSet_singleton _), h_preimage]
  have h_mapg (b : β) (u : γ) : g.map e b {e u} = g b {u} := by
    rw [Kernel.map_apply' _ he _ (measurableSet_singleton _), h_preimage]
  have := Kernel.IsMarkovKernel.map ρ he
  have := Kernel.IsMarkovKernel.map g he
  have h_guess : guessProb μ (ρ.map e) κ (g.map e) = guessProb μ ρ κ g := by
    simp_rw [guessProb_eq_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← e.sum_comp]
    simp [h_mapρ, h_mapg]
  have h_blind : blindGuessProb μ (ρ.map e) = blindGuessProb μ ρ := by
    rw [blindGuessProb, blindGuessProb, ← e.iSup_comp]
    simp_rw [comp_apply_singleton, h_mapρ]
  exact ⟨ρ.map e, inferInstance, g.map e, inferInstance, by rw [h_guess, h_blind]⟩

omit [Fintype γ] in
/-- The guessing ratio of any finite alphabet `γ` is bounded by the operational maximal leakage,
whose definition only ranges over the alphabets `Fin n`. -/
lemma guessProb_div_le_opMaxLeakageSum [Finite γ] [IsMarkovKernel ρ] [IsMarkovKernel κ]
    [IsMarkovKernel g] : guessProb μ ρ κ g / blindGuessProb μ ρ ≤ opMaxLeakageSum μ κ := by
  have := Fintype.ofFinite γ
  obtain ⟨ρ', hρ', g', hg', h⟩ := exists_fin_guessProb_div_eq (μ := μ) (ρ := ρ) (κ := κ) (g := g)
  rw [← h]
  exact le_iSup_of_le _ <| le_iSup₂_of_le ρ' hρ' <| le_iSup₂_of_le g' hg' le_rfl

end Relabel

section Achievability

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

/-- **Achievability half of Theorem 1.** Let `c` be the smallest positive mass of `μ` and `k`
an integer with `1 / k < c`. Take `U = (X, J)` with `J ∈ {0, …, k}`, where given `X = x` we
put mass `c / μ {x}` on the *signal* symbol `(x, 0)` and spread the rest evenly over the
*junk* symbols `(x, 1), …, (x, k)`. Every signal symbol has probability exactly `c` and every
junk symbol at most `1 / k < c`, so `max_u P_U(u) ≤ c`. Guessing the signal symbol of the input
most likely to have produced `y` succeeds with probability `c · ∑_y max_x κ x {y}`.
Together with the converse `guessProb_le`, this guessing problem is optimal: the supremum in
the operational definition is attained. -/
lemma exists_guessProb_div_eq [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    ∃ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ) (g : Kernel β (Fin n))
      (_ : IsMarkovKernel g), guessProb μ ρ κ g / blindGuessProb μ ρ = maxLeakageSum μ κ := by
  classical
  have := Fintype.ofFinite α
  -- The support of `μ`, its smallest mass `c`, and an integer `k` with `1 / k < c`.
  set S := Finset.univ.filter fun x : α ↦ μ {x} ≠ 0
  have hS : S.Nonempty := by
    by_contra h
    have h0 : ∀ x, μ {x} = 0 := fun x ↦ by
      by_contra hx
      exact h ⟨x, by simpa [S] using hx⟩
    have := sum_measure_singleton (μ := μ) (s := Finset.univ)
    simp [h0] at this
  set c := S.inf' hS fun x ↦ μ {x}
  have hc_le (x : α) (hx : μ {x} ≠ 0) : c ≤ μ {x} := Finset.inf'_le _ (by simpa [S] using hx)
  have hc0 : c ≠ 0 := by
    obtain ⟨x, hxS, hx⟩ := Finset.exists_mem_eq_inf' hS fun x ↦ μ {x}
    have hcx : c = μ {x} := hx
    rw [hcx]
    simpa [S] using hxS
  obtain ⟨x₀, hx₀⟩ := hS
  have hctop : c ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ {x₀}) (hc_le x₀ (by simpa [S] using hx₀))
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hc0
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by
    rintro h
    simp [h] at hk
  -- The randomization `ρ` producing `U = (X, J)`.
  set t : α → ℝ≥0∞ := fun x ↦ if μ {x} = 0 then 1 else c / μ {x}
  have ht_le (x : α) : t x ≤ 1 := by
    by_cases hx : μ {x} = 0
    · simp [t, hx]
    · simp only [t, hx, ite_false]
      exact ENNReal.div_le_of_le_mul (by simpa using hc_le x hx)
  have ht_mul (x : α) (hx : μ {x} ≠ 0) : t x * μ {x} = c := by
    simp only [t, hx, ite_false]
    exact ENNReal.div_mul_cancel hx (measure_ne_top μ _)
  set w : α → α × Fin (k + 1) → ℝ≥0∞ := fun x p ↦
    if p.1 = x then (if p.2 = 0 then t x else (1 - t x) / k) else 0
  set ρ : Kernel α (α × Fin (k + 1)) :=
    Kernel.ofFunOfCountable fun x ↦ ∑ p, w x p • Measure.dirac p
  have hρ (x : α) (p : α × Fin (k + 1)) : ρ x {p} = w x p := by
    simp [ρ, Kernel.ofFunOfCountable, Measure.dirac_apply' _ (measurableSet_singleton p),
      Set.indicator]
  have hw_sum (x : α) : ∑ p, w x p = 1 := by
    rw [Fintype.sum_prod_type_right]
    simp only [w, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Fin.sum_univ_succ]
    simp only [ite_true, Fin.succ_ne_zero, ite_false, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm, ENNReal.div_mul_cancel hk0 (ENNReal.natCast_ne_top k),
      add_tsub_cancel_of_le (ht_le x)]
  have : IsMarkovKernel ρ := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hρ, hw_sum]⟩⟩
  -- The guessing rule: the signal symbol of a most likely input.
  choose xs hxsS hxs_max using fun y : β ↦ S.exists_max_image (fun x ↦ κ x {y}) ⟨x₀, hx₀⟩
  have hxs (y : β) : μ {xs y} ≠ 0 := by simpa [S] using hxsS y
  have hM (y : β) : (⨆ (x) (_ : μ {x} ≠ 0), κ x {y}) = κ (xs y) {y} :=
    le_antisymm (iSup₂_le fun x hx ↦ hxs_max y x (by simpa [S] using hx))
      (le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y}) (xs y) (hxs y))
  set g : Kernel β (α × Fin (k + 1)) :=
    Kernel.deterministic (fun y ↦ (xs y, 0)) (measurable_of_finite _)
  have hg (y : β) : g y {(xs y, 0)} = 1 := by simp [g, Kernel.deterministic_apply]
  -- `P_U(u) ≤ c` for every `u`.
  have h_blind : blindGuessProb μ ρ ≤ c := by
    refine iSup_le fun p ↦ ?_
    rw [comp_apply_singleton, Finset.sum_eq_single p.1 (fun x _ hx ↦ by simp [hρ, w, Ne.symm hx])
      (by simp)]
    rw [hρ]
    by_cases hp : p.2 = 0
    · by_cases hx : μ {p.1} = 0
      · simp [hx]
      · simp [w, hp, ht_mul p.1 hx]
    · simp only [w, ite_true, hp, ite_false]
      calc (1 - t p.1) / k * μ {p.1} ≤ 1 / k * 1 := by
            gcongr
            · exact tsub_le_self
            · exact prob_le_one
        _ ≤ c := by simpa using hk.le
  -- `P[U = Û] ≥ c · ∑_y max_x κ x {y}`.
  have h_guess : maxLeakageSum μ κ * c ≤ guessProb μ ρ κ g := by
    calc maxLeakageSum μ κ * c
        = ∑ y, g y {(xs y, 0)} * κ (xs y) {y} * ρ (xs y) {(xs y, 0)} * μ {xs y} := by
          rw [maxLeakageSum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [hM, hg, hρ, mul_assoc _ (w _ _), mul_comm (w _ _), ← mul_assoc]
          simp only [w, ite_true, ← ht_mul _ (hxs y)]
          ring
      _ ≤ ∑ y, ∑ x, ∑ u, g y {u} * κ x {y} * ρ x {u} * μ {x} :=
          Finset.sum_le_sum fun y _ ↦ (Finset.single_le_sum (fun _ _ ↦ zero_le)
            (Finset.mem_univ (xs y))).trans' <|
              Finset.single_le_sum (f := fun u ↦ g y {u} * κ (xs y) {y} * ρ (xs y) {u} *
                μ {xs y}) (fun _ _ ↦ zero_le) (Finset.mem_univ _)
      _ = ∑ x, ∑ y, ∑ u, g y {u} * κ x {y} * ρ x {u} * μ {x} := Finset.sum_comm
      _ = guessProb μ ρ κ g := by
          rw [guessProb_eq_sum]
          exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm
  have h_ge : maxLeakageSum μ κ ≤ guessProb μ ρ κ g / blindGuessProb μ ρ :=
    calc maxLeakageSum μ κ = maxLeakageSum μ κ * c / c :=
          (ENNReal.mul_div_cancel_right hc0 hctop).symm
      _ ≤ guessProb μ ρ κ g / c := ENNReal.div_le_div_right h_guess _
      _ ≤ guessProb μ ρ κ g / blindGuessProb μ ρ := ENNReal.div_le_div_left h_blind _
  -- The converse gives the reverse inequality, so the construction is optimal.
  have h_eq : guessProb μ ρ κ g / blindGuessProb μ ρ = maxLeakageSum μ κ :=
    le_antisymm (ENNReal.div_le_of_le_mul guessProb_le) h_ge
  obtain ⟨ρ', hρ', g', hg', h⟩ := exists_fin_guessProb_div_eq (μ := μ) (ρ := ρ) (κ := κ) (g := g)
  exact ⟨_, ρ', hρ', g', hg', h.trans h_eq⟩

lemma maxLeakageSum_le_opMaxLeakageSum [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    maxLeakageSum μ κ ≤ opMaxLeakageSum μ κ := by
  obtain ⟨n, ρ, hρ, g, hg, h⟩ := exists_guessProb_div_eq (μ := μ) (κ := κ)
  rw [← h]
  exact le_iSup_of_le n <| le_iSup₂_of_le ρ hρ <| le_iSup₂_of_le g hg le_rfl

end Achievability

section MainTheorem

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

/-- **Theorem 1 of Issa–Wagner–Kamath**, multiplicative form: for finite alphabets, the
operational maximal leakage equals `∑_y max_{x ∈ supp μ} κ x {y}`. -/
theorem opMaxLeakageSum_eq_maxLeakageSum [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    opMaxLeakageSum μ κ = maxLeakageSum μ κ := by
  refine le_antisymm ?_ maxLeakageSum_le_opMaxLeakageSum
  refine iSup_le fun n ↦ iSup₂_le fun ρ _ ↦ iSup₂_le fun g _ ↦ ?_
  exact ENNReal.div_le_of_le_mul guessProb_le

/-- Theorem 1 of Issa–Wagner–Kamath, stated as the logarithm of the supremum of the guessing
ratios. See `isGreatest_log_guessRatio` for the supremum of the logarithms. -/
theorem log_opMaxLeakageSum_eq_maxLeakage [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    Real.log (opMaxLeakageSum μ κ).toReal = maxLeakage μ κ := by
  rw [opMaxLeakageSum_eq_maxLeakageSum, maxLeakage]

/-- **Theorem 1 of Issa–Wagner–Kamath**, in the form of their Definition 1: over all guessing
problems `U - X - Y - Û` on a common finite alphabet, the largest value of
`log (P[U = Û] / max_u P_U(u))` is `maxLeakage μ κ = log ∑_y max_{x ∈ supp μ} κ x {y}`, and it
is attained. Problems with `P[U = Û] = 0` contribute `-∞` in the paper and are excluded here. -/
theorem isGreatest_log_guessRatio [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    IsGreatest {r : ℝ | ∃ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ)
      (g : Kernel β (Fin n)) (_ : IsMarkovKernel g), guessProb μ ρ κ g ≠ 0 ∧
        r = Real.log (guessProb μ ρ κ g / blindGuessProb μ ρ).toReal} (maxLeakage μ κ) := by
  have := Fintype.ofFinite α
  obtain ⟨x₀, hx₀⟩ : ∃ x, μ {x} ≠ 0 := by
    by_contra! h
    have := sum_measure_singleton (μ := μ) (s := Finset.univ)
    simp [h] at this
  refine ⟨?_, ?_⟩
  · obtain ⟨n, ρ, hρ, g, hg, h⟩ := exists_guessProb_div_eq (μ := μ) (κ := κ)
    refine ⟨n, ρ, hρ, g, hg, fun h0 ↦ ?_, by rw [h, maxLeakage]⟩
    rw [h0, ENNReal.zero_div] at h
    exact absurd ((one_le_maxLeakageSum (κ := κ) hx₀).trans_eq h.symm) (by simp)
  · rintro r ⟨n, ρ, hρ, g, hg, h0, rfl⟩
    have hle : guessProb μ ρ κ g / blindGuessProb μ ρ ≤ maxLeakageSum μ κ :=
      ENNReal.div_le_of_le_mul guessProb_le
    have h_blind : blindGuessProb μ ρ ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ ↦ prob_le_one)
    have hpos : 0 < (guessProb μ ρ κ g / blindGuessProb μ ρ).toReal :=
      ENNReal.toReal_pos (by simp [ENNReal.div_eq_zero_iff, h0, h_blind])
        (ne_top_of_le_ne_top maxLeakageSum_ne_top hle)
    exact Real.log_le_log hpos (ENNReal.toReal_mono maxLeakageSum_ne_top hle)

end MainTheorem

end InformationTheory
