/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Divergence.MaximalLeakage.MutualInfo
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Privacy-utility tradeoffs under differential privacy and Hamming distortion

This file formalizes the main results of K. Kalantari, L. Sankar and A. D. Sarwate, *Robust
privacy-utility tradeoffs under differential privacy and Hamming distortion*, IEEE Trans. Inf.
Forensics Security 13(11), 2018 ([arXiv:1601.06426](https://arxiv.org/abs/1601.06426)).

A data value `X` from a finite alphabet `α` of size `M` is released through a mechanism `Q`, a
row-stochastic matrix with `Q x y` the probability of releasing `y` when the data is `x`. Privacy
is measured by (local) differential privacy: `Q` is `ε`-DP if `Q(y | x₁) ≤ e^ε Q(y | x₂)` for all
`x₁, x₂, y`. Utility is measured by the expected Hamming distortion
`E[1{X ≠ X̂}] = ∑_x P(x) (1 - Q(x | x))`, required to be at most `D` for *every* law `P` in a source
set `S` known to the publisher. The optimal leakage `ε*_DP(S, D)` is the least `ε` achieved by such
a mechanism.

Source laws are vectors `P : α → ℝ` (in the probability simplex where needed) and mechanisms are
matrices in `Matrix.rowStochastic ℝ α`; the reduction step of Lemma 3
(`mem_achievableDP_of_injective`) shows that this square output alphabet loses nothing.
Logarithms are natural.

## Main definitions

* `IsLocalDP Q ε`: `Q` is `ε`-differentially private (Definition 3).
* `hammingDistortion P Q`: the expected Hamming distortion.
* `validMechanisms S D`: the `(S, D)`-valid mechanisms (Definition 2).
* `achievableDP S D`, `optimalDP S D`: the privacy levels achieved by `(S, D)`-valid mechanisms,
  and their infimum `ε*_DP(S, D)` in `EReal`, which is `⊤` when the set is empty (Definition 4).
* `IsClassI S`: the convex hull of `S` contains the uniform law (Definition 1, Class I).
* `symmMechanism D`: the symmetric mechanism `Q_D` of (7) (randomized response).
* `distortionThreshold S k`: the thresholds `D^(k)` of (9), for source sets on `Fin M`.

## Main statements

* `optimalDP_of_isClassI`: **Theorem 1**, for a Class I source set and `0 < D`,
  `ε*_DP(S, D) = log ((M - 1)(1 - D) / D)` if `D < (M - 1) / M` and `0` otherwise.
* `isLeast_achievableDP_of_lt`: the symmetric mechanism is optimal whenever the convex hull of `S`
  contains a law with every mass `> D / (M - 1)`; this contains the first cases of Theorems 1 and 2.
* `isLeast_achievableDP_of_lt_distortionThreshold_one`: **Theorem 2(b)**, case `0 < D < D^(1)`.
* `notMem_validMechanisms_of_lt_distortionThreshold`: **Theorem 2(a)**.
* `isLeast_achievableDP_zero_iff_distortionThreshold_le`: **Lemma 7**, and the case
  `D ≥ D^(M-1)` of Theorem 2(b).
* `toReal_mutualInfo_compProd_le_of_isLocalDP`: DP leakage bounds MI leakage, through
  `maxLeakage_le_of_isLocalDP` (maximal leakage is at most `ε`).

## Correspondence with the paper

* Definitions 1–4: `IsClassI`, `validMechanisms`, `IsLocalDP`, `achievableDP` / `optimalDP`.
* Lemma 1: `convex_setOf_isLocalDP` (convexity of the sublevel sets `{Q | ε_DP(Q) ≤ ε}`).
* Lemma 2: `validMechanisms_convexHull`, `achievableDP_convexHull`.
* Lemma 3, reduction step (any achievable `ε` is achieved by a square mechanism, rather than the
  existence of an optimal one): `exists_square_mechanism`, `mem_achievableDP_of_injective`.
* Lemma 4, reduction step (any achievable `ε` is achieved by a mechanism with sorted distortions,
  rather than the existence of such an optimal one): `exists_monotone_distortion`.
* Theorem 1: `isLeast_achievableDP_of_isClassI`, `isLeast_achievableDP_zero`,
  `optimalDP_of_isClassI`.
* Theorem 2(a) and Lemma 8: `notMem_validMechanisms_of_lt_distortionThreshold`.
* Theorem 2(b), first case: `isLeast_achievableDP_of_lt_distortionThreshold_one`, with converse
  `card_sub_one_mul_le_exp_mul` (eq. (46)) and achievability `isLocalDP_symmMechanism` (eq. (47)).
* Theorem 2(b), last case, and Lemma 7: `isLeast_achievableDP_zero_iff_distortionThreshold_le`,
  and the general form `isLeast_achievableDP_zero_iff` for laws with a common mode.
* Lemma 10: `sum_mul_le_sum_mul_of_forall_ne_le`.
* Section III-A, "DP leakage is an upper bound on MI leakage":
  `toReal_mutualInfo_compProd_le_of_isLocalDP`.

## Implementation notes

* A statement `ε*_DP(S, D) = v` of the paper is formalized as `IsLeast (achievableDP S D) v`: some
  `(S, D)`-valid mechanism is `v`-DP and none is `ε`-DP for `ε < v`. This implies
  `optimalDP S D = v` (`optimalDP_eq_of_isLeast`). The infimum `optimalDP` is taken in `EReal` so
  that an infeasible regime (no valid mechanism with finite leakage, e.g. `D = 0` on an alphabet
  with at least two symbols when `S` contains a full-support law) gives `⊤` rather than a junk
  value.
* Class II source sets are taken in the normalized form of Remark 1: laws on `Fin M` that are
  nonincreasing (`Antitone`). The Class II results do not need the hypothesis "not Class I" of
  Definition 1, so they are stated without it. The thresholds `D^(k)` are suprema over `S`
  (maxima in the paper), which is why `S` is assumed nonempty.
* The converse `card_sub_one_mul_le_exp_mul` is proved directly, without the coloring arguments
  of Lemma 9.

## Not formalized

* Theorem 2(b) for `D^(1) ≤ D < D^(M-1)` (the linear programs (10)–(11) and Lemma 9) and
  Theorem 3 with Corollary 1 (Class III bounds built on them).
* Lemmas 5 and 6 on the optimal mutual-information leakage.
-/

@[expose] public section

open Finset Real

namespace InformationTheory

variable {α β : Type*}

/-! ### Definitions -/

/-- **Local differential privacy** (Definition 3 of Kalantari–Sankar–Sarwate): a mechanism `Q`,
where `Q x y` is the probability of releasing `y` when the data is `x`, is `ε`-differentially
private if `Q(y | x₁) ≤ e^ε Q(y | x₂)` for all inputs `x₁, x₂` and outputs `y`. -/
def IsLocalDP (Q : α → β → ℝ) (ε : ℝ) : Prop :=
  ∀ x₁ x₂ y, Q x₁ y ≤ exp ε * Q x₂ y

section LocalDP

variable {Q : α → β → ℝ} {ε : ℝ}

/-- An `ε`-differentially private mechanism is `ε'`-differentially private for every `ε' ≥ ε`. -/
lemma IsLocalDP.mono (hQ : ∀ x y, 0 ≤ Q x y) {ε' : ℝ} (h : IsLocalDP Q ε)
    (hεε' : ε ≤ ε') : IsLocalDP Q ε' := fun x₁ x₂ y ↦
  (h x₁ x₂ y).trans (mul_le_mul_of_nonneg_right (exp_le_exp.2 hεε') (hQ x₂ y))

/-- **Lemma 1** (quasi-convexity of the leakage): for every `ε`, the set of `ε`-differentially
private mechanisms is convex. This is the sublevel-set characterization of the quasi-convexity of
`Q ↦ ε_DP(Q)` used in the paper. -/
theorem convex_setOf_isLocalDP (ε : ℝ) : Convex ℝ {Q : α → β → ℝ | IsLocalDP Q ε} := by
  intro Q₁ h₁ Q₂ h₂ a b ha hb _ x₁ x₂ y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc a * Q₁ x₁ y + b * Q₂ x₁ y ≤ a * (exp ε * Q₁ x₂ y) + b * (exp ε * Q₂ x₂ y) := by
        gcongr
        · exact h₁ x₁ x₂ y
        · exact h₂ x₁ x₂ y
    _ = exp ε * (a * Q₁ x₂ y + b * Q₂ x₂ y) := by ring

end LocalDP

section Definitions

variable [Fintype α] [DecidableEq α]

/-- The expected Hamming distortion `E[d(X, X̂)] = ∑_{x, x̂} P(x) Q(x̂ | x) 1{x ≠ x̂}` of a
mechanism `Q` whose output alphabet is the input alphabet, for a source with law `P`. -/
def hammingDistortion (P : α → ℝ) (Q : Matrix α α ℝ) : ℝ :=
  ∑ x, ∑ y, P x * Q x y * if x = y then 0 else 1

/-- The `(S, D)`-valid mechanisms (Definition 2): the row-stochastic matrices whose expected
Hamming distortion is at most `D` for every source law `P ∈ S`. -/
def validMechanisms (S : Set (α → ℝ)) (D : ℝ) : Set (Matrix α α ℝ) :=
  {Q | Q ∈ Matrix.rowStochastic ℝ α ∧ ∀ P ∈ S, hammingDistortion P Q ≤ D}

/-- The privacy levels `ε` for which some `(S, D)`-valid mechanism is `ε`-differentially
private. This set is empty when no `(S, D)`-valid mechanism has finite DP leakage (for instance
for `D = 0`, an alphabet with at least two symbols and `S` containing a full-support law, where
only the identity is valid and it is not `ε`-DP for any finite `ε`); otherwise the
optimal leakage `ε*_DP(S, D)` of Definition 4 is its least element when it has one. -/
def achievableDP (S : Set (α → ℝ)) (D : ℝ) : Set ℝ :=
  {ε | ∃ Q ∈ validMechanisms S D, IsLocalDP Q ε}

/-- The optimal differential privacy leakage `ε*_DP(S, D) ∈ [-∞, ∞]` (Definition 4): the infimum
of the privacy levels achieved by `(S, D)`-valid mechanisms, in `EReal`. It is `⊤` (infinite
leakage) when no `(S, D)`-valid mechanism has finite DP leakage (`optimalDP_eq_top`). The main
results below show that the infimum is attained (`IsLeast (achievableDP S D) _`), which pins down
its value (`optimalDP_eq_of_isLeast`). -/
noncomputable def optimalDP (S : Set (α → ℝ)) (D : ℝ) : EReal :=
  ⨅ ε ∈ achievableDP S D, (ε : EReal)

omit [DecidableEq α] in
/-- A source set `S` is of **Class I** (Definition 1) if its convex hull contains the uniform
distribution. -/
def IsClassI (S : Set (α → ℝ)) : Prop :=
  (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∈ convexHull ℝ S

/-- The symmetric mechanism `Q_D` of (7) (randomized response): keep the input with probability
`1 - D`, otherwise release one of the other `M - 1` symbols uniformly at random. -/
noncomputable def symmMechanism (D : ℝ) : Matrix α α ℝ :=
  fun x y ↦ if x = y then 1 - D else D / (Fintype.card α - 1)

end Definitions

/-! ### Basic properties -/

section Basic

variable [Fintype α] [DecidableEq α] {S T : Set (α → ℝ)} {D ε : ℝ} {Q : Matrix α α ℝ}

/-- For a row-stochastic `Q`, the expected Hamming distortion is `∑_x P(x) (1 - Q(x | x))`. -/
lemma hammingDistortion_eq (hQ : Q ∈ Matrix.rowStochastic ℝ α) (P : α → ℝ) :
    hammingDistortion P Q = ∑ x, P x * (1 - Q x x) := by
  refine sum_congr rfl fun x _ ↦ ?_
  have h (y : α) : P x * Q x y * (if x = y then 0 else 1) =
      P x * (Q x y - if x = y then Q x y else 0) := by
    split_ifs <;> ring
  simp_rw [h, ← mul_sum, sum_sub_distrib, sum_ite_eq, Matrix.sum_row_of_mem_rowStochastic hQ]
  simp

/-- The privacy level of a differentially private mechanism is nonnegative. -/
lemma IsLocalDP.nonneg [Nonempty α] (hQ : Q ∈ Matrix.rowStochastic ℝ α) (h : IsLocalDP Q ε) :
    0 ≤ ε := by
  by_contra! hε
  obtain ⟨x⟩ := ‹Nonempty α›
  have h0 (y : α) : Q x y ≤ 0 := by
    nlinarith [h x x y, exp_lt_one_iff.2 hε,
      Matrix.nonneg_of_mem_rowStochastic hQ (i := x) (j := y)]
  linarith [Matrix.sum_row_of_mem_rowStochastic hQ x, sum_nonpos fun y (_ : y ∈ univ) ↦ h0 y]

/-- The expected Hamming distortion is linear in the source law. -/
lemma isLinearMap_hammingDistortion (Q : Matrix α α ℝ) :
    IsLinearMap ℝ fun P : α → ℝ ↦ hammingDistortion P Q where
  map_add P₁ P₂ := by simp only [hammingDistortion, Pi.add_apply, add_mul, sum_add_distrib]
  map_smul c P := by simp only [hammingDistortion, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

/-- **Lemma 2**: a mechanism is valid for a source set iff it is valid for its convex hull. -/
theorem validMechanisms_convexHull : validMechanisms (convexHull ℝ S) D = validMechanisms S D := by
  ext Q
  refine ⟨fun h ↦ ⟨h.1, fun P hP ↦ h.2 P (subset_convexHull ℝ S hP)⟩, fun h ↦ ⟨h.1, ?_⟩⟩
  exact (convex_halfSpace_le (isLinearMap_hammingDistortion Q) D).convexHull_subset_iff.2 h.2

/-- **Lemma 2**: the minimal leakage of a source set is that of its convex hull. -/
theorem achievableDP_convexHull : achievableDP (convexHull ℝ S) D = achievableDP S D := by
  simp [achievableDP, validMechanisms_convexHull]

/-- If the minimum of the achievable privacy levels is `v`, then `ε*_DP(S, D) = v`. -/
lemma optimalDP_eq_of_isLeast {v : ℝ} (h : IsLeast (achievableDP S D) v) : optimalDP S D = v :=
  le_antisymm (iInf₂_le v h.1) (le_iInf₂ fun _ hε ↦ EReal.coe_le_coe_iff.2 (h.2 hε))

/-- If no `(S, D)`-valid mechanism is `ε`-differentially private for any real `ε`, then
`ε*_DP(S, D) = ∞`. -/
lemma optimalDP_eq_top (h : achievableDP S D = ∅) : optimalDP S D = ⊤ := by
  simp [optimalDP, h]

/-- More knowledge about the source (a smaller source set) can only decrease the leakage. -/
lemma achievableDP_anti (h : S ⊆ T) : achievableDP T D ⊆ achievableDP S D :=
  fun _ ⟨Q, hQ, hε⟩ ↦ ⟨Q, ⟨hQ.1, fun P hP ↦ hQ.2 P (h hP)⟩, hε⟩

end Basic

/-! ### The symmetric mechanism -/

section Symmetric

variable [Fintype α] [DecidableEq α] [Nontrivial α] {D : ℝ}

lemma sum_symmMechanism (D : ℝ) (x : α) : ∑ y, symmMechanism D x y = 1 := by
  have hM : (1 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.one_lt_card
  have h (y : α) : symmMechanism D x y = D / (Fintype.card α - 1) +
      if x = y then 1 - D - D / (Fintype.card α - 1) else 0 := by
    unfold symmMechanism; split_ifs <;> ring
  simp_rw [h, sum_add_distrib, sum_ite_eq, sum_const, card_univ, nsmul_eq_mul]
  simp only [mem_univ, ↓reduceIte]
  field_simp
  ring

lemma symmMechanism_mem_rowStochastic (hD₀ : 0 ≤ D) (hD₁ : D ≤ 1) :
    (symmMechanism D : Matrix α α ℝ) ∈ Matrix.rowStochastic ℝ α := by
  have hM : (1 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.one_lt_card
  refine Matrix.mem_rowStochastic_iff_sum.2 ⟨fun x y ↦ ?_, sum_symmMechanism D⟩
  unfold symmMechanism
  split_ifs
  · linarith
  · exact div_nonneg hD₀ (by linarith)

/-- The symmetric mechanism has expected Hamming distortion exactly `D` for every source law. -/
lemma hammingDistortion_symmMechanism (hD₀ : 0 ≤ D) (hD₁ : D ≤ 1) {P : α → ℝ}
    (hP : ∑ x, P x = 1) : hammingDistortion P (symmMechanism D) = D := by
  rw [hammingDistortion_eq (symmMechanism_mem_rowStochastic hD₀ hD₁)]
  simp [symmMechanism, ← sum_mul, hP]

/-- The symmetric mechanism `Q_D` is `log ((M - 1)(1 - D) / D)`-differentially private for
`0 < D ≤ (M - 1) / M`. -/
lemma isLocalDP_symmMechanism (hD₀ : 0 < D) (hD : D ≤ (Fintype.card α - 1) / Fintype.card α) :
    IsLocalDP (symmMechanism D : Matrix α α ℝ) (log ((Fintype.card α - 1) * (1 - D) / D)) := by
  set M : ℝ := (Fintype.card α : ℝ)
  have hM : 1 < M := by simp only [M]; exact_mod_cast Fintype.one_lt_card (α := α)
  have hMD : M * D ≤ M - 1 := by rwa [le_div_iff₀ (by linarith), mul_comm] at hD
  set w := D / (M - 1)
  set c := (M - 1) * (1 - D) / D
  have hw : 0 ≤ w := div_nonneg hD₀.le (by linarith)
  have hcw : c * w = 1 - D := by simp only [c, w]; field_simp
  have hwD : w ≤ 1 - D := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hc : 1 ≤ c := by rw [le_div_iff₀ hD₀]; nlinarith
  intro x₁ x₂ y
  rw [exp_log (by linarith)]
  unfold symmMechanism
  split_ifs <;> nlinarith

end Symmetric

/-! ### The converse -/

section Converse

/-- **Lemma 10** (a rearrangement bound). Let `∑ a = ∑ a'`, let `b` be smallest at `i₀`, and let
`a' i ≤ a i` for every `i ≠ i₀`. Then `∑ a' b ≤ ∑ a b`. The paper states this for `b` sorted
nondecreasingly and `i₀` the first index, and also assumes `a'_{i₀} ≥ a_{i₀}`, which follows from
the other hypotheses; the bounds `0 ≤ a, a', b ≤ 1` of the paper are not needed. -/
lemma sum_mul_le_sum_mul_of_forall_ne_le {ι : Type*} [Fintype ι] {a a' b : ι → ℝ} {i₀ : ι}
    (hsum : ∑ i, a i = ∑ i, a' i) (hb : ∀ i, b i₀ ≤ b i) (h : ∀ i ≠ i₀, a' i ≤ a i) :
    ∑ i, a' i * b i ≤ ∑ i, a i * b i := by
  have key : ∑ i, (a i - a' i) * b i₀ ≤ ∑ i, (a i - a' i) * b i := sum_le_sum fun i _ ↦ by
    rcases eq_or_ne i i₀ with rfl | hi
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (hb i) (sub_nonneg.2 (h i hi))
  rw [← sum_mul, sum_sub_distrib, hsum, sub_self, zero_mul] at key
  simpa [sub_mul, sum_sub_distrib] using key

variable [Fintype α] [DecidableEq α] [Nontrivial α] {D ε : ℝ} {Q : Matrix α α ℝ}

/-- **Converse bound** behind Theorems 1 and 2(b). Let `Q` be an `ε`-differentially private
mechanism with expected Hamming distortion at most `D > 0` under a source law `P` that puts mass
more than `D / (M - 1)` on every symbol. Then `(M - 1)(1 - D) ≤ e^ε D`, i.e.
`ε ≥ log ((M - 1)(1 - D) / D)`.

The proof follows Section V-F of the paper but needs neither Lemma 4 nor the structural Lemma 9:
the row `i` of smallest distortion `D_i` already satisfies `e^ε D_i ≥ ∑_{y ≠ i} (1 - D_y)`, and
comparing `P` with the law `(1 - D, D / (M - 1), …, D / (M - 1))` as in Lemma 10 and (45) gives
`(1 - D) D_i + D / (M - 1) ∑_{y ≠ i} D_y ≤ D`. -/
theorem card_sub_one_mul_le_exp_mul (hQ : Q ∈ Matrix.rowStochastic ℝ α) (hε : IsLocalDP Q ε)
    {P : α → ℝ} (hP : ∑ x, P x = 1) (hD : 0 < D) (hPD : ∀ x, D / (Fintype.card α - 1) < P x)
    (hdist : hammingDistortion P Q ≤ D) :
    (Fintype.card α - 1) * (1 - D) ≤ exp ε * D := by
  set M : ℝ := (Fintype.card α : ℝ)
  have hM : 1 < M := by simp only [M]; exact_mod_cast Fintype.one_lt_card (α := α)
  set w := D / (M - 1) with hw_def
  have hw : 0 ≤ w := div_nonneg hD.le (by linarith)
  have hMw : (M - 1) * w = D := by rw [hw_def]; field_simp
  have hQ₀ (x y : α) : 0 ≤ Q x y := Matrix.nonneg_of_mem_rowStochastic hQ
  have hrow := Matrix.sum_row_of_mem_rowStochastic hQ
  -- The row `i` with the largest diagonal entry, i.e. the smallest distortion `D_i`.
  obtain ⟨i, hi⟩ := Finite.exists_max fun x ↦ Q x x
  set q := Q i i
  set s := ∑ y ∈ univ.erase i, Q y y
  -- Each `Q(y | y)` with `y ≠ i` is at most `e^ε Q(y | i)`, and these sum to `e^ε (1 - q)`.
  have hrow_i : ∑ y ∈ univ.erase i, Q i y = 1 - q := by
    rw [← hrow i, ← add_sum_erase _ _ (mem_univ i)]; ring
  have hs : s ≤ exp ε * (1 - q) := by
    rw [← hrow_i, mul_sum]; exact sum_le_sum fun y _ ↦ hε y i y
  -- The distortion constraint `∑ P(x) Q(x | x) ≥ 1 - D`, split along the weights `P - w ≥ 0`.
  rw [hammingDistortion_eq hQ] at hdist
  have hdist' : 1 - D ≤ ∑ x, P x * Q x x := by
    simp only [mul_sub, mul_one, sum_sub_distrib, hP] at hdist; linarith
  have hsplit : ∑ x, P x * Q x x = ∑ x, (P x - w) * Q x x + w * (q + s) := by
    rw [show q + s = ∑ x, Q x x from add_sum_erase _ (fun x ↦ Q x x) (mem_univ i), mul_sum,
      ← sum_add_distrib]
    exact sum_congr rfl fun x _ ↦ by ring
  have hle : ∑ x, (P x - w) * Q x x ≤ ∑ x, (P x - w) * q :=
    sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hi x) (sub_nonneg.2 (hPD x).le)
  have hsum : ∑ x, (P x - w) * q = (1 - M * w) * q := by
    rw [← sum_mul, sum_sub_distrib, hP]; simp [M]
  have hMwq : (M - 1) * w * q = D * q := by rw [hMw]
  rcases (Matrix.le_one_of_mem_rowStochastic hQ (i := i) (j := i)).lt_or_eq with hq | hq
  · have h1 : (1 - D) * (1 - q) ≤ w * exp ε * (1 - q) := by
      nlinarith [mul_le_mul_of_nonneg_left hs hw]
    have h2 : 1 - D ≤ w * exp ε := le_of_mul_le_mul_right h1 (by linarith)
    calc (M - 1) * (1 - D) ≤ (M - 1) * (w * exp ε) := by gcongr
      _ = exp ε * D := by rw [← hMw]; ring
  · -- If `Q(i | i) = 1`, every other diagonal entry vanishes and `P` cannot meet the constraint.
    exfalso
    replace hq : q = 1 := hq
    have hs₀ : s = 0 :=
      le_antisymm (by simpa [q, hq] using hs) (sum_nonneg fun y _ ↦ hQ₀ y y)
    obtain ⟨j, hj⟩ := exists_ne i
    have hj₀ : Q j j = 0 :=
      (sum_eq_zero_iff_of_nonneg fun y _ ↦ hQ₀ y y).1 hs₀ j (mem_erase.2 ⟨hj, mem_univ j⟩)
    have hlt : ∑ x, (P x - w) * Q x x < ∑ x, (P x - w) * q := by
      refine sum_lt_sum (fun x _ ↦ mul_le_mul_of_nonneg_left (hi x) (sub_nonneg.2 (hPD x).le))
        ⟨j, mem_univ j, ?_⟩
      rw [hj₀, hq, mul_zero, mul_one]
      linarith [hPD j]
    simp only [hq, hs₀, mul_one, add_zero] at hsum hMwq hlt hsplit
    linarith

end Converse

/-! ### Optimal leakage: Theorem 1 -/

section Optimal

variable [Fintype α] [DecidableEq α] {S : Set (α → ℝ)} {D : ℝ}

/-- **Perfect privacy at large distortion** (Theorem 1, second case, which the paper notes holds
for source sets of any class): for `D ≥ (M - 1) / M`, the uniform mechanism `Q(x̂ | x) = 1 / M` is
`0`-differentially private and `(S, D)`-valid for every source set `S`, so `ε*_DP(S, D) = 0`. -/
theorem isLeast_achievableDP_zero [Nonempty α] (hS : ∀ P ∈ S, ∑ x, P x = 1)
    (hD : (Fintype.card α - 1) / Fintype.card α ≤ D) :
    IsLeast (achievableDP S D) 0 := by
  have hM : (Fintype.card α : ℝ) ≠ 0 := by simp
  have hQ : (fun _ _ ↦ (Fintype.card α : ℝ)⁻¹ : Matrix α α ℝ) ∈ Matrix.rowStochastic ℝ α :=
    Matrix.mem_rowStochastic_iff_sum.2 ⟨fun _ _ ↦ by positivity, fun _ ↦ by simp [hM]⟩
  refine ⟨⟨_, ⟨hQ, fun P hP ↦ ?_⟩, fun _ _ _ ↦ by simp⟩, fun ε ⟨Q, hQ, hε⟩ ↦ hε.nonneg hQ.1⟩
  rw [hammingDistortion_eq hQ, ← sum_mul, hS P hP, one_mul]
  rwa [sub_div, div_self hM, one_div] at hD

/-- **Optimal leakage when some source law is spread out** (common generalization of the first
cases of Theorem 1 and Theorem 2(b)). If `0 < D` and the convex hull of the source set `S`
contains a law `P` with `P(x) > D / (M - 1)` for every symbol `x`, then the symmetric mechanism is
optimal and `ε*_DP(S, D) = log ((M - 1)(1 - D) / D)`. -/
theorem isLeast_achievableDP_of_lt [Nontrivial α] (hS : ∀ P ∈ S, ∑ x, P x = 1) (hD : 0 < D)
    {P : α → ℝ} (hP : P ∈ convexHull ℝ S) (hPD : ∀ x, D / (Fintype.card α - 1) < P x) :
    IsLeast (achievableDP S D) (log ((Fintype.card α - 1) * (1 - D) / D)) := by
  have hP₁ : ∑ x, P x = 1 := by
    have hlin : IsLinearMap ℝ fun P : α → ℝ ↦ ∑ x, P x :=
      ⟨fun _ _ ↦ sum_add_distrib, fun c P ↦ by simp [mul_sum]⟩
    exact (convex_hyperplane hlin 1).convexHull_subset_iff.2 hS hP
  set M : ℝ := (Fintype.card α : ℝ)
  have hM : 1 < M := by simp only [M]; exact_mod_cast Fintype.one_lt_card (α := α)
  -- Summing `P(x) > D / (M - 1)` over `x` gives `D < (M - 1) / M`.
  have hDM : D < (M - 1) / M := by
    have h := sum_lt_sum_of_nonempty univ_nonempty fun x (_ : x ∈ univ) ↦ hPD x
    rw [hP₁, sum_const, card_univ, nsmul_eq_mul, mul_div_assoc', div_lt_one (by linarith)] at h
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hD₁ : D < 1 := hDM.trans ((div_lt_one (by linarith)).2 (by linarith))
  refine ⟨⟨symmMechanism D, ⟨symmMechanism_mem_rowStochastic hD.le hD₁.le, fun P' hP' ↦
    (hammingDistortion_symmMechanism hD.le hD₁.le (hS P' hP')).le⟩,
    isLocalDP_symmMechanism hD hDM.le⟩, ?_⟩
  rintro ε ⟨Q, hQ, hε⟩
  rw [← validMechanisms_convexHull] at hQ
  have h := card_sub_one_mul_le_exp_mul hQ.1 hε hP₁ hD hPD (hQ.2 P hP)
  rw [log_le_iff_le_exp (div_pos (mul_pos (by linarith) (by linarith)) hD), div_le_iff₀ hD]
  exact h

/-- **Theorem 1** (Class I source sets, `0 < D < (M - 1) / M`): if the convex hull of `S` contains
the uniform distribution, the symmetric mechanism `Q_D` is optimal and
`ε*_DP(S, D) = log ((M - 1)(1 - D) / D)`. -/
theorem isLeast_achievableDP_of_isClassI [Nontrivial α] (hS : ∀ P ∈ S, ∑ x, P x = 1)
    (hI : IsClassI S) (hD : 0 < D) (hDM : D < (Fintype.card α - 1) / Fintype.card α) :
    IsLeast (achievableDP S D) (log ((Fintype.card α - 1) * (1 - D) / D)) := by
  have hM : (1 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.one_lt_card (α := α)
  refine isLeast_achievableDP_of_lt hS hD hI fun x ↦ ?_
  rw [div_lt_iff₀ (by linarith), inv_mul_eq_div]
  rw [lt_div_iff₀ (by linarith)] at hDM
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- **Theorem 1**, eq. (8): for a Class I source set and `0 < D`,
`ε*_DP(S, D) = log ((M - 1)(1 - D) / D)` if `D < (M - 1) / M`, and `0` otherwise. The endpoint
`D = 0` of (8), where `ε*_DP = ∞`, is excluded. -/
theorem optimalDP_of_isClassI [Nontrivial α] (hS : ∀ P ∈ S, ∑ x, P x = 1) (hI : IsClassI S)
    (hD : 0 < D) :
    optimalDP S D = ((if D < (Fintype.card α - 1) / Fintype.card α then
      log ((Fintype.card α - 1) * (1 - D) / D) else 0 : ℝ) : EReal) := by
  split_ifs with hDM
  · exact optimalDP_eq_of_isLeast (isLeast_achievableDP_of_isClassI hS hI hD hDM)
  · exact optimalDP_eq_of_isLeast (isLeast_achievableDP_zero hS (not_lt.1 hDM))

end Optimal

/-! ### Square mechanisms suffice: the reduction of Lemma 3 -/

section OutputAlphabet

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {S : Set (α → ℝ)} {D ε : ℝ}

/-- The reduction step of **Lemma 3** (an output alphabet of size `M` suffices). Let
`Q : α → β → ℝ` be a mechanism with an arbitrary finite output alphabet `β` containing the input
alphabet through an injection `ι`, and Hamming distortion `d(x, x̂) = 1{ι x ≠ x̂}`. Merging all
outputs outside the image of `ι` into one output gives a square mechanism that is
`ε`-differentially private whenever `Q` is, and whose expected Hamming distortion is no larger
under any source law. -/
theorem exists_square_mechanism [Nonempty α] {ι : α → β} (hι : ι.Injective)
    {Q : α → β → ℝ} (hQ₀ : ∀ x y, 0 ≤ Q x y) (hQ₁ : ∀ x, ∑ y, Q x y = 1) :
    ∃ Q' ∈ Matrix.rowStochastic ℝ α, (∀ ε, IsLocalDP Q ε → IsLocalDP Q' ε) ∧
      ∀ P : α → ℝ, (∀ x, 0 ≤ P x) →
        hammingDistortion P Q' ≤ ∑ x, ∑ y, P x * Q x y * if ι x = y then 0 else 1 := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  set R : Finset β := (univ.image ι)ᶜ
  set Q' : Matrix α α ℝ := fun x x' ↦ Q x (ι x') + if x' = x₀ then ∑ y ∈ R, Q x y else 0
  have hR (x : α) : 0 ≤ ∑ y ∈ R, Q x y := sum_nonneg fun y _ ↦ hQ₀ x y
  have hrow (x : α) : ∑ x', Q x (ι x') + ∑ y ∈ R, Q x y = 1 := by
    rw [← sum_image (s := univ) (f := Q x) hι.injOn, sum_add_sum_compl, hQ₁]
  have hQ' : Q' ∈ Matrix.rowStochastic ℝ α := by
    refine Matrix.mem_rowStochastic_iff_sum.2 ⟨fun x x' ↦ ?_, fun x ↦ ?_⟩
    · exact add_nonneg (hQ₀ _ _) (by split_ifs; exacts [hR x, le_rfl])
    · simp only [Q', sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte, hrow]
  refine ⟨Q', hQ', fun ε hε x₁ x₂ x' ↦ ?_, fun P hP ↦ ?_⟩
  · simp only [Q', mul_add]
    refine add_le_add (hε _ _ _) ?_
    split_ifs
    · rw [mul_sum]; exact sum_le_sum fun y _ ↦ hε _ _ _
    · simp
  · rw [hammingDistortion_eq hQ']
    refine sum_le_sum fun x _ ↦ ?_
    have h (y : β) : P x * Q x y * (if ι x = y then 0 else 1) =
        P x * (Q x y - if ι x = y then Q x y else 0) := by
      split_ifs <;> ring
    simp_rw [h, ← mul_sum, sum_sub_distrib, sum_ite_eq, hQ₁]
    simp only [mem_univ, ↓reduceIte]
    refine mul_le_mul_of_nonneg_left ?_ (hP x)
    simp only [Q']
    split_ifs <;> linarith [hR x]

/-- The reduction step of **Lemma 3**: optimizing over mechanisms with an arbitrary finite output
alphabet gives nothing beyond square mechanisms. Any privacy level achieved by a mechanism
`Q : α → β → ℝ` meeting the distortion constraint for every (nonnegative) source law in `S` is
achieved by a `(S, D)`-valid square mechanism. The paper's Lemma 3 (existence of an optimal
mechanism with at most `M` outputs) follows by applying this to an optimal mechanism, when one
exists. -/
theorem mem_achievableDP_of_injective [Nonempty α] (hS : ∀ P ∈ S, ∀ x, 0 ≤ P x)
    {ι : α → β} (hι : ι.Injective) {Q : α → β → ℝ} (hQ₀ : ∀ x y, 0 ≤ Q x y)
    (hQ₁ : ∀ x, ∑ y, Q x y = 1)
    (hQD : ∀ P ∈ S, ∑ x, ∑ y, P x * Q x y * (if ι x = y then 0 else 1) ≤ D)
    (hε : IsLocalDP Q ε) : ε ∈ achievableDP S D := by
  obtain ⟨Q', hQ', hdp, hdist⟩ := exists_square_mechanism hι hQ₀ hQ₁
  exact ⟨Q', ⟨hQ', fun P hP ↦ (hdist P (hS P hP)).trans (hQD P hP)⟩, hdp ε hε⟩

end OutputAlphabet

/-! ### Zero leakage: Lemma 7 -/

section ZeroLeakage

variable [Fintype α] [DecidableEq α] {S : Set (α → ℝ)} {D : ℝ}

/-- **Lemma 7**, general form. Suppose every source law in `S` puts its largest mass on a common
symbol `x₀` (for a Class II source set, the first symbol). Then a `(S, D)`-valid `0`-differentially
private mechanism exists iff `1 - P(x₀) ≤ D` for every `P ∈ S`. -/
theorem zero_mem_achievableDP_iff {x₀ : α} (hS : ∀ P ∈ S, ∑ x, P x = 1)
    (hx₀ : ∀ P ∈ S, ∀ x, P x ≤ P x₀) :
    0 ∈ achievableDP S D ↔ ∀ P ∈ S, 1 - P x₀ ≤ D := by
  constructor
  · rintro ⟨Q, ⟨hQ, hQD⟩, hε⟩ P hP
    -- A `0`-DP mechanism has constant columns: `Q(y | x) = Q(y | x₀)`.
    have hcol (x y : α) : Q x y = Q x₀ y :=
      le_antisymm (by simpa using hε x x₀ y) (by simpa using hε x₀ x y)
    calc 1 - P x₀ = 1 - ∑ x, P x₀ * Q x₀ x := by
          rw [← mul_sum, Matrix.sum_row_of_mem_rowStochastic hQ, mul_one]
      _ ≤ 1 - ∑ x, P x * Q x₀ x := sub_le_sub_left (sum_le_sum fun x _ ↦
          mul_le_mul_of_nonneg_right (hx₀ P hP x) (Matrix.nonneg_of_mem_rowStochastic hQ)) 1
      _ = hammingDistortion P Q := by
          simp [hammingDistortion_eq hQ, mul_sub, sum_sub_distrib, hS P hP, hcol]
      _ ≤ D := hQD P hP
  · intro h
    have hQ : (fun _ y ↦ if y = x₀ then 1 else 0 : Matrix α α ℝ) ∈ Matrix.rowStochastic ℝ α :=
      Matrix.mem_rowStochastic_iff_sum.2 ⟨fun _ _ ↦ by split_ifs <;> norm_num, fun _ ↦ by simp⟩
    refine ⟨_, ⟨hQ, fun P hP ↦ ?_⟩, fun _ _ _ ↦ by simp⟩
    simpa [hammingDistortion_eq hQ, mul_sub, sum_sub_distrib, hS P hP] using h P hP

/-- **Lemma 7**, general form, stated for the optimal leakage: `ε*_DP(S, D) = 0` iff
`1 - P(x₀) ≤ D` for every `P ∈ S`, when all laws in `S` have a common mode `x₀`. -/
theorem isLeast_achievableDP_zero_iff {x₀ : α} (hS : ∀ P ∈ S, ∑ x, P x = 1)
    (hx₀ : ∀ P ∈ S, ∀ x, P x ≤ P x₀) :
    IsLeast (achievableDP S D) 0 ↔ ∀ P ∈ S, 1 - P x₀ ≤ D :=
  have : Nonempty α := ⟨x₀⟩
  ⟨fun h ↦ (zero_mem_achievableDP_iff hS hx₀).1 h.1, fun h ↦
    ⟨(zero_mem_achievableDP_iff hS hx₀).2 h, fun _ ⟨_, hQ, hε⟩ ↦ hε.nonneg hQ.1⟩⟩

end ZeroLeakage

/-! ### Class II source sets: Theorem 2 -/

section ClassII

variable {M : ℕ} {S : Set (Fin M → ℝ)} {D : ℝ}

/-- The reduction step of **Lemma 4**: for a Class II source set (laws nonincreasing on `Fin M`,
Remark 1), any privacy level achieved by a `(S, D)`-valid mechanism is achieved by one whose
distortions `D_i = 1 - Q(i | i)` are nondecreasing, `D_1 ≤ ⋯ ≤ D_M`. It is obtained by relabeling
the symbols so as to sort the distortions, using the rearrangement inequality. The paper's
Lemma 4 (existence of such an optimal mechanism) follows by applying this to an optimal
mechanism, when one exists. -/
theorem exists_monotone_distortion (hord : ∀ P ∈ S, Antitone P) {ε : ℝ}
    {Q : Matrix (Fin M) (Fin M) ℝ} (hQ : Q ∈ validMechanisms S D) (hε : IsLocalDP Q ε) :
    ∃ Q' ∈ validMechanisms S D, IsLocalDP Q' ε ∧ Monotone fun i ↦ 1 - Q' i i := by
  set g : Fin M → ℝ := fun i ↦ 1 - Q i i
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin M), Monotone (g ∘ σ) := ⟨_, Tuple.monotone_sort g⟩
  have hQ' : (fun i j ↦ Q (σ i) (σ j) : Matrix (Fin M) (Fin M) ℝ) ∈
      Matrix.rowStochastic ℝ (Fin M) := by
    refine Matrix.mem_rowStochastic_iff_sum.2
      ⟨fun i j ↦ Matrix.nonneg_of_mem_rowStochastic hQ.1, fun i ↦ ?_⟩
    rw [Equiv.sum_comp σ (Q (σ i)), Matrix.sum_row_of_mem_rowStochastic hQ.1]
  refine ⟨_, ⟨hQ', fun P hP ↦ ?_⟩, fun _ _ _ ↦ hε _ _ _, hσ⟩
  have h := ((hord P hP).antivary hσ).sum_mul_le_sum_mul_comp_perm
    (σ := σ⁻¹)
  have hPQ := hQ.2 P hP
  rw [hammingDistortion_eq hQ.1] at hPQ
  rw [hammingDistortion_eq hQ']
  simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, g] at h
  exact h.trans hPQ

/-- The distortion thresholds `D^(k) = max_{P ∈ S} ∑_{i = M - k + 1}^{M} P_i` of (9): the largest
total mass of the `k` least likely symbols, for a Class II source set whose laws are nonincreasing
on `Fin M` (Remark 1). It is a supremum over the (nonempty, bounded) set `S`. -/
noncomputable def distortionThreshold (S : Set (Fin M → ℝ)) (k : ℕ) : ℝ :=
  ⨆ P : S, ∑ i : Fin M with M ≤ i.val + k, (P : Fin M → ℝ) i

/-- There are at most `k` symbols among the `k` last ones. -/
lemma card_filter_le_add_le (k : ℕ) : #{i : Fin M | M ≤ (i : ℕ) + k} ≤ k := by
  calc #{i : Fin M | M ≤ (i : ℕ) + k}
      ≤ #(range k) := card_le_card_of_injOn (fun i : Fin M ↦ M - 1 - (i : ℕ))
        (fun i hi ↦ by simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi
                       simp only [coe_range, Set.mem_Iio]; omega)
        (fun i _ j _ h ↦ Fin.ext (by simp only at h; omega))
    _ = k := card_range k

/-- For a nonincreasing nonnegative `P` on `Fin M`, the `k` last symbols carry the least mass
among all sets of at least `k` symbols. -/
lemma sum_filter_le_sum_of_antitone {P : Fin M → ℝ} (hP₀ : ∀ i, 0 ≤ P i) (hP : Antitone P)
    {Z : Finset (Fin M)} {k : ℕ} (hk : k ≤ #Z) :
    ∑ i : Fin M with M ≤ i.val + k, P i ≤ ∑ i ∈ Z, P i := by
  set L : Finset (Fin M) := {i | M ≤ (i : ℕ) + k}
  have hLZ : #(L \ Z) ≤ #(Z \ L) :=
    card_sdiff_le_card_sdiff_iff.2 ((card_filter_le_add_le k).trans hk)
  have hlt : ∀ z ∈ Z \ L, ∀ l ∈ L \ Z, z ≤ l := by
    intro z hz l hl
    simp only [L, mem_sdiff, mem_filter, mem_univ, true_and, not_le] at hz hl
    exact Fin.le_def.2 (by omega)
  have key : ∑ i ∈ L \ Z, P i ≤ ∑ i ∈ Z \ L, P i := by
    rcases (Z \ L).eq_empty_or_nonempty with h | h
    · rw [h, card_empty, Nat.le_zero, card_eq_zero] at hLZ
      simp [h, hLZ]
    · calc ∑ i ∈ L \ Z, P i ≤ #(L \ Z) • P ((Z \ L).max' h) :=
            sum_le_card_nsmul _ _ _ fun l hl ↦ hP (hlt _ (max'_mem _ h) l hl)
        _ ≤ #(Z \ L) • P ((Z \ L).max' h) := nsmul_le_nsmul_left (hP₀ _) hLZ
        _ ≤ ∑ i ∈ Z \ L, P i := card_nsmul_le_sum _ _ _ fun i hi ↦ hP (le_max' _ i hi)
  calc ∑ i ∈ L, P i = ∑ i ∈ L ∩ Z, P i + ∑ i ∈ L \ Z, P i := (sum_inter_add_sum_sdiff L Z P).symm
    _ ≤ ∑ i ∈ Z ∩ L, P i + ∑ i ∈ Z \ L, P i := by rw [inter_comm]; gcongr
    _ = ∑ i ∈ Z, P i := sum_inter_add_sum_sdiff Z L P

/-- **Theorem 2(a)** (Lemma 8): for a nonempty Class II source set (nonnegative laws,
nonincreasing on `Fin M`) and `D < D^(k)`, no mechanism with `k` or more all-zero columns is
`(S, D)`-valid. -/
theorem notMem_validMechanisms_of_lt_distortionThreshold (hS₀ : ∀ P ∈ S, ∀ i, 0 ≤ P i)
    (hord : ∀ P ∈ S, Antitone P) (hne : S.Nonempty) {k : ℕ} {Q : Matrix (Fin M) (Fin M) ℝ}
    (hQ : Q ∈ Matrix.rowStochastic ℝ (Fin M)) (hk : k ≤ #{y | ∀ x, Q x y = 0})
    (hD : D < distortionThreshold S k) : Q ∉ validMechanisms S D := by
  have := hne.to_subtype
  obtain ⟨⟨P, hP⟩, hPD⟩ := exists_lt_of_lt_ciSup hD
  rintro ⟨-, hQD⟩
  have h : ∑ i with ∀ x, Q x i = 0, P i ≤ hammingDistortion P Q := by
    rw [hammingDistortion_eq hQ]
    calc ∑ i with ∀ x, Q x i = 0, P i = ∑ i with ∀ x, Q x i = 0, P i * (1 - Q i i) :=
          sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2 i]; ring
      _ ≤ ∑ i, P i * (1 - Q i i) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ mul_nonneg (hS₀ P hP i)
            (by linarith [Matrix.le_one_of_mem_rowStochastic hQ (i := i) (j := i)])
  linarith [sum_filter_le_sum_of_antitone (hS₀ P hP) (hord P hP) hk, hQD P hP]

/-- **Lemma 7** (and the last case of Theorem 2(b)): for a nonempty Class II source set,
`ε*_DP(S, D) = 0` iff `D ≥ D^(M-1)`. -/
theorem isLeast_achievableDP_zero_iff_distortionThreshold_le [NeZero M]
    (hS : ∀ P ∈ S, (∀ i, 0 ≤ P i) ∧ ∑ i, P i = 1) (hord : ∀ P ∈ S, Antitone P)
    (hne : S.Nonempty) :
    IsLeast (achievableDP S D) 0 ↔ distortionThreshold S (M - 1) ≤ D := by
  have := hne.to_subtype
  have hsum (P : Fin M → ℝ) (hP : P ∈ S) :
      ∑ i : Fin M with M ≤ i.val + (M - 1), P i = 1 - P 0 := by
    have h : ({i | M ≤ (i : ℕ) + (M - 1)} : Finset (Fin M)) = univ.erase 0 := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq, Fin.ext_iff, Fin.val_zero,
        and_true]
      have := NeZero.pos M
      omega
    rw [h, ← (hS P hP).2, ← add_sum_erase _ _ (mem_univ 0)]
    ring
  have hbdd : BddAbove
      (Set.range fun P : S ↦ ∑ i : Fin M with M ≤ i.val + (M - 1), (P : Fin M → ℝ) i) :=
    ⟨1, by
      rintro _ ⟨⟨P, hP⟩, rfl⟩
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ ↦ (hS P hP).1 i).trans
        (hS P hP).2.le⟩
  rw [isLeast_achievableDP_zero_iff (x₀ := 0) (fun P hP ↦ (hS P hP).2)
    (fun P hP i ↦ hord P hP (Fin.zero_le i)), distortionThreshold, ciSup_le_iff hbdd]
  simp only [Subtype.forall]
  exact forall₂_congr fun P hP ↦ by rw [hsum P hP]

/-- **Theorem 2(b)**, first case: for a nonempty Class II source set and `0 < D < D^(1)`, the
symmetric mechanism is optimal and `ε*_DP(S, D) = log ((M - 1)(1 - D) / D)`. -/
theorem isLeast_achievableDP_of_lt_distortionThreshold_one (hM : 2 ≤ M)
    (hS : ∀ P ∈ S, (∀ i, 0 ≤ P i) ∧ ∑ i, P i = 1) (hord : ∀ P ∈ S, Antitone P)
    (hne : S.Nonempty) (hD : 0 < D) (hD₁ : D < distortionThreshold S 1) :
    IsLeast (achievableDP S D) (log ((M - 1) * (1 - D) / D)) := by
  have : Nontrivial (Fin M) := Fin.nontrivial_iff_two_le.2 hM
  have := hne.to_subtype
  obtain ⟨⟨P, hP⟩, hPD⟩ := exists_lt_of_lt_ciSup hD₁
  -- Every symbol has probability larger than `D`, since the last one does.
  have hPx (x : Fin M) : D < P x := by
    refine hPD.trans_le ?_
    calc ∑ i : Fin M with M ≤ i.val + 1, P i ≤ #{i : Fin M | M ≤ (i : ℕ) + 1} • P x :=
          sum_le_card_nsmul _ _ _ fun i hi ↦ hord P hP <| by
            simp only [mem_filter, mem_univ, true_and] at hi
            exact Fin.le_def.2 (by omega)
      _ ≤ 1 • P x := nsmul_le_nsmul_left ((hS P hP).1 x) (card_filter_le_add_le 1)
      _ = P x := one_nsmul _
  have hM' : (1 : ℝ) ≤ M - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  simpa using isLeast_achievableDP_of_lt (fun P hP ↦ (hS P hP).2) hD (subset_convexHull ℝ S hP)
    fun x ↦ by simpa using (div_le_self hD.le hM').trans_lt (hPx x)

end ClassII

/-! ### Differential privacy bounds maximal leakage and mutual information -/

section Leakage

open MeasureTheory ProbabilityTheory

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {κ : Kernel α β}
  {ε : ℝ} [Fintype β] [MeasurableSingletonClass β] [IsMarkovKernel κ]

/-- If the channel `κ` is `ε`-differentially private, i.e. its matrix of transition probabilities
`(κ x {y})` is, then `∑_y max_x κ x {y} ≤ e^ε`. -/
lemma maxLeakageSum_le_of_isLocalDP [Nonempty α]
    (hκ : IsLocalDP (fun x y ↦ (κ x {y}).toReal) ε) :
    maxLeakageSum μ κ ≤ ENNReal.ofReal (exp ε) := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  calc maxLeakageSum μ κ ≤ ∑ y, ENNReal.ofReal (exp ε) * κ x₀ {y} := by
        refine sum_le_sum fun y _ ↦ iSup₂_le fun x _ ↦ ?_
        rw [← ENNReal.ofReal_toReal (measure_ne_top (κ x) {y}),
          ← ENNReal.ofReal_toReal (measure_ne_top (κ x₀) {y}),
          ← ENNReal.ofReal_mul (exp_pos ε).le]
        exact ENNReal.ofReal_le_ofReal (hκ x x₀ y)
    _ = ENNReal.ofReal (exp ε) := by simp [← mul_sum, sum_measure_singleton (μ := κ x₀)]

lemma toReal_maxLeakageSum_le_of_isLocalDP [Nonempty α]
    (hκ : IsLocalDP (fun x y ↦ (κ x {y}).toReal) ε) : (maxLeakageSum μ κ).toReal ≤ exp ε :=
  (ENNReal.toReal_mono ENNReal.ofReal_ne_top (maxLeakageSum_le_of_isLocalDP hκ)).trans_eq
    (ENNReal.toReal_ofReal (exp_pos ε).le)

-- The instances `[Countable α] [MeasurableSingletonClass α]` are not used in the proof: they
-- restrict the statement to purely atomic inputs, where `maxLeakage` is the operational quantity.
/-- **Differential privacy bounds maximal leakage**: if the channel `κ` is `ε`-differentially
private, then `L(X → Y) ≤ ε` for every nonzero input law `μ` on a countable alphabet with
measurable singletons (so that `μ` is purely atomic and `maxLeakage μ κ` is the operational
maximal leakage). The atom `x₀` exists for every nonzero such `μ`. -/
@[nolint unusedArguments]
theorem maxLeakage_le_of_isLocalDP [Countable α] [MeasurableSingletonClass α] {x₀ : α}
    (hx₀ : μ {x₀} ≠ 0) (hκ : IsLocalDP (fun x y ↦ (κ x {y}).toReal) ε) :
    maxLeakage μ κ ≤ ε := by
  have : Nonempty α := ⟨x₀⟩
  rw [maxLeakage, log_le_iff_le_exp (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx₀])]
  exact toReal_maxLeakageSum_le_of_isLocalDP hκ

omit [Fintype β] in
/-- **DP leakage upper bounds MI leakage** (Section III-A): if the channel `κ` is
`ε`-differentially private, then `I(X; X̂) ≤ ε` for every input law on a countable alphabet. In
particular the worst-case MI leakage `max_{P ∈ S} I(P; Q)` of (20) is at most the DP leakage. -/
theorem toReal_mutualInfo_compProd_le_of_isLocalDP [Finite β] [Countable α]
    [IsProbabilityMeasure μ]
    (hκ : IsLocalDP (fun x y ↦ (κ x {y}).toReal) ε) : (mutualInfo (μ ⊗ₘ κ)).toReal ≤ ε := by
  have := Fintype.ofFinite β
  obtain ⟨x, hx⟩ := MeasureTheory.Measure.exists_measure_singleton_ne_zero μ
  have : Nonempty α := ⟨x⟩
  refine toReal_mutualInfo_compProd_le_maxLeakage.trans ?_
  rw [maxLeakage, log_le_iff_le_exp (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx])]
  exact toReal_maxLeakageSum_le_of_isLocalDP hκ

end Leakage

end InformationTheory
