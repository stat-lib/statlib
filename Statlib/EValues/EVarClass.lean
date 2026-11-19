/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Statlib.EValues.EVariable

/-!
# Classes of e-variables

The existence proof of the numeraire (`Statlib.EValues.NumeraireExistence`) uses only a few
properties of the class `{X | IsEVar X S}` of e-variables for a set of measures `S`: it consists of
measurable functions, contains `1`, is convex and is closed under `liminf` of sequences. This file
isolates those properties in the predicate `IsEVarClass`, so that the results also apply to classes
which are not of the form `{X | IsEVar X S}`, for example classes obtained by adding a constraint
such as adaptedness.

## Main definitions

* `IsEVarClass 𝓔`: `𝓔` is a set of measurable functions containing `1`, convex and closed under
  `liminf` of sequences.
* `midSeq X`: the iterated midpoints of a sequence `X`, a convex combination of `X 0, …, X n` with
  positive weights.

## Main statements

* `isEVarClass_isEVar`: the e-variables for a set of measures of mass at most one form an
  `IsEVarClass`. The results proved for a class thus apply to e-variables.
* `IsEVarClass.inter`: the intersection of a class with a convex, `liminf`-closed set containing `1`
  is again a class.
* `IsEVarClass.exists_forall_ae_eq_top`: for an s-finite measure `P`, some element of the class is
  infinite wherever any other element is, up to a `P`-null set.
-/

@[expose] public section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Measure 𝓧} {S : Set (Measure 𝓧)}
  {𝓔 : Set (𝓧 → ℝ≥0∞)}

/-- A class of functions with the properties of the class of e-variables that the existence proof
of the numeraire uses: it consists of measurable functions, contains the constant `1`, is convex,
and is closed under `liminf` of sequences.

The class of e-variables for a set of measures of mass at most one is an example
(`isEVarClass_isEVar`). -/
structure IsEVarClass (𝓔 : Set (𝓧 → ℝ≥0∞)) : Prop where
  measurable ⦃X⦄ (hX : X ∈ 𝓔) : Measurable X
  one_mem : 1 ∈ 𝓔
  convex : Convex ℝ≥0∞ 𝓔
  liminf_mem (X : ℕ → 𝓧 → ℝ≥0∞) (hX : ∀ n, X n ∈ 𝓔) : (fun ω ↦ liminf (X · ω) atTop) ∈ 𝓔

lemma IsEVarClass.nonempty (h𝓔 : IsEVarClass 𝓔) : 𝓔.Nonempty := ⟨1, h𝓔.one_mem⟩

/-- The e-variables for a set of measures of mass at most one form an `IsEVarClass`. The bound on
the masses is what makes the constant `1` an e-variable (`isEVar_one_iff`). -/
lemma isEVarClass_isEVar (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, μ Set.univ ≤ 1) :
    IsEVarClass {X | IsEVar X S} where
  measurable _ hX := hX.measurable
  one_mem := isEVar_one hS
  convex := convex_isEVar S
  liminf_mem _ hX := isEVar_liminf hX

/-- Adding a constraint: the intersection of a class with a convex, `liminf`-closed set containing
`1` is again a class. -/
lemma IsEVarClass.inter (h𝓔 : IsEVarClass 𝓔) {C : Set (𝓧 → ℝ≥0∞)} (hC_one : 1 ∈ C)
    (hC_convex : Convex ℝ≥0∞ C)
    (hC_liminf : ∀ X : ℕ → 𝓧 → ℝ≥0∞, (∀ n, X n ∈ C) → (fun ω ↦ liminf (X · ω) atTop) ∈ C) :
    IsEVarClass (𝓔 ∩ C) where
  measurable _ hX := h𝓔.measurable hX.1
  one_mem := ⟨h𝓔.one_mem, hC_one⟩
  convex := h𝓔.convex.inter hC_convex
  liminf_mem X hX := ⟨h𝓔.liminf_mem X fun n ↦ (hX n).1, hC_liminf X fun n ↦ (hX n).2⟩

section TopSet

/-! ### The maximal set of infinities

The existence proof of the numeraire needs one element of the class to be infinite wherever any
other element is. This follows from `IsEVarClass` alone: we maximize the measure of the set of
infinities along a sequence and take iterated midpoints, which are infinite as soon as one of their
terms is. -/

/-- Iterated midpoints of a sequence: a convex combination of `X 0, …, X n` in which every term
has a positive weight, so it takes the value `∞` as soon as one of them does. -/
noncomputable def midSeq (X : ℕ → 𝓧 → ℝ≥0∞) : ℕ → 𝓧 → ℝ≥0∞
  | 0 => X 0
  | (n + 1) => (2 : ℝ≥0∞)⁻¹ • midSeq X n + (2 : ℝ≥0∞)⁻¹ • X (n + 1)

omit [MeasurableSpace 𝓧] in
@[simp]
lemma midSeq_zero (X : ℕ → 𝓧 → ℝ≥0∞) : midSeq X 0 = X 0 := rfl

omit [MeasurableSpace 𝓧] in
lemma midSeq_succ (X : ℕ → 𝓧 → ℝ≥0∞) (n : ℕ) :
    midSeq X (n + 1) = (2 : ℝ≥0∞)⁻¹ • midSeq X n + (2 : ℝ≥0∞)⁻¹ • X (n + 1) := rfl

lemma midSeq_mem (h𝓔 : IsEVarClass 𝓔) {X : ℕ → 𝓧 → ℝ≥0∞} (hX : ∀ n, X n ∈ 𝓔) (n : ℕ) :
    midSeq X n ∈ 𝓔 := by
  induction n with
  | zero => simpa using hX 0
  | succ k ih =>
    rw [midSeq_succ]
    exact h𝓔.convex ih (hX (k + 1)) (by simp) (by simp) ENNReal.inv_two_add_inv_two

omit [MeasurableSpace 𝓧] in
lemma midSeq_eq_top {X : ℕ → 𝓧 → ℝ≥0∞} {x : 𝓧} {n : ℕ} (hn : X n x = ∞) :
    ∀ m, n ≤ m → midSeq X m x = ∞ := by
  have h_inv : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  intro m
  induction m with
  | zero =>
    intro hm
    rw [Nat.le_zero] at hm
    subst hm
    simpa using hn
  | succ k ih =>
    intro hm
    have h_top : midSeq X k x = ∞ ∨ X (k + 1) x = ∞ := by
      rcases Nat.eq_or_lt_of_le hm with h | h
      · subst h
        exact .inr hn
      · exact .inl (ih (Nat.lt_succ_iff.mp h))
    rw [midSeq_succ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases h_top with h | h <;> simp [h, ENNReal.mul_top h_inv]

private lemma exists_forall_ae_eq_top_of_isFiniteMeasure (h𝓔 : IsEVarClass 𝓔) (P : Measure 𝓧)
    [IsFiniteMeasure P] :
    ∃ Z ∈ 𝓔, ∀ X ∈ 𝓔, ∀ᵐ x ∂P, X x = ∞ → Z x = ∞ := by
  have h_meas {X : 𝓧 → ℝ≥0∞} (hX : X ∈ 𝓔) : MeasurableSet {x | X x = ∞} :=
    (measurableSet_singleton _).preimage (h𝓔.measurable hX)
  -- maximize the measure of the set of infinities along a sequence
  set V := {y | ∃ X ∈ 𝓔, y = P {x | X x = ∞}} with hV_def
  have hV : V.Nonempty := ⟨P {x | (1 : 𝓧 → ℝ≥0∞) x = ∞}, ⟨1, h𝓔.one_mem, rfl⟩⟩
  have hV_bdd : BddAbove V := by
    refine ⟨P Set.univ, ?_⟩
    rintro _ ⟨X, -, rfl⟩
    exact measure_mono (Set.subset_univ _)
  obtain ⟨u, -, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sSup hV hV_bdd
  simp only [Set.mem_ofPred_eq, hV_def] at hu_mem
  choose X hX_mem hu_eq using hu_mem
  -- the iterated midpoints are infinite wherever any term of the sequence is
  set Z : 𝓧 → ℝ≥0∞ := fun x ↦ liminf (fun n ↦ midSeq X n x) atTop with hZ_def
  have hZ_mem : Z ∈ 𝓔 := h𝓔.liminf_mem _ (midSeq_mem h𝓔 hX_mem)
  have h_sub (n : ℕ) : {x | X n x = ∞} ⊆ {x | Z x = ∞} := by
    intro x hx
    have h_ev : ∀ᶠ m in atTop, midSeq X m x = ∞ :=
      eventually_atTop.mpr ⟨n, fun m hm ↦ midSeq_eq_top hx m hm⟩
    simp only [Set.mem_ofPred_eq, hZ_def]
    rw [liminf_congr h_ev]
    simp
  -- so `Z` attains the maximum
  have h_sSup : sSup V ≤ P {x | Z x = ∞} := by
    refine le_of_tendsto hu_tendsto (Eventually.of_forall fun n ↦ ?_)
    rw [hu_eq n]
    exact measure_mono (h_sub n)
  refine ⟨Z, hZ_mem, fun Y hY ↦ ?_⟩
  -- the midpoint of `Z` and `Y` is infinite on the union of the two sets of infinities
  have hW_mem : (2 : ℝ≥0∞)⁻¹ • Z + (2 : ℝ≥0∞)⁻¹ • Y ∈ 𝓔 :=
    h𝓔.convex hZ_mem hY (by simp) (by simp) ENNReal.inv_two_add_inv_two
  have hW_eq : {x | ((2 : ℝ≥0∞)⁻¹ • Z + (2 : ℝ≥0∞)⁻¹ • Y) x = ∞}
      = {x | Z x = ∞} ∪ {x | Y x = ∞} := by
    ext x
    simp [ENNReal.add_eq_top, ENNReal.mul_eq_top]
  have h_union_le : P ({x | Z x = ∞} ∪ {x | Y x = ∞}) ≤ P {x | Z x = ∞} := by
    rw [← hW_eq]
    have hW_V : P {x | ((2 : ℝ≥0∞)⁻¹ • Z + (2 : ℝ≥0∞)⁻¹ • Y) x = ∞} ∈ V := ⟨_, hW_mem, rfl⟩
    exact (le_sSup hW_V).trans h_sSup
  -- hence the part of `{Y = ∞}` outside `{Z = ∞}` is `P`-null
  rw [ae_iff]
  have h_eq : {x | ¬(Y x = ∞ → Z x = ∞)} = {x | Y x = ∞} \ {x | Z x = ∞} := by ext; simp
  rw [h_eq]
  have h_add : P {x | Z x = ∞} + P ({x | Y x = ∞} \ {x | Z x = ∞})
      = P ({x | Z x = ∞} ∪ {x | Y x = ∞}) := by
    rw [← measure_union disjoint_sdiff_self_right ((h_meas hY).diff (h_meas hZ_mem)),
      Set.union_sdiff_self]
  have h_le : P {x | Z x = ∞} + P ({x | Y x = ∞} \ {x | Z x = ∞}) ≤ P {x | Z x = ∞} + 0 := by
    rw [h_add, add_zero]
    exact h_union_le
  simpa using (ENNReal.add_le_add_iff_left (measure_ne_top P _)).mp h_le

/-- **A class of e-variables has a `P`-maximal set of infinities.** For an s-finite measure `P`,
some element of `𝓔` is `∞` wherever any other element of `𝓔` is, up to a `P`-null set. -/
theorem IsEVarClass.exists_forall_ae_eq_top (h𝓔 : IsEVarClass 𝓔) (P : Measure 𝓧) [SFinite P] :
    ∃ Z ∈ 𝓔, ∀ X ∈ 𝓔, ∀ᵐ x ∂P, X x = ∞ → Z x = ∞ := by
  obtain ⟨Z, hZ, h⟩ := exists_forall_ae_eq_top_of_isFiniteMeasure h𝓔 P.toFinite
  exact ⟨Z, hZ, fun X hX ↦ (absolutelyContinuous_toFinite P).ae_le (h X hX)⟩

end TopSet

end ProbabilityTheory
