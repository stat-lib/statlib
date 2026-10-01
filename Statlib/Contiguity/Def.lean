/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Contiguity

Filter-based definitions of contiguity for families of probability measures.

Only completed definitions and proofs are Lean declarations. Planned characterizations are retained
as `TODO` comments so that unproved or AI-generated proofs do not enter the trusted environment.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set

variable {α : Type*} {Ω : α → Type*} [∀ a, MeasurableSpace (Ω a)]

/-
Some definitions can be stated for `Measure` rather than `ProbabilityMeasure`. We use
`ProbabilityMeasure` throughout to avoid coercion issues between the definitions and because its
topology is needed below.
-/

section Definitions

/-- Contiguity tested along every subfilter of `l` using measurable sets. -/
def Contiguous1 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ ⦃s : ∀ a, Set (Ω a)⦄ ⦃h : Filter α⦄, (∀ a, MeasurableSet (s a)) → h ≤ l →
    Tendsto (fun a => P a (s a)) h (𝓝 0) → Tendsto (fun a => Q a (s a)) h (𝓝 0)

/-- Contiguity characterized by weak limits of laws of Radon–Nikodym derivatives.

The subfilter `h` is required to be nontrivial because otherwise `Tendsto ... h ...` follows
trivially from `Filter.tendsto_bot`.
-/
def Contiguous2 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (L : ProbabilityMeasure ℝ≥0∞) ⦃h : Filter α⦄, h ≤ l → h.NeBot →
    Tendsto (fun a => (Q a).map
      ((Measure.measurable_rnDeriv (P a) (Q a)).aemeasurable)) h (𝓝 L) →
      L {0} = 0

/-- Contiguity characterized by unit mean for weak limits of reciprocal likelihood-ratio laws. -/
def Contiguous3 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (V : ProbabilityMeasure ℝ≥0∞) ⦃h : Filter α⦄, h ≤ l → h.NeBot →
    Tendsto (fun a => (P a).map
      ((Measure.measurable_rnDeriv (Q a) (P a)).aemeasurable)) h (𝓝 V) →
      ∫⁻ ω, ω ∂V = 1

/-- Convergence in measure for a family of probability measures on varying measurable spaces. -/
def TendstoInMeasure (μ : ∀ a, ProbabilityMeasure (Ω a))
    (f : ∀ a, Ω a → ℝ) (l : Filter α) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i => μ i {x | ε ≤ |f i x|}) l (𝓝 0)

/-- Contiguity formulated as preservation of convergence in measure along every subfilter of `l`. -/
def Contiguous4 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (T : ∀ a, Ω a → ℝ) ⦃h : Filter α⦄, h ≤ l → TendstoInMeasure P T h →
    TendstoInMeasure Q T h

/-- Contiguity tested directly along `l` using measurable sets. -/
def Contiguous5 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ ⦃s : ∀ a, Set (Ω a)⦄, (∀ a, MeasurableSet (s a)) →
    Tendsto (fun a => P a (s a)) l (𝓝 0) → Tendsto (fun a => Q a (s a)) l (𝓝 0)

end Definitions

section BasicResults

lemma NNReal.tendsto_of_tendsto_of_le {l : Filter α} {f g : α → ℝ≥0}
    (hfg : ∀ᶠ a in l, f a ≤ g a) (hg : Tendsto g l (𝓝 0)) :
    Tendsto f l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) hg (by simp) hfg

lemma setOf_le_abs_indicator_one_eq {β : Type*} (s : Set β) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    {x | ε ≤ |s.indicator (fun _ => (1 : ℝ)) x|} = s := by
  ext x
  by_cases hx : x ∈ s
  · simp [hx, hε1]
  · simp [hx, hε0.not_ge]

/-- Given `0 < δ`, it suffices to check `0 < ε ≤ δ` to conclude convergence in measure. -/
lemma tendstoInMeasure_iff_forall_le {μ : ∀ a, ProbabilityMeasure (Ω a)}
    {f : ∀ a, Ω a → ℝ} {l : Filter α} {δ : ℝ} (hδ : 0 < δ) :
    TendstoInMeasure μ f l ↔
      ∀ ε, 0 < ε → ε ≤ δ →
        Tendsto (fun i => μ i {x | ε ≤ |f i x|}) l (𝓝 0) := by
  refine ⟨fun h ε hε _ => h ε hε, fun h ε hε => ?_⟩
  by_cases! hεδ : ε ≤ δ
  · exact h ε hε hεδ
  · refine NNReal.tendsto_of_tendsto_of_le ?_ (h δ hδ le_rfl)
    filter_upwards with i using (μ i).apply_mono fun x hx => hεδ.le.trans hx

/-- The probabilities of sets tend to zero iff their indicators tend to zero in measure. -/
lemma tendstoInMeasure_iff (s : ∀ a, Set (Ω a))
    (P : ∀ a, ProbabilityMeasure (Ω a)) (l : Filter α) :
    Tendsto (fun a => P a (s a)) l (𝓝 0) ↔
      TendstoInMeasure P (fun a => (s a).indicator fun _ => 1) l where
  mp ht := by
    refine (tendstoInMeasure_iff_forall_le zero_lt_one).2 fun ε hε hε1 => ?_
    exact ht.congr fun a => by rw [setOf_le_abs_indicator_one_eq (s a) hε hε1]
  mpr ht :=
    (ht 1 zero_lt_one).congr fun a => by
      rw [setOf_le_abs_indicator_one_eq (s a) zero_lt_one le_rfl]

theorem contiguous1_iff_contiguous4 {l : Filter α}
    (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    Contiguous1 l P Q ↔ Contiguous4 l P Q where
  mp hc := by
    refine fun s h hle hp ε hε => NNReal.tendsto_of_tendsto_of_le
      (g := fun a => Q a (toMeasurable (P a) {x | ε ≤ |s a x|})) ?_ ?_
    · filter_upwards with a using (Q a).apply_mono <| subset_toMeasurable _ _
    · refine hc (fun a => measurableSet_toMeasurable _ _) hle ((hp ε hε).congr ?_)
      simp [← ENNReal.coe_inj]
  mpr hc := by
    refine fun s h hms hle hp => (tendstoInMeasure_iff s Q h).2 ?_
    exact hc (fun a => (s a).indicator (fun _ => 1)) hle <|
      (tendstoInMeasure_iff s P h).1 hp

theorem Filter.tendsto_of_forall_filter_le_exists_tendsto
    {α β : Type*} {f : α → β} {l : Filter α} {lb : Filter β}
    (h : ∀ m, m ≤ l → ∃ n, n ≤ m ∧ n.NeBot ∧ Tendsto f n lb) :
    Tendsto f l lb := by
  by_contra hlim
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hlim
  let m := l ⊓ principal {x | f x ∉ s}
  obtain ⟨n, hnle, hnne, hnt⟩ := h m inf_le_left
  exact hnne.ne (eventually_false_iff_eq_bot.1 ((hnt.eventually_mem hs).mp
    (hnle (mem_inf_of_right (by simp)))))

theorem Contiguous1.contiguous5 {l : Filter α} {P Q : ∀ a, ProbabilityMeasure (Ω a)}
    (hPQ : Contiguous1 l P Q) : Contiguous5 l P Q :=
  fun _ hs hP => hPQ hs le_rfl hP

end BasicResults

section PlannedCharacterizations

/- TODO: Prove that `Contiguous1` implies `Contiguous2`.
theorem Contiguous1.contiguous2 {l : Filter α}
    (P Q : ∀ a, ProbabilityMeasure (Ω a))
    (hPQ : Contiguous1 l P Q) : Contiguous2 l P Q
-/

/- TODO: Prove the equivalence of `Contiguous2` and `Contiguous3`.
theorem contiguous2_iff_contiguous3 {l : Filter α}
    (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    Contiguous2 l P Q ↔ Contiguous3 l P Q
-/

/- TODO: Prove that `Contiguous3` implies `Contiguous1`.
theorem Contiguous3.contiguous1 {l : Filter α}
    (P Q : ∀ a, ProbabilityMeasure (Ω a))
    (hPQ : Contiguous3 l P Q) : Contiguous1 l P Q
-/

/- TODO: Prove that the first four definitions of contiguity are equivalent.
theorem Contiguous.TFAE {l : Filter α}
    (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    List.TFAE [Contiguous1 l P Q, Contiguous2 l P Q, Contiguous3 l P Q, Contiguous4 l P Q]
-/

/- TODO: Replace the AI-generated proof with a reviewed proof.
theorem Contiguous5.contiguous1_of_hasAntitoneBasis_le_cofinite {l : Filter α}
    {P Q : ∀ a, ProbabilityMeasure (Ω a)} {b : ℕ → Set α}
    (hPQ : Contiguous5 l P Q) (hb : l.HasAntitoneBasis b) (hl : l ≤ cofinite) :
    Contiguous1 l P Q
-/

/- TODO: Prove the countably generated specialization after the antitone-basis result.
theorem Contiguous5.contiguous1_of_isCountablyGenerated_le_cofinite {l : Filter α}
    [l.IsCountablyGenerated] {P Q : ∀ a, ProbabilityMeasure (Ω a)}
    (hPQ : Contiguous5 l P Q) (hl : l ≤ cofinite) : Contiguous1 l P Q
-/

section Nat

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P Q : ∀ n, ProbabilityMeasure (Ω n)}

/- TODO: Prove the `atTop` specialization of `Contiguous5 → Contiguous1`.
theorem Contiguous5.contiguous1_atTop (hPQ : Contiguous5 atTop P Q) :
    Contiguous1 atTop P Q
-/

/- TODO: Prove the equivalence of `Contiguous1` and `Contiguous5` for sequences.
theorem contiguous5_atTop_iff_contiguous1 :
    Contiguous1 atTop P Q ↔ Contiguous5 atTop P Q
-/

/- TODO: Prove that all five definitions are equivalent for sequences.
theorem Contiguous.nat_TFAE :
    List.TFAE [Contiguous1 atTop P Q, Contiguous2 atTop P Q, Contiguous3 atTop P Q,
      Contiguous4 atTop P Q, Contiguous5 atTop P Q]
-/

end Nat

end PlannedCharacterizations
