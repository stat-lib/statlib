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
public import Mathlib.Tactic.TFAE

/-!
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set

variable {α : Type*} {Ω : α → Type*} [∀ a, MeasurableSpace (Ω a)]

/-
Some definitions can actually be defined for `Measure` instead of `ProbabilityMeasure`, but to avoid
coercion issues when we prove equivalences between them, we use `ProbabilityMeasure` in all these
definitions. Also we don't want to use the typeclass assumption `IsProbabilityMeasure` because we
need to use the topology on `ProbabilityMeasure`.
-/

section Definitions

def Contiguous1 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ ⦃s : ∀ a, Set (Ω a)⦄ ⦃h : Filter α⦄, (∀ a, MeasurableSet (s a)) → h ≤ l →
    Tendsto (fun a => P a (s a)) h (𝓝 0) → Tendsto (fun a => Q a (s a)) h (𝓝 0)

/-- We require `h` to be nontrivial in the following definition because otherwise
`Tendsto ... h ...` is trivial by `Filter.tendsto_bot`. -/
def Contiguous2 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (L : ProbabilityMeasure ℝ≥0∞) ⦃h : Filter α⦄, h ≤ l → h.NeBot →
    Tendsto (fun a => (Q a).map ((Measure.measurable_rnDeriv (P a) (Q a)).aemeasurable)) h (𝓝 L) →
      L {0} = 0

def Contiguous3 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (V : ProbabilityMeasure ℝ≥0∞) ⦃h : Filter α⦄, h ≤ l → h.NeBot →
    Tendsto (fun a => (P a).map ((Measure.measurable_rnDeriv (Q a) (P a)).aemeasurable)) h (𝓝 V) →
      ∫⁻ ω, ω ∂V = 1

/-- The following notion of convergence in measure is introduced because the current mathlib
version only support for a single measure. -/
def TendstoInMeasure (μ : ∀ α, ProbabilityMeasure (Ω α)) (f : ∀ α, Ω α → ℝ) (l : Filter α) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i => μ i { x | ε ≤ |f i x| }) l (𝓝 0)

def Contiguous4 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ (T : ∀ α, Ω α → ℝ) ⦃h : Filter α⦄, h ≤ l → TendstoInMeasure P T h →
    TendstoInMeasure Q T h

/-- This corresponds to the definition of sequences for contiguity. -/
def Contiguous5 (l : Filter α) (P Q : ∀ a, ProbabilityMeasure (Ω a)) : Prop :=
  ∀ ⦃s : ∀ a, Set (Ω a)⦄, (∀ a, MeasurableSet (s a)) →
    Tendsto (fun a => P a (s a)) l (𝓝 0) → Tendsto (fun a => Q a (s a)) l (𝓝 0)

end Definitions

section -- Contiguous1 and contiguous4 are equivalent.

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

/-- Given `0 < δ`. We only need to check convergence for `0 < ε ≤ δ` to conclude convergence in
measure. -/
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

/-- The probability of a sequence of sets converges to zero iff their corresponding indicator
functions converge in measure to zero. -/
lemma tendstoInMeasure_iff (s : ∀ a, Set (Ω a)) (P : ∀ a, ProbabilityMeasure (Ω a)) (l : Filter α) :
    Tendsto (fun a => (P a) (s a)) l (𝓝 0) ↔
      TendstoInMeasure P (fun a => (s a).indicator fun _ => 1) l where
  mp ht := by
    refine (tendstoInMeasure_iff_forall_le zero_lt_one).2 fun ε hε hε1 => ?_
    exact ht.congr fun a => by rw [setOf_le_abs_indicator_one_eq (s a) hε hε1]
  mpr ht :=
    (ht 1 zero_lt_one).congr fun a => by rw [setOf_le_abs_indicator_one_eq (s a) zero_lt_one le_rfl]

theorem contiguous1_iff_contiguous4 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    Contiguous1 l P Q ↔ Contiguous4 l P Q where
  mp hc := by
    refine fun s h hle hp ε hε => NNReal.tendsto_of_tendsto_of_le
      (g := fun a => (Q a) (toMeasurable (P a) {x | ε ≤ |s a x|})) ?_ ?_
    · filter_upwards with a using (Q a).apply_mono <| subset_toMeasurable _ _
    · refine hc (fun a => measurableSet_toMeasurable _ _) hle ((hp ε hε).congr ?_)
      simp [← ENNReal.coe_inj]
  mpr hc := by
    refine fun s h hms hle hp => (tendstoInMeasure_iff s Q h).2 ?_
    exact hc (fun a => (s a).indicator (fun _ => 1)) hle <| (tendstoInMeasure_iff s P h).1 hp

section -- Contiguous1 implies contiguous2

theorem Contiguous1.contiguous2 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a))
    (hPQ : Contiguous1 l P Q) : Contiguous2 l P Q := by
  sorry

end

section -- Contiguous2 and contiguous3 are equivalent

theorem contiguous2_iff_contiguous3 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    Contiguous2 l P Q ↔ Contiguous3 l P Q := by
  sorry

end

section -- Contiguous3 implies contiguous1

theorem Filter.tendsto_of_forall_filter_le_exists_tendsto {α β : Type*} {f : α → β} {l : Filter α}
    {lb : Filter β} (h : ∀ m, m ≤ l → ∃ n, n ≤ m ∧ n.NeBot ∧ Tendsto f n lb) :
    Tendsto f l lb := by
  by_contra hlim
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hlim
  let m := l ⊓ principal {x | f x ∉ s}
  obtain ⟨n, hnle, hnne, hnt⟩ := h m inf_le_left
  exact hnne.ne (eventually_false_iff_eq_bot.1 ((hnt.eventually_mem hs).mp
    (hnle (mem_inf_of_right (by simp)))))

theorem Contiguous3.contiguous1 {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a))
    (hPQ : Contiguous3 l P Q) : Contiguous1 l P Q := by
  refine fun s h hsm hle hP => tendsto_of_forall_filter_le_exists_tendsto ?_
  sorry

end

/-- The first four definitions of contiguity are equivalent. -/
theorem Contiguous.TFAE {l : Filter α} (P Q : ∀ a, ProbabilityMeasure (Ω a)) :
    List.TFAE [Contiguous1 l P Q, Contiguous2 l P Q, Contiguous3 l P Q, Contiguous4 l P Q] := by
  tfae_have 1 ↔ 4 := (contiguous1_iff_contiguous4 P Q)
  tfae_have 2 ↔ 3 := (contiguous2_iff_contiguous3 P Q)
  tfae_have 1 → 2 := fun h => h.contiguous2
  tfae_have 3 → 1 := fun h => h.contiguous1
  tfae_finish

section -- Contiguous5 and contiguous1 are equivalent.

theorem Contiguous1.contiguous5 {l : Filter α} {P Q : ∀ a, ProbabilityMeasure (Ω a)}
    (hPQ : Contiguous1 l P Q) : Contiguous5 l P Q :=
  fun _ hs hP => hPQ hs le_rfl hP

/-- TODO: This proof is generated by codex and needs to be cleaned up. -/
theorem Contiguous5.contiguous1_of_hasAntitoneBasis_le_cofinite {l : Filter α}
    {P Q : ∀ a, ProbabilityMeasure (Ω a)} {b : ℕ → Set α} (hPQ : Contiguous5 l P Q)
    (hb : l.HasAntitoneBasis b) (hl : l ≤ cofinite) : Contiguous1 l P Q := by
  intro s h hs hle hP
  by_contra hQ
  have hP_small : ∀ δ, 0 < δ → ∀ᶠ a in h, P a (s a) < δ := by
    simpa only [mem_Iio] using (NNReal.nhds_zero_basis.tendsto_right_iff.1 hP)
  rw [NNReal.nhds_zero_basis.tendsto_right_iff] at hQ
  simp only [mem_Iio] at hQ
  push Not at hQ
  obtain ⟨ε, hε, hQε⟩ := hQ
  classical
  have hchoose : ∀ k : ℕ, ∃ a : α,
      ε ≤ Q a (s a) ∧ P a (s a) < (((k + 1 : ℕ) : ℝ≥0)⁻¹) ∧ a ∈ b k := by
    intro k
    have hPk : ∀ᶠ a in h, P a (s a) < (((k + 1 : ℕ) : ℝ≥0)⁻¹) :=
      hP_small _ (by positivity)
    have hbk : ∀ᶠ a in h, a ∈ b k := hle (hb.mem k)
    exact (hQε.and_eventually (hPk.and hbk)).exists
  choose u hu using hchoose
  let t : ∀ a, Set (Ω a) := fun a => if ∃ k, u k = a then s a else ∅
  have ht_meas : ∀ a, MeasurableSet (t a) := by
    intro a
    by_cases ha : ∃ k, u k = a
    · simp [t, ha, hs a]
    · simp [t, ha]
  have htP : Tendsto (fun a => P a (t a)) l (𝓝 0) := by
    rw [NNReal.nhds_zero_basis.tendsto_right_iff]
    intro δ hδ
    obtain ⟨K, hKpos, hK⟩ := NNReal.exists_nat_pos_inv_lt hδ
    let F : Set α := u '' {k | k < K}
    have hFfinite : F.Finite := (Set.finite_lt_nat K).image u
    filter_upwards [hl hFfinite.compl_mem_cofinite] with a haF
    by_cases harange : ∃ k, u k = a
    · rcases harange with ⟨k, rfl⟩
      have hkge : K ≤ k := by
        by_contra hk
        exact haF ⟨k, Nat.lt_of_not_ge hk, rfl⟩
      have hle_inv : (((k + 1 : ℕ) : ℝ≥0)⁻¹) ≤ (K : ℝ≥0)⁻¹ := by
        exact inv_anti₀ (by exact_mod_cast hKpos) (by exact_mod_cast hkge.trans k.le_succ)
      have huk_range : ∃ j, u j = u k := ⟨k, rfl⟩
      simpa [t, huk_range] using ((hu k).2.1.trans_le hle_inv).trans hK
    · simp [t, harange, hδ]
  have htQ : Tendsto (fun a => Q a (t a)) l (𝓝 0) := hPQ ht_meas htP
  have hu_tendsto : Tendsto u atTop l := hb.tendsto fun k => (hu k).2.2
  have hcomp : Tendsto (fun k => Q (u k) (t (u k))) atTop (𝓝 0) := htQ.comp hu_tendsto
  have hsmall : ∀ᶠ k : ℕ in atTop, Q (u k) (t (u k)) < ε :=
    (NNReal.nhds_zero_basis.tendsto_right_iff.1 hcomp) ε hε
  have hlarge : ∀ᶠ k : ℕ in atTop, ε ≤ Q (u k) (t (u k)) := by
    filter_upwards with k
    have huk_range : ∃ j, u j = u k := ⟨k, rfl⟩
    simpa [t, huk_range] using (hu k).1
  obtain ⟨k, hleε, hltε⟩ := (hlarge.and hsmall).exists
  exact (not_lt_of_ge hleε) hltε

/-- Contiguous5 implies contiguous1 under the assumption that the filter `l` is countably generated
and `≤ cofinite`. -/
theorem Contiguous5.contiguous1_of_isCountablyGenerated_le_cofinite {l : Filter α}
    [l.IsCountablyGenerated] {P Q : ∀ a, ProbabilityMeasure (Ω a)}
    (hPQ : Contiguous5 l P Q) (hl : l ≤ cofinite) : Contiguous1 l P Q := by
  obtain ⟨b, _, hb⟩ := (Filter.basis_sets l).exists_antitone_subbasis
  exact hPQ.contiguous1_of_hasAntitoneBasis_le_cofinite hb hl

section Nat

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P Q : ∀ n, ProbabilityMeasure (Ω n)}

theorem Contiguous5.contiguous1_atTop (hPQ : Contiguous5 atTop P Q) :
    Contiguous1 atTop P Q := by
  refine hPQ.contiguous1_of_hasAntitoneBasis_le_cofinite (b := Set.Ici) ?_ atTop_le_cofinite
  exact ⟨atTop_basis, fun _ _ hij _ hx => hij.trans hx⟩

theorem contiguous5_atTop_iff_contiguou1 :
    Contiguous1 atTop P Q ↔ Contiguous5 atTop P Q :=
  ⟨Contiguous1.contiguous5, Contiguous5.contiguous1_atTop⟩

end Nat

end

#min_imports -- Let's keep this until we finish all the proof.
