/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Jonas Bayer, Simon (Citronhat)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# A Komlós lemma for `ℝ≥0∞`-valued functions

Komlós-type lemmas state that a sequence which is bounded in a suitable sense admits a sequence of
*forward convex combinations*, that is, `g n ∈ convexHull (Set.range fun m ↦ f (n + m))`, which
converges in a suitable sense. We prove that for any sequence of measurable `ℝ≥0∞`-valued functions
and any s-finite measure, some forward convex combinations converge almost everywhere. No
boundedness or integrability is needed, since the limit is allowed to take the value `∞`.

The proof has two steps.

* `komlos_convex`: for any function `φ` which is bounded below everywhere and bounded above on the
  sequence, some forward convex combinations make the midpoint defect
  `φ (g n) / 2 + φ (g m) / 2 - φ ((g n + g m) / 2)` arbitrarily small for large `n` and `m`.
  This is done by choosing `g n` to almost minimize `φ` over the convex hull of the `n`-th tail.
* `MeasureTheory.komlos_ennreal_of_isFiniteMeasure`: for a finite measure `P`, we apply
  `komlos_convex` to `φ Y = ∫ exp (-Y) ^ 2 ∂P`. Since
  `exp (-(x + y) / 2) ^ 2 = exp (-x) * exp (-y)`, the midpoint defect of `φ` is exactly half the
  squared `L²` distance between `exp (-g n)` and `exp (-g m)`. Hence `exp (-g n)` is Cauchy in
  `L²`, a subsequence converges almost everywhere, and so does the corresponding subsequence of
  `g n`, since `x ↦ exp (-x)` is a homeomorphism from `ℝ≥0∞` onto `[0, 1]`. The case of an
  s-finite measure follows by passing to an equivalent finite measure.

## Main statements

* `komlos_convex`: abstract Komlós lemma, for a function `φ` on a module.
* `MeasureTheory.komlos_ennreal`: **Komlós lemma** for `ℝ≥0∞`-valued functions and an s-finite
  measure.

## References

This file is adapted from the Brownian motion project
(https://github.com/RemyDegenne/brownian-motion): `komlos_convex` is from the file
`BrownianMotion/StochasticIntegral/Komlos.lean`, by Rémy Degenne and Jonas Bayer, and the strategy
of the proof of `komlos_ennreal` (transform by `x ↦ exp (-x)` and apply `komlos_convex`) is from the
pull request https://github.com/RemyDegenne/brownian-motion/pull/358, by Simon (Citronhat).
The identity relating the midpoint defect to the `L²` distance replaces the compactness argument
of that pull request.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- **Abstract Komlós lemma.** Let `φ` be bounded below, and bounded above on the sequence `f`.
Then there are forward convex combinations `g n` of `f` such that the midpoint defect
`φ (g n) / 2 + φ (g m) / 2 - φ ((g n + g m) / 2)` is arbitrarily small for `n` and `m` large. -/
theorem komlos_convex {R E : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommMonoid E] [Module R E] {f : ℕ → E} {φ : E → ℝ} (hφ_bddBelow : BddBelow (range φ))
    (hφ_bddAbove : BddAbove (range fun n ↦ φ (f n))) :
    ∃ g : ℕ → E, (∀ n, g n ∈ convexHull R (range fun m ↦ f (n + m))) ∧
      ∀ δ > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
        2⁻¹ * φ (g n) + 2⁻¹ * φ (g m) - φ ((2 : R)⁻¹ • (g n + g m)) < δ := by
  -- the convex hulls `C n` of the tails of `f` decrease
  set C : ℕ → Set E := fun n ↦ convexHull R (range fun m ↦ f (n + m))
  have hC_anti : Antitone C := by
    refine antitone_nat_of_succ_le fun n ↦ convexHull_mono ?_
    rintro _ ⟨m, rfl⟩
    exact ⟨m + 1, by simp only [add_assoc, add_comm 1 m]⟩
  have hf_mem n : f n ∈ C n := subset_convexHull R _ ⟨0, rfl⟩
  have hC_ne n : (φ '' C n).Nonempty := ⟨_, mem_image_of_mem φ (hf_mem n)⟩
  have hC_bdd n : BddBelow (φ '' C n) :=
    hφ_bddBelow.mono (image_subset_range _ _)
  -- the infimum `r n` of `φ` on `C n` increases to a limit `A`
  set r : ℕ → ℝ := fun n ↦ sInf (φ '' C n)
  have hr_mono : Monotone r := fun n m hnm ↦
    csInf_le_csInf (hC_bdd n) (hC_ne m) (image_mono (hC_anti hnm))
  obtain ⟨M, hM⟩ := hφ_bddAbove
  have hr_bdd : BddAbove (range r) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (csInf_le (hC_bdd n) (mem_image_of_mem φ (hf_mem n))).trans (hM ⟨n, rfl⟩)
  set A := ⨆ n, r n
  have hr_tendsto : Tendsto r atTop (𝓝 A) := tendsto_atTop_ciSup hr_mono hr_bdd
  -- choose `g n ∈ C n` with `φ (g n) < r n + 1 / (n + 1)`
  have h_exists n : ∃ x ∈ C n, φ x < r n + 1 / (n + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hx_lt⟩ :=
      exists_lt_of_csInf_lt (hC_ne n) (lt_add_of_pos_right (r n) Nat.one_div_pos_of_nat)
    exact ⟨x, hx, hx_lt⟩
  choose g hg_mem hg_lt using h_exists
  refine ⟨g, hg_mem, fun δ hδ ↦ ?_⟩
  obtain ⟨N, hN_r, hN_inv⟩ : ∃ N, A - δ / 2 < r N ∧ 1 / ((N : ℝ) + 1) < δ / 2 :=
    ((hr_tendsto.eventually (lt_mem_nhds (by linarith))).and
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by linarith)))).exists
  refine ⟨N, fun n hn m hm ↦ ?_⟩
  -- the midpoint of `g n` and `g m` lies in `C N`, hence `φ` is at least `r N` there
  have h_mid : (2 : R)⁻¹ • (g n + g m) ∈ C N := by
    rw [smul_add]
    exact convex_convexHull R _ (hC_anti hn (hg_mem n)) (hC_anti hm (hg_mem m))
      (by positivity) (by positivity) (by rw [← one_div]; exact add_halves 1)
  have h_mid_ge : r N ≤ φ ((2 : R)⁻¹ • (g n + g m)) := csInf_le (hC_bdd N) ⟨_, h_mid, rfl⟩
  -- and `φ (g k) < A + δ / 2` for `k ≥ N`
  have hg_le k (hk : N ≤ k) : φ (g k) < A + δ / 2 := by
    refine (hg_lt k).trans_le (add_le_add (le_ciSup hr_bdd k) ?_)
    exact (Nat.one_div_le_one_div hk).trans hN_inv.le
  linarith [hg_le n hn, hg_le m hm]

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Komlos

/-- The map `x ↦ exp (-x)` from `ℝ≥0∞` to `[0, 1]`, with value `0` at `∞`. -/
noncomputable def expNeg (x : ℝ≥0∞) : ℝ := (EReal.exp (-x)).toReal

lemma expNeg_of_ne_top {x : ℝ≥0∞} (hx : x ≠ ∞) : expNeg x = Real.exp (-x.toReal) := by
  lift x to ℝ≥0 using hx
  simp [expNeg, EReal.coe_nnreal_eq_coe_real, ← EReal.coe_neg, Real.exp_nonneg]

@[simp]
lemma expNeg_top : expNeg ∞ = 0 := by simp [expNeg]

lemma expNeg_nonneg (x : ℝ≥0∞) : 0 ≤ expNeg x := ENNReal.toReal_nonneg

lemma expNeg_le_one (x : ℝ≥0∞) : expNeg x ≤ 1 := by
  rcases eq_or_ne x ∞ with rfl | hx
  · simp
  rw [expNeg_of_ne_top hx, Real.exp_le_one_iff, neg_nonpos]
  exact ENNReal.toReal_nonneg

lemma _root_.EReal.exp_neg_coe_ennreal_ne_top (x : ℝ≥0∞) : EReal.exp (-x) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (EReal.exp_le_one_iff.mpr (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg x)))

lemma continuous_expNeg : Continuous expNeg :=
  ENNReal.continuousOn_toReal.comp_continuous
    (ENNReal.continuous_exp.comp (continuous_neg.comp continuous_coe_ennreal_ereal))
    EReal.exp_neg_coe_ennreal_ne_top

lemma expNeg_injective : Function.Injective expNeg := by
  intro x y h
  rw [expNeg, expNeg, ENNReal.toReal_eq_toReal_iff' (EReal.exp_neg_coe_ennreal_ne_top x)
    (EReal.exp_neg_coe_ennreal_ne_top y)] at h
  exact_mod_cast neg_injective (EReal.exp_strictMono.injective h)

lemma isClosedEmbedding_expNeg : Topology.IsClosedEmbedding expNeg :=
  continuous_expNeg.isClosedEmbedding expNeg_injective

/-- The key identity: `exp (-(x + y) / 2) ^ 2 = exp (-x) * exp (-y)`. -/
lemma expNeg_midpoint_sq (x y : ℝ≥0∞) : expNeg (2⁻¹ * (x + y)) ^ 2 = expNeg x * expNeg y := by
  rcases eq_or_ne x ∞ with rfl | hx
  · simp [ENNReal.mul_top]
  rcases eq_or_ne y ∞ with rfl | hy
  · simp [ENNReal.mul_top]
  have hxy : 2⁻¹ * (x + y) ≠ ∞ := ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨hx, hy⟩)
  rw [expNeg_of_ne_top hx, expNeg_of_ne_top hy, expNeg_of_ne_top hxy, ← Real.exp_add,
    ← Real.exp_natCast_mul, ENNReal.toReal_mul, ENNReal.toReal_add hx hy]
  congr 1
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, Nat.cast_ofNat]
  ring

end Komlos

open Komlos

/-- **Komlós lemma** for `ℝ≥0∞`-valued functions and a finite measure.
See `komlos_ennreal` for s-finite measures. -/
theorem komlos_ennreal_of_isFiniteMeasure {X : ℕ → Ω → ℝ≥0∞} (hX : ∀ n, Measurable (X n))
    (P : Measure Ω) [IsFiniteMeasure P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) := by
  -- apply the abstract Komlós lemma to `φ Y = ∫ exp (-Y) ^ 2 ∂P`
  set φ : (Ω → ℝ≥0∞) → ℝ := fun Y ↦ ∫ ω, expNeg (Y ω) ^ 2 ∂P with hφ
  have hφ_nonneg Y : 0 ≤ φ Y := integral_nonneg fun ω ↦ sq_nonneg _
  have hφ_le Y : φ Y ≤ P.real univ := by
    calc φ Y ≤ ∫ _, (1 : ℝ) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const 1)
            (ae_of_all _ fun ω ↦ pow_le_one₀ (expNeg_nonneg _) (expNeg_le_one _))
      _ = P.real univ := by simp
  obtain ⟨g, hg_mem, hg_defect⟩ := komlos_convex (R := ℝ≥0) (f := X) (φ := φ)
    ⟨0, by rintro _ ⟨Y, rfl⟩; exact hφ_nonneg Y⟩ ⟨P.real univ, by rintro _ ⟨n, rfl⟩; exact hφ_le _⟩
  have hg_meas n : Measurable (g n) := by
    have : g n ∈ {Y : Ω → ℝ≥0∞ | Measurable Y} := by
      refine convexHull_min ?_ (fun Y hY Z hZ a b _ _ _ ↦ ?_) (hg_mem n)
      · rintro _ ⟨m, rfl⟩
        exact hX _
      · exact (hY.const_smul a).add (hZ.const_smul b)
    exact this
  have h_meas_expNeg : Measurable expNeg := continuous_expNeg.measurable
  -- the midpoint defect of `φ` is half the squared `L²` distance between `exp (-g n)` and
  -- `exp (-g m)`
  have h_int {F : Ω → ℝ} (hF : Measurable F) (hF_le : ∀ ω, |F ω| ≤ 1) : Integrable F P :=
    .of_bound hF.aestronglyMeasurable 1 (ae_of_all _ hF_le)
  have h_defect n m : 2⁻¹ * φ (g n) + 2⁻¹ * φ (g m) - φ ((2 : ℝ≥0)⁻¹ • (g n + g m))
      = 2⁻¹ * ∫ ω, (expNeg (g n ω) - expNeg (g m ω)) ^ 2 ∂P := by
    have h_mid ω : expNeg (((2 : ℝ≥0)⁻¹ • (g n + g m)) ω) ^ 2
        = expNeg (g n ω) * expNeg (g m ω) := by
      simpa [ENNReal.smul_def, mul_add] using expNeg_midpoint_sq (g n ω) (g m ω)
    have h_bound (k : ℕ) ω : 0 ≤ expNeg (g k ω) ∧ expNeg (g k ω) ≤ 1 :=
      ⟨expNeg_nonneg _, expNeg_le_one _⟩
    have h1 k : Integrable (fun ω ↦ expNeg (g k ω) ^ 2) P := h_int (by fun_prop) fun ω ↦ by
      obtain ⟨h0, h1⟩ := h_bound k ω
      rw [abs_le]; constructor <;> nlinarith
    have h2 : Integrable (fun ω ↦ expNeg (g n ω) * expNeg (g m ω)) P :=
      h_int (by fun_prop) fun ω ↦ by
        obtain ⟨hn0, hn1⟩ := h_bound n ω
        obtain ⟨hm0, hm1⟩ := h_bound m ω
        rw [abs_le]; constructor <;> nlinarith
    have h_sq : ∫ ω, (expNeg (g n ω) - expNeg (g m ω)) ^ 2 ∂P
        = ∫ ω, expNeg (g n ω) ^ 2 ∂P + ∫ ω, expNeg (g m ω) ^ 2 ∂P
          - 2 * ∫ ω, expNeg (g n ω) * expNeg (g m ω) ∂P := by
      calc ∫ ω, (expNeg (g n ω) - expNeg (g m ω)) ^ 2 ∂P
      _ = ∫ ω, (expNeg (g n ω) ^ 2 + expNeg (g m ω) ^ 2)
            - 2 * (expNeg (g n ω) * expNeg (g m ω)) ∂P := by
        congr with ω
        ring
      _ = _ := by
        rw [integral_sub (f := fun ω ↦ expNeg (g n ω) ^ 2 + expNeg (g m ω) ^ 2)
            (g := fun ω ↦ 2 * (expNeg (g n ω) * expNeg (g m ω))) ((h1 n).add (h1 m))
            (h2.const_mul 2),
          integral_add (h1 n) (h1 m), integral_const_mul]
    simp only [hφ, h_mid, h_sq]
    ring
  -- hence `exp (-g n)` is Cauchy in `L²`, and we extract a subsequence with a fast rate
  have h_cauchy k : ∃ N, ∀ N' ≥ N, ∀ n ≥ N', ∀ m ≥ N',
      ∫ ω, (expNeg (g n ω) - expNeg (g m ω)) ^ 2 ∂P < ((2 : ℝ)⁻¹ ^ k) ^ 2 := by
    obtain ⟨N, hN⟩ := hg_defect (((2 : ℝ)⁻¹ ^ k) ^ 2 / 2) (by positivity)
    refine ⟨N, fun N' hN' n hn m hm ↦ ?_⟩
    have h := hN n (hN'.trans hn) m (hN'.trans hm)
    rw [h_defect] at h
    linarith
  obtain ⟨ns, hns_mono, hns⟩ := extraction_forall_of_eventually' h_cauchy
  -- the subsequence `exp (-g (ns k))` converges almost everywhere
  have h_ae : ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k ↦ expNeg (g (ns k) ω)) atTop (𝓝 l) := by
    refine Lp.ae_tendsto_of_cauchy_eLpNorm (f := fun k ω ↦ expNeg (g (ns k) ω)) (p := 2)
      (fun k ↦ (by fun_prop : Measurable _).aestronglyMeasurable) one_le_two
      (B := fun k ↦ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k)) ?_ fun K n m hn hm ↦ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity)
        (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
      exact ENNReal.ofReal_ne_top
    have h_memLp : MemLp ((fun ω ↦ expNeg (g (ns n) ω)) - fun ω ↦ expNeg (g (ns m) ω)) 2 P := by
      refine .of_bound (by fun_prop : Measurable _).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)
      obtain ⟨hn0, hn1⟩ := And.intro (expNeg_nonneg (g (ns n) ω)) (expNeg_le_one (g (ns n) ω))
      obtain ⟨hm0, hm1⟩ := And.intro (expNeg_nonneg (g (ns m) ω)) (expNeg_le_one (g (ns m) ω))
      simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    rw [h_memLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have h_eq : ∫ ω, ‖((fun ω ↦ expNeg (g (ns n) ω)) - fun ω ↦ expNeg (g (ns m) ω)) ω‖
        ^ (2 : ℝ≥0∞).toReal ∂P = ∫ ω, (expNeg (g (ns n) ω) - expNeg (g (ns m) ω)) ^ 2 ∂P := by
      congr with ω
      simp [Real.norm_eq_abs, sq_abs]
    rw [h_eq, ENNReal.toReal_ofNat]
    calc (∫ ω, (expNeg (g (ns n) ω) - expNeg (g (ns m) ω)) ^ 2 ∂P) ^ (2 : ℝ)⁻¹
    _ < (((2 : ℝ)⁻¹ ^ K) ^ 2) ^ (2 : ℝ)⁻¹ :=
      Real.rpow_lt_rpow (integral_nonneg fun _ ↦ sq_nonneg _)
        (hns K _ (hns_mono.monotone hn) _ (hns_mono.monotone hm)) (by norm_num)
    _ = (2 : ℝ)⁻¹ ^ K := by
      exact_mod_cast Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ K) two_ne_zero
  -- since `x ↦ exp (-x)` is a closed embedding, `g (ns k)` converges almost everywhere
  have h_conv : ∀ᵐ ω ∂P, ∃ y, Tendsto (fun k ↦ g (ns k) ω) atTop (𝓝 y) := by
    filter_upwards [h_ae] with ω ⟨l, hl⟩
    obtain ⟨y, rfl⟩ : l ∈ range expNeg :=
      isClosedEmbedding_expNeg.isClosed_range.mem_of_tendsto hl
        (.of_forall fun k ↦ mem_range_self _)
    exact ⟨y, isClosedEmbedding_expNeg.isInducing.tendsto_nhds_iff.mpr hl⟩
  refine ⟨fun k ↦ g (ns k), fun ω ↦ liminf (fun k ↦ g (ns k) ω) atTop, fun k ↦ ?_,
    .liminf fun k ↦ hg_meas _, ?_⟩
  · -- `g (ns k)` is a convex combination of the `ns k`-th tail, hence of the `k`-th tail
    have h_sub : range (fun m ↦ X (ns k + m)) ⊆ range fun m ↦ X (k + m) := by
      rintro _ ⟨m, rfl⟩
      have hk : k ≤ ns k := hns_mono.id_le k
      exact ⟨ns k - k + m, by simp only; congr 1; omega⟩
    exact convexHull_mono h_sub (convexHull_min (subset_convexHull ℝ≥0∞ _)
      ((convex_convexHull ℝ≥0∞ _).lift ℝ≥0) (hg_mem (ns k)))
  · filter_upwards [h_conv] with ω ⟨y, hy⟩
    rwa [hy.liminf_eq]

/-- **Komlós lemma** for `ℝ≥0∞`-valued functions: for any sequence of measurable functions and any
s-finite measure, some forward convex combinations converge almost everywhere. -/
theorem komlos_ennreal {X : ℕ → Ω → ℝ≥0∞} (hX : ∀ n, Measurable (X n)) (P : Measure Ω)
    [SFinite P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) := by
  obtain ⟨Y, Y_lim, hY_mem, hY_lim_meas, hY_tendsto⟩ :=
    komlos_ennreal_of_isFiniteMeasure hX P.toFinite
  exact ⟨Y, Y_lim, hY_mem, hY_lim_meas, (absolutelyContinuous_toFinite P).ae_le hY_tendsto⟩

end MeasureTheory
