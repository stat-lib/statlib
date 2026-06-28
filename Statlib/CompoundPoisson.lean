import Mathlib
import Statlib.Tweedie
open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Pointwise
open scoped NNReal ENNReal
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false
/-!
# A construction of a compound Poisson random variable
Given a probability measure `μ` on `ℝ` (the *jump distribution*) and a rate `lam : ℝ≥0`, the
compound Poisson random variable is
`X = ∑_{i < N} Y_i`,
where `N` is a Poisson(`lam`) random variable and `(Y_i)_{i ∈ ℕ}` is an i.i.d. sequence with law
`μ`, independent of `N`.
We realise this on the probability space `ℕ × (ℕ → ℝ)` equipped with the product of the Poisson
measure (on the first coordinate `N`) and the infinite product measure `μ^{⊗ℕ}` (on the second
coordinate, the sequence of jumps).  The compound Poisson law is then the push-forward of this base
measure under `jumpSum (N, y) = ∑_{i < N} y i`.
As a sanity check we show that the law puts positive mass on `{0}` and, *when `μ` is atomless*,
that this mass is exactly `ℙ(N = 0) = e^{-lam}`.
The atomless hypothesis is genuinely needed for the equality: if for instance `μ = δ₀`, then
`X = 0` almost surely, so `ℙ(X = 0) = 1 > e^{-lam}`.  Positivity, on the other hand, holds because
`{N = 0} ⊆ {X = 0}`.
-/
namespace CompoundPoisson
open MeasureTheory ProbabilityTheory
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℝ≥0)
/-- The base probability space: the first coordinate is the Poisson count `N`, the second is the
i.i.d. sequence of jumps with common law `μ`. -/
noncomputable def baseMeasure : Measure (ℕ × (ℕ → ℝ)) :=
  (poissonMeasure lam).prod (Measure.infinitePi (fun _ : ℕ => μ))
instance : IsProbabilityMeasure (baseMeasure μ lam) := by
  unfold baseMeasure; infer_instance
/-- The compound Poisson random variable: the sum of the first `N` jumps. -/
def jumpSum (p : ℕ × (ℕ → ℝ)) : ℝ := ∑ i ∈ Finset.range p.1, p.2 i
lemma measurable_jumpSum : Measurable (jumpSum : ℕ × (ℕ → ℝ) → ℝ) := by
  unfold jumpSum
  apply measurable_from_prod_countable_right
  intro n; simp only
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
/-- The compound Poisson law: the push-forward of the base measure under `jumpSum`. -/

noncomputable def compoundPoisson : Measure ℝ :=
  (baseMeasure μ lam).map jumpSum

instance : IsProbabilityMeasure (compoundPoisson μ lam) := by
  unfold compoundPoisson
  exact Measure.isProbabilityMeasure_map measurable_jumpSum.aemeasurable

/-! ### The mass of `{0}` under the Poisson count -/
lemma poissonMeasure_singleton_zero :
    poissonMeasure lam {0} = ENNReal.ofReal (Real.exp (-lam)) := by
  unfold poissonMeasure
  rw [Measure.sum_apply]
  simp [Pi.single, Function.update]
  exact measurableSet_singleton 0

lemma poissonMeasure_singleton_zero_pos : 0 < poissonMeasure lam {0} := by
  rw [poissonMeasure_singleton_zero]
  simp [ENNReal.ofReal_pos, Real.exp_pos]
/-! ### The atomless key lemmas -/
/-
For a nonempty finite index set, the product of an atomless probability measure assigns zero
mass to the hyperplane `{∑ i, g i = 0}`.  This is the statement that an `n`-fold convolution of an
atomless measure (`n ≥ 1`) is again atomless at `0`.
-/
lemma pi_sum_eq_zero {ι : Type*} [Fintype ι] [Nonempty ι] [NoAtoms μ] :
    Measure.pi (fun _ : ι => μ) {g : ι → ℝ | ∑ i, g i = 0} = 0 := by
  -- Let $j$ be an arbitrary element of $\iota$.
  obtain ⟨j, hj⟩ : ∃ j : ι, True := by
    exact ⟨ Classical.arbitrary ι, trivial ⟩
  set p : ι → Prop := fun i => i ≠ j
  set t := {q : (({i // p i}) → ℝ) × (({i // ¬ p i}) → ℝ) | (∑ i, q.1 i) + (∑ i, q.2 i) = 0};
  -- By the measure-preserving property, the measure of the preimage of $t$ under $e$ is equal to the measure of $t$ under the product measure.
  have h_preimage : (Measure.pi (fun _ : ι => μ)) {g : ι → ℝ | ∑ i, g i = 0} = (Measure.prod (Measure.pi (fun _ : {i // p i} => μ)) (Measure.pi (fun _ : {i // ¬p i} => μ))) t := by
    have h_preimage : (Measure.pi (fun _ : ι => μ)) {g : ι → ℝ | ∑ i, g i = 0} = (Measure.pi (fun _ : ι => μ)) (Set.preimage (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p) t) := by
      congr with g ; simp +decide [ t ];
      rw [ show ( Finset.univ : Finset ι ) = Finset.image ( fun i : { i // p i } => i.val ) Finset.univ ∪ { j } from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_image, p ];
      · rw [ show ( Finset.univ : Finset { i // ¬p i } ) = { ⟨ j, by aesop ⟩ } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_univ _, fun x hx => by aesop ⟩ ] ; simp +decide [ p ];
      · ext i; by_cases hi : i = j <;> aesop;
    rw [ h_preimage, MeasureTheory.MeasurePreserving.measure_preimage ];
    · convert MeasureTheory.measurePreserving_piEquivPiSubtypeProd ( fun _ : ι => μ ) p using 1;
    · refine' MeasurableSet.nullMeasurableSet _;
      exact measurableSet_eq_fun ( by measurability ) ( by measurability );
  -- For fixed `a`, `Prod.mk a ⁻¹' t = {b : {i//¬p i} → ℝ | (∑ i, a i) + (∑ i, b i) = 0}`.
  -- Since `{i // ¬ p i} = {i // i = j}` is a singleton type with unique element `j₀ := ⟨j, by simp⟩`, `∑ i, b i = b j₀`.
  -- Hence the slice is `{b | b j₀ = -(∑ i, a i)}`.
  have h_slice : ∀ a : ({i // p i} → ℝ), (Measure.pi (fun _ : {i // ¬p i} => μ)) {b : {i // ¬p i} → ℝ | (∑ i, a i) + (∑ i, b i) = 0} = 0 := by
    intro a
    have h_singleton : {b : {i // ¬p i} → ℝ | (∑ i, a i) + (∑ i, b i) = 0} = {fun _ => -(∑ i, a i)} := by
      ext b; simp [p];
      rw [ show ( Finset.univ : Finset { i // ¬p i } ) = { ⟨ j, by aesop ⟩ } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_univ _, fun x hx => Subtype.ext <| by aesop ⟩ ] ; simp +decide [ add_eq_zero_iff_eq_neg ] ;
      exact ⟨ fun h => funext fun x => by rw [ show x = ⟨ j, by aesop ⟩ from Subtype.ext <| by aesop ] ; linarith, fun h => by rw [ h ] ; simp +decide ⟩;
    aesop;
  rw [ h_preimage, MeasureTheory.Measure.prod_apply ];
  · aesop;
  · exact measurableSet_eq_fun ( by measurability ) ( by measurability )
/-
The infinite product measure assigns zero mass to the event that the first `m+1` jumps sum to
zero, whenever `μ` is atomless.
-/
lemma infinitePi_sum_range_succ_eq_zero [NoAtoms μ] (m : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ)
      {f : ℕ → ℝ | ∑ i ∈ Finset.range (m + 1), f i = 0} = 0 := by
  -- Let's denote the finite set $\{0, 1, ..., m\}$ by $I$.
  set I : Finset ℕ := Finset.range (m + 1) with hI_def;
  -- By `MeasureTheory.Measure.infinitePi_map_restrict (fun _ : ℕ => μ)`, we have `Measure.map I.restrict (Measure.infinitePi (fun _ : ℕ => μ)) = Measure.pi (fun i : ↥I => μ)`.
  have h_map : Measure.map (fun f : ℕ → ℝ => fun i : I => f i) (Measure.infinitePi (fun _ : ℕ => μ)) = Measure.pi (fun i : I => μ) := by
    convert MeasureTheory.Measure.infinitePi_map_restrict ( fun _ : ℕ => μ ) using 1;
  convert congr_arg ( fun μ => μ { g : I → ℝ | ∑ i, g i = 0 } ) h_map using 1;
  · rw [ MeasureTheory.Measure.map_apply ];
    · congr! 2;
      ext; simp +decide [ Finset.sum_attach ] ;
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · exact measurableSet_eq_fun ( by measurability ) ( by measurability );
  · convert Eq.symm ( pi_sum_eq_zero μ ) using 1;
    exact ⟨ 0, Finset.mem_range.mpr ( Nat.succ_pos _ ) ⟩
/-! ### The sanity check -/
/-
The probability that the compound Poisson variable is `0` equals `ℙ(N = 0)`, provided the jump
distribution `μ` is atomless.
-/
theorem compoundPoisson_singleton_zero [NoAtoms μ] :
    compoundPoisson μ lam {(0 : ℝ)} = poissonMeasure lam {0} := by
  have h_integral : ∫⁻ n, (Measure.infinitePi (fun _ : ℕ => μ)) {f : ℕ → ℝ | ∑ i ∈ Finset.range n, f i = 0} ∂(poissonMeasure lam) = (poissonMeasure lam) {0} := by
    rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator_one ];
    · exact MeasurableSingletonClass.measurableSet_singleton _;
    · filter_upwards [ ] with n;
      cases n <;> simp_all +decide [ infinitePi_sum_range_succ_eq_zero ];
  convert h_integral using 1;
  rw [ compoundPoisson, baseMeasure, MeasureTheory.Measure.map_apply ];
  · convert MeasureTheory.Measure.prod_apply _ using 1;
    · infer_instance;
    · exact measurable_jumpSum ( MeasurableSingletonClass.measurableSet_singleton _ );
  · exact measurable_jumpSum
  · exact MeasurableSingletonClass.measurableSet_singleton _
/-- The probability that the compound Poisson variable is `0` is positive (assuming `μ` atomless),
and in fact equals `e^{-lam}`. -/
theorem compoundPoisson_singleton_zero_pos [NoAtoms μ] :
    0 < compoundPoisson μ lam {(0 : ℝ)} := by
  rw [compoundPoisson_singleton_zero μ lam]
  exact poissonMeasure_singleton_zero_pos lam
end CompoundPoisson

open CompoundPoisson
-- Now we can construct Tweedie:
noncomputable def tweedie_construction (μ : ℝ) (hμ : 0 ≤ μ) {φ p : ℝ}
    (hφ : 0 ≤ φ)
    (hp₂ : p < 2) :=
  compoundPoisson
    (ProbabilityTheory.gammaMeasure
      (φ * (p - 1) * μ ^ (p - 1))   -- scale
      ((2 - p) / (p - 1))           -- rate or shape
    )
    ⟨μ^(2-p) / (φ * (2-p)), by positivity⟩ -- Poisson rate


instance (a r : ℝ) : MeasureTheory.NoAtoms
  (ProbabilityTheory.gammaMeasure a r) := by
  refine { measure_singleton := ?_ }
  intro x
  simp [ProbabilityTheory.gammaMeasure]

-- instance (a r : ℝ) (ha : 0 < a) (hr : 0 < r) : MeasureTheory.IsProbabilityMeasure
--     (ProbabilityTheory.gammaMeasure a r) :=
--   ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by positivity)
--     (by positivity)

instance tweedie_gamma_IsProbabilityMeasure {μ : ℝ} (hμ : 0 < μ) {φ p : ℝ}
    (hφ : 0 < φ) (hp₁ : 1 < p)
    (hp₂ : p < 2) : MeasureTheory.IsProbabilityMeasure
    (ProbabilityTheory.gammaMeasure
    (φ * (p - 1) * μ ^ (p - 1)) ((2 - p) / (p - 1))) :=
  ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by positivity)
    (by positivity)

/-- Show that the `tweedie_construction` agrees
with the Tweedie distribution at 0. -/
lemma tweedie_zero_sanity_check (μ : ℝ) (hμ : 0 < μ) {φ p : ℝ}
    (hφ : 0 < φ) (hp₁ : 1 < p)
    (hp₂ : p < 2) : tweedie_construction μ (by linarith)
      (show 0 ≤ φ by linarith)
       hp₂ {0} = tweedie_prob_zero μ φ p := by
  unfold tweedie_construction
  rw [@compoundPoisson_singleton_zero _
    (tweedie_gamma_IsProbabilityMeasure hμ hφ hp₁ hp₂)]
  unfold tweedie_prob_zero
  rw [poissonMeasure_singleton_zero]
  norm_cast
  have : NNReal.toReal ⟨μ ^ (2 - p) / (φ * (2 - p)),
    by positivity⟩
    = μ ^ (2 - p) / (φ * (2 - p)) := rfl
  rw [this]
  have (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal x = ENNReal.ofNNReal (⟨x,hx⟩ : {y // (0:ℝ) ≤ y}) := by
      refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
      simp
      simp
      exact ENNReal.toReal_ofReal hx
  rw [this]
  simp
  congr
  field_simp
  exact Real.exp_nonneg (-(μ ^ (2 - p) / (φ * (2 - p))))

/-- The Tweedie measure, which was introduced without explanation,
equals the Tweedie construction, which is compound Poisson,
at least on the set {0}.
-/
lemma tweedie_zero_sanity_check₂ (μ : ℝ) (hμ : 0 < μ) {φ p : ℝ}
    (hφ : 0 < φ) (hp₁ : 1 < p)
    (hp₂ : p < 2) :
    let hμ₀ := le_of_lt hμ
    let hφ₀ := le_of_lt hφ
    tweedie_construction μ hμ₀ hφ₀ hp₂ {0} = -- hp₁ not needed to obtain positivity of λ
    tweedieMeasure       μ hφ₀ hp₁ hp₂ {0} := by
  intro hμ₀ hφ₀
  rw [tweedie_zero_sanity_check μ hμ hφ hp₁ hp₂]
  simp [tweedieMeasure]
