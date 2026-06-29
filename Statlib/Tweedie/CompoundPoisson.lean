import Mathlib
import Statlib.Tweedie.Tweedie
import Statlib.Tweedie.GammaConvolution
import Statlib.Tweedie.CompoundPoissonCore
import Statlib.Tweedie.TweedieAux
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
/-! The compound-Poisson construction lives in `CompoundPoissonCore`. -/

namespace CompoundPoisson
open MeasureTheory ProbabilityTheory
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℝ≥0)
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
open GammaConv
-- Now we can construct Tweedie:
/-
The compound-Poisson construction of the Tweedie distribution uses a
`Gamma` jump distribution with **shape** `α = (2 - p)/(p - 1)` and **rate**
`γ = μ^(1-p)/(φ (p-1))` (equivalently scale `φ (p-1) μ^(p-1)`), and Poisson rate
`λ = μ^(2-p)/(φ (2-p))`.

In Mathlib, `ProbabilityTheory.gammaMeasure a r` takes its **first** argument `a` as the shape
and its **second** argument `r` as the rate (density `r^a/Γ a * x^(a-1) * e^{-r x}`).
-/
noncomputable def tweedie_construction (μ : ℝ) (hμ : 0 ≤ μ) {φ p : ℝ}
    (hφ : 0 ≤ φ)
    (hp₂ : p < 2) :=
  compoundPoisson
    (ProbabilityTheory.gammaMeasure
      ((2 - p) / (p - 1))            -- shape α
      (μ ^ (1 - p) / (φ * (p - 1)))  -- rate γ
    )
    ⟨μ^(2-p) / (φ * (2-p)), by positivity⟩ -- Poisson rate

instance (a r : ℝ) : MeasureTheory.NoAtoms
  (ProbabilityTheory.gammaMeasure a r) := by
  refine { measure_singleton := ?_ }
  intro x
  simp [ProbabilityTheory.gammaMeasure]


instance tweedie_gamma_IsProbabilityMeasure {μ : ℝ} (hμ : 0 < μ) {φ p : ℝ}
    (hφ : 0 < φ) (hp₁ : 1 < p)
    (hp₂ : p < 2) : MeasureTheory.IsProbabilityMeasure
    (ProbabilityTheory.gammaMeasure
    ((2 - p) / (p - 1)) (μ ^ (1 - p) / (φ * (p - 1)))) :=
  ProbabilityTheory.isProbabilityMeasure_gammaMeasure
    (div_pos (by linarith) (by linarith))
    (div_pos (Real.rpow_pos_of_pos hμ _) (by nlinarith))

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
    tweedie_construction μ hμ₀ hφ₀ hp₂ {0} =
    tweedieMeasure       μ hφ₀ hp₁ hp₂ {0} := by
  intro hμ₀ hφ₀
  rw [tweedie_zero_sanity_check μ hμ hφ hp₁ hp₂]
  simp [tweedieMeasure]

open MeasureTheory ProbabilityTheory in
/-- Closed form of a `tw_G` summand as a Poisson-weight times a gamma density, valid for `y > 0`.
This is the pointwise correspondence between the `j`-th term of the Tweedie density series and the
`j`-fold-convolution (gamma) term of the compound-Poisson law. -/
lemma tw_G_eq_gamma (μ : ℝ) (hμ : 0 < μ) {φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hφ : 0 < φ)
    (j : ℕ) {y : ℝ} (hy : 0 < y) :
    tw_G μ φ p j y
      = Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (j.factorial)
        * gammaPDFReal ((j : ℝ) * ((2 - p) / (p - 1))) (μ ^ (1 - p) / (φ * (p - 1))) y := by
  have h1p : (1 - p) ≠ 0 := by linarith
  have hpm1 : (p - 1) ≠ 0 := by linarith
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [tw_G_zero, gammaPDFReal, if_pos hy.le]
    simp [Real.Gamma_zero]
  · have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
    have hAneg : (2 - p) / (1 - p) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
    have hargpos : 0 < -(j : ℝ) * ((2 - p) / (1 - p)) :=
      mul_pos_of_neg_of_neg (by simpa using hjR) hAneg
    have hΓ : Real.Gamma (-(j : ℝ) * ((2 - p) / (1 - p))) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos hargpos)
    rw [tw_pt μ hp₁ hφ j hy, gammaPDFReal, if_pos hy.le]
    have hAB : (j : ℝ) * ((2 - p) / (p - 1)) = -(j : ℝ) * ((2 - p) / (1 - p)) := by
      field_simp; ring
    have hdenom : φ ^ ((j : ℝ) * (1 - (2 - p) / (1 - p))) * (2 - p) ^ j ≠ 0 := by positivity
    have key := TweedieAux.tw_scalar_identity μ φ p hμ hφ hp₁ hp₂ j
    rw [hAB] at key
    rw [eq_div_iff hdenom] at key
    rw [hAB, ← key]
    simp only [tw_z]
    have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
    have hphirpow : φ ^ ((j : ℝ) * (1 - (2 - p) / (1 - p))) ≠ 0 := by positivity
    have h2pj : ((2 - p) : ℝ) ^ j ≠ 0 := by positivity
    have hphi2p : φ * (2 - p) ≠ 0 := by positivity
    field_simp [hΓ, hfac, hphirpow, h2pj, hphi2p]

open MeasureTheory ProbabilityTheory in
/-- The compound-Poisson law of a Gamma jump distribution splits as an atom at `0` (mass
`e^{-lam}`) plus an absolutely continuous part whose density is the Poisson-weighted sum of the
convolution (gamma) densities. -/
lemma compound_split (α γ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (lam : ℝ≥0) :
    CompoundPoisson.compoundPoisson (gammaMeasure α γ) lam
      = ENNReal.ofReal (Real.exp (-(lam : ℝ))) • Measure.dirac 0
        + volume.withDensity (fun z => ∑' n : ℕ,
            ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (n + 1) / ((n + 1).factorial))
              * gammaPDF (((n + 1 : ℕ) : ℝ) * α) γ z) := by
  haveI : IsProbabilityMeasure (gammaMeasure α γ) := isProbabilityMeasure_gammaMeasure hα hγ
  have hgPDFmeas : ∀ a : ℝ, Measurable (fun z => gammaPDF a γ z) := fun a =>
    (measurable_gammaPDFReal a γ).ennreal_ofReal
  set d : ℝ → ℝ≥0∞ := fun z => ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (n + 1) / ((n + 1).factorial))
        * gammaPDF (((n + 1 : ℕ) : ℝ) * α) γ z with hd
  have hd_meas : Measurable d := by
    apply Measurable.tsum
    intro n
    exact (hgPDFmeas _).const_mul _
  refine MeasureTheory.Measure.ext_of_lintegral _ (fun f hf => ?_)
  rw [compoundPoisson_lintegral _ lam hf]
  rw [MeasureTheory.lintegral_add_measure, MeasureTheory.lintegral_smul_measure,
    MeasureTheory.lintegral_dirac,
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hd_meas hf]
  rw [tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · rw [GammaConv.convPow_zero, MeasureTheory.lintegral_dirac, smul_eq_mul]
    congr 1
    norm_num
  · have hmeas_term : ∀ n : ℕ, Measurable (fun z =>
        ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (n + 1) / ((n + 1).factorial))
          * gammaPDF (((n + 1 : ℕ) : ℝ) * α) γ z * f z) := by
      intro n; exact ((hgPDFmeas _).const_mul _).mul hf
    have step : ∀ n : ℕ,
        ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (n + 1) / ((n + 1).factorial))
            * ∫⁻ z, f z ∂(GammaConv.convPow (gammaMeasure α γ) (n + 1))
          = ∫⁻ z, ENNReal.ofReal (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (n + 1) / ((n + 1).factorial))
              * gammaPDF (((n + 1 : ℕ) : ℝ) * α) γ z * f z ∂volume := by
      intro n
      rw [GammaConv.convPow_gamma α γ hα hγ (n + 1) (Nat.succ_pos n)]
      rw [show gammaMeasure (((n + 1 : ℕ) : ℝ) * α) γ
            = volume.withDensity (gammaPDF (((n + 1 : ℕ) : ℝ) * α) γ) from rfl]
      rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ (hgPDFmeas _) hf]
      simp only [Pi.mul_apply]
      rw [← MeasureTheory.lintegral_const_mul _ ((hgPDFmeas _).mul hf)]
      congr 1; ext z; ring
    rw [tsum_congr step]
    rw [← MeasureTheory.lintegral_tsum (fun n => (hmeas_term n).aemeasurable)]
    congr 1; ext z
    simp only [Pi.mul_apply, hd]
    rw [← ENNReal.tsum_mul_right]

open MeasureTheory ProbabilityTheory in
/-- For (Lebesgue-)almost every `y > 0`, the Tweedie term series `j ↦ tw_G μ φ p j y` is summable.
This follows from the summability of the integral norms (`tw_summable_norm`): the integrable
series has finite total integral, hence is summable pointwise a.e. -/
lemma tw_G_ae_summable (μ : ℝ) {φ p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    ∀ᵐ y ∂volume, y ∈ Set.Ioi (0 : ℝ) → Summable (fun j : ℕ => tw_G μ φ p j y) := by
  rw [← MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  exact TweedieAux.ae_summable_of_summable_integral_norm
    (fun j => tw_integrable_on hp₁ hp₂ hμ hφ j)
    (tw_summable_norm μ φ p hp₁ hp₂ hμ hφ)

open MeasureTheory ProbabilityTheory in
/-- The Poisson-weighted sum of the gamma densities (shape `(n+1)·α`) equals the Tweedie density,
Lebesgue-almost everywhere. -/
lemma tweedie_density_series_ae (μ : ℝ) (hμ : 0 < μ) {φ p : ℝ} (hφ : 0 < φ) (hp₁ : 1 < p)
    (hp₂ : p < 2) :
    (fun z => ∑' n : ℕ, ENNReal.ofReal
        (Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ (n + 1) / ((n + 1).factorial))
      * gammaPDF (((n + 1 : ℕ) : ℝ) * ((2 - p) / (p - 1))) (μ ^ (1 - p) / (φ * (p - 1))) z)
      =ᵐ[volume] (fun z => tweediePDF' μ hp₁ (le_of_lt hp₂) (le_of_lt hφ) z) := by
  have hzne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [tw_G_ae_summable μ hp₁ hp₂ hμ hφ, hzne] with z hzsum hzne0
  have hpdf' : tweediePDF' μ hp₁ (le_of_lt hp₂) (le_of_lt hφ) z
      = ENNReal.ofReal (tweediePDF μ φ p z) := by
    unfold tweediePDF'
    exact (ENNReal.ofReal_eq_coe_nnreal
      (tweediePDF_nonneg (le_of_lt hφ) hp₁ (le_of_lt hp₂))).symm
  rw [hpdf']
  rcases lt_or_gt_of_ne hzne0 with hzlt | hzgt
  · -- z < 0 : both sides vanish
    have h1 : tweediePDF μ φ p z = 0 := by
      simp only [tweediePDF]
      rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq]; linarith)]
    rw [h1, ENNReal.ofReal_zero, ENNReal.tsum_eq_zero]
    intro n
    rw [gammaPDF_of_neg hzlt, mul_zero]
  · -- z > 0 : use the pointwise Tweedie series
    have hpw : tweediePDF μ φ p z = ∑' j : ℕ, tw_G μ φ p j z := by
      simp only [tweediePDF]
      rw [Set.indicator_of_mem (by simp only [Set.mem_setOf_eq]; exact hzgt)]
      exact tw_pointwise μ φ p z
    rw [hpw,
      ENNReal.ofReal_tsum_of_nonneg
        (fun j => tw_G_nonneg μ φ p hp₁ hp₂ hφ j hzgt) (hzsum hzgt)]
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
    rw [tw_G_zero, ENNReal.ofReal_zero, zero_add]
    have htwz : 0 ≤ tw_z μ φ p := by rw [tw_z]; positivity
    refine tsum_congr (fun n => ?_)
    rw [tw_G_eq_gamma μ hμ hp₁ hp₂ hφ (n + 1) hzgt,
      ENNReal.ofReal_mul
        (div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg htwz _)) (by positivity)),
      gammaPDF]

theorem tweedie_eq (μ : ℝ) (hμ : 0 < μ) {φ p : ℝ}
    (hφ : 0 < φ) (hp₁ : 1 < p)
    (hp₂ : p < 2) :
    let hμ₀ := le_of_lt hμ
    let hφ₀ := le_of_lt hφ
    tweedie_construction μ hμ₀ hφ₀ hp₂ =
    tweedieMeasure       μ hφ₀ hp₁ hp₂ := by
  intro hμ₀ hφ₀
  have hα : (0 : ℝ) < (2 - p) / (p - 1) := div_pos (by linarith) (by linarith)
  have hγ : (0 : ℝ) < μ ^ (1 - p) / (φ * (p - 1)) :=
    div_pos (Real.rpow_pos_of_pos hμ _) (by nlinarith)
  unfold tweedie_construction
  rw [compound_split ((2 - p) / (p - 1)) (μ ^ (1 - p) / (φ * (p - 1))) hα hγ
    ⟨μ ^ (2 - p) / (φ * (2 - p)), by positivity⟩]
  rw [tweedieMeasure]
  congr 1
  · -- atom at 0
    rw [ENNReal.smul_def]
    congr 1
    rw [tweedie_prob_zero, ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)]
    congr 1
    apply NNReal.coe_injective
    show Real.exp (-(μ ^ (2 - p) / (φ * (2 - p))))
        = Real.exp (-μ ^ (2 - p) / (φ * (2 - p)))
    rw [neg_div]
  · -- absolutely continuous part
    exact MeasureTheory.withDensity_congr_ae (tweedie_density_series_ae μ hμ hφ hp₁ hp₂)
