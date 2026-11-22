/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Statlib.Divergence.FDiv.Binary
public import Statlib.ForMathlib.Probability.Decision.Risk.Basic

/-!
# Lower bounds on the Bayes risk from f-divergences

Consider an estimation problem with parameter space `Θ`, data generating kernels `P Q : Θ ⇝ 𝓧`,
priors `π ξ` on `Θ` and a loss `ℓ : Θ → 𝓨 → ℝ≥0∞` with values in `[0, 1]`. We prove that the
f-divergence between the joint laws `π ⊗ₘ Q` and `ξ ⊗ₘ P` is at least the binary f-divergence
`d_f(R_π^Q, R_ξ^P)` between the Bernoulli distributions whose parameters are the two Bayes risks.

## Main statements

* `fDiv_bernoulliMeasure_avgRisk_le`: for any estimator `κ`, the binary f-divergence between the
  average risks of `κ` in the two problems is at most `fDiv f (π ⊗ₘ Q) (ξ ⊗ₘ P)`.
* `fDiv_bernoulliMeasure_bayesRisk_le`: the binary f-divergence between the Bayes risks is at most
  `fDiv f (π ⊗ₘ Q) (ξ ⊗ₘ P)`.

## Implementation notes

The parameters of the Bernoulli distributions are elements `p q : I` of the unit interval, related
to the risks by hypotheses of the form `ENNReal.ofReal p = bayesRisk ℓ Q π`.

The proof of the reference uses a Bayes estimator, which need not exist. We use instead estimators
whose risk is arbitrarily close to the Bayes risk, and the continuity of the binary f-divergence in
its first argument (`fDiv_bernoulliMeasure_le_of_forall_exists`). The case in which the first Bayes
risk is larger than the second one is reduced to the other case by swapping the measures with the
conjugate divergence function `f.conj`.
-/

@[expose] public section

open MeasureTheory Function unitInterval

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ℝ≥0∞} {f : DivFunction}

variable {π ξ : Measure Θ} [IsProbabilityMeasure π] [IsProbabilityMeasure ξ]
  {P Q : Kernel Θ 𝓧} [IsMarkovKernel P] [IsMarkovKernel Q]

/-- **Data processing for the risk of an estimator**: for any estimator `κ` (a Markov kernel, or
zero), the binary f-divergence between the average risks of `κ` for `(Q, π)` and for `(P, ξ)` is at
most `fDiv f (π ⊗ₘ Q) (ξ ⊗ₘ P)`. -/
theorem fDiv_bernoulliMeasure_avgRisk_le (hℓ : Measurable (uncurry ℓ)) (hℓ1 : ∀ θ y, ℓ θ y ≤ 1)
    (κ : Kernel 𝓧 𝓨) [IsZeroOrMarkovKernel κ] {p q : I} (hp : ENNReal.ofReal p = avgRisk ℓ Q κ π)
    (hq : ENNReal.ofReal q = avgRisk ℓ P κ ξ) :
    fDiv f Ber(true, false, p) Ber(true, false, q) ≤ fDiv f (π ⊗ₘ Q) (ξ ⊗ₘ P) := by
  refine fDiv_bernoulliMeasure_le_of_lintegral_eq _ _ (measurable_lintegral_loss hℓ κ)
    (fun z ↦ ?_) ?_ ?_
  · calc ∫⁻ y, ℓ z.1 y ∂κ z.2 ≤ ∫⁻ _, 1 ∂κ z.2 := lintegral_mono (hℓ1 z.1)
      _ ≤ 1 := by simpa using prob_le_one
  · rw [hp, avgRisk_eq_lintegral_compProd hℓ]
  · rw [hq, avgRisk_eq_lintegral_compProd hℓ]

/-- Auxiliary lemma for `fDiv_bernoulliMeasure_bayesRisk_le`: the case `p ≤ q`. -/
private lemma fDiv_bernoulliMeasure_bayesRisk_le_of_le (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) {p q : I} (hp : ENNReal.ofReal p = bayesRisk ℓ Q π)
    (hq : ENNReal.ofReal q = bayesRisk ℓ P ξ) (hpq : p ≤ q) :
    fDiv f Ber(true, false, p) Ber(true, false, q) ≤ fDiv f (π ⊗ₘ Q) (ξ ⊗ₘ P) := by
  refine fDiv_bernoulliMeasure_le_of_forall_exists hpq fun ε hε ↦ ?_
  -- an estimator with risk at most `p + ε` for the first problem
  have h_lt : bayesRisk ℓ Q π < ENNReal.ofReal (p + ε) := by
    rw [← hp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [p.property.1])).mpr (by linarith)
  obtain ⟨κ, hκ, hκ_lt⟩ : ∃ κ : Kernel 𝓧 𝓨, ∃ _ : IsMarkovKernel κ,
      avgRisk ℓ Q κ π < ENNReal.ofReal (p + ε) := by
    simpa [bayesRisk, iInf_lt_iff] using h_lt
  -- the average risks of `κ` in the two problems, as elements of `I`
  have h_mem {r : ℝ≥0∞} (hr : r ≤ 1) : ∃ a : I, ENNReal.ofReal a = r :=
    ⟨⟨_, ENNReal.toReal_mem_unitInterval hr⟩,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hr)⟩
  obtain ⟨a, ha⟩ := h_mem (avgRisk_le_one hℓ1 Q κ π)
  obtain ⟨b, hb⟩ := h_mem (avgRisk_le_one hℓ1 P κ ξ)
  refine ⟨a, b, ?_, ?_, ?_, fDiv_bernoulliMeasure_avgRisk_le hℓ hℓ1 κ ha hb⟩
  · rw [← Subtype.coe_le_coe, ← ENNReal.ofReal_le_ofReal_iff a.property.1, ha, hp]
    exact bayesRisk_le_avgRisk ℓ Q κ π
  · exact (ENNReal.ofReal_le_ofReal_iff (by linarith [p.property.1])).1 (ha.trans_lt hκ_lt).le
  · rw [← Subtype.coe_le_coe, ← ENNReal.ofReal_le_ofReal_iff b.property.1, hb, hq]
    exact bayesRisk_le_avgRisk ℓ P κ ξ

/-- **Lower bound on the f-divergence from the Bayes risks**: for a loss with values in `[0, 1]`,
the binary f-divergence between the Bayes risks `R_π^Q` and `R_ξ^P` is at most
`fDiv f (π ⊗ₘ Q) (ξ ⊗ₘ P)`. -/
theorem fDiv_bernoulliMeasure_bayesRisk_le (hℓ : Measurable (uncurry ℓ))
    (hℓ1 : ∀ θ y, ℓ θ y ≤ 1) {p q : I} (hp : ENNReal.ofReal p = bayesRisk ℓ Q π)
    (hq : ENNReal.ofReal q = bayesRisk ℓ P ξ) :
    fDiv f Ber(true, false, p) Ber(true, false, q) ≤ fDiv f (π ⊗ₘ Q) (ξ ⊗ₘ P) := by
  rcases le_total p q with hpq | hqp
  · exact fDiv_bernoulliMeasure_bayesRisk_le_of_le hℓ hℓ1 hp hq hpq
  · rw [← fDiv_conj, ← fDiv_conj (ξ ⊗ₘ P) (π ⊗ₘ Q)]
    exact fDiv_bernoulliMeasure_bayesRisk_le_of_le hℓ hℓ1 hq hp hqp

end ProbabilityTheory
