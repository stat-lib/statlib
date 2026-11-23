/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Statlib.Privacy.RenyiDP.Basic
public import Statlib.Privacy.ZCDP.Basic

/-!
# Zero-concentrated DP as Rényi DP at every order

Bun and Steinke (*Concentrated differential privacy: simplifications, extensions, and lower
bounds*, TCC 2016, arXiv:1605.02065, Definition 1.1) define `(ξ, ρ)`-zCDP by the bound
`D_α(M S ‖ M S') ≤ ξ + ρ α` for every order `α > 1`, which is Mironov's `(α, ξ + ρ α)`-Rényi
differential privacy (*Rényi differential privacy*, CSF 2017, arXiv:1702.07476, Definition 4)
holding simultaneously at every order `α > 1`. Both papers note this correspondence; this file
records it as an equivalence between the library's `IsZCDP` and `IsRenyiDP`.

## Main statements

* `isZCDP_iff_forall_isRenyiDP`: for `ξ, ρ ≥ 0`, `(ξ, ρ)`-zCDP holds iff the mechanism is
  `(α, ξ + ρ α)`-RDP for every `α > 1`.
* `isZCDP_zero_iff_forall_isRenyiDP`: the case `ξ = 0` (`ρ`-zCDP).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace InformationTheory

variable {𝒟 Y : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}
  {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop}

/-- **zCDP is RDP at every order**: for nonnegative `ξ, ρ`, the mechanism is `(ξ, ρ)`-zCDP
(Bun–Steinke, Definition 1.1) iff it is `(α, ξ + ρ α)`-Rényi DP (Mironov, Definition 4) for every
order `α > 1`. -/
theorem isZCDP_iff_forall_isRenyiDP (ξ ρ : ℝ≥0) :
    IsZCDP M Adj ξ ρ ↔ ∀ α : ℝ, 1 < α → IsRenyiDP M Adj α (ξ + ρ * α.toNNReal) := by
  rw [isZCDP_iff_le_ofReal ξ.coe_nonneg ρ.coe_nonneg]
  have key : ∀ α : ℝ, 1 < α →
      ENNReal.ofReal ((ξ : ℝ) + ρ * α) = ((ξ + ρ * α.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    intro α hα
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [Real.coe_toNNReal _ (by linarith)]
  constructor
  · intro h α hα S S' hS
    rw [← key α hα]
    exact h hS α hα
  · intro h S S' hS α hα
    rw [key α hα]
    exact h α hα hS

/-- `ρ`-zCDP iff `(α, ρ α)`-Rényi DP at every order `α > 1`. -/
theorem isZCDP_zero_iff_forall_isRenyiDP (ρ : ℝ≥0) :
    IsZCDP M Adj 0 ρ ↔ ∀ α : ℝ, 1 < α → IsRenyiDP M Adj α (ρ * α.toNNReal) := by
  simpa using isZCDP_iff_forall_isRenyiDP (M := M) (Adj := Adj) 0 ρ

end InformationTheory
