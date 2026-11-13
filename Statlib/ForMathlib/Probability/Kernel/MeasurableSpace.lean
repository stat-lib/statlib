/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Measurable space of kernels

The space of kernels `Kernel 𝓧 𝓨` carries the σ-algebra induced by the coercion to functions
`𝓧 → Measure 𝓨`: the coarsest one for which all the evaluations `κ ↦ κ x` are measurable.

## Main statements

* `ProbabilityTheory.measurable_kernel_iff`: a map into a space of kernels is measurable if and only
  if all its evaluations are measurable.
* `ProbabilityTheory.Kernel.measurable_eval`: the evaluations `κ ↦ κ x` are measurable.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {𝓧 𝓨 𝓩 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}

instance instMeasurableSpaceKernel : MeasurableSpace (Kernel 𝓧 𝓨) :=
  MeasurableSpace.comap (fun κ ↦ (κ : 𝓧 → Measure 𝓨)) inferInstance

lemma measurable_kernel_iff (f : 𝓧 → Kernel 𝓨 𝓩) : Measurable f ↔ ∀ y, Measurable (f · y) := by
  unfold instMeasurableSpaceKernel
  rw [measurable_comap_iff, measurable_pi_iff]
  simp

namespace Kernel

lemma measurable_eval (x : 𝓧) : Measurable fun κ : Kernel 𝓧 𝓨 ↦ κ x :=
  (measurable_kernel_iff (id : Kernel 𝓧 𝓨 → Kernel 𝓧 𝓨)).1 measurable_id x

lemma measurable_eval' (x : 𝓧) {s : Set 𝓨} (hs : MeasurableSet s) :
    Measurable fun κ : Kernel 𝓧 𝓨 ↦ κ x s :=
  (Measure.measurable_coe hs).comp (measurable_eval x)

@[fun_prop]
lemma measurable_const : Measurable (@Kernel.const 𝓧 𝓨 m𝓧 m𝓨) := by
  rw [measurable_kernel_iff]
  simp only [const_apply]
  fun_prop

end Kernel

end ProbabilityTheory
