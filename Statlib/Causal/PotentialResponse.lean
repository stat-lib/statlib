/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/

module

public import Mathlib.Init

/-!
# Potential Responses

This module supplies an assumption-free functional representation of potential responses.

`PotentialResponse.id` is the identity for same-unit substitution.
`PotentialResponse.select` produces a theoretical selected response, not a recorded outcome.
`PotentialResponse.comp` performs same-unit substitution.

For example, given `mediator : PotentialResponse Treatment Unit Mediator` and
`outcome : PotentialResponse (Treatment × Mediator) Unit Outcome`, the response

```lean
outcome.comp (fun (treatment, mediatorTreatment) unit ↦
  (treatment, mediator mediatorTreatment unit))
```

evaluated at `(a, a')` and `u` is `outcome (a, mediator a' u) u`, representing the nested
response $Y(a, M(a'))$. The mediator and outcome responses are evaluated at the same unit `u`.

Causal assumptions, estimands, estimators, probability structure, and statistical inference are
deferred to later modules.
-/

@[expose] public section

/-- A potential response assigns a value to each intervention and unit. -/
abbrev PotentialResponse
    (Intervention : Type*) (Unit : Type*) (Value : Type*) :=
  Intervention → Unit → Value

namespace PotentialResponse

variable {Intervention : Type*} {Unit : Type*} {Value : Type*}
  {Index : Type*} {Source : Type*}

/-- The identity potential response returns its intervention and ignores the unit. -/
def id : PotentialResponse Intervention Unit Intervention :=
  fun intervention _ ↦ intervention

/-- Selects each unit's response at the intervention supplied for that unit. -/
def select
    (response : PotentialResponse Intervention Unit Value)
    (intervention : Unit → Intervention) :
    Unit → Value :=
  fun u ↦ response (intervention u) u

/-- Substitutes an intervention response into a response, evaluating both at the same unit. -/
def comp
    (response : PotentialResponse Intervention Unit Value)
    (intervention :
      PotentialResponse Index Unit Intervention) :
    PotentialResponse Index Unit Value :=
  fun index u ↦ response (intervention index u) u

@[simp] theorem id_apply (intervention : Intervention) (u : Unit) :
    (id : PotentialResponse Intervention Unit Intervention) intervention u = intervention := rfl

@[simp] theorem select_apply
    (response : PotentialResponse Intervention Unit Value)
    (intervention : Unit → Intervention)
    (u : Unit) :
    response.select intervention u =
      response (intervention u) u := rfl

@[simp] theorem comp_apply
    (response : PotentialResponse Intervention Unit Value)
    (intervention :
      PotentialResponse Index Unit Intervention)
    (index : Index)
    (u : Unit) :
    response.comp intervention index u =
      response (intervention index u) u := rfl

@[simp] theorem comp_id
    (response : PotentialResponse Intervention Unit Value) :
    response.comp id = response := rfl

@[simp] theorem id_comp
    (response : PotentialResponse Intervention Unit Value) :
    id.comp response = response := rfl

theorem comp_assoc
    (response : PotentialResponse Intervention Unit Value)
    (intervention : PotentialResponse Index Unit Intervention)
    (source : PotentialResponse Source Unit Index) :
    (response.comp intervention).comp source =
      response.comp (intervention.comp source) := rfl

end PotentialResponse
