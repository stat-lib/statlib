# Proposed design document template

This is a reference checklist, not a required format. Use the sections that are helpful for the
project you want to propose, and discuss the design itself in a GitHub issue before beginning a
large implementation.

# Project: topic
## 1. Goal
What is your goal? Why is it important?

## 2. Completion criteria
Which theorem (big or small) marks this roadmap as done?

## 3. Scope
What definitions and results will you formalize?

## 4. Out of scope
What related topics will you leave out, and why?

## 5. Mathematical model
What informal math (paper or textbook) are you formalizing, and how does your Lean version differ from it?

## 6. Design decisions and conventions
Fix some design choices (select items below that are applicable to your goal):
- Carrier type: what Lean type represents the object you study (e.g. a plain function, a structure, a measure)?
- Namespace: which namespace will your definitions and lemmas live in?
- Parameter order: in what order does each definition take its arguments, given that this fixes what can be partially applied?
- Totalization/boundary behavior: what do your functions return where the math is undefined (junk values such as `x / 0 = 0`)?
- Composition convention: if your objects compose, what does `f.comp g` mean and in which order does it apply?
- Typeclass assumptions: what minimal structure (e.g. `[MeasurableSpace Ω]`, `[Fintype ι]`) does each definition or theorem require?
- Finite/infinite conventions: do you assume finite or general settings (sums vs. integrals, `ℝ` vs. `ℝ≥0∞`/`EReal`)?


## 7. Existing Mathlib and Statlib foundations
Which files or PRs will you build on, and which related ones will you not use?

## 8. Proposed file organization

```text
Project/Area/Basic.lean
Project/Area/Operations.lean
Project/Area/MainTheorem.lean
``` 
The goal is to make important design choices explicit, reduce communication overhead, and leave a
useful record for contributors who join the project later.
