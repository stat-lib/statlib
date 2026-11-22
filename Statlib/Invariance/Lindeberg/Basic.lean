/-
Copyright (c) 2026 Swagato Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Swagato Das
-/
module

public import Mathlib

/-!
# Lindeberg swap, Chatterjee's sup-norm version

This file formalizes the Lindeberg replacement principle in the form proved by Chatterjee
(*A simple invariance theorem*, arXiv:math/0508213, Theorem 1.1). Given two vectors of
independent real random variables `X = (X_1, …, X_n)` and `Y = (Y_1, …, Y_n)` whose coordinates
have the same first and second moments, the expectation of `g (f (·))` changes by a controlled
amount when `X` is replaced by `Y`, for a test function `g : ℝ → ℝ` and a function
`f : ℝⁿ → ℝ` that is smooth in each coordinate separately.

The error bound involves only the coordinatewise suprema of the derivatives of `f` (the
quantities `λ₂(f)` and `λ₃(f)` below) and the sup-norms of the first three derivatives of `g`.
It does not involve any joint (multivariate) Lipschitz or Hessian norm of `f`.

## The statement

For every truncation level `K`,

`|E g(f(X)) − E g(f(Y))|
   ≤ C₁(g) λ₂(f) ∑ᵢ (E(Xᵢ²; |Xᵢ| > K) + E(Yᵢ²; |Yᵢ| > K))
   + C₂(g) λ₃(f) ∑ᵢ (E(|Xᵢ|³; |Xᵢ| ≤ K) + E(|Yᵢ|³; |Yᵢ| ≤ K))`,

where `C₁(g) = ‖g'‖ + ‖g''‖`, `C₂(g) = ‖g'‖/6 + ‖g''‖/2 + ‖g'''‖/6`,
`λ₂(f) = sup (|∂ᵢf|², |∂ᵢ²f|)` and `λ₃(f) = sup (|∂ᵢf|³, |∂ᵢ²f|^{3/2}, |∂ᵢ³f|)`, the suprema
being over all coordinates `i` and all points. This is `Statlib.Invariance.swap_bound`.

Letting `K → ∞` (when third moments exist) gives the classical Lindeberg bound
`2 C₂(g) λ₃(f) ∑ᵢ max (E|Xᵢ|³, E|Yᵢ|³)`; letting `K` be a multiple of `√n` is what produces the
Lindeberg condition in the central limit theorem. Neither consequence is proved here.

## Proof outline

1. *Hybrids.* Put `Z_k = (X_1, …, X_k, Y_{k+1}, …, Y_n)`, so `Z_0 = Y` and `Z_n = X`. By the
   triangle inequality it suffices to bound `|E g(f(Z_{k+1})) − E g(f(Z_k))|` for each `k`
   (`abs_sub_le_sum_range`, `hyb`).
2. *One slot.* `Z_{k+1}` and `Z_k` differ only in slot `k`, where they carry `X_k` and `Y_k`.
   Both are obtained from the *same* base point `W_k` (with `0` in slot `k`) by writing `X_k`,
   respectively `Y_k`, into slot `k` (`baseVec`, `hyb_succ_eq`, `hyb_eq`). Moreover `X_k`,
   `Y_k` are independent of `W_k` (`indep_slot`).
3. *Taylor expansion in the slot.* For the one-variable function `s ↦ g (f (W with s in slot
   k))`, expand to second order at `0`. The coefficients depend on `W_k` only, so by
   independence the first-order term contributes `E[X_k] · E[∂ term]` and the second-order term
   `E[X_k²]/2 · E[∂² term]` (`slot_expansion`). These are equal for `X_k` and `Y_k` by the
   moment-matching hypotheses, and they cancel (`slot_swap`).
4. *Remainder.* What is left is the Taylor remainder. For `|a| ≤ K` it is at most
   `C₂(g) λ₃(f) |a|³` (Lagrange form, third derivative). For `|a| > K` it is at most
   `C₁(g) λ₂(f) a²` (first-order Taylor plus the second-order term, both bounded through the
   second derivative). This is `remainder_slice_le`; integrating over `a = X_k` and `a = Y_k`
   gives the `tailSq` and `truncCube` terms (`abs_integral_slotRem_le`).
5. *Sum over `k`.* Add up the `n` slot bounds (`swap_bound`).

## Main definitions

* `coordDeriv p f i x`: the `p`-th derivative of `f` in coordinate `i` at `x`.
* `lam r f`: `λ_r(f) = sup |∂ᵢ^p f|^{r/p}` over `i`, `1 ≤ p ≤ r` and `x`. It is valued in
  `ℝ≥0∞`, so that "unbounded" is `⊤` rather than a junk value.
* `CoordC3 f`: `f` is `C³` along every coordinate line.
* `BddC3 g`: `g : ℝ → ℝ` is `C³` with bounded derivatives of orders 1, 2 and 3.
* `C₁ g`, `C₂ g`: the constants `‖g'‖ + ‖g''‖` and `‖g'‖/6 + ‖g''‖/2 + ‖g'''‖/6`.
* `tailSq P Z K = E(Z²; |Z| > K)` and `truncCube P Z K = E(|Z|³; |Z| ≤ K)`.

## Main statements

* `swap_bound`: the theorem displayed above.
* `slot_swap`: the same statement for a single coordinate, with an arbitrary base point `W`
  independent of the two swapped variables. `swap_bound` is a telescoping sum of these.
* `remainder_slice_le`: the pointwise Taylor remainder bound, with no probability involved.

## Hypotheses of `swap_bound`, and how they differ from the paper

The paper assumes `f` is smooth (it never discusses measurability) and the `Xᵢ`, `Yᵢ` are
independent. Here the following are made explicit.

* `g` is bounded (`hgb`), in addition to `BddC3 g`. This makes every expectation exist, so that
  no integrability bookkeeping on `g ∘ f` is needed. It holds for the test functions used in the
  central limit theorem (`C_b³`).
* `f` is measurable and so are its first two coordinate derivatives (`hfm`, `hd1`, `hd2`).
  This is automatic for jointly `C³` functions. It is needed to take expectations of the
  slice derivatives that appear in the Taylor expansion.
* Independence is stated as `iIndepFun (Sum.elim X Y) P`: the `2n` variables `X_1, …, X_n,
  Y_1, …, Y_n` are jointly independent. This is what the proof uses (the base point of slot `k`
  mixes some `X_j` and some `Y_j`).
* Second moments exist, and first and second moments of `Xᵢ` and `Yᵢ` agree (`hX2`, `hY2`,
  `hmean`, `hsq`).
* `lam 2 f ≠ ⊤` and `lam 3 f ≠ ⊤`: both scales are finite. Otherwise the right-hand side is
  infinite and the statement is vacuous.
* `K` is any real number; the paper takes `K > 0`, but the proof does not use the sign of `K`.

## Not formalized here

* The central limit theorem and the Lindeberg–Feller theorem obtained from `swap_bound`.
* The statement that `C_b³` test functions determine weak convergence on `ℝ`.
* Chatterjee's version for dependent summands and the soft-max extension to maxima.
* Mossel–O'Donnell–Oleszkiewicz's invariance principle for multilinear polynomials.

## References

* S. Chatterjee, *A simple invariance theorem*, arXiv:math/0508213 (2005), Theorem 1.1.
* S. Chatterjee, *A generalization of the Lindeberg principle*, Ann. Probab. 34 (2006).
* J. W. Lindeberg, *Eine neue Herleitung des Exponentialgesetzes in der
  Wahrscheinlichkeitsrechnung*, Math. Z. 15 (1922).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Statlib.Invariance

variable {n : ℕ}

/-- The `p`-th derivative of `f` in coordinate `i`, at `x`.

It is the `p`-th derivative at `t = x i` of the one-variable function `t ↦ f (update x i t)`,
which changes only the `i`-th entry of `x`. For `p = 0` it is `f x`. -/
noncomputable def coordDeriv (p : ℕ) (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  iteratedDeriv p (fun t => f (Function.update x i t)) (x i)

/-- Chatterjee's scale `λ_r(f) = sup_{i, 1 ≤ p ≤ r, x} |∂ᵢ^p f (x)|^{r/p}`.

For `r = 2` this is the supremum of `|∂ᵢ f|²` and `|∂ᵢ² f|`; for `r = 3` the supremum of
`|∂ᵢ f|³`, `|∂ᵢ² f|^{3/2}` and `|∂ᵢ³ f|`. The exponents `r/p` are chosen so that
the terms combine, for instance `|∂ᵢ f| · |∂ᵢ² f| ≤ λ₃(f)`, which is used in the third-order
bound.

The value is in `ℝ≥0∞`: `lam r f = ⊤` means that some derivative is unbounded, and then every
bound that mentions `λ_r(f)` is vacuous. Theorems assume `lam r f ≠ ⊤` and use `.toReal`. -/
noncomputable def lam (r : ℕ) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ (i : Fin n) (p : ℕ) (_ : 1 ≤ p ∧ p ≤ r) (x : Fin n → ℝ),
    ENNReal.ofReal (|coordDeriv p f i x| ^ ((r : ℝ) / p))

/-- `f` is `C³` along every coordinate line: for every point `x` and coordinate `i`, the
function `t ↦ f (update x i t)` is three times continuously differentiable.

No joint regularity of `f` is assumed (a separately smooth function need not even be
continuous). Measurability of `f` and of its partial derivatives is a separate hypothesis. -/
def CoordC3 (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n) (x : Fin n → ℝ), ContDiff ℝ 3 (fun t => f (Function.update x i t))

/-- Test functions of the swap theorem: `g : ℝ → ℝ` is `C³` and its derivatives of orders
1, 2 and 3 are bounded. The function `g` itself need not be bounded here; `swap_bound`
assumes that separately. -/
structure BddC3 (g : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 3 g
  bdd : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∃ M : ℝ, ∀ x, |iteratedDeriv k g x| ≤ M

/-- `‖g^{(k)}‖_∞ = sup_x |g^{(k)}(x)|`.

This is a real supremum, so it is the junk value `0` when `g^{(k)}` is unbounded. For `BddC3`
functions and `1 ≤ k ≤ 3` this does not happen, see `abs_iteratedDeriv_le_supDeriv`. -/
noncomputable def supDeriv (k : ℕ) (g : ℝ → ℝ) : ℝ := ⨆ x, |iteratedDeriv k g x|

/-- `C₁(g) = ‖g'‖ + ‖g''‖`, the constant in front of the second-moment tail term. -/
noncomputable def C₁ (g : ℝ → ℝ) : ℝ := supDeriv 1 g + supDeriv 2 g

/-- `C₂(g) = ‖g'‖/6 + ‖g''‖/2 + ‖g'''‖/6`, the constant in front of the truncated third-moment
term. It is `1/6` times the bound `‖g'‖ + 3‖g''‖ + ‖g'''‖` for the third derivative of
`g ∘ u` when `|u'|³, |u''|^{3/2}, |u'''| ≤ 1`. -/
noncomputable def C₂ (g : ℝ → ℝ) : ℝ := supDeriv 1 g / 6 + supDeriv 2 g / 2 + supDeriv 3 g / 6

/-!
## Part 1. Calculus for `g ∘ u` in one variable

`u` is a real function of one real variable (later a coordinate slice of `f`). We compute the
second and third derivatives of `g ∘ u` and bound them by sup-norms of `g'`, `g''`, `g'''` times
powers of the derivatives of `u`.
-/

/-- The second iterated derivative is the derivative of the derivative. -/
lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- Pointwise bound by the sup-norm: `|g^{(k)}(x)| ≤ ‖g^{(k)}‖_∞` for `BddC3` functions and
`1 ≤ k ≤ 3`. The only content is that the range of `|g^{(k)}|` is bounded above, which is
exactly the `bdd` field of `BddC3`. -/
lemma abs_iteratedDeriv_le_supDeriv {g : ℝ → ℝ} (hg : BddC3 g) {k : ℕ} (hk₁ : 1 ≤ k)
    (hk₃ : k ≤ 3) (x : ℝ) : |iteratedDeriv k g x| ≤ supDeriv k g := by
  obtain ⟨M, hM⟩ := hg.bdd k hk₁ hk₃
  unfold supDeriv
  exact le_ciSup (f := fun y => |iteratedDeriv k g y|)
    ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩ x

/-- Chain rule, second order: `(g ∘ u)'' = g''(u) · u'² + g'(u) · u''`.

Proof: `(g ∘ u)' = (g' ∘ u) · u'`, then differentiate the product using the chain rule for
`g' ∘ u` and the product rule. -/
lemma iteratedDeriv_two_comp {g u : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hu : ContDiff ℝ 2 u)
    (t : ℝ) :
    iteratedDeriv 2 (g ∘ u) t =
      iteratedDeriv 2 g (u t) * deriv u t ^ 2 + deriv g (u t) * iteratedDeriv 2 u t := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hgd' : Differentiable ℝ (deriv g) := by
    have := hg.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have hud' : Differentiable ℝ (deriv u) := by
    have := hu.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have h1 : deriv (g ∘ u) = fun s => deriv g (u s) * deriv u s := by
    funext s
    exact deriv_comp s (hgd (u s)) (hud s)
  simp only [iteratedDeriv_two_eq]
  rw [h1]
  have a : HasDerivAt (deriv g) (deriv (deriv g) (u t)) (u t) := (hgd' (u t)).hasDerivAt
  have b : HasDerivAt u (deriv u t) t := (hud t).hasDerivAt
  have c : HasDerivAt (deriv u) (deriv (deriv u) t) t := (hud' t).hasDerivAt
  have d : HasDerivAt (fun s => deriv g (u s)) (deriv (deriv g) (u t) * deriv u t) t :=
    a.comp t b
  have e : HasDerivAt (fun s => deriv g (u s) * deriv u s)
    (deriv (deriv g) (u t) * deriv u t * deriv u t
    + deriv g (u t) * deriv (deriv u) t) t := d.mul c
  rw [e.deriv]
  ring

/-- `|(g ∘ u)''| ≤ C₁(g) · L` whenever `|u'|² ≤ L` and `|u''| ≤ L`.

By `iteratedDeriv_two_comp`, `|(g ∘ u)''| ≤ ‖g''‖ |u'|² + ‖g'‖ |u''| ≤ (‖g''‖ + ‖g'‖) L`.
Here `L` plays the role of `λ₂(f)`. -/
lemma abs_iteratedDeriv_two_comp_le {g u : ℝ → ℝ} (hg : BddC3 g) (hu : ContDiff ℝ 2 u)
    {L : ℝ} (t : ℝ) (h1 : |deriv u t| ^ 2 ≤ L) (h2 : |iteratedDeriv 2 u t| ≤ L) :
    |iteratedDeriv 2 (g ∘ u) t| ≤ C₁ g * L := by
  have hg2 : ContDiff ℝ 2 g := hg.contDiff.of_le (by norm_num)
  rw [iteratedDeriv_two_comp hg2 hu t]
  have A := abs_iteratedDeriv_le_supDeriv hg (k := 2) (by norm_num) (by norm_num) (u t)
  have B : |deriv g (u t)| ≤ supDeriv 1 g := by
    simpa [iteratedDeriv_one] using
      abs_iteratedDeriv_le_supDeriv hg (k := 1) le_rfl (by norm_num) (u t)
  have e1 : |iteratedDeriv 2 g (u t) * deriv u t ^ 2| ≤ supDeriv 2 g * L := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul A h1 (by positivity) ((abs_nonneg _).trans A)
  have e2 : |deriv g (u t) * iteratedDeriv 2 u t| ≤ supDeriv 1 g * L := by
    rw [abs_mul]
    exact mul_le_mul B h2 (abs_nonneg _) ((abs_nonneg _).trans B)
  calc _ ≤ |iteratedDeriv 2 g (u t) * deriv u t ^ 2| + |deriv g (u t) * iteratedDeriv 2 u t| :=
        abs_add_le _ _
    _ ≤ supDeriv 2 g * L + supDeriv 1 g * L := add_le_add e1 e2
    _ = C₁ g * L := by unfold C₁; ring

/-- The third iterated derivative is the derivative of the derivative of the derivative. -/
lemma iteratedDeriv_three_eq (f : ℝ → ℝ) :
    iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_eq]

/-- Chain rule, third order:
`(g ∘ u)''' = g'''(u) · u'³ + 3 g''(u) · u' · u'' + g'(u) · u'''`.

Proof: differentiate the second-order formula `iteratedDeriv_two_comp` term by term, using
the product rule, the chain rule for `g'' ∘ u` and `g' ∘ u`, and `(u'²)' = 2 u' u''`. -/
lemma iteratedDeriv_three_comp {g u : ℝ → ℝ} (hg : ContDiff ℝ 3 g) (hu : ContDiff ℝ 3 u)
    (t : ℝ) :
    iteratedDeriv 3 (g ∘ u) t =
      iteratedDeriv 3 g (u t) * deriv u t ^ 3
        + 3 * iteratedDeriv 2 g (u t) * deriv u t * iteratedDeriv 2 u t
        + deriv g (u t) * iteratedDeriv 3 u t := by
  have hg1 : Differentiable ℝ (deriv g) := by
    have := hg.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have hg2 : Differentiable ℝ (deriv (deriv g)) := by
    have := hg.differentiable_iteratedDeriv 2 (by norm_num)
    rwa [iteratedDeriv_two_eq] at this
  have hu0 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu1 : Differentiable ℝ (deriv u) := by
    have := hu.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have hu2 : Differentiable ℝ (deriv (deriv u)) := by
    have := hu.differentiable_iteratedDeriv 2 (by norm_num)
    rwa [iteratedDeriv_two_eq] at this
  have h2 : deriv (deriv (g ∘ u)) = fun s =>
      deriv (deriv g) (u s) * deriv u s ^ 2 + deriv g (u s) * deriv (deriv u) s := by
    funext s
    have := iteratedDeriv_two_comp (hg.of_le (by norm_num)) (hu.of_le (by norm_num)) s
    simp only [iteratedDeriv_two_eq] at this
    exact this
  simp only [iteratedDeriv_three_eq, iteratedDeriv_two_eq]
  rw [h2]
  have A : HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) (u t)) (u t) :=
    (hg2 (u t)).hasDerivAt
  have B : HasDerivAt (deriv g) (deriv (deriv g) (u t)) (u t) := (hg1 (u t)).hasDerivAt
  have b : HasDerivAt u (deriv u t) t := (hu0 t).hasDerivAt
  have c : HasDerivAt (deriv u) (deriv (deriv u) t) t := (hu1 t).hasDerivAt
  have c2 : HasDerivAt (deriv (deriv u)) (deriv (deriv (deriv u)) t) t := (hu2 t).hasDerivAt
  have dA : HasDerivAt (fun s => deriv (deriv g) (u s))
      (deriv (deriv (deriv g)) (u t) * deriv u t) t := A.comp t b
  have dB : HasDerivAt (fun s => deriv g (u s)) (deriv (deriv g) (u t) * deriv u t) t :=
    B.comp t b
  have p : HasDerivAt (fun s => deriv u s ^ 2) (2 * deriv u t * deriv (deriv u) t) t := by
    have e : (fun s => deriv u s ^ 2) = deriv u * deriv u := by
      funext s; simp [pow_two]
    rw [e]
    exact (c.mul c).congr_deriv (by ring)
  have e1 : HasDerivAt (fun s => deriv (deriv g) (u s) * deriv u s ^ 2)
      (deriv (deriv (deriv g)) (u t) * deriv u t * deriv u t ^ 2
        + deriv (deriv g) (u t) * (2 * deriv u t * deriv (deriv u) t)) t := dA.mul p
  have e2 : HasDerivAt (fun s => deriv g (u s) * deriv (deriv u) s)
      (deriv (deriv g) (u t) * deriv u t * deriv (deriv u) t
        + deriv g (u t) * deriv (deriv (deriv u)) t) t := dB.mul c2
  have e3 : HasDerivAt
      (fun s => deriv (deriv g) (u s) * deriv u s ^ 2 + deriv g (u s) * deriv (deriv u) s)
      ((deriv (deriv (deriv g)) (u t) * deriv u t * deriv u t ^ 2
        + deriv (deriv g) (u t) * (2 * deriv u t * deriv (deriv u) t))
        + (deriv (deriv g) (u t) * deriv u t * deriv (deriv u) t
        + deriv g (u t) * deriv (deriv (deriv u)) t)) t := e1.add e2
  rw [e3.deriv]
  ring

/-- `|(g ∘ u)'''| ≤ 6 C₂(g) · L` whenever `|u'|³ ≤ L`, `|u''|³ ≤ L²` and `|u'''| ≤ L`.

The hypotheses on `u''` and `u'''` avoid real powers: `|u''|³ ≤ L²` says `|u''|^{3/2} ≤ L`.
They give `|u'| · |u''| ≤ L`, because `(|u'| · |u''|)³ ≤ L · L² = L³`. Then by
`iteratedDeriv_three_comp`,
`|(g ∘ u)'''| ≤ ‖g'''‖ L + 3 ‖g''‖ L + ‖g'‖ L = 6 C₂(g) L`.
Here `L` plays the role of `λ₃(f)`. -/
lemma abs_iteratedDeriv_three_comp_le {g u : ℝ → ℝ} (hg : BddC3 g) (hu : ContDiff ℝ 3 u)
    {L : ℝ} (t : ℝ) (hL : 0 ≤ L) (h1 : |deriv u t| ^ 3 ≤ L)
    (h2 : |iteratedDeriv 2 u t| ^ 3 ≤ L ^ 2) (h3 : |iteratedDeriv 3 u t| ≤ L) :
    |iteratedDeriv 3 (g ∘ u) t| ≤ 6 * C₂ g * L := by
  rw [iteratedDeriv_three_comp hg.contDiff hu t]
  have A1 : |deriv g (u t)| ≤ supDeriv 1 g := by
    simpa [iteratedDeriv_one] using
      abs_iteratedDeriv_le_supDeriv hg (k := 1) le_rfl (by norm_num) (u t)
  have A2 := abs_iteratedDeriv_le_supDeriv hg (k := 2) (by norm_num) (by norm_num) (u t)
  have A3 := abs_iteratedDeriv_le_supDeriv hg (k := 3) (by norm_num) le_rfl (u t)
  have hS2 : 0 ≤ supDeriv 2 g := (abs_nonneg _).trans A2
  have hm : |deriv u t| * |iteratedDeriv 2 u t| ≤ L := by
    have h : (|deriv u t| * |iteratedDeriv 2 u t|) ^ 3 ≤ L ^ 3 := by
      rw [mul_pow]
      calc |deriv u t| ^ 3 * |iteratedDeriv 2 u t| ^ 3 ≤ L * L ^ 2 :=
            mul_le_mul h1 h2 (by positivity) hL
        _ = L ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hL (by norm_num)).1 h
  have e1 : |iteratedDeriv 3 g (u t) * deriv u t ^ 3| ≤ supDeriv 3 g * L := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul A3 h1 (by positivity) ((abs_nonneg _).trans A3)
  have e2 : |3 * iteratedDeriv 2 g (u t) * deriv u t * iteratedDeriv 2 u t|
      ≤ 3 * supDeriv 2 g * L := by
    calc _ = 3 * |iteratedDeriv 2 g (u t)| * (|deriv u t| * |iteratedDeriv 2 u t|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]; ring
      _ ≤ 3 * supDeriv 2 g * L :=
          mul_le_mul (by linarith) hm (by positivity) (by linarith)
  have e3 : |deriv g (u t) * iteratedDeriv 3 u t| ≤ supDeriv 1 g * L := by
    rw [abs_mul]
    exact mul_le_mul A1 h3 (abs_nonneg _) ((abs_nonneg _).trans A1)
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ supDeriv 3 g * L + 3 * supDeriv 2 g * L + supDeriv 1 g * L :=
        add_le_add (add_le_add e1 e2) e3
    _ = 6 * C₂ g * L := by unfold C₂; ring

/-!
## Part 2. From `λ_r(f)` to bounds along a coordinate line

`coordDeriv` is the derivative along a coordinate direction. This part shows that the derivative
of the slice `s ↦ f (update x i s)` at `t` is `coordDeriv` at the moved point `update x i t`,
and that every `coordDeriv` is bounded by the appropriate power of `λ_r(f)`. Combined with
Part 1 this bounds the second and third derivatives of `g ∘ slice`.
-/

/-- Differentiating the slice of `f` through `x` in coordinate `i`, at the parameter `t`, is
the same as taking `coordDeriv` at the moved point `update x i t`. This holds because moving the
base point along the slice does not change the slice: `update (update x i t) i s = update x i s`. -/
lemma iteratedDeriv_update_eq (p : ℕ) (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ)
    (t : ℝ) :
    iteratedDeriv p (fun s => f (Function.update x i s)) t =
      coordDeriv p f i (Function.update x i t) := by
  simp [coordDeriv, Function.update_idem]

/-- Every term of the supremum defining `lam r f` is bounded by it:
`|∂ᵢ^p f (x)|^{r/p} ≤ λ_r(f)` for `1 ≤ p ≤ r`, provided `λ_r(f) < ⊤`. -/
lemma rpow_le_toReal_lam {f : (Fin n → ℝ) → ℝ} {r p : ℕ} (hr : lam r f ≠ ⊤) (i : Fin n)
    (hp₁ : 1 ≤ p) (hpr : p ≤ r) (x : Fin n → ℝ) :
    |coordDeriv p f i x| ^ ((r : ℝ) / p) ≤ (lam r f).toReal := by
  have h : ENNReal.ofReal (|coordDeriv p f i x| ^ ((r : ℝ) / p)) ≤ lam r f := by
    unfold lam
    exact le_iSup_of_le i (le_iSup_of_le p
      (le_iSup_of_le ⟨hp₁, hpr⟩ (le_iSup_of_le x le_rfl)))
  exact (ENNReal.ofReal_le_iff_le_toReal hr).1 h

section LamBounds

variable {f : (Fin n → ℝ) → ℝ}

/-- `|∂ᵢ f|² ≤ λ₂(f)`. -/
lemma coordDeriv_one_sq_le (hr : lam 2 f ≠ ⊤) (i : Fin n) (y : Fin n → ℝ) :
    |coordDeriv 1 f i y| ^ 2 ≤ (lam 2 f).toReal := by
  have h := rpow_le_toReal_lam hr i (p := 1) le_rfl (by norm_num) y
  simpa using h

/-- `|∂ᵢ² f| ≤ λ₂(f)`. -/
lemma coordDeriv_two_le (hr : lam 2 f ≠ ⊤) (i : Fin n) (y : Fin n → ℝ) :
    |coordDeriv 2 f i y| ≤ (lam 2 f).toReal := by
  have h := rpow_le_toReal_lam hr i (p := 2) (by norm_num) le_rfl y
  simpa using h

/-- `|∂ᵢ f|³ ≤ λ₃(f)`. -/
lemma coordDeriv_one_cube_le (hr : lam 3 f ≠ ⊤) (i : Fin n) (y : Fin n → ℝ) :
    |coordDeriv 1 f i y| ^ 3 ≤ (lam 3 f).toReal := by
  have h := rpow_le_toReal_lam hr i (p := 1) le_rfl (by norm_num) y
  simpa using h

/-- `|∂ᵢ³ f| ≤ λ₃(f)`. -/
lemma coordDeriv_three_le (hr : lam 3 f ≠ ⊤) (i : Fin n) (y : Fin n → ℝ) :
    |coordDeriv 3 f i y| ≤ (lam 3 f).toReal := by
  have h := rpow_le_toReal_lam hr i (p := 3) (by norm_num) le_rfl y
  simpa using h

/-- `|∂ᵢ² f|³ ≤ λ₃(f)²`, the polynomial form of `|∂ᵢ² f|^{3/2} ≤ λ₃(f)`.

Proof: square both sides of the real-power bound from `rpow_le_toReal_lam` and use
`(a^{3/2})² = a³`. -/
lemma coordDeriv_two_cube_le (hr : lam 3 f ≠ ⊤) (i : Fin n) (y : Fin n → ℝ) :
    |coordDeriv 2 f i y| ^ 3 ≤ (lam 3 f).toReal ^ 2 := by
  have h := rpow_le_toReal_lam hr i (p := 2) (by norm_num) (by norm_num) y
  push_cast at h
  have h0 : 0 ≤ |coordDeriv 2 f i y| := abs_nonneg _
  have e : (|coordDeriv 2 f i y| ^ ((3 : ℝ) / 2)) ^ 2 = |coordDeriv 2 f i y| ^ 3 := by
    rw [← Real.rpow_mul_natCast h0]; norm_num
  rw [← e]
  exact pow_le_pow_left₀ (Real.rpow_nonneg h0 _) h 2

/-- `|(g ∘ slice)''| ≤ C₁(g) λ₂(f)`: the second derivative of `g ∘ f` along a coordinate
line, at any point of any line. This is `abs_iteratedDeriv_two_comp_le` with `u` the slice and
`L = λ₂(f)`. -/
lemma abs_iteratedDeriv_two_slice_le (hf : CoordC3 f) (hr : lam 2 f ≠ ⊤) {g : ℝ → ℝ}
    (hg : BddC3 g) (i : Fin n) (x : Fin n → ℝ) (t : ℝ) :
    |iteratedDeriv 2 (g ∘ fun s => f (Function.update x i s)) t| ≤
      C₁ g * (lam 2 f).toReal := by
  have hu : ContDiff ℝ 2 (fun s => f (Function.update x i s)) :=
    (hf i x).of_le (by norm_num)
  refine abs_iteratedDeriv_two_comp_le hg hu t ?_ ?_
  · rw [← iteratedDeriv_one, iteratedDeriv_update_eq]
    exact coordDeriv_one_sq_le hr i _
  · rw [iteratedDeriv_update_eq]
    exact coordDeriv_two_le hr i _

/-- `|(g ∘ slice)'''| ≤ 6 C₂(g) λ₃(f)`: the third derivative of `g ∘ f` along a coordinate
line, at any point of any line. This is `abs_iteratedDeriv_three_comp_le` with `u` the slice
and `L = λ₃(f)`. -/
lemma abs_iteratedDeriv_three_slice_le (hf : CoordC3 f) (hr : lam 3 f ≠ ⊤) {g : ℝ → ℝ}
    (hg : BddC3 g) (i : Fin n) (x : Fin n → ℝ) (t : ℝ) :
    |iteratedDeriv 3 (g ∘ fun s => f (Function.update x i s)) t| ≤
      6 * C₂ g * (lam 3 f).toReal := by
  refine abs_iteratedDeriv_three_comp_le hg (hf i x) t ENNReal.toReal_nonneg ?_ ?_ ?_
  · rw [← iteratedDeriv_one, iteratedDeriv_update_eq]
    exact coordDeriv_one_cube_le hr i _
  · rw [iteratedDeriv_update_eq]
    exact coordDeriv_two_cube_le hr i _
  · rw [iteratedDeriv_update_eq]
    exact coordDeriv_three_le hr i _

end LamBounds

/-!
## Part 3. Taylor expansion and the remainder in one slot

First the Lagrange form of Taylor's theorem on `[0, 1]` (orders 1 and 2), rescaled to an
arbitrary displacement `a`, then applied to the slice of `g ∘ f`. The end result,
`remainder_slice_le`, is Chatterjee's truncated remainder bound
`|R(a)| ≤ C₂ λ₃ |a|³ 1{|a| ≤ K} + C₁ λ₂ a² 1{|a| > K}`.
-/

/-- On `[0, 1]`, the within-derivative of a `C³` function agrees with the ordinary derivative
(of order at most `3`). The interval has unique differentiability at each of its points, so the
two notions coincide. Used to turn Mathlib's `taylorWithinEval` into ordinary derivatives. -/
lemma iteratedDerivWithin_Icc_eq {k : ℝ → ℝ} (hk : ContDiff ℝ 3 k) {m : ℕ} (hm : m ≤ 3)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin m k (Set.Icc 0 1) y = iteratedDeriv m k y := by
  have hmm : (m : WithTop ℕ∞) ≤ 3 := by
    interval_cases m <;> norm_num
  exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    (hk.contDiffAt.of_le hmm) hy

/-- Taylor's theorem with Lagrange remainder on `[0, 1]`, order 2:
`|k(1) − k(0) − k'(0) − k''(0)/2| ≤ N/6` whenever `|k'''| ≤ N`.

Mathlib's `taylor_mean_remainder_lagrange_iteratedDeriv` gives
`k(1) − (Taylor polynomial of order 2 at 0) = k'''(c)/3!` for some `c ∈ (0, 1)`. -/
lemma taylor_two_unit {k : ℝ → ℝ} (hk : ContDiff ℝ 3 k) {N : ℝ}
    (hN : ∀ s, |iteratedDeriv 3 k s| ≤ N) :
    |k 1 - (k 0 + iteratedDeriv 1 k 0 + iteratedDeriv 2 k 0 / 2)| ≤ N / 6 := by
  have hf : ContDiffOn ℝ (((2 : ℕ) : WithTop ℕ∞) + 1) k (Set.uIcc 0 1) :=
    hk.contDiffOn.of_le (by norm_num)
  obtain ⟨c, -, hlag⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := k) (x := 1) (x₀ := 0) (n := 2) zero_ne_one hf
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [Set.uIcc_of_le zero_le_one, taylor_within_apply] at hlag
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hlag
  rw [iteratedDerivWithin_Icc_eq hk (m := 0) (by norm_num) h0,
    iteratedDerivWithin_Icc_eq hk (m := 1) (by norm_num) h0,
    iteratedDerivWithin_Icc_eq hk (m := 2) (by norm_num) h0] at hlag
  have key : k 1 - (k 0 + iteratedDeriv 1 k 0 + iteratedDeriv 2 k 0 / 2) =
      iteratedDeriv 3 k c / 6 := by
    norm_num [iteratedDeriv_zero, Nat.factorial] at hlag
    rw [iteratedDeriv_one]
    linarith
  rw [key, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  linarith [hN c]

/-- Second-order Taylor bound at `0` for any displacement `a ∈ ℝ`:
`|h(a) − h(0) − a h'(0) − (a²/2) h''(0)| ≤ |a|³ M / 6` whenever `|h'''| ≤ M`.

Apply `taylor_two_unit` to `k(τ) = h(a τ)`. By the chain rule, `k^{(m)}(τ) = a^m h^{(m)}(a τ)`
(`iteratedDeriv_comp_const_mul`), so `|k'''| ≤ |a|³ M`. Rescaling to `[0, 1]` is what removes
the need to treat positive and negative `a` separately. -/
lemma taylor_two_scaled {h : ℝ → ℝ} (hh : ContDiff ℝ 3 h) {M : ℝ}
    (hM : ∀ s, |iteratedDeriv 3 h s| ≤ M) (a : ℝ) :
    |h a - (h 0 + a * iteratedDeriv 1 h 0 + a ^ 2 / 2 * iteratedDeriv 2 h 0)| ≤
      |a| ^ 3 * M / 6 := by
  have c1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) h := hh.of_le (by norm_num)
  have c2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) h := hh.of_le (by norm_num)
  have c3 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) h := hh.of_le (by norm_num)
  have hk : ContDiff ℝ 3 (fun τ => h (a * τ)) := hh.comp (contDiff_const.mul contDiff_id)
  have e1 : ∀ s, iteratedDeriv 1 (fun x => h (a * x)) s = a ^ 1 * iteratedDeriv 1 h (a * s) :=
    fun s => congrFun (iteratedDeriv_comp_const_mul c1 a) s
  have e2 : ∀ s, iteratedDeriv 2 (fun x => h (a * x)) s = a ^ 2 * iteratedDeriv 2 h (a * s) :=
    fun s => congrFun (iteratedDeriv_comp_const_mul c2 a) s
  have e3 : ∀ s, iteratedDeriv 3 (fun x => h (a * x)) s = a ^ 3 * iteratedDeriv 3 h (a * s) :=
    fun s => congrFun (iteratedDeriv_comp_const_mul c3 a) s
  have T := taylor_two_unit hk (N := |a| ^ 3 * M) (fun s => by
    rw [e3 s, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity))
  rw [e1 0, e2 0] at T
  simp only [mul_one, mul_zero, pow_one] at T
  refine le_trans (le_of_eq ?_) T
  congr 1
  ring

/-- Chatterjee's Taylor step in one slot. Expanding `g ∘ f` in coordinate `i` around `x`, to
second order at the point with `0` in slot `i`, leaves a remainder of at most
`|a|³ · C₂(g) · λ₃(f)` at displacement `a`.

This is `taylor_two_scaled` for `h = g ∘ slice`, with `M = 6 C₂(g) λ₃(f)` from
`abs_iteratedDeriv_three_slice_le`; the factor `6` cancels the `1/6` of Taylor's formula. -/
lemma taylor_remainder_slice {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f)
    (hr : lam 3 f ≠ ⊤) (hg : BddC3 g) (i : Fin n) (x : Fin n → ℝ) (a : ℝ) :
    |g (f (Function.update x i a)) -
        (g (f (Function.update x i 0))
          + a * iteratedDeriv 1 (g ∘ fun s => f (Function.update x i s)) 0
          + a ^ 2 / 2 * iteratedDeriv 2 (g ∘ fun s => f (Function.update x i s)) 0)| ≤
      |a| ^ 3 * (C₂ g * (lam 3 f).toReal) := by
  have hh : ContDiff ℝ 3 (g ∘ fun s => f (Function.update x i s)) :=
    hg.contDiff.comp (hf i x)
  have T := taylor_two_scaled hh (M := 6 * C₂ g * (lam 3 f).toReal)
    (fun s => abs_iteratedDeriv_three_slice_le hf hr hg i x s) a
  have hb : |a| ^ 3 * (6 * C₂ g * (lam 3 f).toReal) / 6 =
      |a| ^ 3 * (C₂ g * (lam 3 f).toReal) := by ring
  rw [hb] at T
  exact T

/-- Taylor's theorem with Lagrange remainder on `[0, 1]`, order 1:
`|k(1) − k(0) − k'(0)| ≤ N/2` whenever `|k''| ≤ N`. -/
lemma taylor_one_unit {k : ℝ → ℝ} (hk : ContDiff ℝ 3 k) {N : ℝ}
    (hN : ∀ s, |iteratedDeriv 2 k s| ≤ N) :
    |k 1 - (k 0 + iteratedDeriv 1 k 0)| ≤ N / 2 := by
  have hf : ContDiffOn ℝ (((1 : ℕ) : WithTop ℕ∞) + 1) k (Set.uIcc 0 1) :=
    hk.contDiffOn.of_le (by norm_num)
  obtain ⟨c, -, hlag⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := k) (x := 1) (x₀ := 0) (n := 1) zero_ne_one hf
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [Set.uIcc_of_le zero_le_one, taylor_within_apply] at hlag
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hlag
  rw [iteratedDerivWithin_Icc_eq hk (m := 0) (by norm_num) h0,
    iteratedDerivWithin_Icc_eq hk (m := 1) (by norm_num) h0] at hlag
  have key : k 1 - (k 0 + iteratedDeriv 1 k 0) = iteratedDeriv 2 k c / 2 := by
    norm_num [iteratedDeriv_zero, Nat.factorial] at hlag
    rw [iteratedDeriv_one]
    linarith
  rw [key, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [hN c]

/-- First-order Taylor bound at `0` for any displacement `a ∈ ℝ`:
`|h(a) − h(0) − a h'(0)| ≤ a² M / 2` whenever `|h''| ≤ M`. Rescaling argument as in
`taylor_two_scaled`. -/
lemma taylor_one_scaled {h : ℝ → ℝ} (hh : ContDiff ℝ 3 h) {M : ℝ}
    (hM : ∀ s, |iteratedDeriv 2 h s| ≤ M) (a : ℝ) :
    |h a - (h 0 + a * iteratedDeriv 1 h 0)| ≤ a ^ 2 * M / 2 := by
  have c1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) h := hh.of_le (by norm_num)
  have c2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) h := hh.of_le (by norm_num)
  have hk : ContDiff ℝ 3 (fun τ => h (a * τ)) := hh.comp (contDiff_const.mul contDiff_id)
  have e1 : ∀ s, iteratedDeriv 1 (fun x => h (a * x)) s = a ^ 1 * iteratedDeriv 1 h (a * s) :=
    fun s => congrFun (iteratedDeriv_comp_const_mul c1 a) s
  have e2 : ∀ s, iteratedDeriv 2 (fun x => h (a * x)) s = a ^ 2 * iteratedDeriv 2 h (a * s) :=
    fun s => congrFun (iteratedDeriv_comp_const_mul c2 a) s
  have T := taylor_one_unit hk (N := a ^ 2 * M) (fun s => by
    rw [e2 s, abs_mul, abs_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (sq_nonneg a))
  rw [e1 0] at T
  simp only [mul_one, mul_zero, pow_one] at T
  exact T

/-- Chatterjee's truncated remainder bound in one slot (pointwise, no probability):

`|g(f(x with a in slot i)) − [g(f(x with 0 in slot i)) + a·D₁ + (a²/2)·D₂]|`
`  ≤ C₂(g) λ₃(f) |a|³ · 1{|a| ≤ K} + C₁(g) λ₂(f) a² · 1{|a| > K}`,

where `D₁`, `D₂` are the first and second derivatives at `0` of `s ↦ g (f (x with s in slot i))`.

* If `|a| ≤ K`, use the second-order bound `taylor_remainder_slice`.
* If `|a| > K`, use the first-order bound `|h(a) − h(0) − a h'(0)| ≤ a² C₁λ₂ / 2` and the
  estimate `|(a²/2) D₂| ≤ a² C₁λ₂ / 2`; the two halves add up to `C₁(g) λ₂(f) a²`. -/
lemma remainder_slice_le {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f)
    (hr₂ : lam 2 f ≠ ⊤) (hr₃ : lam 3 f ≠ ⊤) (hg : BddC3 g) (i : Fin n)
    (x : Fin n → ℝ) (a K : ℝ) :
    |g (f (Function.update x i a)) -
        (g (f (Function.update x i 0))
          + a * iteratedDeriv 1 (g ∘ fun s => f (Function.update x i s)) 0
          + a ^ 2 / 2 * iteratedDeriv 2 (g ∘ fun s => f (Function.update x i s)) 0)| ≤
      C₂ g * (lam 3 f).toReal * (if |a| ≤ K then |a| ^ 3 else 0)
        + C₁ g * (lam 2 f).toReal * (if K < |a| then a ^ 2 else 0) := by
  by_cases hK : |a| ≤ K
  · rw [ite_eq_left hK, ite_eq_right (not_lt.2 hK)]
    linarith [taylor_remainder_slice hf hr₃ hg i x a]
  · rw [ite_eq_right hK, ite_eq_left (not_le.1 hK)]
    have hh : ContDiff ℝ 3 (g ∘ fun s => f (Function.update x i s)) :=
      hg.contDiff.comp (hf i x)
    have m2 : ∀ s, |iteratedDeriv 2 (g ∘ fun s => f (Function.update x i s)) s| ≤
        C₁ g * (lam 2 f).toReal := fun s => abs_iteratedDeriv_two_slice_le hf hr₂ hg i x s
    have T1 : |g (f (Function.update x i a)) -
        (g (f (Function.update x i 0))
          + a * iteratedDeriv 1 (g ∘ fun s => f (Function.update x i s)) 0)| ≤
        a ^ 2 * (C₁ g * (lam 2 f).toReal) / 2 := taylor_one_scaled hh m2 a
    have hD := abs_le.1 (m2 0)
    have p1 := mul_le_mul_of_nonneg_left hD.2 (by positivity : (0 : ℝ) ≤ a ^ 2 / 2)
    have p2 := mul_le_mul_of_nonneg_left hD.1 (by positivity : (0 : ℝ) ≤ a ^ 2 / 2)
    obtain ⟨t1, t2⟩ := abs_le.1 T1
    rw [abs_le]
    constructor <;> nlinarith [p1, p2, t1, t2]

/-- `|(g ∘ slice)'| ≤ ‖g'‖ (1 + λ₂(f))`: the first derivative of `g ∘ f` along a coordinate line
is uniformly bounded.

The constant is not sharp: from `|u'|² ≤ λ₂` we only use `|u'| ≤ 1 + λ₂`. It is enough for
integrability of the first Taylor term in `slot_expansion`. -/
lemma abs_iteratedDeriv_one_slice_le {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f)
    (hr₂ : lam 2 f ≠ ⊤) (hg : BddC3 g) (i : Fin n) (x : Fin n → ℝ) (t : ℝ) :
    |iteratedDeriv 1 (g ∘ fun s => f (Function.update x i s)) t| ≤
      supDeriv 1 g * (1 + (lam 2 f).toReal) := by
  have hgd : Differentiable ℝ g := hg.contDiff.differentiable (by norm_num)
  have hud : Differentiable ℝ (fun s => f (Function.update x i s)) :=
    (hf i x).differentiable (by norm_num)
  have e : coordDeriv 1 f i (Function.update x i t) =
      deriv (fun s => f (Function.update x i s)) t := by
    rw [← iteratedDeriv_update_eq, iteratedDeriv_one]
  have hsq : |deriv (fun s => f (Function.update x i s)) t| ^ 2 ≤ (lam 2 f).toReal := by
    rw [← e]; exact coordDeriv_one_sq_le hr₂ i _
  have hle : |deriv (fun s => f (Function.update x i s)) t| ≤ 1 + (lam 2 f).toReal := by
    nlinarith [sq_nonneg (|deriv (fun s => f (Function.update x i s)) t| - 1)]
  have A : |deriv g (f (Function.update x i t))| ≤ supDeriv 1 g := by
    simpa [iteratedDeriv_one] using
      abs_iteratedDeriv_le_supDeriv hg (k := 1) le_rfl (by norm_num)
        (f (Function.update x i t))
  rw [iteratedDeriv_one, deriv_comp t (hgd _) (hud t), abs_mul]
  exact mul_le_mul A hle (abs_nonneg _) ((abs_nonneg _).trans A)

/-!
## Part 4. Expectation over one slot (measure theory)

Here the random variables enter. `slot_expansion` writes `E g(f(W with ξ in slot i))` as the value
at `ξ = 0`, plus the first and second Taylor terms, plus the expected remainder, and uses
independence of `ξ` and the base point `W` to factor the two Taylor terms into products of
expectations. The auxiliary lemmas prove that the slice derivatives are measurable and bounded
so that every integral that occurs exists.
-/

/-- The `k`-th derivative at `0` of `g` composed with the `i`-th coordinate slice of `f` through
`w`: `sliceD k f g i w = (d/ds)^k g (f (update w i s)) |_{s=0}`.

These are the coefficients in the Taylor expansion in slot `i` around the base point
`update w i 0`. They depend on `w` only through the coordinates other than `i`. -/
noncomputable def sliceD (k : ℕ) (f : (Fin n → ℝ) → ℝ) (g : ℝ → ℝ) (i : Fin n)
    (w : Fin n → ℝ) : ℝ :=
  iteratedDeriv k (g ∘ fun s => f (Function.update w i s)) 0

/-- If `W` and `ξ` are measurable, then so is the random vector obtained from `W` by replacing
its `i`-th entry with `ξ`. -/
lemma measurable_update_fun {Ω : Type*} [MeasurableSpace Ω] {W : Ω → Fin n → ℝ}
    (hW : Measurable W) {ξ : Ω → ℝ} (hξ : Measurable ξ) (i : Fin n) :
    Measurable fun ω => Function.update (W ω) i (ξ ω) := by
  rw [measurable_pi_iff]
  intro j
  by_cases h : j = i
  · subst h
    simpa using hξ
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply j).comp hW

/-- One-slot expansion. Let `W` be a random base point and `ξ` a real random variable with a
finite second moment, independent of `W`. Then, with `D₁ = sliceD 1`, `D₂ = sliceD 2`,

`E g(f(W with ξ in slot i)) = E g(f(W with 0 in slot i))`
`    + E[ξ] · E[D₁(W)] + (E[ξ²]/2) · E[D₂(W)] + E[remainder]`,

where `remainder = g(f(W with ξ in slot i)) − [g(f(W with 0 in slot i)) + ξ D₁(W) +
(ξ²/2) D₂(W)]`.

Proof: this is linearity of the integral once each piece is known to be integrable, plus
`E[ξ · D₁(W)] = E[ξ] · E[D₁(W)]` and `E[(ξ²/2) · D₂(W)] = E[ξ²/2] · E[D₂(W)]`, which hold by
independence. Integrability: `g` is bounded and `f` measurable for the first two terms; `D₁(W)`
and `D₂(W)` are bounded (`abs_iteratedDeriv_one_slice_le`, `abs_iteratedDeriv_two_slice_le`)
and `ξ`, `ξ²` are integrable. -/
lemma slot_expansion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f)
    (hr₂ : lam 2 f ≠ ⊤) (hg : BddC3 g) {Mg : ℝ} (hgb : ∀ x, |g x| ≤ Mg)
    (hfm : Measurable f) (i : Fin n) {W : Ω → Fin n → ℝ} (hW : Measurable W)
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (hξ2 : MemLp ξ 2 P) (hind : IndepFun ξ W P)
    (hD1 : Measurable (sliceD 1 f g i)) (hD2 : Measurable (sliceD 2 f g i)) :
    ∫ ω, g (f (Function.update (W ω) i (ξ ω))) ∂P =
      ∫ ω, g (f (Function.update (W ω) i 0)) ∂P
        + (∫ ω, ξ ω ∂P) * ∫ ω, sliceD 1 f g i (W ω) ∂P
        + (∫ ω, ξ ω ^ 2 ∂P) / 2 * ∫ ω, sliceD 2 f g i (W ω) ∂P
        + ∫ ω, (g (f (Function.update (W ω) i (ξ ω))) -
            (g (f (Function.update (W ω) i 0)) + ξ ω * sliceD 1 f g i (W ω)
              + ξ ω ^ 2 / 2 * sliceD 2 f g i (W ω))) ∂P := by
  have hgm : Measurable g := hg.contDiff.continuous.measurable
  have hupd : Measurable fun ω => Function.update (W ω) i (ξ ω) :=
    measurable_update_fun hW hξ i
  have hupd0 : Measurable fun ω => Function.update (W ω) i (0 : ℝ) :=
    measurable_update_fun hW measurable_const i
  have hAm : Measurable fun ω => g (f (Function.update (W ω) i (ξ ω))) :=
    hgm.comp (hfm.comp hupd)
  have hBm : Measurable fun ω => g (f (Function.update (W ω) i 0)) :=
    hgm.comp (hfm.comp hupd0)
  have hAi : Integrable (fun ω => g (f (Function.update (W ω) i (ξ ω)))) P :=
    Integrable.of_bound hAm.aestronglyMeasurable Mg (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hgb _)
  have hBi : Integrable (fun ω => g (f (Function.update (W ω) i 0))) P :=
    Integrable.of_bound hBm.aestronglyMeasurable Mg (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hgb _)
  have hd1m : Measurable fun ω => sliceD 1 f g i (W ω) := hD1.comp hW
  have hd2m : Measurable fun ω => sliceD 2 f g i (W ω) := hD2.comp hW
  have hd1i : Integrable (fun ω => sliceD 1 f g i (W ω)) P :=
    Integrable.of_bound hd1m.aestronglyMeasurable (supDeriv 1 g * (1 + (lam 2 f).toReal))
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact abs_iteratedDeriv_one_slice_le hf hr₂ hg i (W ω) 0)
  have hd2i : Integrable (fun ω => sliceD 2 f g i (W ω)) P :=
    Integrable.of_bound hd2m.aestronglyMeasurable (C₁ g * (lam 2 f).toReal)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact abs_iteratedDeriv_two_slice_le hf hr₂ hg i (W ω) 0)
  have hξi : Integrable ξ P := hξ2.integrable one_le_two
  have hξh : Integrable (fun ω => ξ ω ^ 2 / 2) P := hξ2.integrable_sq.div_const 2
  have hind1 : IndepFun ξ (fun ω => sliceD 1 f g i (W ω)) P :=
    hind.comp measurable_id hD1
  have hind2 : IndepFun (fun ω => ξ ω ^ 2 / 2) (fun ω => sliceD 2 f g i (W ω)) P :=
    hind.comp (φ := fun x : ℝ => x ^ 2 / 2) (by fun_prop) hD2
  have hpi1 : Integrable (fun ω => ξ ω * sliceD 1 f g i (W ω)) P :=
    hind1.integrable_mul hξi hd1i
  have hpi2 : Integrable (fun ω => ξ ω ^ 2 / 2 * sliceD 2 f g i (W ω)) P :=
    hind2.integrable_mul hξh hd2i
  have hp1 : ∫ ω, ξ ω * sliceD 1 f g i (W ω) ∂P =
      (∫ ω, ξ ω ∂P) * ∫ ω, sliceD 1 f g i (W ω) ∂P :=
    IndepFun.integral_fun_mul_eq_mul_integral hind1 hξi.aestronglyMeasurable
      hd1i.aestronglyMeasurable
  have hp2 : ∫ ω, ξ ω ^ 2 / 2 * sliceD 2 f g i (W ω) ∂P =
      (∫ ω, ξ ω ^ 2 / 2 ∂P) * ∫ ω, sliceD 2 f g i (W ω) ∂P :=
    IndepFun.integral_fun_mul_eq_mul_integral hind2 hξh.aestronglyMeasurable
      hd2i.aestronglyMeasurable
  have hS1 : Integrable (fun ω => g (f (Function.update (W ω) i 0))
      + ξ ω * sliceD 1 f g i (W ω)) P := hBi.add hpi1
  have hS : Integrable (fun ω => g (f (Function.update (W ω) i 0))
      + ξ ω * sliceD 1 f g i (W ω) + ξ ω ^ 2 / 2 * sliceD 2 f g i (W ω)) P :=
    hS1.add hpi2
  rw [integral_sub hAi hS, integral_add hS1 hpi2, integral_add hBi hpi1, hp1, hp2,
    integral_div]
  ring

/-- Chain rule for `sliceD 1`: `D₁(w) = g'(f(w₀)) · ∂ᵢ f(w₀)` where `w₀ = update w i 0`. -/
lemma sliceD_one_eq {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f) (hg : BddC3 g)
    (i : Fin n) (w : Fin n → ℝ) :
    sliceD 1 f g i w = deriv g (f (Function.update w i 0)) *
      coordDeriv 1 f i (Function.update w i 0) := by
  have hgd : Differentiable ℝ g := hg.contDiff.differentiable (by norm_num)
  have hud : Differentiable ℝ (fun s => f (Function.update w i s)) :=
    (hf i w).differentiable (by norm_num)
  have e : coordDeriv 1 f i (Function.update w i 0) =
      deriv (fun s => f (Function.update w i s)) 0 := by
    rw [← iteratedDeriv_one]
    exact (iteratedDeriv_update_eq 1 f i w 0).symm
  unfold sliceD
  rw [iteratedDeriv_one, deriv_comp 0 (hgd _) (hud 0), e]

/-- Chain rule for `sliceD 2`:
`D₂(w) = g''(f(w₀)) · (∂ᵢ f(w₀))² + g'(f(w₀)) · ∂ᵢ² f(w₀)` where `w₀ = update w i 0`. -/
lemma sliceD_two_eq {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f) (hg : BddC3 g)
    (i : Fin n) (w : Fin n → ℝ) :
    sliceD 2 f g i w = iteratedDeriv 2 g (f (Function.update w i 0)) *
        coordDeriv 1 f i (Function.update w i 0) ^ 2 +
      deriv g (f (Function.update w i 0)) * coordDeriv 2 f i (Function.update w i 0) := by
  have e1 : coordDeriv 1 f i (Function.update w i 0) =
      deriv (fun s => f (Function.update w i s)) 0 := by
    rw [← iteratedDeriv_one]
    exact (iteratedDeriv_update_eq 1 f i w 0).symm
  have e2 : coordDeriv 2 f i (Function.update w i 0) =
      iteratedDeriv 2 (fun s => f (Function.update w i s)) 0 :=
    (iteratedDeriv_update_eq 2 f i w 0).symm
  unfold sliceD
  rw [iteratedDeriv_two_comp (hg.contDiff.of_le (by norm_num)) ((hf i w).of_le (by norm_num)) 0,
    e1, e2]

/-- The slice derivatives `sliceD 1` and `sliceD 2` are measurable, provided `f` and its first
two coordinate derivatives are. By `sliceD_one_eq` and `sliceD_two_eq` they are built from
`deriv g`, `iteratedDeriv 2 g` (continuous), `f`, `∂ᵢ f`, `∂ᵢ² f` and the measurable map
`w ↦ update w i 0`. -/
lemma measurable_sliceD {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f) (hg : BddC3 g)
    (hfm : Measurable f) (i : Fin n) (hd1 : Measurable (coordDeriv 1 f i))
    (hd2 : Measurable (coordDeriv 2 f i)) :
    Measurable (sliceD 1 f g i) ∧ Measurable (sliceD 2 f g i) := by
  have hup : Measurable fun w : Fin n → ℝ => Function.update w i (0 : ℝ) :=
    measurable_update_fun (W := fun w => w) (ξ := fun _ => (0 : ℝ)) measurable_id
      measurable_const i
  have hgc : Continuous (deriv g) := by
    have := hg.contDiff.continuous_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using this
  have hg2c : Continuous (iteratedDeriv 2 g) :=
    hg.contDiff.continuous_iteratedDeriv 2 (by norm_num)
  have hfu : Measurable fun w : Fin n → ℝ => f (Function.update w i 0) := hfm.comp hup
  constructor
  · have h : sliceD 1 f g i = fun w => deriv g (f (Function.update w i 0)) *
        coordDeriv 1 f i (Function.update w i 0) := funext (sliceD_one_eq hf hg i)
    rw [h]
    exact (hgc.measurable.comp hfu).mul (hd1.comp hup)
  · have h : sliceD 2 f g i = fun w => iteratedDeriv 2 g (f (Function.update w i 0)) *
          coordDeriv 1 f i (Function.update w i 0) ^ 2 +
        deriv g (f (Function.update w i 0)) * coordDeriv 2 f i (Function.update w i 0) :=
      funext (sliceD_two_eq hf hg i)
    rw [h]
    exact ((hg2c.measurable.comp hfu).mul ((hd1.comp hup).pow_const 2)).add
      ((hgc.measurable.comp hfu).mul (hd2.comp hup))

/-!
## Part 5. Swapping one coordinate

`slot_swap` subtracts the expansions of `slot_expansion` for two variables `X` and `Y` that are
both independent of `W` and have equal first and second moments. The first two Taylor terms
cancel and the difference is bounded by the integrated remainders.
-/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `E(Z²; |Z| > K)`: the second moment of `Z` on the event that it exceeds `K` in absolute
value. -/
noncomputable def tailSq (P : Measure Ω) (Z : Ω → ℝ) (K : ℝ) : ℝ :=
  ∫ ω in {ω | K < |Z ω|}, (Z ω) ^ 2 ∂P

/-- `E(|Z|³; |Z| ≤ K)`: the truncated third absolute moment of `Z`. -/
noncomputable def truncCube (P : Measure Ω) (Z : Ω → ℝ) (K : ℝ) : ℝ :=
  ∫ ω in {ω | |Z ω| ≤ K}, |Z ω| ^ 3 ∂P

/-- The second-order Taylor remainder in slot `i` at displacement `a` and base point `w`:
`g(f(w with a in slot i)) − [g(f(w with 0 in slot i)) + a·D₁(w) + (a²/2)·D₂(w)]`. -/
noncomputable def slotRem (f : (Fin n → ℝ) → ℝ) (g : ℝ → ℝ) (i : Fin n) (w : Fin n → ℝ)
    (a : ℝ) : ℝ :=
  g (f (Function.update w i a)) -
    (g (f (Function.update w i 0)) + a * sliceD 1 f g i w + a ^ 2 / 2 * sliceD 2 f g i w)

/-- `E[|Z|³ · 1{|Z| ≤ K}] = truncCube P Z K`: an integral of an `if` equals the set integral. -/
lemma integral_ite_trunc {P : Measure Ω} {Z : Ω → ℝ} (hZ : Measurable Z) (K : ℝ) :
    ∫ ω, (if |Z ω| ≤ K then |Z ω| ^ 3 else 0) ∂P = truncCube P Z K := by
  have hs : MeasurableSet {ω | |Z ω| ≤ K} :=
    measurableSet_le (continuous_abs.measurable.comp hZ) measurable_const
  unfold truncCube
  rw [← integral_indicator hs]
  congr 1

/-- `E[Z² · 1{|Z| > K}] = tailSq P Z K`: an integral of an `if` equals the set integral. -/
lemma integral_ite_tail {P : Measure Ω} {Z : Ω → ℝ} (hZ : Measurable Z) (K : ℝ) :
    ∫ ω, (if K < |Z ω| then Z ω ^ 2 else 0) ∂P = tailSq P Z K := by
  have hs : MeasurableSet {ω | K < |Z ω|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hZ)
  unfold tailSq
  rw [← integral_indicator hs]
  congr 1

/-- The expected remainder of one slot is bounded by the truncated moments:
`|E[slotRem(W, Z)]| ≤ C₂(g) λ₃(f) · truncCube P Z K + C₁(g) λ₂(f) · tailSq P Z K`.

Integrate the pointwise bound `remainder_slice_le` over `a = Z ω`. No independence is used. -/
lemma abs_integral_slotRem_le {P : Measure Ω} [IsProbabilityMeasure P]
    {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f) (hr₂ : lam 2 f ≠ ⊤)
    (hr₃ : lam 3 f ≠ ⊤) (hg : BddC3 g) (i : Fin n) (W : Ω → Fin n → ℝ)
    {Z : Ω → ℝ} (hZ : Measurable Z) (hZ2 : MemLp Z 2 P) (K : ℝ) :
    |∫ ω, slotRem f g i (W ω) (Z ω) ∂P| ≤
      C₂ g * (lam 3 f).toReal * truncCube P Z K + C₁ g * (lam 2 f).toReal * tailSq P Z K := by
  have hZa : Measurable fun ω => |Z ω| := continuous_abs.measurable.comp hZ
  have hT : Integrable (fun ω => if |Z ω| ≤ K then |Z ω| ^ 3 else 0) P := by
    refine Integrable.of_bound (Measurable.ite (measurableSet_le hZa measurable_const)
      (hZa.pow_const 3) measurable_const).aestronglyMeasurable (|K| ^ 3)
      (ae_of_all _ fun ω => ?_)
    by_cases h : |Z ω| ≤ K
    · simp only [h, ↓reduceIte]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (h.trans (le_abs_self K)) 3
    · simp only [h, ↓reduceIte, norm_zero]
      positivity
  have hQ : Integrable (fun ω => if K < |Z ω| then Z ω ^ 2 else 0) P := by
    refine Integrable.mono' hZ2.integrable_sq (Measurable.ite
      (measurableSet_lt measurable_const hZa) (hZ.pow_const 2)
      measurable_const).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    by_cases h : K < |Z ω|
    · simp only [h, ↓reduceIte]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    · simp only [h, ↓reduceIte, norm_zero]
      positivity
  have hbnd : Integrable (fun ω => C₂ g * (lam 3 f).toReal * (if |Z ω| ≤ K then |Z ω| ^ 3 else 0)
      + C₁ g * (lam 2 f).toReal * (if K < |Z ω| then Z ω ^ 2 else 0)) P :=
    (hT.const_mul _).add (hQ.const_mul _)
  calc |∫ ω, slotRem f g i (W ω) (Z ω) ∂P| = ‖∫ ω, slotRem f g i (W ω) (Z ω) ∂P‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, (C₂ g * (lam 3 f).toReal * (if |Z ω| ≤ K then |Z ω| ^ 3 else 0)
          + C₁ g * (lam 2 f).toReal * (if K < |Z ω| then Z ω ^ 2 else 0)) ∂P :=
        norm_integral_le_of_norm_le hbnd (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]
          exact remainder_slice_le hf hr₂ hr₃ hg i (W ω) (Z ω) K)
    _ = C₂ g * (lam 3 f).toReal * truncCube P Z K + C₁ g * (lam 2 f).toReal * tailSq P Z K := by
        rw [integral_add (hT.const_mul _) (hQ.const_mul _), integral_const_mul,
          integral_const_mul, integral_ite_trunc hZ, integral_ite_tail hZ]

/-- Swapping one coordinate. Suppose `X` and `Y` are both independent of the base point `W`,
have finite second moments, and have equal first and second moments. Then

`|E g(f(W with X in slot i)) − E g(f(W with Y in slot i))|`
`  ≤ C₁(g) λ₂(f) (tailSq X + tailSq Y) + C₂(g) λ₃(f) (truncCube X + truncCube Y)`.

Proof: apply `slot_expansion` to `X` and to `Y`. The terms `E g(f(W with 0 in slot i))`,
`E[ξ] E[D₁(W)]` and `(E[ξ²]/2) E[D₂(W)]` coincide for the two variables and cancel, leaving the
difference of the expected remainders, each bounded by `abs_integral_slotRem_le`. -/
lemma slot_swap {P : Measure Ω} [IsProbabilityMeasure P]
    {f : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (hf : CoordC3 f) (hr₂ : lam 2 f ≠ ⊤)
    (hr₃ : lam 3 f ≠ ⊤) (hg : BddC3 g) {Mg : ℝ} (hgb : ∀ x, |g x| ≤ Mg)
    (hfm : Measurable f) (i : Fin n) {W : Ω → Fin n → ℝ} (hW : Measurable W)
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hXW : IndepFun X W P) (hYW : IndepFun Y W P)
    (hmean : ∫ ω, X ω ∂P = ∫ ω, Y ω ∂P) (hsq : ∫ ω, X ω ^ 2 ∂P = ∫ ω, Y ω ^ 2 ∂P)
    (hD1 : Measurable (sliceD 1 f g i)) (hD2 : Measurable (sliceD 2 f g i)) (K : ℝ) :
    |(∫ ω, g (f (Function.update (W ω) i (X ω))) ∂P) -
        ∫ ω, g (f (Function.update (W ω) i (Y ω))) ∂P| ≤
      C₁ g * (lam 2 f).toReal * (tailSq P X K + tailSq P Y K) +
        C₂ g * (lam 3 f).toReal * (truncCube P X K + truncCube P Y K) := by
  have eX := slot_expansion hf hr₂ hg hgb hfm i hW hX hX2 hXW hD1 hD2
  have eY := slot_expansion hf hr₂ hg hgb hfm i hW hY hY2 hYW hD1 hD2
  have key : (∫ ω, g (f (Function.update (W ω) i (X ω))) ∂P) -
        ∫ ω, g (f (Function.update (W ω) i (Y ω))) ∂P =
      (∫ ω, slotRem f g i (W ω) (X ω) ∂P) - ∫ ω, slotRem f g i (W ω) (Y ω) ∂P := by
    simp only [slotRem]
    rw [eX, eY, hmean, hsq]
    ring
  have hx := abs_le.1 (abs_integral_slotRem_le hf hr₂ hr₃ hg i W hX hX2 K)
  have hy := abs_le.1 (abs_integral_slotRem_le hf hr₂ hr₃ hg i W hY hY2 K)
  rw [key, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-!
## Part 6. Hybrids and independence of the base point

`hyb X Y k` is the vector with `X` in slots `< k` and `Y` in the others. Going from `hyb X Y k`
to `hyb X Y (k + 1)` changes exactly slot `k`, and both vectors are obtained from the base point
`baseVec X Y k` by writing a value into that slot. Joint independence of `X` and `Y` gives
independence of the swapped variable from the base point.
-/

/-- Base point for slot `k`: `X j` in slots `j < k`, `Y j` in slots `j > k`, and `0` in slot `k`. -/
def baseVec (X Y : Fin n → Ω → ℝ) (k : ℕ) (ω : Ω) : Fin n → ℝ := fun j =>
  if j.val < k then X j ω else if k < j.val then Y j ω else 0

/-- The hybrid vector `Z_k = (X_1, …, X_k, Y_{k+1}, …, Y_n)`: `X j` in the slots `j < k`
and `Y j` in the remaining slots. Slots are indexed from `0`, so `hyb X Y 0 = Y` and
`hyb X Y n = X`. -/
def hyb (X Y : Fin n → Ω → ℝ) (k : ℕ) (ω : Ω) : Fin n → ℝ := fun j =>
  if j.val < k then X j ω else Y j ω

omit [MeasurableSpace Ω] in
/-- `Z_{k+1}` is the base point of slot `k` with `X_k` written into slot `k`. -/
lemma hyb_succ_eq (X Y : Fin n → Ω → ℝ) {k : ℕ} (i : Fin n) (hik : i.val = k) (ω : Ω) :
    hyb X Y (k + 1) ω = Function.update (baseVec X Y k ω) i (X i ω) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [hyb, hik]
  · have hne : j.val ≠ k := fun hv => h (Fin.ext (hv.trans hik.symm))
    simp only [hyb, baseVec, Function.update_of_ne h]
    split_ifs <;> first | rfl | omega

omit [MeasurableSpace Ω] in
/-- `Z_k` is the base point of slot `k` with `Y_k` written into slot `k`. -/
lemma hyb_eq (X Y : Fin n → Ω → ℝ) {k : ℕ} (i : Fin n) (hik : i.val = k) (ω : Ω) :
    hyb X Y k ω = Function.update (baseVec X Y k ω) i (Y i ω) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [hyb, hik]
  · have hne : j.val ≠ k := fun hv => h (Fin.ext (hv.trans hik.symm))
    simp only [hyb, baseVec, Function.update_of_ne h]
    split_ifs <;> first | rfl | omega

/-- In slot `k`, the variable `X_k` (or `Y_k`) is independent of the base point.

If the `2n` variables `X_1, …, X_n, Y_1, …, Y_n` are jointly independent, then the variable
`Sum.elim X Y s` with `s = inl i` or `inr i`, `i.val = k`, is independent of the family
indexed by the other coordinates that enter the base point: `X_j` for `j < k` and `Y_j` for
`j > k`. These index sets are disjoint, and the base point is a measurable function of the
second family. -/
lemma indep_slot {P : Measure Ω} {X Y : Fin n → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hYm : ∀ i, Measurable (Y i)) (hind : iIndepFun (Sum.elim X Y) P) {k : ℕ} (i : Fin n)
    (hik : i.val = k) (s : Fin n ⊕ Fin n) (hs : s = Sum.inl i ∨ s = Sum.inr i) :
    IndepFun (Sum.elim X Y s) (fun ω => baseVec X Y k ω) P := by
  classical
  let S : Finset (Fin n ⊕ Fin n) := {s}
  let T : Finset (Fin n ⊕ Fin n) :=
    Finset.univ.filter fun s => Sum.elim (fun j : Fin n => j.val < k) (fun j => k < j.val) s
  have hdisj : Disjoint S T := by
    change Disjoint {s} T
    rw [Finset.disjoint_singleton_left]
    rcases hs with h | h <;> simp [T, h, hik]
  have hmeas : ∀ s, Measurable (Sum.elim X Y s) := fun s => by
    cases s with
    | inl j => exact hXm j
    | inr j => exact hYm j
  have h := hind.indepFun_finset S T hdisj hmeas
  let ψ : (T → ℝ) → (Fin n → ℝ) := fun v j =>
    if hj : j.val < k then v ⟨Sum.inl j, by simp [T, hj]⟩
    else if hj' : k < j.val then v ⟨Sum.inr j, by simp [T, hj']⟩ else 0
  have hψ : Measurable ψ := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j.val < k
    · simp only [ψ, dite_eq_left hj]
      exact measurable_pi_apply _
    · by_cases hj' : k < j.val
      · simp only [ψ, dite_eq_right hj, dite_eq_left hj']
        exact measurable_pi_apply _
      · simp only [ψ, dite_eq_right hj, dite_eq_right hj']
        exact measurable_const
  have hφ : Measurable fun v : S → ℝ => v ⟨s, by simp [S]⟩ := measurable_pi_apply _
  have hW : (fun ω => baseVec X Y k ω) = fun ω => ψ (fun s : T => Sum.elim X Y s ω) := by
    funext ω j
    by_cases hj : j.val < k
    · simp [ψ, baseVec, hj]
    · by_cases hj' : k < j.val
      · simp [ψ, baseVec, hj, hj']
      · simp [ψ, baseVec, hj, hj']
  rw [hW]
  exact h.comp hφ hψ

/-- Telescoping: if consecutive differences of `a` are bounded by `B`, then so is the total:
`|a N − a 0| ≤ ∑_{k < N} B k`. -/
lemma abs_sub_le_sum_range (a B : ℕ → ℝ) (N : ℕ) (h : ∀ k < N, |a (k + 1) - a k| ≤ B k) :
    |a N - a 0| ≤ ∑ k ∈ Finset.range N, B k := by
  rw [← Finset.sum_range_sub a N]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun k hk => h k (Finset.mem_range.1 hk))

/-!
## Part 7. The theorem

Telescoping over the hybrids and applying `slot_swap` in each slot.
-/

/-- **Chatterjee's Lindeberg swap theorem** (arXiv:math/0508213, Theorem 1.1).

Let `X = (X_1, …, X_n)` and `Y = (Y_1, …, Y_n)` be random vectors whose `2n` coordinates are
jointly independent (`hind`), with finite second moments (`hX2`, `hY2`) and
`E Xᵢ = E Yᵢ`, `E Xᵢ² = E Yᵢ²` (`hmean`, `hsq`). Let `f : ℝⁿ → ℝ` be `C³` along coordinate
lines (`hf`) with `λ₂(f), λ₃(f) < ∞` (`hf₂`, `hf₃`), measurable together with its first two
coordinate derivatives (`hfm`, `hd1`, `hd2`), and let `g` be bounded (`hgb`) and `BddC3`.
Then for every `K`,

`|E g(f(X)) − E g(f(Y))|
   ≤ C₁(g) λ₂(f) ∑ᵢ (E(Xᵢ²; |Xᵢ| > K) + E(Yᵢ²; |Yᵢ| > K))
   + C₂(g) λ₃(f) ∑ᵢ (E(|Xᵢ|³; |Xᵢ| ≤ K) + E(|Yᵢ|³; |Yᵢ| ≤ K))`.

Proof: the hybrids `Z_k = hyb X Y k` interpolate between `Y = Z_0` and `X = Z_n`. By
`abs_sub_le_sum_range` it is enough to bound each step `|E g(f(Z_{k+1})) − E g(f(Z_k))|`.
In step `k` the two hybrids are the base point `baseVec X Y k` with `X_k`, respectively `Y_k`,
written into slot `k` (`hyb_succ_eq`, `hyb_eq`), and `X_k`, `Y_k` are independent of the base
point (`indep_slot`). So `slot_swap` gives the bound for step `k`, and summing over `k` gives
the claim. -/
theorem swap_bound {P : Measure Ω} [IsProbabilityMeasure P]
    (X Y : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hind : iIndepFun (Sum.elim X Y) P)
    (hX2 : ∀ i, MemLp (X i) 2 P) (hY2 : ∀ i, MemLp (Y i) 2 P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = ∫ ω, Y i ω ∂P)
    (hsq : ∀ i, ∫ ω, X i ω ^ 2 ∂P = ∫ ω, Y i ω ^ 2 ∂P)
    {f : (Fin n → ℝ) → ℝ} (hf : CoordC3 f) (hfm : Measurable f)
    (hd1 : ∀ i, Measurable (coordDeriv 1 f i)) (hd2 : ∀ i, Measurable (coordDeriv 2 f i))
    (hf₂ : lam 2 f ≠ ⊤) (hf₃ : lam 3 f ≠ ⊤)
    {g : ℝ → ℝ} (hg : BddC3 g) {Mg : ℝ} (hgb : ∀ x, |g x| ≤ Mg) (K : ℝ) :
    |(∫ ω, g (f fun i => X i ω) ∂P) - ∫ ω, g (f fun i => Y i ω) ∂P| ≤
      C₁ g * (lam 2 f).toReal * ∑ i, (tailSq P (X i) K + tailSq P (Y i) K) +
      C₂ g * (lam 3 f).toReal * ∑ i, (truncCube P (X i) K + truncCube P (Y i) K) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun k => ∫ ω, g (f (hyb X Y k ω)) ∂P := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, B = fun k =>
      if h : k < n then
        C₁ g * (lam 2 f).toReal * (tailSq P (X ⟨k, h⟩) K + tailSq P (Y ⟨k, h⟩) K) +
          C₂ g * (lam 3 f).toReal * (truncCube P (X ⟨k, h⟩) K + truncCube P (Y ⟨k, h⟩) K)
      else 0 := ⟨_, rfl⟩
  have hstep : ∀ k < n, |a (k + 1) - a k| ≤ B k := by
    intro k hk
    have hik : (⟨k, hk⟩ : Fin n).val = k := rfl
    have hW : Measurable fun ω => baseVec X Y k ω := by
      rw [measurable_pi_iff]
      intro j
      by_cases hj : j.val < k
      · simp only [baseVec, hj, ↓reduceIte]; exact hXm j
      · by_cases hj' : k < j.val
        · simp only [baseVec, hj, hj', ↓reduceIte]; exact hYm j
        · simp only [baseVec, hj, hj', ↓reduceIte]; exact measurable_const
    have hs := measurable_sliceD hf hg hfm ⟨k, hk⟩ (hd1 _) (hd2 _)
    have hsw := slot_swap hf hf₂ hf₃ hg hgb hfm ⟨k, hk⟩ hW (hXm _) (hYm _) (hX2 _) (hY2 _)
      (indep_slot hXm hYm hind ⟨k, hk⟩ hik (Sum.inl ⟨k, hk⟩) (Or.inl rfl))
      (indep_slot hXm hYm hind ⟨k, hk⟩ hik (Sum.inr ⟨k, hk⟩) (Or.inr rfl))
      (hmean _) (hsq _) hs.1 hs.2 K
    have h1 : a (k + 1) =
        ∫ ω, g (f (Function.update (baseVec X Y k ω) ⟨k, hk⟩ (X ⟨k, hk⟩ ω))) ∂P := by
      simp only [ha, hyb_succ_eq X Y ⟨k, hk⟩ hik]
    have h0 : a k =
        ∫ ω, g (f (Function.update (baseVec X Y k ω) ⟨k, hk⟩ (Y ⟨k, hk⟩ ω))) ∂P := by
      simp only [ha, hyb_eq X Y ⟨k, hk⟩ hik]
    rw [h1, h0, hB]
    simp only [dite_eq_left hk]
    exact hsw
  have htel := abs_sub_le_sum_range a B n hstep
  have hyb0 : ∀ ω, hyb X Y 0 ω = fun i => Y i ω := fun ω => by
    funext j; simp [hyb]
  have hybn : ∀ ω, hyb X Y n ω = fun i => X i ω := fun ω => by
    funext j; simp [hyb, j.isLt]
  have e0 : a 0 = ∫ ω, g (f fun i => Y i ω) ∂P := by simp only [ha, hyb0]
  have en : a n = ∫ ω, g (f fun i => X i ω) ∂P := by simp only [ha, hybn]
  have hsum : ∑ k ∈ Finset.range n, B k =
      C₁ g * (lam 2 f).toReal * ∑ i, (tailSq P (X i) K + tailSq P (Y i) K) +
      C₂ g * (lam 3 f).toReal * ∑ i, (truncCube P (X i) K + truncCube P (Y i) K) := by
    rw [← Fin.sum_univ_eq_sum_range B n, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hB, i.isLt]
  rw [e0, en] at htel
  exact htel.trans (le_of_eq hsum)

end Moments

end Statlib.Invariance
