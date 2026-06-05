import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "../"
set_option verso.exampleModule "Statlib.QMD"

-- The mean-zero score proof anchor is heavy to elaborate when rendered.
set_option maxHeartbeats 1000000

#doc (Manual) "Quadratic Mean Differentiability" =>
%%%
htmlSplit := .never
%%%

Quadratic mean differentiability (QMD) is one of the foundational concepts of
asymptotic statistics. It underlies the local asymptotic efficiency theories of
Hájek and Le Cam, and it is the notion that lets one generalize the asymptotic
theory of Cramér, Wald, and Wilks. Informally, QMD equips a parametrized family of
probability measures with a notion of differentiability as a function of the
parameter, expressed through square-root densities in $`L^2`. This is strictly more
flexible than pointwise differentiability of densities, which fails to accommodate
the efficiency theory of classical models such as the Laplace family.

Throughout, $`\mathcal{P}(\Theta) = \{\mathbb{P}_\theta : \theta \in \Theta\}` is a
family of probability measures on a measurable space $`(\Omega,\mathcal{A})`,
dominated by a common $`\sigma`-finite measure $`\mu`, and
$`p_\theta = d\mathbb{P}_\theta / d\mu` denotes a Radon–Nikodym derivative.

# The classical definition

The most common definition of QMD uses a Euclidean parameter set. We start here to
fix intuition, then relax the parameter space below.

Let $`\Theta \subseteq \mathbb{R}^k` and let $`\mu` dominate the family. The family
$`\mathcal{P}(\Theta)` is QMD at an interior point $`\theta^\star` if there exists
a score $`h \in L^2(\mathbb{P}_{\theta^\star})` such that

$$`\left\|
     \frac{p_{\theta^\star + t}^{1/2} - p_{\theta^\star}^{1/2}}{\|t\|}
     - \tfrac{1}{2}\, h\, p_{\theta^\star}^{1/2}
   \right\|_{L^2(\mu)} \longrightarrow 0,`

as $`\|t\| \to 0`. The function $`h` is the score at $`\theta^\star`.

A cornerstone result is that the score has mean zero under $`\mathbb{P}_{\theta^\star}`.
Inspecting its proof shows that one can weaken both the parameter space and the
notion of differentiability and still reach the conclusion.

# QMD over a normed space

The first generalization replaces $`\mathbb{R}^k` by a normed vector space $`E`.
Let $`\Theta \subseteq E`, let $`\mu` be $`\sigma`-finite, and assume
$`\mathbb{P}_\theta \ll \mu` for all $`\theta \in \Theta`. The family is QMD at an
interior point $`\theta^\star` with a bounded linear score
$`A_{\theta^\star} : E \to L^2(\mathbb{P}_{\theta^\star})` if

$$`\left\|
     \sqrt{p_{\theta^\star + h}} - \sqrt{p_{\theta^\star}}
     - \tfrac{1}{2}\, A_{\theta^\star}(h)\, \sqrt{p_{\theta^\star}}
   \right\|_{L^2(\mu)} = o(\|h\|_E).`

```anchor hasQuadraticMeanDeriv
def HasQuadraticMeanDerivWithinAt {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] (P : E → Measure Ω) (μ : Measure Ω) (s : Set E) (x : E)
    (A : E →ₗ[ℝ] (Ω →₂[P x] ℝ)) : Prop :=
  (fun y =>
    lpNorm (fun ω => √((P y).rnDeriv μ ω).toReal - √((P x).rnDeriv μ ω).toReal -
    2⁻¹ * A (y - x) ω * √((P x).rnDeriv μ ω).toReal) 2 μ) =o[ℝ; 𝓝[s] x] (fun y => y - x)
```

The main result of interest at this level of generality is the mean-zero score
property: if $`\mathcal{P}(\Theta)` is QMD at an interior point $`\theta^\star` with
score $`A_{\theta^\star}`, then $`\mathbb{E}_{\mathbb{P}_{\theta^\star}}\!\big(A_{\theta^\star}(h)\big) = 0`
for every $`h \in E`.

However, the notion of differentiability can be weakened further to achieve this.

# Hadamard QMD over a topological vector space

The mean-zero-score conclusion survives an even weaker hypothesis: $`E` may be a
topological vector space, and differentiability may be tested only along local paths.
This _Hadamard_ formulation is what the Lean development uses, because it is both
weaker than the classical condition and easier to work with.

The family is _Hadamard QMD_ (H.Q.M.D.) at an interior point $`\theta^\star` with
linear score $`A_{\theta^\star}` if, whenever $`t \to 0`, $`a_t \to h` in $`E`, and
$`\theta^\star + t\,a_t \in \Theta` eventually,

$$`\frac{1}{t}\left\|
     \sqrt{p_{\theta^\star + t a_t}} - \sqrt{p_{\theta^\star}}
     - \tfrac{1}{2}\, A_{\theta^\star}(t h)\, \sqrt{p_{\theta^\star}}
   \right\|_{L^2(\mu)} \longrightarrow 0.`

In Lean the local path is encoded by a filter $`l` on $`\mathbb{R} \times E` whose
first coordinate tends to $`0` and whose second coordinate tends to $`h`, with the
path eventually staying in $`\Theta`.

```anchor hasHadamardQuadraticMeanDeriv
def HasHadamardQuadraticMeanDerivWithinAt {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] (P : E → Measure Ω) (μ : Measure Ω) (s : Set E) (θ : E)
    (A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)) : Prop :=
  ∀ (h : E) (l : Filter (ℝ × E)), Tendsto Prod.fst l (𝓝 0) →
    Tendsto Prod.snd l (𝓝 h) → (∀ᶠ p in l, θ + p.1 • p.2 ∈ s) → Tendsto (fun p =>
    p.1⁻¹ * lpNorm (fun ω => √((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
    √((P θ).rnDeriv μ ω).toReal -
    2⁻¹ * A (p.1 • h) ω * √((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0)
```

The Hadamard notion is genuinely weaker: a quadratic mean derivative within a set is
always a Hadamard QMD derivative.

```anchor qmdImpliesHadamard
theorem HasQuadraticMeanDerivWithinAt.hasHadamardQuadraticMeanDerivWithinAt {Ω E : Type*}
    {mΩ : MeasurableSpace Ω} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {P : E → Measure Ω}
    {μ : Measure Ω} [SigmaFinite μ] {s : Set E} {θ : E} {A : E →L[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) :
    HasHadamardQuadraticMeanDerivWithinAt P μ s θ A :=
  (hasHadamardQuadraticMeanDerivWithinAt_iff A hθ hprob hs).2
    fun _ _ hzero hh he => hA.tendsto_local_path_remainder hzero hh he
```

# The mean-zero score theorem

The central result, formalized as `integral_score_eq_zero`, is the following.

> _Theorem_ (Mean-zero score). Let $`\mathcal{P}(\Theta) = \{\mathbb{P}_\theta\}_{\theta \in \Theta}`
> be a class of probability measures on a measurable space $`(\Omega,\mathcal{A})`, where
> $`\Theta \subseteq E` for a topological vector space $`E` and $`\mu` is a $`\sigma`-finite
> measure satisfying $`\mathbb{P}_\theta \ll \mu` for all $`\theta \in \Theta`. Suppose that
> $`\mathcal{P}(\Theta)` is Hadamard quadratic mean differentiable at an interior point
> $`\theta^\star \in \Theta` with score $`A_{\theta^\star} : E \to L^2(\mathbb{P}_{\theta^\star})`.
> Then
> $$`\mathbb{E}_{\mathbb{P}_{\theta^\star}}\!\big(A_{\theta^\star}(h)\big) = 0 \qquad \text{for all } h \in E.`

## Proof sketch

The argument is the classical difference-of-squares computation. Start from the
normalization $`\int p_\theta \, d\mu = 1`, which for two parameters gives

$$`0 = \int
     \big(\sqrt{p_{\theta^\star + t a_t}} + \sqrt{p_{\theta^\star}}\big)
     \big(\sqrt{p_{\theta^\star + t a_t}} - \sqrt{p_{\theta^\star}}\big)
   \, d\mu.`

Write the QMD remainder

$$`R_t = \sqrt{p_{\theta^\star + t a_t}} - \sqrt{p_{\theta^\star}}
        - \tfrac{1}{2}\, A(t h)\, \sqrt{p_{\theta^\star}},`

and split the integral as $`0 = T_1 + T_2`, where

$$`T_1 = \int \big(\sqrt{p_{\theta^\star + t a_t}} + \sqrt{p_{\theta^\star}}\big) R_t \, d\mu,
   \qquad
   T_2 = \tfrac{1}{2} \int
     \big(\sqrt{p_{\theta^\star + t a_t}} + \sqrt{p_{\theta^\star}}\big)
     A(t h)\, \sqrt{p_{\theta^\star}} \, d\mu.`

_The remainder term vanishes._ By Cauchy–Schwarz,

$$`\frac{|T_1|}{|t|}
   \le \frac{\|R_t\|_{L^2(\mu)}}{|t|}\,
       \big\|\, p_{\theta^\star + t a_t}^{1/2} + p_{\theta^\star}^{1/2} \,\big\|_{L^2(\mu)}.`

The sum of square-root densities is bounded in $`L^2`: since each $`p` is a probability
density, $`\big\| p_{\theta^\star + t a_t}^{1/2} + p_{\theta^\star}^{1/2} \big\|_{L^2(\mu)} \le 2`.
Meanwhile H.Q.M.D. gives $`\|R_t\|_{L^2(\mu)} / |t| \to 0`. Hence $`T_1 / t \to 0`.

_The score term converges._ By linearity of $`A_{\theta^\star}`,

$$`\frac{T_2}{t}
   = \frac{1}{2}\int A(h)\, p_{\theta^\star}^{1/2}
     \big(p_{\theta^\star + t a_t}^{1/2} + p_{\theta^\star}^{1/2}\big) \, d\mu.`

Continuity of the square-root density along the path gives
$`p_{\theta^\star + t a_t}^{1/2} + p_{\theta^\star}^{1/2} \to 2\, p_{\theta^\star}^{1/2}`
in $`L^2(\mu)`, so

$$`\frac{T_2}{t}
   \longrightarrow \int A(h)\, p_{\theta^\star} \, d\mu
   = \mathbb{E}_{\mathbb{P}_{\theta^\star}}\!\big(A(h)\big).`

Since $`T_1/t + T_2/t = 0` for every $`t \neq 0`, taking the limit yields
$`\mathbb{E}_{\mathbb{P}_{\theta^\star}}(A(h)) = 0`, as claimed.

## The formalized proof

The mean-zero score result is the theorem `integral_score_eq_zero`. We present the
statement below.

```anchor integralScoreEqZeroSig
theorem integral_score_eq_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ h : E} {A : E →ₗ[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    [l.NeBot] (hzero : Tendsto Prod.fst l (𝓝[≠] 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    ∫ ω, A h ω ∂P θ = 0 := by
```

The proof follows the difference-of-squares argument above: the limits $`T_1/t \to 0`
and $`T_2/t \to \mathbb{E}_{\mathbb{P}_{\theta^\star}}(A(h))` are the lemmas `tendsto_zero`
and `tendsto_integral_score`, and uniqueness of limits pins the score integral to $`0`.
