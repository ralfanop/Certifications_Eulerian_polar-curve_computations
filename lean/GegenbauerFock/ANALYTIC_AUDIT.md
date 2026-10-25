# Gegenbauer–Fock: analytical formalisation obligations and audit

Updated 25 October 2026. This is a **mathematical proof specification**, not a
collection of Lean theorems. The accepted V097 manuscript and the existing
Eulerian certificates remain untouched.

## Parameters and Hilbert-space model

Assume `α>0`, `λ>0`. Define the probability measure
`dν_λ(u) = Γ(λ+1)/(√π Γ(λ+1/2)) (1-u²)^(λ-1/2) 1_{(-1,1)} du`.

Prove normalization and exact moments:
`∫ u^(2n) dν_λ = (1/2)_n/(λ+1)_n`,
`∫ u^(2n+1) dν_λ = 0`.

Let `F_α` denote the Gaussian holomorphic Bargmann–Fock Hilbert space
with normalized Gaussian weight `(α/π) exp(-α|z|²) dA(z)`.
Define, **via Bochner integration in the Fock Hilbert space**,
`C_{λ,α} f (z) = ∫ f(u) exp(i z u/2) dν_λ(u)`.

## Proposed rigorous analytic theorem obligations

1. **Boundedness and Hilbert–Schmidt:** show the section kernel has squared
   Fock norm `exp(u²/(4α))`. Infer
   `‖C‖²_HS = ∫ exp(u²/(4α)) dν_λ =
   ₁F₁(1/2; λ+1; 1/(4α))`.
   Establish measurability/Bochner integrability and the evaluation
   operator, not just the scalar integral formula.

2. **Adjoint:** with inner products *linear in their first argument*,
   prove `(C*F)(u) = F(-i u/(2α))` almost everywhere.
   This is point evaluation after continuous restriction to the imaginary
   segment; prove boundedness as an L²-valued operator.

3. **Gram operator:** derive
   `(C*C f)(u)=∫ exp(uv/(4α)) f(v) dν_λ(v)`.
   Prove positive, selfadjoint, compact and trace class.
   Positivity for `c=1/(4α)>0` follows from the convergent
   nonnegative moment-square expansion
   `⟨f,S_c f⟩ = Σ_{n≥0} c^n/n! |∫u^n f(u)dν_λ|²`.
   Require a justified interchange of integrals and infinite series.

4. **Injectivity and dense range:** `C f=0` implies all moments
   vanish. Polynomial density in `L²(ν_λ)` implies `f=0`.
   `C*F=0` implies an entire `F` vanishes on a set with
   accumulation point, hence `F=0` by the identity theorem.
   Neither compactness nor dense range implies surjectivity.

5. **Second-boson intertwiner and domains:** show that
   `C f ∈ domain(b_α)` and
   `b_α C f = (i/(2√α)) C (M_u f)`,
   with `b_α = α^(-1/2)∂_z` and `M_u f=u f`.
   Since `M_u` is bounded selfadjoint but `b_α` is unbounded,
   this is a nonunitary *quasiaffine* intertwining, not unitary
   equivalence.

6. **Gegenbauer Sturm–Liouville:** define the canonical spectral
   selfadjoint realization via the orthonormal Gegenbauer basis:
   `D_λ p_n = n(n+2λ) p_n`.
   Show the formula `D_λ f=-(1-u²)f''+(2λ+1)u f'`
   on the polynomial core and prove
   `𝒟_λ C p = C D_λ p` for every polynomial,
   where `𝒟_λ=z²∂_z²+(2λ+1)z∂_z+z²/4`.
   Do **not** assert that `𝒟_λ` is selfadjoint in the Gaussian norm.

7. **Spheroidal commutation:** for `c=1/(4α)` define
   `L_{λ,c}=D_λ-c²M_{u²}` as a bounded perturbation of
   the selfadjoint `D_λ`. The pointwise identity
   `L_{λ,c}^{(u)} exp(cuv)=L_{λ,c}^{(v)} exp(cuv)`
   is necessary but not sufficient; prove the weighted Green
   formula/integration by parts with natural endpoint conditions on
   a dense invariant core, then extend to the desired operator domains
   to obtain `L_{λ,c}S_c=S_cL_{λ,c}`.
   On the polynomial core, `(1-u²)^{λ+1/2}p'(u)`
   vanishes at endpoints when `λ>0`. For an unbounded
   selfadjoint realization, explicitly verify the domain invariance
   needed by the claimed commutation.

8. **Schatten estimates:** use the rank-`N` truncation of
   the coherent-state series and the exact monomial Fock norms
   to bound `s_{N+1}(C)`; derive membership in all Schatten
   classes `S_p` (`p>0`) only *after* formalizing the
   approximation-number inequalities and the convergent tail.

## Existing certified layers

- `KernelCore.lean` — algebraic polynomial kernel factor balance,
  Fourier–Gegenbauer *symbol* identity, Legendre coefficient examples,
  finite sum-of-squares positivity.
- `OscillatorCore.lean` — formal two-mode coefficient algebra,
  bosonic CCR and mixed commutations.
- `AnalyticKernel.lean` — real exponential kernel derivatives and
  pointwise spheroidal differential equation; CI and axiom audit must
  independently succeed before this is called kernel-certified.

The `AnalyticKernel.lean` theorem intentionally establishes the
**pointwise differential-kernel equation**, not the weighted-integral
commutation or Hilbert-space operator-domain result.

## Suggested formal development order

`Measure → Even moments → Coherent Fock sections → Hilbert-space
Bochner transform → Adjoints/Gram → Density/injectivity → Intertwiner
and domain → Sturm–Liouville spectral realization → Green identity →
Spheroidal commutation → Schatten bounds`.

Each proof package should be compiled with the repository's pinned
Lean `v4.35.0-rc3` and Mathlib commit
`0272bbe1c093d038d7257ab15306abd58245f9ff`, then
audited with `#print axioms`. Only `propext`,
`Classical.choice` and `Quot.sound` may appear.
