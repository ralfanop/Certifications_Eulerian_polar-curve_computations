# M16 v16.5 — exact Bessel-graph resolvent bound (§14.1)

Source: author-approved ZIP SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`. This note does not alter that archive or manuscripts 11–15. Parent commit: `3c147ac4d36721bf60776c4fc1538ff42bbfb415`.

## Exact analytic lemma (not yet Lean-certified)

Fix `a > 0` and dimension `d ≥ 1`. On `L²(ℝᵈ)`, define `R_a` by its Fourier multiplier `(a²+|ξ|²)⁻¹` (unitary Fourier convention). Equip `H²(ℝᵈ)` with the Bessel norm `‖u‖_{H²,B}² = ∫ (1+|ξ|²)² |û(ξ)|² dξ`. Then `R_a : L² → H²` is bounded and

`‖R_a‖_{L²→H²,B} = max(1,a⁻²)`.

Moreover `(-Δ+a²)R_a f=f` in `L²` for every `f∈L²`, and `R_a(-Δ+a²)u=u` for every `u∈H²`. Therefore `R_a` is the two-sided inverse of the unbounded operator `-Δ+a² : H²⊂L²→L²`.

## Proof

Plancherel gives `‖R_a f‖²_{H²,B} = ∫ [(1+t)/(a²+t)]² |f̂(ξ)|² dξ`, `t=|ξ|²≥0`. The scalar ratio `h(t)=(1+t)/(a²+t)` has derivative `(a²-1)/(a²+t)²`, hence `sup_{t≥0}h(t)=max(1,a⁻²)`. The upper bound follows. The reverse inequality follows by choosing Fourier supports in annuli of positive measure concentrating at `t=0` if `a²≤1`, or at arbitrarily large `t` if `a²≥1`. Multiplication by `a²+t` establishes both inverse identities. These are identities of the specified graph domains, not merely formal differential expressions.

For the free evanescent regime of Theorem 14.1 set `a²=|κ|²-k²>0`. The separate `L²→L²` norm is `a⁻²`. This statement is *not* a Maxwell boundary realization or a Schatten-class assertion.

## Lean 4 obligations (open)

1. Define the Fourier multiplier on `L²(ℝᵈ)` and the Bessel `H²` space with its exact norm.
2. Establish boundedness via Plancherel and the measurable multiplier bound.
3. Establish the lower operator-norm bound with positive-measure frequency annuli (not pointwise evaluation at ξ=0).
4. Prove Fourier characterization of the graph domain and both inverse equalities.
5. Audit `#print axioms` on the final theorem; reject `sorryAx` and `Lean.ofReduceBool`.

## Certification ledger

- Scalar rational maximization: proved analytically above; **not Lean-checked**.
- Unbounded operator domain and inverse: analytic proof outline; **not Lean-checked**.
- FLINT/Arb: **not applicable** to this symbolic lemma; no 3,600,000-bit numerical claim.
- Full Theorem 14.1: **open**, as kernel identification and remaining physical hypotheses are not covered.
