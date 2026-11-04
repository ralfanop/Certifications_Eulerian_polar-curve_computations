# Manuscript 14.10, Theorem 11.1 — Lindemann and eventual-periodicity proof

**Date:** 4 November 2026.  
**Scope:** exact mathematical argument and Lean 4 obligations.  
**Status:** mathematically proved in the manuscript; **not** yet claimed to be fully kernel-certified.  
**No custom axioms, `sorry`, `sorryAx`, or `Lean.ofReduceBool` are authorized.**

## 1. Transcendence of the Eulerian parameter

Put `a=1/sqrt(2)`, `s=sinh(a)` and `x_E=sqrt(2)*s`.
The number `a` is nonzero and algebraic. By the Hermite–Lindemann
theorem, `y=exp(a)` is transcendental. But
`2*s = y - y^{-1}`, hence `y^2 - 2*s*y - 1=0`.
If `s` were algebraic, `y` would be algebraic over the
algebraic closure of `Q`, hence algebraic over `Q` by transitivity:
a contradiction. Therefore `s` is transcendental, and multiplication
by the nonzero algebraic factor `sqrt(2)` shows that `x_E` is
transcendental.

**Lean obligation:** identify the precise imported statement of
Hermite–Lindemann for a nonzero algebraic real or complex parameter,
and formalize the preceding quadratic-algebraicity contradiction.
The pinned Mathlib snapshot contains a Lindemann–Weierstrass
`AnalyticalPart` file, but its full theorem was not found among the
available certified declarations. This is a *missing formal theorem
dependency*, not a reason to insert an axiom.

## 2. Eventually periodic greedy digits imply an algebraic base

For `1<β<2`, define `r_0=1`, `d_n=floor(β*r_{n-1})`
and `r_n=β*r_{n-1}-d_n` for `n≥1`.
Then `0≤r_n<1` for every `n≥1`. The telescoping identity is

`1 = sum_{n=1}^N d_n * β^{-n} + r_N * β^{-N}`.

As `β>1` and `r_N` is bounded, the remainder tends to zero and

`1 = sum_{n≥1} d_n * β^{-n}`.

Assume the digits are eventually periodic, with preperiod `m≥0`
and positive period `p≥1`: `d_{m+j+kp}=d_{m+j}` for
`1≤j≤p` and `k≥0`. Writing `t=β^{-1}` gives the
rational generating-function identity

`1 = sum_{n=1}^m d_n*t^n
     + (sum_{j=1}^p d_{m+j}*t^{m+j})/(1-t^p)`.

Since `0<t<1`, multiplying by `β^{m+p}` yields the *nonzero*
integer polynomial relation

`P(β) = β^{m+p}-β^m
          - sum_{n=1}^m d_n*(β^{m+p-n}-β^{m-n})
          - sum_{j=1}^p d_{m+j}*β^{p-j} = 0`.

The leading coefficient of `P` is exactly 1: all terms in the
sums have degrees strictly below `m+p`. Hence `β` is algebraic
over `Q`. For the transcendental `β=x_E`, this is impossible.
Therefore `d_{x_E}(1)` is not eventually periodic.

**Lean obligations:** prove the floor-map range, telescoping identity,
convergence to zero of `β^{-N}r_N`, the exact rational
eventual-periodic generating function, construction of `P∈Z[X]`,
and its monicity/nonzero property; then combine this with the
Hermite–Lindemann certificate from §1.

## 3. Existing kernel certificates to reuse, not reproved here

- The **actual**, floor-defined map, terminating word at the
  trinomial endpoint, and one-sided jump are checked in
  `lean/SpecialImaginaryPoint/ParryThresholds.lean` as of successful
  [CI #41801202307](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41801202307).
- Exact root existence/uniqueness for `β_32`, the strict comparison
  with both adjacent roots, and the integrated conditional interval
  statement are checked by
  [CI #41803799893](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41803799893).
- A genuine, assumption-free analytic enclosure of
  `x_E=sqrt(2)*sinh(1/sqrt(2))` is verified by
  [CI #41805294957](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805294957).
- The final combined theorem is reported as certified **only** once
  its new Lean import and proof have passed a separate clean CI.
- Numerical checks: **16/16** in the existing Section 11 Arb job.
  This is not a Lean proof of Lindemann or eventual-periodicity.

The 14.10 theorem is a *single* research theorem; this worksheet does
not create any additional publishable mathematical claim and makes no
merges to V007, V097 or manuscripts 11–13.
