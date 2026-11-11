# Manuscript 15 — Rigorous 10000-bit type-B inverse-central-binomial series

This phase separately evaluates the infinite series from Manuscript 15's
Plouffe/Sprugnoli passage, using the exact rational recurrence

`t_0=1; t_(k+1)=t_k * (2(k+1))/(5(2k+3))`.

The exact integer inequality `2(k+1)<2k+3` proves
`0<t_(k+1)<t_k/5`, and hence for the first N=4000 terms
`0<Σ_(k=N)^∞ t_k < (5/4)t_N`.
No numerical convergence assumption replaces this analytical remainder proof.

The script `numerics/manuscript15_typeB_series_arb10000.py`:
1. Computes the finite rational series via outward-rounded 10000-bit Arb operations.
2. Combines it with the **rigorous geometric tail bound** to obtain a single
   interval enclosing the **entire infinite sum**, not just its truncation.
3. Requires `rel_accuracy_bits()>=8182` for the series, the implied
   `arctan(1/2)`, `α₃`, `p_gamma` and `α₃` in degrees.
4. Independently checks that the series-derived angle lies strictly in the
   rounding cell of the label `53.1301023542°`.
5. Uses an independent Arb `atan` overlap check for consistency only; it is **not**
   treated as a proof of equality of the functions/series.

**Status:** candidate until exact-head GitHub Actions succeeds.
The analytical identity is established in the manuscript by the
beta-integral argument, not by Arb. A future Lean proof should formalize
the beta integral and justify the infinite-series transformations.
All prior work and Manuscripts 11–14 remain unchanged; no merge.
