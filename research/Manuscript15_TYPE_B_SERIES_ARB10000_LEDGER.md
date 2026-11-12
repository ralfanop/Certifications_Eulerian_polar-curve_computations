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

**Status:** candidates until exact-head GitHub Actions succeeds. The branch now also contains four proposed Lean declarations in `lean/Manuscript15/TypeBSeriesRatio.lean`:
- `typeBTermRatio_pos`;
- `typeBTermRatio_lt_fifth`, strict rational ratio below 1/5;
- `typeBTerm_pos`;
- `typeBTerm_decay`, the exact positive-term geometric domination.

The Lean workflow prints axioms and rejects `sorryAx` and `Lean.ofReduceBool`. Note that connecting this recursive term definition with the closed central-binomial summand, and the full infinite-tail `tsum` argument, require further explicit Lean proofs. Until then, the numerical script uses the mathematically exact integer ratio argument separately.
The analytical identity is established in the manuscript by the
beta-integral argument, not by Arb. A future Lean proof should formalize
the beta integral and justify the infinite-series transformations.
All prior work and Manuscripts 11–14 remain unchanged; no merge.


## Verified CI evidence

Both jobs in [GitHub Actions run #43087384447](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43087384447) **SUCCEEDED** on executable-source commit `ee24b42d1eb84172875460391795641317b75de7`. The four Lean declarations `typeBTermRatio_pos`, `typeBTermRatio_lt_fifth`, `typeBTerm_pos` and `typeBTerm_decay` all depend only on `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). The five infinite-series Arb enclosures each achieved **9293–9294 rigorously certified relative bits** at `ctx.prec=10000`, above the threshold of 8182 bits. The exact geometric tail bound and Figure 1 decimal rounding test passed. Analytic identity to the arctan via the beta integral is a manuscript-level step that this CI does **not** formalize in Lean.
