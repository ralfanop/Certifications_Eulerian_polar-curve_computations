# Frozen Manuscript 12 — Appendix A statement reconciliation

Authoritative archive SHA-256: `7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860`.
Verified directly against `Manoscritto_12/12.tex`, lines 2488–2550, and the audited Bridge sources at `595120564632dee861ded1083013569dccc1f90d` (PR #438, run 44495702589).
The former numbering in Bridge source comments is not the current numbering. All existing theorem names below are in `EulerianBridge.AppendixA`. The four new explicit-form adapters are in `M12FrozenAppendixA` and remain candidates until exact-HEAD CI.

| Current equation | Exact label | Lean declaration(s) | Semantic comparison |
|---|---|---|---|
| 279 | eq:A058962-ogf | a_ogf | HasSum over natural k, real x with abs x < 1/4; same rational expression. |
| 280 | eq:A058962-egf | a_egf | HasSum all real x; factorial denominator and exp(4x)(1+8x) agree. |
| 281 | eq:A058962-rec | a_rec; M12FrozenAppendixA.eq281 | Natural additive identity equivalent to the printed subtraction recurrence for index k+2. New adapter directly states subtraction. |
| 282 | eq:moments-log3 | moments_sum; integral_inv_one_sub_sq; M12FrozenAppendixA.eq282_integral_sum | Exact HasSum to 2 arctanh(1/2), arccoth equality, log 3; integral separately proved. New adapter identifies sum of actual moment integrals with the integral value. |
| 283 | eq:gudermannian | gd (definition); gd_eq; gd_strictMono; abs_gd_lt; range_gd | Definition as reciprocal cosh integral on oriented real interval; strict monotonicity and exact open range proved. |
| 284 | eq:lambertian | gdInv (definition); gdInv_eq_log_tan; gdInv_eq_arctanh_sin; gdInv_gd; gd_gdInv | Integral of reciprocal cosine, both closed forms, and both inverse directions on abs phi < pi/2. |
| 285 | eq:lambertian-45 | gdInv_pi_div_four | Both printed equalities in one conjunctive theorem over real numbers. |
| 286 | eq:lambertian-345 | gdInv_arctan_four_thirds | Sin of atan(4/3) and all three displayed equalities, including log 3. |
| 287 | eq:moments-semifactorial | m_semifactorial; oddDF_succ | Actual uniform integral m, oddDF k and oddDF(k+1) encode the odd double factorial convention (k=0 gives 1). |
| 288 | eq:central-binomial-semifactorial | central_binom_semifactorial; factorial_two_mul; M12FrozenAppendixA.eq288 | Old multiplicative natural identity, new real division wrapper with explicit Nat.choose (2*k) k. |
| 289 | eq:catalan-semifactorial | catalan_semifactorial; M12FrozenAppendixA.eq289 | Old factorial multiplication identity, new wrapper states both printed fractions, positive denominators. |
| 290 | eq:moments-uniform | uniform_moments | Genuine interval integral on [-2,2], normalization 1/4, both value and 16^k*m k. |
| 291 | eq:moments-arcsine | arcsine_moment; arcsine_subst; wallis; change_two_sin | Genuine Lebesgue interval integral (endpoints a null set), normalized by 1/pi. Nat.centralBinom k = Nat.choose (2*k) k. |
| 292 | eq:moments-semicircle | semicircle_moment; wallis; change_two_sin | Genuine interval integral on [-2,2], normalized by 1/(2*pi), exact catalan k. |
| 293 | eq:moments-gaussian | gaussian_moment | Whole-real-line Lebesgue integral with exp(-x²/2)/sqrt(2*pi), same odd double factorial convention. |

Unnumbered supporting assertions: m_eq and m_inv prove reciprocal moments. a_eq_hypercube_edges proves the arithmetic odd-bisection formula, **not** a graph-theoretic cardinality theorem independently identifying hypercube edges. The latter counting interpretation is a classical cited observation, and the sum/integral adapter proves the equality of values using two independent analytic proofs rather than an explicit theorem interchanging integral and sum. The quadratic character L8(1) identity is cited to Finch; its scalar evaluations are certified by #384 but this does not constitute a proof about the actual Dirichlet L family. No unsupported coverage of these unnumbered claims is implied. No change to the manuscript, figures, source toolchain, or earlier certificates. This is a scoped reconciliation of 15 displays, not a claim of complete M12 certification.
