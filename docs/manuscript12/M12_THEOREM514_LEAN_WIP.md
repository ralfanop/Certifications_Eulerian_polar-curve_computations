# M12 §5.8 Lean work in progress (20 November 2026)

Independent of PR #490 (Arb Table 1 and analytical revision record). Source statement
reference: PR #490, docs/manuscript12/M12_20261120_THEOREM_5_14_RATE.md.
The author's archive supplied in this conversation (AUTONOMOUS(6)) has §5.1–5.7 only,
SHA-256 of 12.tex 104937827735e80bf35c515ab63c651b3be606353be15abe9ce08a87159c5996;
the proposed §5.8 source in #490 has a different digest, 841bd07488f83c50940cc5343511e472e8790ab5e25b07bb5fcbb5b3e1f4811e.
Reconcile the proposed §5.8 against the adopted text before claiming full theorem correspondence.

| Module | Proof components submitted | Remaining obligations |
|---|---|---|
| Lemma511 | monic derivative pairing; positive Hankel quotient via Theorem59; Freud normalization given integration by parts | construct orthonormal polynomials from gM, prove lower-degree derivative expansion and endpoint-vanishing integration by parts |
| Lemma512 | nonnegative divided differences and finite spectral quadratic form | establish the Jacobi functional calculus, Fourier/Duhamel decay, exact Daleckii–Krein derivative kernel/symmetry and limiting argument |
| Lemma513 | uniform strict interior gap from theorem_5_9 under LL_13_4 | local path/moment argument, exponential tail, B-spline derivative and Legendre endpoint estimate |
| Theorem514 | finite weighted energy/coercivity inequality and square transfer for betaM, Profile.F, Profile.ξ | derive coercivity on the actual window, control residuals, localization, pointwise estimate and assemble the uniform rate |

All four workflows compile the exact PR head independently, perform source hygiene
and individual axiom audits (allowed: propext, Classical.choice, Quot.sound).
The submitted steps are candidate Lean code, pending CI. They are not claimed as complete
formalizations of Lemmas 5.11–5.13 or Theorem 5.14.

Published analytic inputs may enter as explicit propositions (LL_13_4, Duhamel,
Daleckii–Krein, Higham 2008 Theorem 3.11), with all applications proved. Do not
introduce the manuscript's new conclusions as hypotheses disguised as external inputs.
No merger of #490 is implied by this draft.
