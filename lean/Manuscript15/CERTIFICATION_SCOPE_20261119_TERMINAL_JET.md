# M15 §6.2 — actual terminal jets (2026-11-19)

Continuation of #329, #367 and #425 (exact-HEAD success). Source labels
eq:terminal-lagrange-h, eq:terminal-lagrange-leading and
eq:terminal-lagrange-det-ratio. No change to the frozen source.

The new candidates `TerminalJet.Y_order`, `leading_coefficient`,
`graph_order`, `exists_terminal_analytic_remainder`, `graph_jets`
connect the actual analytic graph to the explicit leading coefficient:
at scale a≠0 the coefficient is a terminalCoefficient(M)/a^(2M).
The remainder is itself analytic after dividing by the (2M+1)-st
power of the independent horizontal displacement. Orders below 2M
vanish and the derivative of order 2M is nonzero. The complete
higher-coefficient Lagrange–Bürmann formula is still open.

All new statements are exact symbolic assertions (no new numerical
approximation). Pending exact-HEAD Lean and whitelist audit; no new
certificate claimed until successful. Existing FLINT/Arb obligations
and artifacts are unchanged. No merge.
