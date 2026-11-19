# M15 §6.2 — terminal analytic inverse and graph (2026-11-19)

Continuation of #325, #329, and #367 (the latter passed exact-HEAD CI).
This candidate applies the analytic inverse theorem to the actual reconstructed
coordinate `XConv`, not to a hypothesized analytic chart.

| Obligation | New candidate Lean declaration |
| --- | --- |
| Actual sinc analytic near nonzero terminal points | `TerminalAnalytic.kernel_analytic_nonzero` |
| Both actual coordinates analytic at 2π | `TerminalAnalytic.X_analytic`, `TerminalAnalytic.Y_analytic` |
| Two-sided local inverse, derivative 1/a, M≥2 and a≠0 | `TerminalAnalytic.exists_analytic_inverse` |
| Actual analytic graph and leading limit in the independent X variable | `TerminalAnalytic.exists_analytic_terminal_graph` |

The last declaration uses the right-inverse identity to transfer punctured
neighborhoods; the limit is not merely along the parametrization. Its leading
constant is nonzero by #367. The explicit Lagrange–Bürmann higher coefficient
formula and identification of the higher remainder are still open.
The singular M=1 case is excluded from this inverse construction.

Status: candidate pending exact-HEAD Lean and whitelist checks in
`.github/workflows/m15-terminal-analytic.yml`. No new numerical
approximation is introduced: all identities here are symbolic and exact.
The existing Arb certificates and obligations are unchanged. No change to
the manuscript, figure files, other manuscript projects, or historical
certificates.
