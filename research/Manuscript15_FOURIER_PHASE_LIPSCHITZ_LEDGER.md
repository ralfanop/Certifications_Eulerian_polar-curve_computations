# Manuscript 15 — Sharp Lipschitz Fourier phase bounds

These four formal Lean 4 results are the **pointwise analytical
prerequisites** for the Wasserstein-1 stability estimate of the
probabilistic cycloidal reconstruction:

`|cos(sx)−cos(sy)|≤|s|·|x−y|`
and
`|sin(sx)−sin(sy)|≤|s|·|x−y|`,
including their consequences when a coupling distance majorant δ
controls `|x−y|`.

Their sharp factor 1 comes from the actual Mathlib trigonometric
Lipschitz theorems; no approximated derivative or numeric test is
substituted for the analytic proof.

**Still required:** the probability coupling measure, integration of
the Fourier phase difference under that measure, its marginal
pushforwards, and infimum over couplings defining `W₁(μ,ν)`. The
full Wasserstein inequality is not claimed from these four
pointwise theorems alone. The coordinate bounds
`|ΔX|≤2|a|t²δ` and `|ΔY|≤|a||t|³δ`
are independently kernel-certified in PR #187.

Status: candidate pending the exact-head CI (standard axioms only).
No merge or modifications to Manuscripts 11–14.
