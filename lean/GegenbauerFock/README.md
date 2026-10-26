# Gegenbauer–Fock Lean 4 formalization — isolated draft PR #16

**Status (26 October 2026):** algebraic + selected analytic and integral lemmas
have been kernel-checked under the repository's pinned Lean and Mathlib.
This project remains a **partial** formalization; it is **not** a
certification of all Gegenbauer–Fock Hilbert-space operator theorems.

All changes are confined to the draft branch
`gegenbauer-fock-formalization-20261025`.
The accepted V097 manuscript and previously published Eulerian
certificates are unchanged. Do not merge this branch into `main`
without the author's explicit approval.

## Certified modules

- `KernelCore.lean`: algebraic spheroidal kernel balance, formal
  differential symbols, Legendre recurrence examples and *finite*
  Gram sum-of-squares positivity.
- `OscillatorCore.lean`: formal two-mode bosonic CCR, mixed commutation
  and coefficient-array vacua; **no unbounded-operator domain theory**.
- `AnalyticKernel.lean`: real first and second derivatives of
  `K_c(u,v)=exp(cuv)`, exact *pointwise* spheroidal differential
  kernel equation, positivity, symmetry and uniform compact-square bound.
- `LegendreMoments.lean`: actual normalized interval integrals of the
  uniform Legendre law `du/2` on `[-1,1]`, mass one, every odd moment
  zero, and every even moment `1/(2n+1)`.
- `EulerianFourierIntegral.lean`: special-frequency exact complex
  interval integral of the Eulerian profile
  `∫_{-1/2}^{1/2}exp(it)dt = 2sin(1/2) = sinc(1/2)`.

The new integral theorems use Mathlib's established proofs of
`integral_pow`, `integral_exp_mul_I_eq_sin`, and
`integral_exp_mul_I_eq_sinc`. Each module includes explicit
`#print axioms` statements for representative results.

## Current limitations

Not yet certified: beta-integral moments at arbitrary `λ>0`, the
Bochner-valued Gegenbauer–Fock transform, the full adjoint identity,
Hilbert–Schmidt/Schatten estimates, injectivity/dense range, operator
domains, and the selfadjoint **integral-operator** commutation theorem.
In particular, proving `L_u K=L_v K` pointwise is **not** enough
to conclude `LS=SL` for unbounded selfadjoint operators.

The full list of proof obligations and domain cautions is maintained in
`ANALYTIC_AUDIT.md`.

## Reproducible verification

Uses the repository's existing `lean/` Lake package:
Lean `v4.35.0-rc3`; pinned Mathlib
`0272bbe1c093d038d7257ab15306abd58245f9ff`.

```bash
cd lean
lake update
lake exe cache get
for file in KernelCore OscillatorCore AnalyticKernel LegendreMoments EulerianFourierIntegral; do
  lake env lean "GegenbauerFock/${file}.lean"
done
```

The branch-isolated GitHub Actions workflow additionally rejects
`sorryAx` and `Lean.ofReduceBool` when reported in the audited
theorem-dependency logs. This automatic audit covers the printed
theorems, **not a claim that every imported theorem has been individually
audited**. No `sorry` or `admit` placeholders were authored in the
five modules.

A green workflow is a check of the exact branch commit recorded
on its run page, not a blanket assertion about past failed commits.
