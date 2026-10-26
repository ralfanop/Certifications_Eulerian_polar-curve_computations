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

- `UltrasphericalMeasure.lean`: for every `λ>0`, constructs a **concrete**
  probability measure from the symmetric Mathlib Beta distribution
  `Beta(λ+1/2, λ+1/2)` under `x ↦ 2x-1`. Proves mass one, the
  constant-function integral, and positivity of the Beta density on
  its natural support. The explicit Gamma-normalized density under
  the affine pushforward is not yet a Lean theorem.
- `RationalTrace.lean`: exact rational proof of the fifteen-term
  `λ=1/2, α=1` scalar trace-integral Taylor sum and the exact rational
  endpoint obtained by adding the separately proved analytic tail
  majorant. The infinite-series inequality and the identity to
  the Hilbert–Schmidt operator norm are **not yet Lean-certified**.
  See `V007_RATIONAL_CERTIFICATE.md`.
- `BochnerStage.lean`: actually defines the **complex scalar**
  Bochner Eulerian integral for arbitrary measure and checks linearity
  under integrability, normalization at zero frequency for a
  probability measure and norm domination. It does **not** construct
  the bounded `L²(ν_λ) → Fock_α` map or its Hilbert–Schmidt adjoint.

- `HilbertGram.lean`: **genuine** generic bounded Hilbert-space
  operator `T : E →L[ℂ] F`, its Gram `T†T`, exact quadratic form,
  self-adjointness, positivity, and compactness of Gram **conditional
  on compactness of T**.
- `L2Coefficient.lean`: actual bounded Riesz coefficient functionals
  on `Lp ℂ 2 μ`, including the exact functional norm and adjoint.
- `FiniteCoefficient.lean`: finite-rank compact bounded operators
  from `L²(μ)` into `EuclideanSpace ℂ (Fin N)`, with
  `‖T_N f‖² ≤ (∑_{n<N} ‖k_n‖²) ‖f‖²`.
- `CoherentL2.lean`: continuous globally clamped coherent exponential
  sections and their genuine L² classes over any finite measure.
- `UltrasphericalMeasure.lean` also addresses the actual almost
  everywhere support and unclamped Eulerian exponential coherent
  sections in `L²(ν_λ)`, with bounded Fourier evaluation
  functionals and their exact abstract Riesz adjoints. The
  corresponding complex integral identification is separately
  kernel-checked before being claimed complete.

**These are operator-theory building blocks, not the complete
Gegenbauer–Fock operator `C_{λ,α}: L²(ν_λ) → Fock_α`.**
In particular, the full Fock coefficient-sequence construction,
Hilbert–Schmidt identity, explicit Fock evaluation adjoint, and
infinite-rank compactness must still be proved in Lean. The generic
adjoint and compact finite truncations do not imply those conclusions
for an operator that has not yet been constructed.

All Hilbert-space construction and proof calculations for **V007**
are specified in `V007_HILBERT_PROOF_DOSSIER.md`, with their
kernel-certification status explicitly separated from the mathematical
paper-level derivations. **Nothing is to be added to or merged into V097.**

The new integral theorems use Mathlib's established proofs of
`integral_pow`, `integral_exp_mul_I_eq_sin`, and
`integral_exp_mul_I_eq_sinc`. Each module includes explicit
`#print axioms` statements for representative results.

## Current limitations

Not yet certified: the classical ultraspherical Gamma density equality and beta-integral moments at arbitrary `λ>0`, the
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
for file in KernelCore OscillatorCore AnalyticKernel LegendreMoments EulerianFourierIntegral UltrasphericalMeasure BochnerStage RationalTrace HilbertGram L2Coefficient FiniteCoefficient CoherentL2; do
  lake env lean "GegenbauerFock/${file}.lean"
done
```

The branch-isolated GitHub Actions workflow additionally rejects
`sorryAx` and `Lean.ofReduceBool` when reported in the audited
theorem-dependency logs. This automatic audit covers the printed
theorems, **not a claim that every imported theorem has been individually
audited**. No `sorry` or `admit` placeholders were authored in the
twelve modules (pending final CI verification of the most recent additions).

A green workflow is a check of the exact branch commit recorded
on its run page, not a blanket assertion about past failed commits.
