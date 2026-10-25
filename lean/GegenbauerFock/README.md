# Gegenbauer–Fock Lean proof development (draft)

**Status: submitted for CI compilation, not yet certified.**

These modules are deliberately isolated from the accepted Eulerian/V478
certificates. They add no axioms, sorry or admit and do not alter the existing
library imports or main-branch files.

## Scope

- `KernelCore.lean`: algebraic kernel balance, differential symbols,
  finite Gram positivity, coefficient recurrences, Legendre/Jacobi examples.
- `OscillatorCore.lean`: coefficient-array Weyl algebra for two commuting
  bosonic modes and the degeneracy of the first-mode vacuum.

## What is NOT claimed

No Lean proof of the integral operator, weighted Gegenbauer measure,
adjoint, dense range, compactness/Hilbert–Schmidt/Schatten classes,
unbounded operator domains, selfadjointness or global Sturm–Liouville
commutation has yet been supplied. These are separate analytic obligations.

## Toolchain

Use the **existing** repository Lean project under `lean/`:
Lean `v4.35.0-rc3`, Mathlib revision
`0272bbe1c093d038d7257ab15306abd58245f9ff`.

### Check explicitly

```bash
cd lean
lake update
lake exe cache get
lake env lean GegenbauerFock/KernelCore.lean
lake env lean GegenbauerFock/OscillatorCore.lean
```

A GitHub Actions workflow is included to attempt this check on the
dedicated branch and pull request. Successful CI is required before
calling these theorem statements *kernel-checked*. No merge to main
is intended without author approval.
