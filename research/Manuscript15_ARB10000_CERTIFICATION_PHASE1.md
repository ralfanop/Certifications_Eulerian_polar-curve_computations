# Manuscript 15 — Arb 10000-bit certification register (phase 1)

**Manuscript source:** `Manuscript15_Revision_20261111d`, 23 pages, 11 November 2026.
**Scope:** This PR adds one **independent** 10000-bit Arb evaluation and CI workflow; historical 2000/8192-bit scripts and all Manuscripts 11–14 are left untouched.

## Precision contract

- Arb working precision: **10000 bits**, explicitly asserted using `flint.ctx.prec`.
- Required certified relative accuracy: **at least 8182 bits** for each of the 14 nonzero real values.
- The result is accepted solely when `arb.rel_accuracy_bits()` meets this bound. Working precision alone is **not** a certificate.
- Figure 1's `alpha_3 ≈ 53.1301023542°` is additionally tested against its **strict decimal rounding cell** of half-width `0.5 * 10^-10` using outward-rounded Arb values.
- Only exact Python integer inputs are used. Ball overlap is labeled a consistency check, not an analytic identity proof.
- `python-flint==0.9.0`, Python 3.12 on ubuntu-24.04. Complete ball enclosures and accuracy readings appear in the GitHub Actions artifact.

## Claim-to-certificate map

The `numerics/manuscript15_arb10000.py` computation evaluates:

| Quantity | Manuscript location |
| --- | --- |
| `r_E(pi)=2/pi` | Section 2.2, Eulerian kernel |
| `vartheta_E = 2 atan(1/pi)` | Introduction and Section 2.4 |
| `d_E=8/pi^3` | Section 2.2 |
| `A_E = 2 Si(pi) - 4/pi` | Section 2.2 |
| `alpha_3=2 atan(1/2)` | Figure 1 and Eq. (26) |
| `p_gamma=atan(1/2)/pi` | Introduction / Section 2.3 |
| `r_E(i/sqrt(2))` | Special imaginary point corollary |
| `r_E(i sqrt(2))` | Special imaginary point corollary |
| `L(1)=coth(1)-1` | Langevin identity at x=1 |
| `alpha_3` degrees | Figure 1 label — rounding cell checked |
| `alpha_3/2` degrees | Plouffe/Gregory half-angle |
| `vartheta_E` degrees | Eulerian junction angle |
| `r_E(i)=2 sinh(1/2)` | Kernel / determinant specialization |
| `D(1)=sinh(1)` | Eq. (19) and Fredholm identity specialization |

**Certification status: CERTIFIED for these fourteen numerical expressions.**
The exact-source-head [GitHub Actions run 43080355596](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43080355596)
completed **SUCCESS** for script commit `811112fd4fa2210f4906489c8a025f935c7955b2`.
Its log independently reports **9996–9998 certified relative bits** across all
fourteen real expressions with `flint.ctx.prec=10000`, strictly exceeding
the 8182-bit acceptance threshold. The decimal rounding-cell test for
Figure 1's `alpha_3≈53.1301023542°` passed. All logs are available
in the workflow artifact `manuscript15-arb10000-enclosures`.

This certifies the specified numeric expressions, **not** the
underlying analytic proofs or the printed five-decimal-point
vector figure coordinates.

## Relation to Lean 4 and scope boundaries

The independent existing Lean modules (`lean/Manuscript15/CycloidalReconstruction.lean`, `CoefficientRigidity.lean`, and subsequent Fredholm bridge modules) are **not altered** here. See PRs #112, #115, #159 for the separate formalisation tracks, whose exact hypotheses and CI evidence must be audited declaration by declaration.

The present script does **not** provide Lean proofs of the analytic identities used to define the constants, does **not** certify every theorem in the 23-page manuscript, and does **not** claim exhaustive coverage of every figure ordinate or combinatorial coefficient. Finite rational Eulerian data are subject to an independent exact-integer certification track; other real-valued quantities require further inventory and interval certificates.
