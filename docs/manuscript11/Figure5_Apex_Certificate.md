# Manuscript 11 — Figure 5 exact apex-angle certification

**Date:** 10 November 2026  
**Scope:** Figure 5, page 21, of Manuscript 11; the Eulerian probability histogram for n = 3,...,670.  
**Proof commit:** [`18a1d56125efd1540b9bfd0ceb73f18bcf0f2f21`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/18a1d56125efd1540b9bfd0ceb73f18bcf0f2f21)  
**Lean CI:** [run 42865372478](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/42865372478), **success**, 2,291 build jobs; kernel axiom audit **success**.

## Statement certified

The displayed caption sentence is:

> The top vertex determined by n = 3 has angle 2 arccot(2), where arccot(2) is [18, A073000].

Here `arccot` denotes the principal positive inverse cotangent, so
`arccot(2) = arctan(1/2)`. OEIS [A073000](https://oeis.org/A073000)
is the decimal expansion of the **half-angle** `arctan(1/2)`, not of its double.

Starting from the exact Eulerian numbers `E(3,0)=1`, `E(3,1)=4`,
`E(3,2)=1`, the histogram definitions
`x_(n,k)=k/(n+1)` and `p_(n,k)=E(n,k-1)/n!`
give the three vertices

- A = (1/4, 1/6),
- V = (1/2, 2/3),
- B = (3/4, 1/6).

The outgoing vectors are VA=(-1/4,-1/2) and VB=(1/4,-1/2).
Both squared side lengths are 5/16; the half-base is 1/4 and the
height is 1/2. Thus the half-angle tangent is 1/2. Independently,
the normalized dot product gives `cos(theta)=3/5`.

The angle `theta = 2 arctan(1/2)` lies strictly in `(0,pi)`.
**This strict interval, not merely an equality for its tangent or cosine,
is essential to resolve the inverse-trigonometric branch.**

## Lean 4 / Mathlib certificates

Source: [`lean/EulerianCert/Figure5Apex.lean`](../../lean/EulerianCert/Figure5Apex.lean).
The source imports the repository's existing Eulerian recurrence
[`EulerianCert.Bracket`](../../lean/EulerianCert/Bracket.lean).

| Figure 5 claim | Kernel-checked Lean declaration |
| --- | --- |
| Eulerian row at n=3 | `eulerian_row_three` |
| Exact coordinates | `exact_vertices` |
| The two vectors | `top_to_left`, `top_to_right` |
| Equal side lengths | `equal_squared_lengths`, `equal_side_lengths` |
| Half-base and height, ratio 1/2 | `half_base_height_ratio` |
| Exact cosine 3/5 from dot product | `normalized_dot_product` |
| Principal half-angle and cosine identities | `tan_half_apex`, `cos_apex` |
| Strict internal-angle interval | `apex_angle_mem_open_interval` |
| Uniqueness using cosine on (0,pi) | `unique_internal_angle_of_cos` |
| Uniqueness using principal arctangent on the half-angle | `unique_internal_angle_of_half_tan` |
| Identity with principal arccot(2) | `apex_angle_eq_twice_arccot_two` |

Compiler/toolchain: Lean `v4.35.0-rc3` and Mathlib
`0272bbe1c093d038d7257ab15306abd58245f9ff`, pinned in `lean/`.
The successful job runs `lake build EulerianCert.Figure5Apex` and
`lake env lean Figure5ApexAxioms.lean`, using
[`lean/Figure5ApexAxioms.lean`](../../lean/Figure5ApexAxioms.lean).
The audit of the ten named certificates reports only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or `Lean.ofReduceBool`.
The CI logs are attached to the linked run.

## Isometric-axis qualification

The mathematical angle follows from the **data coordinates**, rather
than measurements of the graphic. For the claim about the actual
rendered figure, the author's source
`FIGURES/Figure5_Eulerian_Isometric_TikZ.tex` was examined from
`Manuscript_11_Figure5_EDGE_TO_EDGE_20261110(1).zip`.

Its SHA-256 is
`0e001405d2165a29602964b5d890337d52667c3029f5f5d83fe0bce684935cc1`.

The n=3 TikZ vertex coordinates are
A=(118.87500 pt,128.41667 pt),
V=(247.00000 pt,384.66667 pt),
B=(375.12500 pt,128.41667 pt).
Both horizontal and vertical physical scales are **512.5 pt per data unit**.
The parent LaTeX uses `\\resizebox{\\textwidth}{!}{...}`,
which preserves the common scale factor.

A reproducible source-hash-bound check is
[`numerics/manuscript11_figure5_isometry.py`](../../numerics/manuscript11_figure5_isometry.py).
It checks the author's supplied TikZ source; it is a *source-layout*
check, not an additional Lean theorem or Arb ball computation.
The source coordinates are stored to five decimal places.

## Numerical certification

**No new Arb numerical certificate is required or claimed.**
All input probabilities, scalar products and length ratios are exact
rationals. The angle is certified symbolically in Lean using
trigonometric identities and strict interval/branch conditions.

## Bibliographic relationship

The histogram extends the classical illustration in Philippe Flajolet
and Robert Sedgewick, *Analytic Combinatorics* (Cambridge University
Press, 2009), Figure IX.14, page 695, from `n=3,...,60` to
`n=3,...,670`. This certification concerns the apex associated
with **n=3**, not a new complete audit of every plotted vertex.

The historical manuscript-wide record
[`Manuscript11_Certification.pdf`](Manuscript11_Certification.pdf)
at commit `3282b7f4` remains unchanged.
