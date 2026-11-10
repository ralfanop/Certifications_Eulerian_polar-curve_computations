# Manuscript 15: Gregory angle and type-B Catalan inverse-binomial series

Priority audit, 10 November 2026. Proposed placement: Section 2.3, **Preliminaries**.

## The primary published antecedent

Renzo Sprugnoli, “Sums of Reciprocals of the Central Binomial Coefficients,” *Integers* **6** (2006), #A27, Theorem 2.4, p. 5, proves
\[
A(u)=\sum_{k\ge0}\frac{(4u)^k}{(2k+1)\binom{2k}{k}}
=\frac1u\sqrt{\frac{u}{1-u}}\arctan\sqrt{\frac{u}{1-u}},\quad0<u<1.
\]
Setting \(u=1/5\) gives
\[
\arctan(1/2)=\frac25\sum_{k\ge0}
\frac{(4/5)^k}{(2k+1)\binom{2k}{k}}.
\]
This is a **direct 2006 published antecedent** of the specialised identity recorded by Peter Bala in OEIS A073000 in 2015. We do not assert it is historically the earliest occurrence.

## Other sources and precise scopes

* John H. Conway and Richard K. Guy, *The Book of Numbers*, Copernicus/Springer (1996), p. 242: \(t_n=\arctan(1/n)\), Gregory angles, and \(t_1=t_2+t_3\); **does not print the specific inverse-binomial series**.
* T. Kyle Petersen, *Eulerian Numbers*, Birkhäuser/Springer (2015), §12.3 p. 277, Table 12.2: \(\mathrm{Cat}(B_n)=\binom{2n}{n}\).
* OEIS A000984: central binomial coefficients, also termed type-B Catalan numbers.
* OEIS A073000: \(\arctan(1/2)\) and the specialised series (Peter Bala contribution 4 February 2015).
* Existing bibliography of Manuscript 11 already contains Sprugnoli 2006: reuse the same editorial convention.

## Exact independent check

\[
\frac1{(2k+1)\binom{2k}{k}}=\int_0^1s^k(1-s)^k\,ds.
\]
Tonelli (all terms nonnegative) and \(v=2s-1\) give
\[
\frac25\sum_{k\ge0}\frac{(4/5)^k}{(2k+1)\binom{2k}{k}}
=\frac25\int_0^1\frac{ds}{1-\frac45s(1-s)}
=\int_{-1}^1\frac{dv}{4+v^2}
=\arctan(1/2).
\]
Hence \(\alpha_3=2\arctan(1/2)\) and
\(p_\gamma=\arctan(1/2)/\pi\) have the exact series in the companion TeX.

## Editorial safeguards

Companion TeX contains unnumbered equations and no theorem declarations so **Theorem 3.1 remains numbered 3.1**. Place all content in Section 2.3, not the novelty section. Formatting and \`\\FilBibURL\` / \`\\FilVolume\` follow Manuscript 11. Do not duplicate the existing OEIS A073000 bibliography entry.

The latest OJAC-layout Manuscript 15 source is not present in accessible files (the PDF is accessible, and a different early LaTeX draft is present). To avoid replacing the newer 15 with an outdated source, this PR stores **insertion-ready changes**, not an edited latest 15.tex or a purported recompiled manuscript. No changes to Manuscripts 11–14, V007, V097. No merge; no Arb or Lean certificate claimed for this exact derivation.

Primary source: https://math.colgate.edu/~integers/g27/g27.pdf

Conway/Guy: https://doi.org/10.1007/978-1-4612-4072-3

Petersen: https://doi.org/10.1007/978-1-4939-3091-3

OEIS: https://oeis.org/A073000 and https://oeis.org/A000984
