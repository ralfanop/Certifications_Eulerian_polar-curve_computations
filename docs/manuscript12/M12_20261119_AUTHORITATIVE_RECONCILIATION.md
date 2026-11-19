# Manuscript 12 — authoritative source reconciliation, 19 November 2026

**Provisional audit supplement, not a claim of complete certification.** The manuscript itself is untouched.

## Source identity and editorial inventory

All three author-supplied archives named Manoscritto_12_20261118.zip, Manoscritto_12_20261118(2).zip and Manoscritto_12_20261118(3).zip have identical SHA-256 `7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860`. Each contains one TeX, one manuscript PDF and one vector-figure PDF. The compiled PDF has 69 pages; its named destinations are exactly equation.1 through equation.293. The source contains 293 numbered rows (accounting for OJACrow, empheq, flalign, multline and nonumber), 287 semantic equation labels and six unlabeled displays. All 41 bibliography entries are cited; no missing citation key, duplicate source label or undefined literal ref/eqref was found by static inspection. Section 10 is now Discussion and 11 is Conclusions; the old Section 10 is removed. Appendix A now has equations (279)–(293). No new compilation is asserted; pdfTeX format was unavailable in the audit environment.

## Evidence and outstanding gates

| Check | Verified run | Number of successful interval checks | Minimum relative bits |
|---|---|---:|---:|
| Original M12 scalar checks | [#318](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43701995391/job/132774933850) | 8 | 3479992 |
| Additional scalar checks | [#384](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44312456543/job/134829827657) | 20 | 3599995 |
| Lanczos M=100 | [#386](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167/job/134831845524) | 5 | 3597107 |
| Lanczos M=200 | [#386](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167/job/134831845297) | 5 | 3593431 |
| Lanczos M=400 | [#386](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167/job/134831845496) | 5 | 3585280 |
| Rabotnov and critical law | [#416](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44482708756/job/135418551581) | 9 | 3599996 |

All 52 checks are at 3,600,000 working bits and pass the strict 1,000,001 significant-digit rounding criterion. These are checks, not 52 necessarily distinct constants or 52 symbolic proofs. For #416 the nine checks additionally pass strict 1,000,001 **fixed decimal places** on exact dyadic endpoints. The other 43 are not yet asserted to satisfy that separate condition. See [#416 artifact](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44482708756/artifacts/14508409529) and the three [#386 artifacts](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44313014167).

Table 1: all 15 finite Lanczos inputs verified, not additional printed cells. Five profile quadratures (t=1/4,1/2,1,2,4) remain pending at full precision: [#385 exact-head workflow](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44312820714) has five successful 256-bit pilots and five cancelled 3.6M-bit jobs. [#390](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44315118699) all four interval-Newton benchmarks (1024/4096 bits) succeeded, not full precision. [#412](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44464418346) is a 256-bit regression only. Twenty derived printed error cells await all five certified profile values and execution of the #387 combiner. Therefore Table 1 is not fully certified at the required precision.

## Lean 4 reconciliation

Historical record at [3282b7f4](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/3282b7f41fd8b9bdf09e5e5142ee6b721e0bf8dd/docs/manuscript12/Manuscript12_Certification.md) and [Bridge map](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/main/lean/EulerianGrothendieck/README_Bridge_V173.md) remain historical evidence for the retained mathematics. Never promote a historical equation number alone to an exact current match.

- Sections 3 and 4 retain the equation numbers (16)–(56) and (59)–(70) cited by Bridge. The current (56) is the convolution identity, **not** the superseded Krapivsky–Luck (56a–c) block in #328. #328 CI succeeded but the named Krapivsky–Luck material is absent from this authoritative TeX; do not claim new coverage from that PR without semantic matching.
- The Section 5 saddle inputs (114)–(119), the seven profile terms (143) and remainder (149) retain their numbers.
- Historical Bridge numbers (152)–(156), (163), (165)–(173), (174)–(179) correspond respectively to current (155)–(159), (166), (168)–(176), (177)–(182), i.e. +3 in those verified ranges. Preserve stated classical hypotheses (Plancherel, cited Eker–Ece criterion, Floater, Levin–Lubinsky, Vourdas, etc.).
- In Section 9, actual norm (187), all-order coefficient majorant (224), explicit constant (229), special scale (246), and expansions (276)–(278) are identified by the current source. Historical projector (253) is now (252); historical critical law (274) is now (273). Do not assert a whole-section uniform offset.
- Appendix A historical (287)–(301) maps to current (279)–(293), by the consecutive identities and labels. For example old (290) moments sum is now (282), and old (301) Gaussian moment is now (293).
- Exclude removed Proposition 10.1 and removed quadratic-character modulo 5 corollary from the current coverage record. Retained independently cited Dirichlet beta/eta and Lambertian quantities are not deleted as collateral.
- Historical audit reports disagree in theorem counts (821 vs 849 in Bridge documentation); resolve using a fresh exact-HEAD audit and declaration types, not by adding historical counts.
- The document's Data Availability link still points to the old pinned record; do not change it to a purported final certificate until the numerical release gates and the exact current statement-to-declaration audit have passed.

## Equation index

This exhaustive index is a source/PDF reconciliation, not an assertion that each entry has a separate Lean theorem or Arb value. Six unlabeled displays are marked `-`. Source line means the beginning of the display block (multiple rows may share it). Page is the actual PDF destination. It is a basis for the remaining per-statement Lean declaration-type matching, hypothesis audit and numerical inventory.

| Eq. | Section | TeX label | PDF page | TeX display starts at line |
|---:|---|---|---:|---:|
| 1 | 1 | `eq:profile` | 4 | 575 |
| 2 | 2 | `eq:entire` | 5 | 594 |
| 3 | 2 | `eq:B-factor` | 5 | 598 |
| 4 | 2 | `eq:endpoint` | 6 | 603 |
| 5 | 2 | `eq:endpoint-part2` | 6 | 603 |
| 6 | 2 | `eq:endpoint-part3` | 6 | 603 |
| 7 | 2 | `eq:buffon-eulerian-value` | 7 | 609 |
| 8 | 2 | `eq:plouffe-general` | 7 | 613 |
| 9 | 2 | `eq:plouffe-euler-angle` | 7 | 613 |
| 10 | 2 | `eq:derivs` | 7 | 624 |
| 11 | 2 | `eq:triangle-density-eulerian` | 7 | 630 |
| 12 | 2 | `eq:dE` | 7 | 638 |
| 13 | 2 | `eq:valean-triple-eulerian` | 8 | 647 |
| 14 | 2 | `eq:valean-double-eulerian` | 8 | 655 |
| 15 | 3 | `eq:quantum-uniform-state` | 9 | 682 |
| 16 | 3 | `eq:quantum-uniform-normalisation` | 9 | 682 |
| 17 | 3 | `eq:quantum-eulerian-momentum` | 9 | 691 |
| 18 | 3 | `eq:quantum-momentum-normalisation` | 9 | 691 |
| 19 | 3 | `eq:fock-space` | 10 | 719 |
| 20 | 3 | `eq:kernel-norm` | 10 | 725 |
| 21 | 3 | `eq:kernel-r` | 10 | 733 |
| 22 | 3 | `eq:kernel-G` | 10 | 733 |
| 23 | 3 | `eq:fock-upper` | 10 | 744 |
| 24 | 3 | `eq:exact-fock-norm` | 11 | 755 |
| 25 | 3 | `eq:exact-G-norm` | 11 | 755 |
| 26 | 3 | `eq:moments` | 11 | 765 |
| 27 | 3 | `eq:segal-input` | 11 | 787 |
| 28 | 3 | `eq:segal-result` | 11 | 792 |
| 29 | 3 | `eq:segal-def` | 11 | 802 |
| 30 | 3 | `eq:bargmann-input` | 12 | 819 |
| 31 | 3 | `eq:segal-isolated-constant` | 12 | 823 |
| 32 | 3 | `eq:bargmann-melzak-product` | 12 | 828 |
| 33 | 3 | `eq:segal-isolated-profile` | 12 | 835 |
| 34 | 3 | `eq:quantum-frame-map` | 13 | 882 |
| 35 | 3 | `eq:quantum-frame-projections` | 13 | 887 |
| 36 | 3 | `eq:quantum-frame-eulerian` | 13 | 892 |
| 37 | 3 | `eq:poly-operators` | 14 | 933 |
| 38 | 3 | `eq:poly-ladder-def` | 14 | 947 |
| 39 | 3 | `eq:poly-ladder-orthogonality` | 14 | 947 |
| 40 | 3 | `eq:poly-raising-lowering` | 14 | 961 |
| 41 | 3 | `eq:poly-raising-lowering-part2` | 14 | 961 |
| 42 | 3 | `eq:poly-raising-lowering-part3` | 14 | 961 |
| 43 | 3 | `eq:poly-exact-order` | 14 | 978 |
| 44 | 3 | `eq:poly-exact-order-part2` | 14 | 978 |
| 45 | 3 | `eq:poly-fock-isometry` | 15 | 987 |
| 46 | 3 | `eq:poly-shi-norm` | 15 | 1005 |
| 47 | 3 | `eq:pw-fourier-convention` | 15 | 1032 |
| 48 | 3 | `eq:pw-fourier-inverse` | 15 | 1032 |
| 49 | 3 | `eq:pw-space-def` | 16 | 1038 |
| 50 | 3 | `eq:pw-kernel` | 16 | 1052 |
| 51 | 3 | `eq:pw-norm` | 16 | 1058 |
| 52 | 3 | `eq:pw-basis` | 16 | 1065 |
| 53 | 3 | `eq:pw-sampling` | 16 | 1071 |
| 54 | 3 | `eq:pw-parseval` | 16 | 1071 |
| 55 | 3 | `eq:pw-projector` | 17 | 1102 |
| 56 | 3 | `eq:pw-convolution` | 17 | 1107 |
| 57 | 4 | `eq:M-def` | 18 | 1140 |
| 58 | 4 | `eq:A-def` | 18 | 1145 |
| 59 | 4 | `eq:bernoulli-two` | 18 | 1153 |
| 60 | 4 | `eq:bernoulli-two-part2` | 18 | 1153 |
| 61 | 4 | `eq:bernoulli-two-part3` | 18 | 1153 |
| 62 | 4 | `eq:bernoulli-moment` | 18 | 1159 |
| 63 | 4 | `eq:bernoulli-plus` | 18 | 1168 |
| 64 | 4 | `eq:bernoulli-minus` | 19 | 1168 |
| 65 | 4 | `eq:M-duplication` | 19 | 1176 |
| 66 | 4 | `eq:M-duplication-part2` | 19 | 1176 |
| 67 | 4 | `eq:sech-operator` | 19 | 1181 |
| 68 | 4 | `eq:sech-euler-polynomials` | 19 | 1185 |
| 69 | 4 | `eq:euler-poly-gf` | 19 | 1189 |
| 70 | 4 | `eq:euler-comparison` | 19 | 1196 |
| 71 | 5 | `eq:conv-definition` | 20 | 1227 |
| 72 | 5 | `eq:lanczos-recurrence` | 21 | 1236 |
| 73 | 5 | `eq:lanczos-recurrence-part2` | 21 | 1236 |
| 74 | 5 | `eq:lanczos-recurrence-part3` | 21 | 1236 |
| 75 | 5 | `eq:lanczos-main` | 21 | 1248 |
| 76 | 5 | `eq:lanczos-mgf` | 21 | 1260 |
| 77 | 5 | `eq:lanczos-cumulant` | 21 | 1265 |
| 78 | 5 | `eq:lanczos-hermite-functional` | 21 | 1278 |
| 79 | 5 | `eq:lanczos-gram` | 22 | 1286 |
| 80 | 5 | `eq:lanczos-gram-origin` | 22 | 1292 |
| 81 | 5 | `eq:lanczos-determinant-jet` | 22 | 1299 |
| 82 | 5 | `eq:lanczos-norm-determinant` | 22 | 1305 |
| 83 | 5 | `eq:lanczos-exact-remainder` | 22 | 1311 |
| 84 | 5 | `eq:lanczos-jacobi-asymptotic` | 22 | 1330 |
| 85 | 5 | `eq:lanczos-low-degrees` | 22 | 1336 |
| 86 | 5 | `eq:lanczos-low-degrees-part2` | 23 | 1336 |
| 87 | 5 | `eq:ul-SM` | 23 | 1351 |
| 88 | 5 | `eq:ul-SM-part2` | 23 | 1351 |
| 89 | 5 | `eq:ul-SM-part3` | 23 | 1351 |
| 90 | 5 | `eq:ul-A` | 23 | 1357 |
| 91 | 5 | `eq:ul-Lambda` | 23 | 1357 |
| 92 | 5 | `eq:ul-Lambdaprime` | 23 | 1362 |
| 93 | 5 | `eq:ul-Lambdaprime-part2` | 23 | 1362 |
| 94 | 5 | `eq:ul-I` | 24 | 1367 |
| 95 | 5 | `eq:ul-I-part2` | 24 | 1367 |
| 96 | 5 | `eq:ul-I-part3` | 24 | 1367 |
| 97 | 5 | `eq:ul-I-part4` | 24 | 1367 |
| 98 | 5 | `eq:ul-Phi` | 24 | 1374 |
| 99 | 5 | `eq:ul-Phi-part2` | 24 | 1374 |
| 100 | 5 | `eq:ul-F` | 24 | 1380 |
| 101 | 5 | `eq:ul-MRS` | 25 | 1386 |
| 102 | 5 | `eq:ul-MRS-part2` | 25 | 1386 |
| 103 | 5 | `eq:ul-LLrec` | 25 | 1391 |
| 104 | 5 | `eq:ul-LLrec-part2` | 25 | 1391 |
| 105 | 5 | `eq:ul-LL134` | 25 | 1396 |
| 106 | 5 | `eq:ul-LL134-part2` | 25 | 1396 |
| 107 | 5 | `eq:ul-Lambdabounds` | 26 | 1406 |
| 108 | 5 | `eq:ul-Lambdabounds-part2` | 26 | 1406 |
| 109 | 5 | `eq:ul-Lambdabounds-part3` | 26 | 1406 |
| 110 | 5 | `eq:ul-Ibounds` | 26 | 1412 |
| 111 | 5 | `eq:ul-hyp` | 26 | 1419 |
| 112 | 5 | `eq:ul-Phislope` | 26 | 1427 |
| 113 | 5 | `eq:ul-Phidiv` | 27 | 1434 |
| 114 | 5 | `eq:ul-eta` | 27 | 1443 |
| 115 | 5 | `eq:ul-saddle` | 27 | 1447 |
| 116 | 5 | `eq:ul-Adecay` | 27 | 1455 |
| 117 | 5 | `eq:ul-rep` | 27 | 1459 |
| 118 | 5 | `eq:ul-rep-part2` | 27 | 1459 |
| 119 | 5 | `eq:ul-rep-part3` | 28 | 1459 |
| 120 | 5 | `eq:ul-dchi` | 28 | 1465 |
| 121 | 5 | `eq:ul-outer` | 28 | 1471 |
| 122 | 5 | `eq:ul-Psi` | 28 | 1475 |
| 123 | 5 | `eq:ul-Psi-part2` | 28 | 1475 |
| 124 | 5 | `eq:ul-cancel` | 28 | 1484 |
| 125 | 5 | `eq:ul-cancel-part2` | 28 | 1484 |
| 126 | 5 | `eq:ul-cancel-part3` | 29 | 1484 |
| 127 | 5 | `eq:ul-w` | 29 | 1490 |
| 128 | 5 | `eq:ul-w-part2` | 29 | 1490 |
| 129 | 5 | `eq:ul-expansion` | 29 | 1495 |
| 130 | 5 | `eq:ul-expansion-part2` | 29 | 1495 |
| 131 | 5 | `eq:ul-JM` | 29 | 1500 |
| 132 | 5 | `eq:ul-JM-part2` | 29 | 1500 |
| 133 | 5 | `eq:ul-endpointest` | 30 | 1518 |
| 134 | 5 | `eq:ul-Phiclose` | 30 | 1525 |
| 135 | 5 | `eq:ul-QjM` | 30 | 1533 |
| 136 | 5 | `eq:ul-QjM-part2` | 30 | 1533 |
| 137 | 5 | `eq:ul-QjM-part3` | 30 | 1533 |
| 138 | 5 | `eq:ul-MRSbox` | 31 | 1541 |
| 139 | 5 | `eq:ul-Lip` | 31 | 1548 |
| 140 | 5 | `eq:ul-MRSreduce` | 31 | 1552 |
| 141 | 5 | `eq:ul-main` | 31 | 1561 |
| 142 | 5 | `eq:ul-scaling` | 32 | 1568 |
| 143 | 5 | `eq:ul-Fseries` | 32 | 1579 |
| 144 | 5 | `eq:ul-Iseries` | 32 | 1586 |
| 145 | 5 | `eq:ul-Phiseries` | 32 | 1590 |
| 146 | 5 | `eq:ul-Lp-taylor` | 33 | 1594 |
| 147 | 5 | `eq:ul-Ip-remainder` | 33 | 1598 |
| 148 | 5 | `eq:ul-Phi-remainder` | 33 | 1602 |
| 149 | 5 | `eq:ul-Fseries-cert` | 33 | 1606 |
| 150 | 5 | `eq:ul-conj2` | 33 | 1613 |
| 151 | 6 | `eq:q-def` | 34 | 1625 |
| 152 | 6 | `eq:q-sech` | 34 | 1633 |
| 153 | 6 | `eq:q-expansion` | 35 | 1641 |
| 154 | 6 | `eq:q-expansion-4` | 35 | 1641 |
| 155 | 6 | `eq:mellin-1` | 35 | 1652 |
| 156 | 6 | `eq:mellin-2` | 35 | 1652 |
| 157 | 6 | `eq:beta2-moment` | 35 | 1659 |
| 158 | 6 | `eq:beta3-moment` | 35 | 1659 |
| 159 | 6 | `eq:zeta3-moment` | 35 | 1659 |
| 160 | 6 | `eq:sech-exponential` | 36 | 1668 |
| 161 | 6 | `eq:mellin-expanded` | 36 | 1674 |
| 162 | 6 | `eq:det-mellin` | 36 | 1685 |
| 163 | 6 | `eq:radius-mellin` | 37 | 1692 |
| 164 | 6 | `eq:beta-zeta-unified` | 37 | 1702 |
| 165 | 6 | `eq:beta-zeta-unified-part2` | 37 | 1702 |
| 166 | 6 | `eq:sech-characteristic` | 37 | 1715 |
| 167 | 7 | `eq:blagouchine` | 38 | 1728 |
| 168 | 7 | `eq:malmsten-q` | 38 | 1738 |
| 169 | 7 | `eq:malmsten-I2` | 38 | 1745 |
| 170 | 7 | `eq:malmsten-dE` | 38 | 1745 |
| 171 | 7 | `eq:catalan-malmsten` | 39 | 1755 |
| 172 | 7 | `eq:catalan-q` | 39 | 1761 |
| 173 | 8 | `eq:rabotnov-eulerian` | 39 | 1773 |
| 174 | 8 | `eq:rabotnov-pi` | 39 | 1779 |
| 175 | 8 | `eq:rabotnov-negpi` | 39 | 1779 |
| 176 | 8 | `eq:rabotnov-ratio` | 40 | 1779 |
| 177 | 9 | `eq:vourdas-overlap` | 41 | 1800 |
| 178 | 9 | `eq:vourdas-projection-trace` | 41 | 1808 |
| 179 | 9 | `eq:vourdas-trace-proof` | 41 | 1816 |
| 180 | 9 | `eq:sigma` | 42 | 1828 |
| 181 | 9 | `eq:sigma-one` | 42 | 1833 |
| 182 | 9 | `eq:sigma-euler` | 42 | 1833 |
| 183 | 9 | `eg:eq:uniform-even` | 42 | 1854 |
| 184 | 9 | `eg:eq:uniform-odd` | 42 | 1854 |
| 185 | 9 | `eg:eq:uniform-variance` | 42 | 1854 |
| 186 | 9 | `eg:eq:uniform-kappa4` | 43 | 1854 |
| 187 | 9 | `eg:eq:norm` | 43 | 1864 |
| 188 | 9 | `eg:eq:restored-01` | 43 | 1875 |
| 189 | 9 | `eg:eq:restored-02` | 43 | 1885 |
| 190 | 9 | `eg:eq:rho` | 43 | 1890 |
| 191 | 9 | `eg:eq:occupancy` | 44 | 1899 |
| 192 | 9 | `eg:eq:momentbound` | 44 | 1903 |
| 193 | 9 | `eg:eq:restored-03` | 44 | 1912 |
| 194 | 9 | `eg:eq:restored-04` | 44 | 1918 |
| 195 | 9 | `eg:eq:restored-05` | 44 | 1922 |
| 196 | 9 | `eg:eq:restored-06` | 44 | 1926 |
| 197 | 9 | `eg:eq:squarebound` | 45 | 1934 |
| 198 | 9 | `eg:eq:restored-07` | 45 | 1941 |
| 199 | 9 | `eg:eq:FA` | 45 | 1949 |
| 200 | 9 | `eg:eq:Bexplicit` | 45 | 1949 |
| 201 | 9 | `eg:eq:explicitnorm` | 45 | 1959 |
| 202 | 9 | `-` | 45 | 1963 |
| 203 | 9 | `eg:eq:23proved` | 45 | 1963 |
| 204 | 9 | `eg:eq:restored-08` | 45 | 1973 |
| 205 | 9 | `eg:eq:restored-09` | 46 | 1978 |
| 206 | 9 | `eg:eq:restored-10` | 46 | 1982 |
| 207 | 9 | `eg:eq:inversebound` | 46 | 1987 |
| 208 | 9 | `eg:eq:restored-11` | 46 | 1996 |
| 209 | 9 | `eg:eq:pinf` | 46 | 2003 |
| 210 | 9 | `eg:eq:restored-12` | 47 | 2017 |
| 211 | 9 | `eg:eq:restored-13` | 47 | 2021 |
| 212 | 9 | `eg:eq:restored-14` | 47 | 2028 |
| 213 | 9 | `-` | 47 | 2032 |
| 214 | 9 | `-` | 47 | 2032 |
| 215 | 9 | `-` | 47 | 2032 |
| 216 | 9 | `-` | 48 | 2032 |
| 217 | 9 | `eg:eq:restored-15` | 48 | 2047 |
| 218 | 9 | `eg:eq:restored-16` | 48 | 2063 |
| 219 | 9 | `eg:eq:Pformal` | 49 | 2068 |
| 220 | 9 | `eg:eq:Pformal-recurrence` | 49 | 2073 |
| 221 | 9 | `eg:eq:gq` | 49 | 2077 |
| 222 | 9 | `eg:eq:qconvolution` | 49 | 2077 |
| 223 | 9 | `eg:eq:exactpoly` | 49 | 2084 |
| 224 | 9 | `eg:eq:majorant` | 49 | 2098 |
| 225 | 9 | `eg:eq:majorant-q` | 49 | 2098 |
| 226 | 9 | `eg:eq:restored-17` | 50 | 2109 |
| 227 | 9 | `eg:eq:restored-18` | 50 | 2118 |
| 228 | 9 | `eg:eq:allnorm` | 50 | 2122 |
| 229 | 9 | `eg:eq:CN` | 50 | 2127 |
| 230 | 9 | `eg:eq:small-k-tail` | 50 | 2136 |
| 231 | 9 | `eg:eq:restored-small-k` | 50 | 2136 |
| 232 | 9 | `eg:eq:restored-19` | 51 | 2146 |
| 233 | 9 | `eg:eq:restored-20` | 51 | 2157 |
| 234 | 9 | `eg:eq:DR` | 51 | 2157 |
| 235 | 9 | `eg:eq:SR` | 51 | 2157 |
| 236 | 9 | `eg:eq:allprob` | 51 | 2166 |
| 237 | 9 | `eg:eq:restored-21` | 51 | 2176 |
| 238 | 9 | `eg:eq:restored-22` | 52 | 2185 |
| 239 | 9 | `eg:eq:beta1` | 52 | 2185 |
| 240 | 9 | `eg:eq:d1` | 52 | 2185 |
| 241 | 9 | `eg:eq:restored-23` | 52 | 2202 |
| 242 | 9 | `eg:eq:restored-24` | 52 | 2207 |
| 243 | 9 | `eg:eq:restored-25` | 53 | 2211 |
| 244 | 9 | `eg:eq:restored-26` | 53 | 2220 |
| 245 | 9 | `eg:eq:restored-27` | 53 | 2226 |
| 246 | 9 | `eg:eq:D12` | 53 | 2237 |
| 247 | 9 | `eg:eq:Eulerphase` | 53 | 2246 |
| 248 | 9 | `eg:eq:Eulerphase-z` | 54 | 2246 |
| 249 | 9 | `eg:eq:Eulerphase-sine` | 54 | 2246 |
| 250 | 9 | `eg:eq:restored-28` | 54 | 2255 |
| 251 | 9 | `eg:eq:Kgram` | 54 | 2255 |
| 252 | 9 | `eg:eq:Pprojection` | 54 | 2255 |
| 253 | 9 | `eg:eq:VVdagger` | 54 | 2264 |
| 254 | 9 | `eg:eq:VVdagger-det` | 54 | 2264 |
| 255 | 9 | `eg:eq:restored-29` | 54 | 2275 |
| 256 | 9 | `eg:eq:gdef` | 54 | 2279 |
| 257 | 9 | `eg:eq:restored-30` | 55 | 2283 |
| 258 | 9 | `eg:eq:restored-31` | 55 | 2288 |
| 259 | 9 | `eg:eq:qexact` | 55 | 2292 |
| 260 | 9 | `eg:eq:qratio` | 55 | 2292 |
| 261 | 9 | `eg:eq:restored-32` | 55 | 2307 |
| 262 | 9 | `-` | 56 | 2317 |
| 263 | 9 | `eg:eq:lambda` | 56 | 2331 |
| 264 | 9 | `eg:eq:lambda-min` | 56 | 2331 |
| 265 | 9 | `eg:eq:Dproved` | 56 | 2339 |
| 266 | 9 | `eg:eq:restored-33` | 56 | 2345 |
| 267 | 9 | `eg:eq:restored-33b` | 56 | 2345 |
| 268 | 9 | `eg:eq:restored-34` | 57 | 2352 |
| 269 | 9 | `eg:eq:restored-34b` | 57 | 2352 |
| 270 | 9 | `eg:eq:L-uniform-remainder` | 57 | 2359 |
| 271 | 9 | `eg:eq:L` | 57 | 2359 |
| 272 | 9 | `eg:eq:restored-35` | 57 | 2367 |
| 273 | 9 | `eg:eq:15proved` | 57 | 2376 |
| 274 | 9 | `eg:eq:restored-36` | 58 | 2384 |
| 275 | 9 | `eg:eq:restored-37` | 58 | 2390 |
| 276 | 9 | `eg:eq:expanded-cumulants` | 58 | 2408 |
| 277 | 9 | `eg:eq:expanded-norm` | 59 | 2426 |
| 278 | 9 | `eg:eq:expanded-vacuum` | 59 | 2442 |
| 279 | A | `eq:A058962-ogf` | 62 | 2490 |
| 280 | A | `eq:A058962-egf` | 63 | 2494 |
| 281 | A | `eq:A058962-rec` | 63 | 2498 |
| 282 | A | `eq:moments-log3` | 63 | 2502 |
| 283 | A | `eq:gudermannian` | 63 | 2506 |
| 284 | A | `eq:lambertian` | 63 | 2510 |
| 285 | A | `eq:lambertian-45` | 63 | 2514 |
| 286 | A | `eq:lambertian-345` | 64 | 2518 |
| 287 | A | `eq:moments-semifactorial` | 64 | 2522 |
| 288 | A | `eq:central-binomial-semifactorial` | 64 | 2526 |
| 289 | A | `eq:catalan-semifactorial` | 64 | 2530 |
| 290 | A | `eq:moments-uniform` | 64 | 2534 |
| 291 | A | `eq:moments-arcsine` | 64 | 2538 |
| 292 | A | `eq:moments-semicircle` | 64 | 2542 |
| 293 | A | `eq:moments-gaussian` | 65 | 2546 |
