/-
# Lean 4 / Mathlib certification of selected results of the V478 manuscript
"Sharp Fourier truncation and limaçon of Pascal approximation of the Eulerian polar curve"

Module map (statement and equation numbers of the V478 PDF):
* `EulerianCert.SignCriterion` — Lemma 3.2 (sign criterion, incl. the exact Hausdorff distance
                                  in ℂ), its truncation case (Cors 3.3, 3.9, Prop. 3.4, abstract
                                  form) and damping case (Cor. 3.11).
* `EulerianCert.Bracket`       — Remark 3.16, Eq. (91): Eulerian numbers by their recurrence,
                                  kernel evaluation of the 669/671 integer inequalities, angle
                                  comparison.
* `EulerianCert.Crossing`      — Remark 3.16: 670 < 216π − 15/2 < 672 (corrected crossing order)
                                  and 672 < 216π (the one-term estimate lies outside the bracket).
* `EulerianCert.Limacon`       — Cor. 3.8; Thm 3.12 (three-point uniqueness); Thm 3.13
                                  (endpoint containment, equality case, scalar balance, logic of
                                  the h_* certificate).
* `EulerianCert.Corner`        — Props 3.6–3.7: derivatives of r_E, Eq. (40), tangents,
                                  corner angle, Sullivan atom.
* `EulerianCert.Combinatorics` — Eq. (21) (telescoping tail bound), Lemma 3.14 (det JᵀJ = n+1),
                                  Gaussian homothety of §3.11.
* `EulerianCert.MontgomeryTaylor` — §3.11: z₀ coth z₀ = (1/√2) cot(1/√2) for z₀ = i/√2 of Eq. (4)
                                  (Montgomery–Taylor constants).
* `EulerianCert.Cyclohedral`   — companion manuscript V500 (cyclohedral zeta targets, Chebyshev
                                  strong-cycle realisations): Cor. 3.1 algebra and zero-free
                                  property, Eq. (76), Prop. 4.1 and Eq. (58), Chebyshev
                                  composition and the a = 2 factorisations of Cor. 4.5, and the
                                  two genus counts of Prop. 4.6.
-/
import EulerianCert.SignCriterion
import EulerianCert.Bracket
import EulerianCert.Crossing
import EulerianCert.Limacon
import EulerianCert.Corner
import EulerianCert.Combinatorics
import EulerianCert.MontgomeryTaylor
import EulerianCert.Cyclohedral
