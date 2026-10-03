/-
# Lean 4 / Mathlib certification of selected results of the V478 manuscript
"Sharp Fourier truncation and limaçon of Pascal approximation of the Eulerian polar curve"

Module map (statement and equation numbers of the V478 PDF):
* `EulerianCert.SignCriterion` — Lemma 3.2 (sign criterion, incl. the exact Hausdorff distance
                                  in ℂ), its truncation case (Cors 3.3, 3.9, Prop. 3.4, abstract
                                  form) and damping case (Cor. 3.11).
* `EulerianCert.Bracket`       — Remark 3.15, Eq. (80): Eulerian numbers by their recurrence,
                                  kernel evaluation of the 669/671 integer inequalities, angle
                                  comparison.
* `EulerianCert.Limacon`       — Cor. 3.8; Thm 3.12 (three-point uniqueness); Thm 3.13
                                  (endpoint containment, equality case, scalar balance, logic of
                                  the h_* certificate).
* `EulerianCert.Corner`        — Props 3.6–3.7: derivatives of r_E, Eq. (40), tangents,
                                  corner angle, Sullivan atom.
* `EulerianCert.Combinatorics` — Eq. (21) (telescoping tail bound), Lemma 3.14 (det JᵀJ = n+1),
                                  Gaussian homothety of §3.11.
-/
import EulerianCert.SignCriterion
import EulerianCert.Bracket
import EulerianCert.Limacon
import EulerianCert.Corner
import EulerianCert.Combinatorics
