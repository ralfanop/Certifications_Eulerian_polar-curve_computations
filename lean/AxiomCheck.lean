/-
Prints the axioms on which the main results depend.  Expected output for every theorem:
`[propext, Classical.choice, Quot.sound]` (the standard axioms of Lean/Mathlib), or a subset.
No `sorryAx`, no `Lean.ofReduceBool` (i.e. no `native_decide`).
Run with:  lake env lean AxiomCheck.lean
-/
import EulerianCert

open EulerianCert

-- Lemma 3.2 and its cases
#print axioms EulerianCert.common_endpoint_sign_criterion
#print axioms EulerianCert.sign_criterion
#print axioms EulerianCert.damping
-- Remark 3.15
#print axioms EulerianCert.Bracket.E_one_zero
#print axioms EulerianCert.Bracket.E_eq_zero_of_le
#print axioms EulerianCert.Bracket.E_succ_zero
#print axioms EulerianCert.Bracket.E_succ
#print axioms EulerianCert.Bracket.c669_lt
#print axioms EulerianCert.Bracket.c671_gt
#print axioms EulerianCert.Bracket.diffs_pos
#print axioms EulerianCert.Bracket.rowsum669
#print axioms EulerianCert.Bracket.rowsum671
#print axioms EulerianCert.Bracket.angle_bracket
#print axioms EulerianCert.Crossing.crossing_bracket
#print axioms EulerianCert.Crossing.one_term_outside
-- Corollary 3.8, Theorems 3.12-3.13
#print axioms EulerianCert.Limacon.limacon_numerator_pos
#print axioms EulerianCert.Limacon.convexity_chain
#print axioms EulerianCert.Limacon.c_sub_two_m_pos
#print axioms EulerianCert.Limacon.affine_unique
#print axioms EulerianCert.Limacon.endpoint_containment
#print axioms EulerianCert.Limacon.endpoint_containment_strict
#print axioms EulerianCert.Limacon.endpoint_equalities
#print axioms EulerianCert.Limacon.balance_unique
#print axioms EulerianCert.Limacon.balance_lower
#print axioms EulerianCert.Limacon.balance_bracket
#print axioms EulerianCert.Limacon.balance_lt
-- Propositions 3.6-3.7
#print axioms EulerianCert.Corner.hasDerivAt_rE
#print axioms EulerianCert.Corner.hasDerivAt_rE'
#print axioms EulerianCert.Corner.rE'_pi
#print axioms EulerianCert.Corner.curvature_numerator
#print axioms EulerianCert.Corner.curvature_numerator_pos
#print axioms EulerianCert.Corner.tangent_minus
#print axioms EulerianCert.Corner.tangent_plus
#print axioms EulerianCert.Corner.tan_half_varthetaE
#print axioms EulerianCert.Corner.arctan_inv_pi
#print axioms EulerianCert.Corner.sullivan_atom
#print axioms EulerianCert.Corner.unit_tangents
#print axioms EulerianCert.Corner.speed_at_corner
-- Eq. (21), Lemma 3.14, Gaussian homothety
#print axioms EulerianCert.Combinatorics.hasSum_telescope
#print axioms EulerianCert.Combinatorics.tail_bound
#print axioms EulerianCert.Combinatorics.tail_bound_strict
#print axioms EulerianCert.Combinatorics.det_JtJ
#print axioms EulerianCert.Combinatorics.gaussian_homothety
