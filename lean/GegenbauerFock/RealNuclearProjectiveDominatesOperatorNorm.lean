import GegenbauerFock.RealNuclearInfimumDominatesOperatorNorm

/-!
# V007 — real projective nuclear norm: nonnegativity and a canonical alias

The sharp estimate `‖T‖ ≤ realNuclearInfimum T` for arbitrary
nuclear real Hilbert operators (including nonnormal ones) has already
been independently kernel-certified in
`RealNuclearInfimumDominatesOperatorNorm.lean`, CI #41723806687.

Rather than maintain a second competing declaration of
`RealNuclearCosts.opNorm_le`, this module only provides a useful
nonnegativity corollary and a backward-compatible alias for the
earlier experimental theorem name.

The witness hypothesis is essential: the cost set for a nonnuclear
operator may be empty, and its sInf is not a finite nuclear norm.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Any genuinely nuclear real Hilbert operator has nonnegative
projective nuclear infimum. -/
theorem realNuclearInfimum_nonneg_of_witness
    (T : H →L[ℝ] H) (hT : HasRealNuclearRankOneSeries T) :
    0 ≤ realNuclearInfimum T :=
  le_trans (norm_nonneg T) (realNuclearInfimum_opNorm_le T hT)

/-- Compatibility alias for the independently certified general
operator-norm lower bound. -/
theorem realNuclearInfimum_opNorm_le_of_witness
    (T : H →L[ℝ] H) (hT : HasRealNuclearRankOneSeries T) :
    ‖T‖ ≤ realNuclearInfimum T :=
  realNuclearInfimum_opNorm_le T hT

#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.opNorm_le
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_nonneg_of_witness
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_opNorm_le_of_witness

end GegenbauerFock.Ultraspherical
