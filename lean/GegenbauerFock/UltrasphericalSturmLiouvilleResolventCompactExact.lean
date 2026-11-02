import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteTailUpper
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteTailLower
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventCompactnessBridge

/-!
# V007 — exact compactness of the canonical closed ultraspherical Sturm resolvent

The actual closed real Gegenbauer–Sturm operator on weighted L² has
a compact positive-shift resolvent for every λ,t>0, with exact
operator-norm error for truncation to the first N eigenpolynomials.
No abstract spectral extension, assumed Hilbert basis, or conditional
tail bound occurs in the statements of the two final theorems.

These theorems depend on separate compilation and axiom audits of
the finite-rank spectral truncation, its Hilbert coefficient formula,
the uniform lp norm upper tail, and the first-omitted eigenmode
lower tail. A source declaration is NOT a Lean certificate until
all the corresponding CI checks pass.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- Exact sharp operator norm of the genuine finite spectral tail,
attained by the first omitted normalized Gegenbauer eigenmode. -/
theorem sturmRealClosedResolvent_finite_tail_norm_eq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (N : ℕ) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
        sturmRealResolventFiniteRankTruncation lam t hlam N‖ =
      (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ := by
  exact le_antisymm
    (sturmRealClosedResolvent_finite_tail_norm_le lam t hlam ht N)
    (sturmRealClosedResolvent_finite_tail_norm_ge lam t hlam ht N)

/-- The resolvent of the **canonical closure** of the genuine
ultraspherical Sturm–Liouville differential operator is compact
on the full real weighted L², for every λ,t>0. -/
theorem sturmRealClosedResolvent_isCompactOperator
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsCompactOperator (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  apply sturmRealClosedResolvent_compact_of_uniform_tail_bound lam t hlam ht
  intro N
  exact sturmRealClosedResolvent_finite_tail_norm_le lam t hlam ht N

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_finite_tail_norm_eq
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_isCompactOperator

end GegenbauerFock.Ultraspherical
