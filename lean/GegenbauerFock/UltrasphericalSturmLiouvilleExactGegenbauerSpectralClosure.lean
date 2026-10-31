import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertUnshiftedDomain
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertClosedDiagonalAction

/-!
# V007 — EXACT identification of canonical closed Gegenbauer Sturm spectrum

This single theorem packages both critical equalities:
1. The domain of the closure of the ACTUAL polynomial differential
   Sturm–Liouville operator is precisely the weighted-ℓ² diagonal
   domain in the explicit, normalized complete Gegenbauer Hilbert basis.
2. On every vector of that very domain, the closed operator's
   coefficient at degree n is -n(n+2λ) times the vector coefficient.

Both underlying results are kernel certified separately. Their
conjunction rules out the weaker claim that one has merely
constructed an abstract closed spectral extension.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The canonical closure of the genuine weighted-real-L²
Gegenbauer polynomial Sturm operator IS the diagonal spectral
realization on its exact unshifted weighted-ℓ² domain. -/
theorem sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
    (lam : ℝ) (hlam : 0 < lam) :
    (((sturmRealPartialOperator lam hlam).closure.domain :
        Set (SturmH lam)) =
      sturmMonicHilbertUnshiftedDomain lam hlam) ∧
    (∀ (x : (sturmRealPartialOperator lam hlam).closure.domain) (n : ℕ),
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        ((sturmRealPartialOperator lam hlam).closure x) n =
      (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) n) := by
  constructor
  · exact sturmRealClosed_domain_eq_monicHilbert_unshiftedL2 lam hlam
  · intro x n
    exact sturmRealClosed_monicHilbert_diagonal_action
      lam 1 hlam (by norm_num) x n

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization

end GegenbauerFock.Ultraspherical
