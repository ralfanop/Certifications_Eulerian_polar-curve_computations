import GegenbauerFock.RealHilbertPositiveDiagonalTraceNorm
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealS1EigenbasisToNuclear
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — conditional positive spectral bridge between real nuclear S1
# and Physlib-compatible complex CFC S1

This theorem compares two ACTUAL bounded positive-diagonal operators
acting on potentially distinct complete Hilbert spaces, one over R
and the other over C, when they have explicitly corresponding complete
countable eigenbases and the SAME nonnegative summable real eigenvalues.

For the real operator, its universal projective nuclear cost infimum is
the spectral sum; for the complex operator, the existing Physlib-compatible
CFC trace norm on ANY complete Hilbert basis has the same value.

The complex operator's genuine CFC IsTraceClass membership is an
EXPLICIT hypothesis: it is NOT inferred from a mere real-nuclear
membership, nor is there any assertion that the two operators are
canonically complexifications of each other. Such a realization
equivalence requires a separate proof.

Both fields' completed Hilbert structures are used in the proof.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open InnerProductSpace

variable {HR HC : Type*}
variable [NormedAddCommGroup HR] [InnerProductSpace ℝ HR] [CompleteSpace HR]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- Two positive diagonal operators, one over R and one over C,
with a common nonnegative summable eigenvalue sequence, have exactly
equal real projective nuclear S1 and genuine complex CFC trace norms,
provided complex CFC membership has independently been established. -/
theorem realProjectiveNuclear_eq_complexPhyslibTraceNorm_of_shared_positive_spectrum
    (R : HR →L[ℝ] HR) (T : HC →L[ℂ] HC)
    (bR : HilbertBasis ℕ ℝ HR) (bC : HilbertBasis ℕ ℂ HC)
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hs : Summable σ)
    (hR : ∀ n, R (bR n) = σ n • bR n)
    (hT : ∀ n, T (bC n) = (σ n : ℂ) • bC n)
    (hTpos : 0 ≤ T)
    (hTclass : ProbabilisticTheory.IsTraceClass T) :
    realNuclearInfimum R =
      ProbabilisticTheory.traceNorm T hTclass := by
  have hseries : R =
      ∑' n : ℕ, σ n • rankOne ℝ (bR n) (bR n) :=
    realPositiveEigenSummable_operator_tsum_eq R bR σ hσ hs hR
  have hRdiag (n : ℕ) :
      inner ℝ (bR n) (R (bR n)) = σ n := by
    rw [hR n, real_inner_smul_right, real_inner_self_eq_norm_sq,
      bR.orthonormal.norm_eq_one n]
    ring
  have hReal : realNuclearInfimum R = ∑' n : ℕ, σ n :=
    realHilbert_positiveDiagonal_nuclearInfimum_eq_trace
      bR R σ hs hσ hseries hRdiag
  have hCdiag (n : ℕ) :
      (inner ℂ (bC n) (T (bC n))).re = σ n := by
    rw [hT n, inner_smul_right, inner_self_eq_norm_sq_to_K,
      bC.orthonormal.norm_eq_one n]
    norm_num
  have hComplex :
      ProbabilisticTheory.traceNorm T hTclass = ∑' n : ℕ, σ n := by
    rw [ProbabilisticTheory.traceNorm_eq_of_hilbertBasis hTclass bC,
      CFC.abs_of_nonneg T hTpos]
    exact tsum_congr hCdiag
  exact hReal.trans hComplex.symm

#print axioms GegenbauerFock.Ultraspherical.realProjectiveNuclear_eq_complexPhyslibTraceNorm_of_shared_positive_spectrum

end GegenbauerFock.Ultraspherical
