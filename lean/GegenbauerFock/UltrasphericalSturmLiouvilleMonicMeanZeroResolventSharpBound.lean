import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedMeanZeroShiftGap
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph

/-!
# V007 — genuine mean-zero full resolvent and improved sharp spectral-gap bound

The exact canonical positive resolvent R_t of the genuine closed
ultraspherical real weighted-L² Sturm operator acts diagonally on the
normalized Gegenbauer Fourier coordinates for every L² datum.

The degree-zero coefficient of R_t f is t⁻¹ times the degree-zero
coefficient of f. Thus mean-zero data produce mean-zero solutions.
The actual closed-graph characterization and the certified sharp
shifted gap then give, for any t>0,

  (t + 1 + 2λ) ‖R_t f‖ ≤ ‖f‖,

on the full mean-zero data subspace. This strictly improves the
global bound t ‖R_t f‖ ≤ ‖f‖.

The estimate is on all weighted real L² data, not finite polynomial
sections, and the operator is exactly the inverse of tI-closure(Lλ).
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine all-L² positive resolvent preserves the mean-zero
subspace defined by the degree-zero normalized Gegenbauer coordinate. -/
theorem sturmRealPositiveResolventFullCLM_preserves_meanZero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) 0 = 0 := by
  have hcoord :=
    sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
      lam t hlam ht f 0
  simpa only [hzero, mul_zero] using hcoord

/-- Strictly improved resolvent norm bound on ALL mean-zero
weighted-real-L² data, derived from the genuine closed Sturm graph. -/
theorem sturmRealPositiveResolventFullCLM_meanZero_sharp_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0) :
    (t + (1 + 2 * lam)) *
        ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ ≤
      ‖f‖ := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
  have hfirst : (x : SturmH lam) = R f := congrArg Prod.fst hx
  have hsecond : A.closure x = t • R f - f := congrArg Prod.snd hx
  have hxzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0 := by
    rw [hfirst]
    exact sturmRealPositiveResolventFullCLM_preserves_meanZero
      lam t hlam ht f hzero
  have hgap :=
    sturmRealClosed_meanZero_positiveShift_gap
      lam t hlam ht.le x hxzero
  have hshift : t • (x : SturmH lam) - A.closure x = f := by
    rw [hfirst, hsecond]
    abel
  rw [hfirst, hshift] at hgap
  exact hgap

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_preserves_meanZero
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_meanZero_sharp_bound

end GegenbauerFock.Ultraspherical
