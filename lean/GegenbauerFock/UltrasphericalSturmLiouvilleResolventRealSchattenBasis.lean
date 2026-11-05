import GegenbauerFock.UltrasphericalSturmLiouvilleResolventSquareSeriesSummable
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2BasisResolvent

/-!
# V007 — real-Hilbert operator Schatten criteria on the actual Gegenbauer basis

Unlike a bare scalar sequence statement, the following two results
calculate the diagonal and the squared operator-image norms of the
ACTUAL positive-shift resolvent of the canonical closed real weighted
Sturm–Liouville operator, on its explicitly kernel-certified full
Hilbert basis.

These are the standard fixed-basis positive-S1 and Hilbert-Schmidt-S2
diagonal criteria. An independent universal CFC trace-class bridge
on real Hilbert spaces is NOT silently assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Positive trace-class diagonal criterion on an explicit complete
REAL Hilbert basis, for a bounded operator acting on the actual space. -/
def IsRealPositiveTraceSummableOnBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H) : Prop :=
  Summable (fun n : ℕ => inner ℝ (b n) (T (b n)))

/-- Hilbert–Schmidt S₂ basis criterion as an operator property:
the norms of the ACTUAL images of normalized basis elements are ℓ². -/
def IsRealHilbertSchmidtOnBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H) : Prop :=
  Summable (fun n : ℕ => ‖T (b n)‖ ^ 2)

/-- Exact diagonal of the real closed Sturm resolvent in the actual
normalized complete Gegenbauer Hilbert basis. -/
theorem sturmRealPositiveResolvent_basis_inner_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    inner ℝ
      ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
      (sturmRealPositiveResolventFullCLM lam t hlam ht
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)) =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have heig := sturmMonicEigenCandidate_realL2_hilbertBasis_resolvent_diagonal
    lam t hlam ht n
  have hnorm : ‖b n‖ = 1 := b.orthonormal.norm_eq_one n
  change inner ℝ (b n) (sturmRealPositiveResolventFullCLM lam t hlam ht (b n)) = _
  rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm]
  ring

/-- Actual closed Sturm resolvent satisfies the real positive-S1
diagonal summability criterion, not just an unrelated scalar bound. -/
theorem sturmRealPositiveResolvent_positive_trace_diagonal_summable
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsRealPositiveTraceSummableOnBasis
      (sturmRealPositiveResolventFullCLM lam t hlam ht)
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) := by
  unfold IsRealPositiveTraceSummableOnBasis
  exact (sturmResolventMultiplier_summable lam t hlam ht).congr
    (fun n => (sturmRealPositiveResolvent_basis_inner_diagonal lam t hlam ht n).symm)

/-- Exact squared-norm of the real resolvent applied to each
normalized Gegenbauer eigenmode. -/
theorem sturmRealPositiveResolvent_basis_norm_sq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht
      ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)‖ ^ 2 =
      ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) ^ 2 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have heig := sturmMonicEigenCandidate_realL2_hilbertBasis_resolvent_diagonal
    lam t hlam ht n
  have hnorm : ‖b n‖ = 1 := b.orthonormal.norm_eq_one n
  have hpos : 0 < (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ :=
    sturmResolventMultiplier_pos lam t hlam ht n
  change ‖sturmRealPositiveResolventFullCLM lam t hlam ht (b n)‖ ^ 2 = _
  rw [heig, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hnorm, mul_one]

/-- The genuine canonical real Sturm resolvent satisfies the
operator Hilbert–Schmidt criterion on its complete weighted-L² basis. -/
theorem sturmRealPositiveResolvent_isHS_on_actual_basis
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsRealHilbertSchmidtOnBasis
      (sturmRealPositiveResolventFullCLM lam t hlam ht)
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) := by
  unfold IsRealHilbertSchmidtOnBasis
  exact (sturmResolventMultiplier_sq_summable lam t hlam ht).congr
    (fun n => (sturmRealPositiveResolvent_basis_norm_sq lam t hlam ht n).symm)

/-- Explicit positive diagonal trace of the ACTUAL resolvent. -/
theorem sturmRealPositiveResolvent_actual_basis_trace_eq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (∑' n : ℕ,
      inner ℝ
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
        (sturmRealPositiveResolventFullCLM lam t hlam ht
          ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n))) =
      sturmResolventSpectralTrace lam t := by
  unfold sturmResolventSpectralTrace
  apply tsum_congr
  intro n
  exact sturmRealPositiveResolvent_basis_inner_diagonal lam t hlam ht n

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_basis_inner_diagonal
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_positive_trace_diagonal_summable
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_basis_norm_sq
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_isHS_on_actual_basis
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_actual_basis_trace_eq

end GegenbauerFock.Ultraspherical
