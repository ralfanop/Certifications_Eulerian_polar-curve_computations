import GegenbauerFock.UltrasphericalSturmLiouvilleMonicMeanZeroResolventSharpOptimal

/-!
# V007 — sharp two-source Lipschitz estimate for the full Sturm resolvent

The full positive resolvent R_t of the genuine closed Gegenbauer Sturm
operator is a bounded linear map on the actual weighted real L² space.
For λ>0 and t>0, the degree-zero Hilbert Fourier mode vanishes for
each of two mean-zero data f and g, so also for their difference.
The certified optimal single-source resolvent estimate thus gives

   (t+1+2λ) ‖R_t f - R_t g‖ ≤ ‖f-g‖.

The same degree-one eigenmode gives sharpness of the coefficient
t+1+2λ among all two-source inequalities of this form. Both
statements concern the complete real Hilbert space, not truncated
spectral vectors or a surrogate inverse.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact improved Lipschitz stability between arbitrary pairs of
mean-zero real weighted-L² data under the genuine bounded resolvent. -/
theorem sturmRealPositiveResolventFullCLM_meanZero_twoSource_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f g : SturmH lam)
    (hf0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0)
    (hg0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g 0 = 0) :
    (t + (1 + 2 * lam)) *
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
        sturmRealPositiveResolventFullCLM lam t hlam ht g‖ ≤
      ‖f - g‖ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hd0 : (b.repr (f - g)) 0 = 0 := by
    rw [map_sub]
    have hfa : (b.repr f) 0 = 0 := hf0
    have hga : (b.repr g) 0 = 0 := hg0
    simpa only [lp.coeFn_sub, Pi.sub_apply, hfa, hga, sub_self]
  have h :=
    sturmRealPositiveResolventFullCLM_meanZero_sharp_bound
      lam t hlam ht (f - g) hd0
  rw [map_sub] at h
  exact h

/-- The coefficient t+1+2λ is also the largest uniform two-source
lower rate for the full Sturm resolvent on mean-zero L² data. -/
theorem sturmRealPositiveResolventFullCLM_meanZero_twoSource_bound_optimal
    (lam t C : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (hbound :
      ∀ f g : SturmH lam,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0 →
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g 0 = 0 →
        C * ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
          sturmRealPositiveResolventFullCLM lam t hlam ht g‖ ≤
          ‖f - g‖) :
    C ≤ t + (1 + 2 * lam) := by
  apply sturmRealPositiveResolventFullCLM_meanZero_bound_optimal
    lam t C hlam ht
  intro f hf0
  have hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (0 : SturmH lam) 0 = 0 := by simp
  have h := hbound f 0 hf0 hzero
  simpa using h

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_meanZero_twoSource_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_meanZero_twoSource_bound_optimal

end GegenbauerFock.Ultraspherical
