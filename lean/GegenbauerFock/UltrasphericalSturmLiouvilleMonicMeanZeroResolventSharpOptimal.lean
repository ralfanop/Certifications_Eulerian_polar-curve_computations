import GegenbauerFock.UltrasphericalSturmLiouvilleMonicMeanZeroResolventSharpBound
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedPoincareSharp

/-!
# V007 — exact attainability and optimality of mean-zero Sturm resolvent norm

The actual real ultraspherical closed Sturm positive resolvent R_t
satisfies the improved quantitative bound

  (t + 1 + 2λ) ‖R_t f‖ ≤ ‖f‖

for every mean-zero input f in the full weighted L² space.
The nonzero genuine degree-one eigenvector of closure(Lλ)
furnishes a mean-zero input for which the inequality is equality.
Consequently the improved bound on the resolvent is sharp, not merely
an upper estimate from the closed-operator spectral gap.

This result does not identify a finite-dimensional resolvent proxy:
it concerns the canonical all-L² bounded extension and true graph
closure of the unbounded Gegenbauer Sturm operator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- A nonzero mean-zero resolvent output attains the exact improved
positive-shift bound on the complete real weighted Hilbert space. -/
theorem sturmRealPositiveResolventFullCLM_meanZero_bound_attained
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ∃ f : SturmH lam,
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0 ∧
      sturmRealPositiveResolventFullCLM lam t hlam ht f ≠ 0 ∧
      (t + (1 + 2 * lam)) *
          ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ = ‖f‖ := by
  let A := (sturmRealPartialOperator lam hlam).closure
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let c : ℝ := t + (1 + 2 * lam)
  obtain ⟨x, hx, hzero, heig⟩ :=
    sturmRealClosed_first_nonconstant_eigenmode_zero_constant lam hlam
  have hc : 0 < c := by dsimp [c]; linarith
  let f : SturmH lam := c • (x : SturmH lam)
  have hfzero : (b.repr f) 0 = 0 := by
    change (b.repr (c • (x : SturmH lam))) 0 = 0
    rw [map_smul]
    change c * (b.repr (x : SturmH lam)) 0 = 0
    rw [hzero, mul_zero]
  have hshift :
      t • (x : SturmH lam) - A x = f := by
    change t • (x : SturmH lam) - A x = c • (x : SturmH lam)
    rw [heig, ← sub_smul]
    congr 1
    dsimp [c]
    ring
  have hR : R f = (x : SturmH lam) := by
    have hInv := sturmRealPositiveResolventFullCLM_left_inverse_closed_shift
      lam t hlam ht x
    rw [hshift] at hInv
    exact hInv
  have hRne : R f ≠ 0 := by
    rw [hR]
    exact hx
  have hsharp : c * ‖R f‖ = ‖f‖ := by
    change c * ‖R f‖ = ‖c • (x : SturmH lam)‖
    rw [hR, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  exact ⟨f, hfzero, hRne, hsharp⟩

/-- The constant t+1+2λ is the largest coefficient for a uniform
full-L² mean-zero resolvent lower bound of the form C‖R_t f‖ ≤ ‖f‖. -/
theorem sturmRealPositiveResolventFullCLM_meanZero_bound_optimal
    (lam t C : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (hbound :
      ∀ f : SturmH lam,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0 →
        C * ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ ≤ ‖f‖) :
    C ≤ t + (1 + 2 * lam) := by
  obtain ⟨f, hzero, hRne, heq⟩ :=
    sturmRealPositiveResolventFullCLM_meanZero_bound_attained lam t hlam ht
  have hh := hbound f hzero
  rw [← heq] at hh
  have hpositive :
      0 < ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ :=
    norm_pos_iff.mpr hRne
  exact (mul_le_mul_iff_of_pos_right hpositive).mp hh

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_meanZero_bound_attained
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_meanZero_bound_optimal

end GegenbauerFock.Ultraspherical
