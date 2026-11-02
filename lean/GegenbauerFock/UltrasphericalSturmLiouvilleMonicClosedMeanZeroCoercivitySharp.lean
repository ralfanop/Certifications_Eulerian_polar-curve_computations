import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedMeanZeroCoercivity
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedPoincareSharp

/-!
# V007 — Optimality of mean-zero coercivity on the genuine closed Sturm domain

The canonical closed Gegenbauer Sturm differential operator has the
quantitative lower estimate

  (1 + 2λ) ‖f‖ ≤ ‖closure(Lλ) f‖

for every mean-zero vector in its closed domain. The actual nonzero
degree-one eigenvector attains equality, so the multiplicative constant
1 + 2λ is not only valid but best possible.

This is a statement about the real weighted-L² differential operator,
not merely a numerical bound for finite spectral sequences.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The nonzero first Gegenbauer eigenmode attains the sharp
operator-norm coercivity constant on the true closed domain. -/
theorem sturmRealClosed_meanZero_coercivity_attained
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) ≠ 0 ∧
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0 ∧
      ‖(sturmRealPartialOperator lam hlam).closure x‖ =
        (1 + 2 * lam) * ‖(x : SturmH lam)‖ := by
  obtain ⟨x, hx, hzero, heig⟩ :=
    sturmRealClosed_first_nonconstant_eigenmode_zero_constant lam hlam
  have hgap : 0 < 1 + 2 * lam := by linarith
  refine ⟨x, hx, hzero, ?_⟩
  rw [heig, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hgap]

/-- Any scalar C satisfying ‖closure(Lλ)f‖ ≥ C‖f‖ for all
mean-zero closed-domain vectors must satisfy C ≤ 1 + 2λ. -/
theorem sturmRealClosed_meanZero_coercivity_constant_optimal
    (lam C : ℝ) (hlam : 0 < lam)
    (hbound :
      ∀ x : (sturmRealPartialOperator lam hlam).closure.domain,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) 0 = 0 →
        C * ‖(x : SturmH lam)‖ ≤
          ‖(sturmRealPartialOperator lam hlam).closure x‖) :
    C ≤ 1 + 2 * lam := by
  obtain ⟨x, hx, hzero, hsharp⟩ :=
    sturmRealClosed_meanZero_coercivity_attained lam hlam
  have h := hbound x hzero
  rw [hsharp] at h
  have hnorm : 0 < ‖(x : SturmH lam)‖ :=
    norm_pos_iff.mpr hx
  exact (mul_le_mul_iff_of_pos_right hnorm).mp h

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_coercivity_attained
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_coercivity_constant_optimal

end GegenbauerFock.Ultraspherical
