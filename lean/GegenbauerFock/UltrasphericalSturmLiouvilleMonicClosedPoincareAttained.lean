import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedPoincareSharp

/-!
# V007 — exact attainment of the sharp closed Sturm Poincaré gap

For every strictly positive ultraspherical parameter, an actual
nonzero vector in the canonical closed differential-operator domain,
orthogonal to the constant Gegenbauer mode, attains equality at the
sharp spectral gap 1+2λ. The witness is the genuine degree-one
Gegenbauer eigenvector, not an approximate eigenvector or merely a
finite sequence of Fourier coefficients.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The best Poincaré constant of the genuine canonical closed
Gegenbauer Sturm operator is actually attained at a nonzero
mean-zero eigenvector of degree one. -/
theorem sturmMonic_realL2_closed_Dirichlet_poincare_attained
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) ≠ 0 ∧
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0 ∧
      (1 + 2 * lam) * ‖(x : SturmH lam)‖ ^ 2 =
        -inner ℝ ((sturmRealPartialOperator lam hlam).closure x)
          (x : SturmH lam) := by
  obtain ⟨x, hx, hzero, heig⟩ :=
    sturmRealClosed_first_nonconstant_eigenmode_zero_constant lam hlam
  refine ⟨x, hx, hzero, ?_⟩
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_closed_Dirichlet_poincare_attained

end GegenbauerFock.Ultraspherical
