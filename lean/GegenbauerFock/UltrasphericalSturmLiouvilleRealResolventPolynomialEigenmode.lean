import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph
import GegenbauerFock.UltrasphericalSturmLiouvilleRealL2LowEigenstates
import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder

/-!
# V007 — exact diagonal action of the genuine full-L² Sturm resolvent

Every genuine polynomial eigenvector for the ultraspherical differential
expression is an eigenvector of the canonical CLOSED Sturm operator,
and then of the bounded positive resolvent R_t on the entire Hilbert
space, with precise eigenvalue (t + n(n+2λ))⁻¹.

This is not a claim that the family of such eigenpolynomials has
already been constructed for every n, nor that it is a complete basis.
These existence/completeness assertions remain separate goals.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every exact polynomial eigenrelation descends to the COMPLETE
closed real weighted-L² operator domain, with the same eigenvalue. -/
theorem sturmRealClosed_polynomial_eigenmode
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) (n : ℕ)
    (hp : sturmPolynomial lam p = sturmEigenvalue lam n • p) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) = sturmRealPolynomialLp lam hlam p ∧
      (sturmRealPartialOperator lam hlam).closure x =
        sturmEigenvalue lam n • (x : SturmH lam) := by
  let u : (sturmRealPartialOperator lam hlam).domain :=
    ⟨sturmRealPolynomialLp lam hlam p,
      sturmRealPolynomialLp_mem_domain lam hlam p⟩
  have haction : sturmRealPartialOperator lam hlam u =
      sturmRealPolynomialLp lam hlam (sturmPolynomial lam p) := by
    change (((sturmRealDomainOperator lam hlam
      (⟨sturmRealPolynomialLp lam hlam p,
        sturmRealPolynomialLp_mem_domain lam hlam p⟩ :
          sturmRealPolynomialDomain lam hlam)) :
      sturmRealPolynomialDomain lam hlam) : SturmH lam) = _
    exact congrArg Subtype.val
      (sturmRealDomainOperator_on_polynomial lam hlam p)
  obtain ⟨x, hx, hAx⟩ :=
    LinearPMap.exists_of_le
      (sturmRealPartialOperator_le_closed_extension lam hlam) u
  refine ⟨x, hx, ?_⟩
  rw [hAx, haction, hp, sturmRealPolynomialLp_smul]
  exact congrArg (fun w : SturmH lam => sturmEigenvalue lam n • w)
    hx.symm

/-- A polynomial eigenvector of degree n has exactly the expected
Gegenbauer positive-resolvent eigenvalue on ALL of real weighted L².
No finite truncation or hypothetical spectral extension is used. -/
theorem sturmRealPositiveResolventFullCLM_polynomial_eigenmode
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (p : ℝ[X]) (n : ℕ)
    (hp : sturmPolynomial lam p = sturmEigenvalue lam n • p) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmRealPolynomialLp lam hlam p) =
      (t - sturmEigenvalue lam n)⁻¹ •
        sturmRealPolynomialLp lam hlam p := by
  let d := sturmEigenvalue lam n
  let v := sturmRealPolynomialLp lam hlam p
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  obtain ⟨x, hx, hAx⟩ :=
    sturmRealClosed_polynomial_eigenmode lam hlam p n hp
  have hd : d ≤ 0 := sturmEigenvalue_nonpos lam hlam n
  have hne : t - d ≠ 0 := ne_of_gt (by linarith)
  have hshift : t • (x : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure x =
      (t - d) • v := by
    rw [hAx, sub_smul, hx]
  have hRv : R ((t - d) • v) = v := by
    have hi := sturmRealPositiveResolventFullCLM_left_inverse_closed_shift
      lam t hlam ht x
    rw [hshift, hx] at hi
    exact hi
  have hscalar : (t - d) • R v = v := by
    simpa only [map_smul] using hRv
  calc
    R v = (t-d)⁻¹ • ((t-d) • R v) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (t-d)⁻¹ • v := by rw [hscalar]

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_polynomial_eigenmode
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_polynomial_eigenmode

end GegenbauerFock.Ultraspherical
