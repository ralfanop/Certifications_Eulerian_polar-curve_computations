import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveShiftInjective

/-!
# V007 — exact and unique real-polynomial L² solution for all positive shifts

For every positive t and every genuine polynomial-image L² target,
the equation (tI - A₀)u = f has exactly one solution in the
actual ultraspherical polynomial domain.

Existence uses the exact finite polynomial inverse; uniqueness
uses the kernel-certified Hilbert Green identity. The theorem does
not confuse solutions on this dense subspace with an everywhere
defined bounded resolvent on the full Hilbert space.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- On the actual real L² polynomial domain, every polynomial
right-hand side of tI-A has one and only one exact polynomial solution. -/
theorem sturmRealPartialPositiveShift_unique_polynomial_preimage
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (p : ℝ[X]) :
    ∃! x : (sturmRealPartialOperator lam hlam).domain,
      t • (x : SturmH lam) -
        sturmRealPartialOperator lam hlam x =
          sturmRealPolynomialLp lam hlam p := by
  obtain ⟨x, hx⟩ :=
    sturmRealPartialPositiveShift_polynomial_preimage lam t hlam ht p
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact sturmRealPartialPositiveShift_injective lam t hlam ht
    (hy.trans hx.symm)

/-- The same exact uniqueness holds for every vector of the
genuine real polynomial-image submodule, not merely named polynomials. -/
theorem sturmRealPartialPositiveShift_unique_domain_preimage
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : sturmRealPolynomialDomain lam hlam) :
    ∃! x : (sturmRealPartialOperator lam hlam).domain,
      t • (x : SturmH lam) -
        sturmRealPartialOperator lam hlam x = (f : SturmH lam) := by
  let p := sturmRealDomainRepresentative lam hlam f
  have hf := sturmRealDomainRepresentative_spec lam hlam f
  obtain ⟨x, hx, huniq⟩ :=
    sturmRealPartialPositiveShift_unique_polynomial_preimage
      lam t hlam ht p
  refine ⟨x, ?_, ?_⟩
  · simpa only [hf] using hx
  · intro y hy
    apply huniq
    simpa only [hf] using hy

#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialPositiveShift_unique_polynomial_preimage
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialPositiveShift_unique_domain_preimage

end GegenbauerFock.Ultraspherical
