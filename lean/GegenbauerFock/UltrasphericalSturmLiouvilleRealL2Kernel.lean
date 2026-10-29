import GegenbauerFock.UltrasphericalSturmLiouvilleRealL2Green

/-!
# V007 — the polynomial differential action descends to the real L² image

The actual real weighted L² Green identity proves that the
polynomial evaluation kernel is preserved by L_lambda.

The key argument needs no unproved global injectivity: if P evaluates
to zero in L², symmetry against Q=L_lambda(P) gives
  inner (eval(L_lambda P)) (eval(L_lambda P)) = 0,
hence eval(L_lambda P)=0 in the genuine Hilbert space.

This shows representation-independence of the differential action
on the image of the polynomial evaluation map. Density, closure,
and self-adjointness are further steps.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- The full actual real L² Green pairing sends the kernel of
polynomial evaluation back into itself. In particular, the
polynomial differential action is well-defined on its image even
before proving polynomial evaluation injective. -/
theorem sturmRealPolynomialLp_kernel_invariant
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X])
    (hp : sturmRealPolynomialLp lam hlam p = 0) :
    sturmRealPolynomialLp lam hlam (sturmPolynomial lam p) = 0 := by
  have hgreen := sturmRealPolynomialLp_green_inner_symm
    lam hlam p (sturmPolynomial lam p)
  have hself :
      inner ℝ
        (sturmRealPolynomialLp lam hlam (sturmPolynomial lam p))
        (sturmRealPolynomialLp lam hlam (sturmPolynomial lam p)) = 0 := by
    simpa [hp] using hgreen
  exact inner_self_eq_zero.mp hself

/-- The genuine polynomial differential action is independent of
representatives of an actual L² polynomial vector. -/
theorem sturmRealPolynomialLp_action_well_defined
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X])
    (hpq : sturmRealPolynomialLp lam hlam p =
      sturmRealPolynomialLp lam hlam q) :
    sturmRealPolynomialLp lam hlam (sturmPolynomial lam p) =
      sturmRealPolynomialLp lam hlam (sturmPolynomial lam q) := by
  have hsub :
      sturmRealPolynomialLp lam hlam (p - q) = 0 := by
    change sturmRealPolynomialLinear lam hlam (p - q) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hpq
  have hzero :=
    sturmRealPolynomialLp_kernel_invariant lam hlam (p - q) hsub
  change sturmRealPolynomialLinear lam hlam
    (sturmPolynomial lam (p - q)) = 0 at hzero
  rw [sturmPolynomial_sub, map_sub] at hzero
  exact sub_eq_zero.mp hzero

#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_kernel_invariant
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_action_well_defined

end GegenbauerFock.Ultraspherical
