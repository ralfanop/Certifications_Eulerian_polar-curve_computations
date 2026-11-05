import GegenbauerFock.UltrasphericalSturmLiouvilleSpectralClosureNonpositive

/-!
# V007 — quantitative positive real shifts of nonpositive Sturm realizations

A nonpositive real Hilbert linear operator has the explicit sharp
lower estimate t‖u‖ ≤ ‖t u - S u‖ for every t>0 and every vector
in its actual operator domain. This theorem applies in particular
to any candidate closed nonpositive spectral realization extending
the genuine ultraspherical polynomial operator.

The result yields uniqueness of positive shifted equations, without
asserting that a solution exists for all right-hand sides.
This separates injectivity/resolvent estimates from surjectivity.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Nonpositive real Hilbert action gives a quantitative lower
positive-shift norm bound on its genuine domain. -/
theorem sturmReal_nonpositive_positive_shift_norm
    (lam t : ℝ) (ht : 0 < t)
    (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hNonpos : ∀ u : S.domain,
      inner ℝ (S u) (u : SturmH lam) ≤ 0)
    (x : S.domain) :
    t * ‖(x : SturmH lam)‖ ≤
      ‖t • (x : SturmH lam) - S x‖ := by
  have hneg : inner ℝ ((x : SturmH lam)) (S x) ≤ 0 := by
    rw [real_inner_comm]
    exact hNonpos x
  have hmul : inner ℝ (t • (x : SturmH lam)) (S x) ≤ 0 := by
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos ht.le hneg
  have hsq :
      ‖t • (x : SturmH lam)‖ ^ 2 ≤
        ‖t • (x : SturmH lam) - S x‖ ^ 2 := by
    have h := norm_sub_sq_real (t • (x : SturmH lam)) (S x)
    nlinarith [sq_nonneg (‖S x‖)]
  have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ht] using h

/-- There can be no nonzero element of a nonpositive domain in
the kernel of a strictly positive shifted Sturm expression. -/
theorem sturmReal_nonpositive_positive_shift_kernel
    (lam t : ℝ) (ht : 0 < t)
    (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hNonpos : ∀ u : S.domain,
      inner ℝ (S u) (u : SturmH lam) ≤ 0)
    (x : S.domain)
    (hx : t • (x : SturmH lam) - S x = 0) :
    x = 0 := by
  have h := sturmReal_nonpositive_positive_shift_norm
    lam t ht S hNonpos x
  rw [hx, norm_zero] at h
  have hnorm : ‖(x : SturmH lam)‖ = 0 := by
    have hn := norm_nonneg (x : SturmH lam)
    nlinarith
  apply Subtype.ext
  exact norm_eq_zero.mp hnorm

#print axioms GegenbauerFock.Ultraspherical.sturmReal_nonpositive_positive_shift_norm
#print axioms GegenbauerFock.Ultraspherical.sturmReal_nonpositive_positive_shift_kernel

end GegenbauerFock.Ultraspherical
