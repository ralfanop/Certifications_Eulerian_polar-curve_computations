import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedDirichletPoincare

/-!
# V007 — sharp mean-zero coercivity of the canonical closed Gegenbauer Sturm operator

The kernel-certified sharp quadratic-form Poincare estimate, together
with real Cauchy--Schwarz, implies the quantitative graph lower bound

  (1+2λ) * ‖u‖ ≤ ‖closure(Lλ) u‖

for every vector in the actual closed differential operator domain
whose constant Gegenbauer Fourier coefficient vanishes.

This operator-norm coercivity is the basic ingredient for a bounded
inverse on the orthogonal complement of the constant mode, and is
stronger than qualitative injectivity there.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Quantitative mean-zero spectral gap on the *full true closed
Sturm graph domain*, with the optimal first positive rate 1+2λ. -/
theorem sturmRealClosed_meanZero_coercive
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0) :
    (1 + 2 * lam) * ‖(x : SturmH lam)‖ ≤
      ‖(sturmRealPartialOperator lam hlam).closure x‖ := by
  let A := (sturmRealPartialOperator lam hlam).closure
  have hp :=
    sturmMonic_realL2_closed_Dirichlet_poincare lam hlam x hzero
  have hcs : |inner ℝ (A x) (x : SturmH lam)| ≤
      ‖A x‖ * ‖(x : SturmH lam)‖ :=
    abs_real_inner_le_norm (A x) (x : SturmH lam)
  by_cases hx : (x : SturmH lam) = 0
  · simp [hx]
  · have hxpos : 0 < ‖(x : SturmH lam)‖ :=
      norm_pos_iff.mpr hx
    have hmul :
        ((1 + 2 * lam) * ‖(x : SturmH lam)‖) *
            ‖(x : SturmH lam)‖ ≤
          ‖A x‖ * ‖(x : SturmH lam)‖ := by
      calc
        ((1 + 2 * lam) * ‖(x : SturmH lam)‖) *
            ‖(x : SturmH lam)‖ =
            (1 + 2 * lam) * ‖(x : SturmH lam)‖ ^ 2 := by ring
        _ ≤ -inner ℝ (A x) (x : SturmH lam) := hp
        _ ≤ |inner ℝ (A x) (x : SturmH lam)| := neg_le_abs _
        _ ≤ ‖A x‖ * ‖(x : SturmH lam)‖ := hcs
    exact (mul_le_mul_iff_of_pos_right hxpos).mp hmul

/-- There is no nontrivial mean-zero nullvector of the genuine
canonical closed Sturm operator, as a corollary of its quantitative gap. -/
theorem sturmRealClosed_meanZero_kernel_trivial
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0)
    (hxA : (sturmRealPartialOperator lam hlam).closure x = 0) :
    (x : SturmH lam) = 0 := by
  have hcoercive := sturmRealClosed_meanZero_coercive lam hlam x hzero
  rw [hxA, norm_zero] at hcoercive
  have hrate : 0 < 1 + 2 * lam := by linarith
  have hnorm : ‖(x : SturmH lam)‖ = 0 := by
    have hn : 0 ≤ ‖(x : SturmH lam)‖ := norm_nonneg _
    nlinarith
  exact norm_eq_zero.mp hnorm

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_coercive
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_kernel_trivial

end GegenbauerFock.Ultraspherical
