import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedMeanZeroShiftGap
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedMeanZeroDifferenceStability

/-!
# V007 — shifted two-source stability in the true weighted real L² Sturm domain

For λ>0 and t≥0, let A denote the canonical closure of the real
ultraspherical Sturm polynomial operator on L²(ν_λ;ℝ). The first
nonconstant Gegenbauer eigenvalue yields the sharp graph bound

  (t + 1 + 2λ) ‖x-y‖ ≤ ‖(tI-A)x - (tI-A)y‖

for any two mean-zero vectors in the actual closed differential
operator domain.

We then derive quantitative stability under noisy shifted data,
and uniqueness on the mean-zero subspace. These are statements
on the genuine infinite-dimensional weighted L² Hilbert space.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The sharp positive-shift gap extends to any two mean-zero
closed-domain vectors by genuine linearity of the closed Sturm graph. -/
theorem sturmRealClosed_meanZero_shift_twoSource_coercive
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0)
    (hy0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (y : SturmH lam) 0 = 0) :
    (t + (1 + 2 * lam)) *
      ‖(x : SturmH lam) - (y : SturmH lam)‖ ≤
      ‖(t • (x : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure x) -
        (t • (y : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure y)‖ := by
  let A := (sturmRealPartialOperator lam hlam).closure
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let d : A.domain := x - y
  have hd0 : (b.repr (d : SturmH lam)) 0 = 0 := by
    change (b.repr ((x : SturmH lam) - (y : SturmH lam))) 0 = 0
    rw [map_sub]
    have hxa : (b.repr (x : SturmH lam)) 0 = 0 := hx0
    have hya : (b.repr (y : SturmH lam)) 0 = 0 := hy0
    simpa only [lp.coeFn_sub, Pi.sub_apply, hxa, hya, sub_self]
  have hgap := sturmRealClosed_meanZero_positiveShift_gap lam t hlam ht d hd0
  have hd : (d : SturmH lam) = (x : SturmH lam) -
      (y : SturmH lam) := rfl
  have hAd : A d = A x - A y := by
    change A (x - y) = A x - A y
    exact LinearPMap.map_sub A x y
  have hshift :
      t • (d : SturmH lam) - A d =
        (t • (x : SturmH lam) - A x) -
          (t • (y : SturmH lam) - A y) := by
    rw [hd, hAd, smul_sub]
    abel
  simpa only [hd, hshift] using hgap

/-- Stable mean-zero reconstruction from a difference of
shifted closed-Sturm outputs bounded by ε. -/
theorem sturmRealClosed_meanZero_shift_twoSource_residual
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0)
    (hy0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (y : SturmH lam) 0 = 0)
    (ε : ℝ)
    (hdata :
      ‖(t • (x : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure x) -
        (t • (y : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure y)‖ ≤ ε) :
    ‖(x : SturmH lam) - (y : SturmH lam)‖ ≤
      ε / (t + (1 + 2 * lam)) := by
  have hpositive : 0 < t + (1 + 2 * lam) := by linarith
  apply (le_div_iff₀ hpositive).2
  calc
    ‖(x : SturmH lam) - (y : SturmH lam)‖ *
        (t + (1 + 2 * lam)) =
      (t + (1 + 2 * lam)) *
        ‖(x : SturmH lam) - (y : SturmH lam)‖ := by ring
    _ ≤ ‖(t • (x : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure x) -
        (t • (y : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure y)‖ :=
      sturmRealClosed_meanZero_shift_twoSource_coercive
        lam t hlam ht x y hx0 hy0
    _ ≤ ε := hdata

/-- The positive-shift differential data uniquely determine any
mean-zero vector in the actual closed ultraspherical Sturm domain. -/
theorem sturmRealClosed_meanZero_shift_unique
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0)
    (hy0 :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (y : SturmH lam) 0 = 0)
    (heq :
      t • (x : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure x =
      t • (y : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure y) :
    x = y := by
  have h := sturmRealClosed_meanZero_shift_twoSource_coercive
    lam t hlam ht x y hx0 hy0
  rw [heq, sub_self, norm_zero] at h
  have hpositive : 0 < t + (1 + 2 * lam) := by linarith
  have hnorm : ‖(x : SturmH lam) - (y : SturmH lam)‖ = 0 := by
    have hnonneg : 0 ≤ (t + (1 + 2 * lam)) *
        ‖(x : SturmH lam) - (y : SturmH lam)‖ :=
      mul_nonneg hpositive.le (norm_nonneg _)
    have hproduct : (t + (1 + 2 * lam)) *
        ‖(x : SturmH lam) - (y : SturmH lam)‖ = 0 :=
      le_antisymm h hnonneg
    exact (mul_eq_zero.mp hproduct).resolve_left hpositive.ne'
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_shift_twoSource_coercive
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_shift_twoSource_residual
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_shift_unique

end GegenbauerFock.Ultraspherical
