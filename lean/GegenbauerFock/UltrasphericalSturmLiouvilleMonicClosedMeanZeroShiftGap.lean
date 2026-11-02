import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedPoincareSharp
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedMeanZeroCoercivity

/-!
# V007 — improved positive-shift gap on the true mean-zero closed Sturm domain

The canonical closure A of the real ultraspherical Sturm polynomial
operator on the genuine weighted real L² space has a sharp Poincare
gap 1+2λ on vectors with zero degree-zero Gegenbauer coordinate.

For all shifts t ≥ 0, on the same mean-zero closed domain,

  (t + 1 + 2λ) * ‖u‖ ≤ ‖t • u - A u‖.

The global positive-shift estimate has only coefficient t. The
improved rate t+1+2λ comes directly from the *genuine closed*
Dirichlet quadratic form. The degree-one eigenvector attains
equality for every such t, proving the shifted coefficient sharp.

No assertion about surjectivity is needed for this graph-norm proof.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The spectral-gap improvement to the positive shift norm
inequality on the genuine mean-zero closed Sturm domain. -/
theorem sturmRealClosed_meanZero_positiveShift_gap
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0) :
    (t + (1 + 2 * lam)) * ‖(x : SturmH lam)‖ ≤
      ‖t • (x : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure x‖ := by
  let A := (sturmRealPartialOperator lam hlam).closure
  have hp :=
    sturmMonic_realL2_closed_Dirichlet_poincare lam hlam x hzero
  have hquad :
      (t + (1 + 2 * lam)) * ‖(x : SturmH lam)‖ ^ 2 ≤
        inner ℝ (t • (x : SturmH lam) - A x) (x : SturmH lam) := by
    calc
      (t + (1 + 2 * lam)) * ‖(x : SturmH lam)‖ ^ 2 =
          t * ‖(x : SturmH lam)‖ ^ 2 +
          (1 + 2 * lam) * ‖(x : SturmH lam)‖ ^ 2 := by ring
      _ ≤ t * ‖(x : SturmH lam)‖ ^ 2 +
          -inner ℝ (A x) (x : SturmH lam) :=
        add_le_add (le_refl _) hp
      _ = inner ℝ (t • (x : SturmH lam) - A x) (x : SturmH lam) := by
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
        ring
  have hcs :
      inner ℝ (t • (x : SturmH lam) - A x) (x : SturmH lam) ≤
        ‖t • (x : SturmH lam) - A x‖ * ‖(x : SturmH lam)‖ :=
    real_inner_le_norm _ _
  by_cases hz : ‖(x : SturmH lam)‖ = 0
  · rw [hz, mul_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖(x : SturmH lam)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hmul :
        ((t + (1 + 2 * lam)) * ‖(x : SturmH lam)‖) *
            ‖(x : SturmH lam)‖ ≤
          ‖t • (x : SturmH lam) - A x‖ * ‖(x : SturmH lam)‖ := by
      calc
        ((t + (1 + 2 * lam)) * ‖(x : SturmH lam)‖) *
            ‖(x : SturmH lam)‖ =
            (t + (1 + 2 * lam)) * ‖(x : SturmH lam)‖ ^ 2 := by ring
        _ ≤ inner ℝ (t • (x : SturmH lam) - A x)
            (x : SturmH lam) := hquad
        _ ≤ ‖t • (x : SturmH lam) - A x‖ *
            ‖(x : SturmH lam)‖ := hcs
    exact (mul_le_mul_iff_of_pos_right hpos).mp hmul

/-- Degree one is an actual mean-zero closed-domain equality witness
for every nonnegative positive-shift parameter. -/
theorem sturmRealClosed_meanZero_positiveShift_gap_attained
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) ≠ 0 ∧
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0 ∧
      ‖t • (x : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure x‖ =
        (t + (1 + 2 * lam)) * ‖(x : SturmH lam)‖ := by
  obtain ⟨x, hx, hzero, heig⟩ :=
    sturmRealClosed_first_nonconstant_eigenmode_zero_constant lam hlam
  have hgap : 0 < t + (1 + 2 * lam) := by linarith
  refine ⟨x, hx, hzero, ?_⟩
  have hshift :
      t • (x : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure x =
        (t + (1 + 2 * lam)) • (x : SturmH lam) := by
    rw [heig]
    rw [← sub_smul]
    congr 1
    ring
  rw [hshift, norm_smul, Real.norm_eq_abs, abs_of_pos hgap]

/-- The rate t+1+2λ is optimal among uniform mean-zero closed-domain
positive-shift norm lower bounds, for every t≥0. -/
theorem sturmRealClosed_meanZero_positiveShift_gap_optimal
    (lam t C : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t)
    (hbound :
      ∀ x : (sturmRealPartialOperator lam hlam).closure.domain,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) 0 = 0 →
        C * ‖(x : SturmH lam)‖ ≤
          ‖t • (x : SturmH lam) -
            (sturmRealPartialOperator lam hlam).closure x‖) :
    C ≤ t + (1 + 2 * lam) := by
  obtain ⟨x, hx, hzero, hsharp⟩ :=
    sturmRealClosed_meanZero_positiveShift_gap_attained lam t hlam ht
  have h := hbound x hzero
  rw [hsharp] at h
  have hpos : 0 < ‖(x : SturmH lam)‖ :=
    norm_pos_iff.mpr hx
  exact (mul_le_mul_iff_of_pos_right hpos).mp h

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_positiveShift_gap
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_positiveShift_gap_attained
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_positiveShift_gap_optimal

end GegenbauerFock.Ultraspherical
