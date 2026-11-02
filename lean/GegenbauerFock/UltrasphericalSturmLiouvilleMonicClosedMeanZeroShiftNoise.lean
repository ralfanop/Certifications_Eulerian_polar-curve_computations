import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedMeanZeroShiftTwoSource

/-!
# V007 — stable noisy-data reconstruction and optimal shifted two-source gap

The true canonical closed Gegenbauer Sturm operator A on weighted real L²
satisfies a sharp two-source bound on its mean-zero domain. For t >= 0,
residuals εx and εy relative to one common shifted observation imply

  ‖x-y‖ <= (εx+εy)/(t+1+2λ).

The rate t+1+2λ is also optimal for pairs of mean-zero sources,
by selecting the second source to be zero and the first to be the
degree-one normalized Gegenbauer eigenmode.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory
private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Common-observation noise stability for two mean-zero genuine
closed-domain sources of the shifted differential equation. -/
theorem sturmRealClosed_meanZero_shift_commonObservation_noise
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (x : SturmH lam) 0 = 0)
    (hy0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (y : SturmH lam) 0 = 0)
    (observation : SturmH lam) (εx εy : ℝ)
    (hxnoise :
      ‖(t • (x : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure x) -
        observation‖ ≤ εx)
    (hynoise :
      ‖(t • (y : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure y) -
        observation‖ ≤ εy) :
    ‖(x : SturmH lam) - (y : SturmH lam)‖ ≤
      (εx + εy) / (t + (1 + 2 * lam)) := by
  let A := (sturmRealPartialOperator lam hlam).closure
  let Sx : SturmH lam := t • (x : SturmH lam) - A x
  let Sy : SturmH lam := t • (y : SturmH lam) - A y
  have hdata : ‖Sx - Sy‖ ≤ εx + εy := by
    calc
      ‖Sx - Sy‖ = ‖(Sx - observation) + -(Sy - observation)‖ := by
        congr 1
        abel
      _ ≤ ‖Sx - observation‖ + ‖-(Sy - observation)‖ :=
        norm_add_le _ _
      _ = ‖Sx - observation‖ + ‖Sy - observation‖ := by rw [norm_neg]
      _ ≤ εx + εy := add_le_add hxnoise hynoise
  exact sturmRealClosed_meanZero_shift_twoSource_residual
    lam t hlam ht x y hx0 hy0 (εx + εy) hdata

/-- The sharp rate t+1+2λ cannot be increased in any uniform
two-source mean-zero shifted lower bound on the closed operator. -/
theorem sturmRealClosed_meanZero_shift_twoSource_constant_optimal
    (lam t C : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t)
    (hbound :
      ∀ x y : (sturmRealPartialOperator lam hlam).closure.domain,
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) 0 = 0 →
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (y : SturmH lam) 0 = 0 →
        C * ‖(x : SturmH lam) - (y : SturmH lam)‖ ≤
          ‖(t • (x : SturmH lam) -
              (sturmRealPartialOperator lam hlam).closure x) -
            (t • (y : SturmH lam) -
              (sturmRealPartialOperator lam hlam).closure y)‖) :
    C ≤ t + (1 + 2 * lam) := by
  apply sturmRealClosed_meanZero_positiveShift_gap_optimal lam t C hlam ht
  intro x hx0
  have hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        ((0 : (sturmRealPartialOperator lam hlam).closure.domain) : SturmH lam)
        0 = 0 := by simp
  have h := hbound x 0 hx0 hzero
  simpa using h

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_shift_commonObservation_noise
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_shift_twoSource_constant_optimal

end GegenbauerFock.Ultraspherical
