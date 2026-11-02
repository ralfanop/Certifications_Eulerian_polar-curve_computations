import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedMeanZeroCoercivitySharp

/-!
# V007 — two-source quantitative stability for the true closed Sturm operator

For λ>0, set A=closure(L_λ) on the actual real Hilbert space
L²(ν_λ;ℝ). Suppose x and y belong to its genuine closed graph
domain, and each has vanishing degree-zero Gegenbauer Fourier mode.

The certified sharp one-source coercivity estimate, applied to the
difference x-y in the *actual linear graph domain*, gives

    (1+2λ)‖x-y‖ ≤ ‖A x-A y‖.

Consequently, if two operator data differ by at most ε, then their
mean-zero preimages differ by at most ε/(1+2λ). In particular, the
unbounded closed operator is quantitatively injective on its
mean-zero subspace, with a sharp inverse-Lipschitz estimate.

The proof uses genuine domain linearity and the linear isometry
of the normalized Gegenbauer Fourier basis, not any finite-cutoff
identification.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The canonical closed Sturm operator satisfies a two-source
coercivity estimate, sharp in the degree-one Fourier direction. -/
theorem sturmRealClosed_meanZero_twoSource_coercive
    (lam : ℝ) (hlam : 0 < lam)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (x : SturmH lam) 0 = 0)
    (hy0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (y : SturmH lam) 0 = 0) :
    (1 + 2 * lam) * ‖(x : SturmH lam) - (y : SturmH lam)‖ ≤
      ‖(sturmRealPartialOperator lam hlam).closure x -
        (sturmRealPartialOperator lam hlam).closure y‖ := by
  let A := (sturmRealPartialOperator lam hlam).closure
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let d : A.domain := x - y
  have hd0 : (b.repr (d : SturmH lam)) 0 = 0 := by
    change (b.repr ((x : SturmH lam) - (y : SturmH lam))) 0 = 0
    rw [map_sub]
    simp [hx0, hy0]
  have hcoercive := sturmRealClosed_meanZero_coercive lam hlam d hd0
  change (1 + 2 * lam) * ‖(d : SturmH lam)‖ ≤ ‖A d‖ at hcoercive
  have hd : (d : SturmH lam) = (x : SturmH lam) - (y : SturmH lam) := rfl
  have hAd : A d = A x - A y := by
    change A (x - y) = A x - A y
    exact LinearPMap.map_sub A x y
  simpa only [hd, hAd] using hcoercive

/-- Quantitative two-source inverse stability with a bound on the
difference between the *actual* closed Sturm differential outputs. -/
theorem sturmRealClosed_meanZero_twoSource_residual_stability
    (lam : ℝ) (hlam : 0 < lam)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (x : SturmH lam) 0 = 0)
    (hy0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (y : SturmH lam) 0 = 0)
    (ε : ℝ)
    (hdata : ‖(sturmRealPartialOperator lam hlam).closure x -
        (sturmRealPartialOperator lam hlam).closure y‖ ≤ ε) :
    ‖(x : SturmH lam) - (y : SturmH lam)‖ ≤
      ε / (1 + 2 * lam) := by
  have hgap : 0 < 1 + 2 * lam := by linarith
  apply (le_div_iff₀ hgap).2
  calc
    ‖(x : SturmH lam) - (y : SturmH lam)‖ * (1 + 2 * lam) =
        (1 + 2 * lam) * ‖(x : SturmH lam) - (y : SturmH lam)‖ := by ring
    _ ≤ ‖(sturmRealPartialOperator lam hlam).closure x -
        (sturmRealPartialOperator lam hlam).closure y‖ :=
      sturmRealClosed_meanZero_twoSource_coercive lam hlam x y hx0 hy0
    _ ≤ ε := hdata

/-- Uniqueness of mean-zero closed Sturm sources with equal
operator data, without assuming a bounded whole-space inverse. -/
theorem sturmRealClosed_meanZero_unique_of_same_data
    (lam : ℝ) (hlam : 0 < lam)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (x : SturmH lam) 0 = 0)
    (hy0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (y : SturmH lam) 0 = 0)
    (heq : (sturmRealPartialOperator lam hlam).closure x =
      (sturmRealPartialOperator lam hlam).closure y) :
    x = y := by
  have h :=
    sturmRealClosed_meanZero_twoSource_coercive lam hlam x y hx0 hy0
  rw [heq, sub_self, norm_zero] at h
  have hgap : 0 < 1 + 2 * lam := by linarith
  have hnorm : ‖(x : SturmH lam) - (y : SturmH lam)‖ = 0 := by
    have hnonneg : 0 ≤ (1 + 2 * lam) *
        ‖(x : SturmH lam) - (y : SturmH lam)‖ :=
      mul_nonneg hgap.le (norm_nonneg _)
    have hprod : (1 + 2 * lam) *
        ‖(x : SturmH lam) - (y : SturmH lam)‖ = 0 :=
      le_antisymm h hnonneg
    exact (mul_eq_zero.mp hprod).resolve_left hgap.ne'
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Two mean-zero solutions approximately matching the *same noisy*
weighted-L² observation are close, with the certified sharp spectral
gap and the sum of their individual residual tolerances. -/
theorem sturmRealClosed_meanZero_commonObservation_noise_stability
    (lam : ℝ) (hlam : 0 < lam)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (x : SturmH lam) 0 = 0)
    (hy0 : (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (y : SturmH lam) 0 = 0)
    (observation : SturmH lam) (εx εy : ℝ)
    (hxnoise : ‖(sturmRealPartialOperator lam hlam).closure x -
      observation‖ ≤ εx)
    (hynoise : ‖(sturmRealPartialOperator lam hlam).closure y -
      observation‖ ≤ εy) :
    ‖(x : SturmH lam) - (y : SturmH lam)‖ ≤
      (εx + εy) / (1 + 2 * lam) := by
  let A := (sturmRealPartialOperator lam hlam).closure
  have hdata : ‖A x - A y‖ ≤ εx + εy := by
    calc
      ‖A x - A y‖ =
          ‖(A x - observation) + -(A y - observation)‖ := by
            congr 1
            abel
      _ ≤ ‖A x - observation‖ + ‖-(A y - observation)‖ :=
        norm_add_le _ _
      _ = ‖A x - observation‖ + ‖A y - observation‖ := by
        rw [norm_neg]
      _ ≤ εx + εy := add_le_add hxnoise hynoise
  exact sturmRealClosed_meanZero_twoSource_residual_stability
    lam hlam x y hx0 hy0 (εx + εy) hdata

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_twoSource_coercive
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_twoSource_residual_stability
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_unique_of_same_data
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_meanZero_commonObservation_noise_stability

end GegenbauerFock.Ultraspherical
