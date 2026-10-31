import GegenbauerFock.SingularDiagonalCoordinates
import GegenbauerFock.CanonicalCFCRootNoUniformRecoverySequence
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# V007 — strong finite-singular-cutoff regularization of the true Fock transform

The complete source and target singular Hilbert bases of the actual
ultraspherical-to-Fock operator yield bounded finite-rank spectral
cutoff reconstruction maps. Their compositions with the actual Fock
operator tend strongly to the identity as the finite spectral
index set increases.

This does NOT assert convergence in operator norm (which was separately
proved impossible). It makes no assertion of a bounded exact inverse.
-/

noncomputable section

open MeasureTheory Filter InnerProductSpace

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Actual finite-rank reconstruction of Hilbert source data from the
target singular coefficients, divided by strictly positive singular
values. The index set is an arbitrary finite subset of the complete
singular-basis index type. -/
private def singularCutoff
    {H K ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : HilbertBasis ι ℂ H) (v : HilbertBasis ι ℂ K)
    (mu : ι → ℝ) (s : Finset ι) : K →L[ℂ] H :=
  ∑ i ∈ s, ((Real.sqrt (mu i) : ℂ)⁻¹) •
    (rankOne ℂ (u i) (v i))

/-- A diagonalization of a bounded transform in complete singular
Hilbert bases implies strong finite-rank spectral cutoff recovery.
Positivity of each squared singular value is the only spectral
assumption: no uniform lower bound is needed. -/
theorem singularCutoff_strong_recovery
    {H K ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K)
    (u : HilbertBasis ι ℂ H) (v : HilbertBasis ι ℂ K)
    (mu : ι → ℝ)
    (hpos : ∀ i, 0 < mu i)
    (hdiag : ∀ (f : H) (i : ι),
      v.repr (T f) i = (Real.sqrt (mu i) : ℂ) * u.repr f i)
    (f : H) :
    Tendsto
      (fun s : Finset ι => singularCutoff u v mu s (T f))
      atTop (nhds f) := by
  classical
  have hterm (i : ι) :
      (((Real.sqrt (mu i) : ℂ)⁻¹) •
        (rankOne ℂ (u i) (v i))) (T f) =
        (u.repr f i) • u i := by
    have hne : (Real.sqrt (mu i) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hpos i)))
    calc
      (((Real.sqrt (mu i) : ℂ)⁻¹) •
          (rankOne ℂ (u i) (v i))) (T f) =
          ((Real.sqrt (mu i) : ℂ)⁻¹ *
            v.repr (T f) i) • u i := by
            simp only [ContinuousLinearMap.smul_apply,
              rankOne_apply, smul_smul, v.repr_apply_apply]
      _ = (u.repr f i) • u i := by
            rw [hdiag f i, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hsum : HasSum
      (fun i : ι =>
        (((Real.sqrt (mu i) : ℂ)⁻¹) •
          rankOne ℂ (u i) (v i)) (T f)) f := by
    have heq :
        (fun i : ι =>
          (((Real.sqrt (mu i) : ℂ)⁻¹) •
            rankOne ℂ (u i) (v i)) (T f)) =
          (fun i : ι => u.repr f i • u i) := by
      funext i
      exact hterm i
    rw [heq]
    exact u.hasSum_repr f
  simpa only [singularCutoff, Finset.sum_apply] using hsum

/-- The true compact Gegenbauer–Fock operator has an actual family of
bounded finite-rank singular-cutoff reconstructors with strong recovery
on the FULL infinite-dimensional weighted L² source space. -/
theorem exists_C_singularCutoff_strong_recovery
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (R : Finset ι →
        InfiniteAnalysis.FockCoefficients →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)),
      ∀ (f : Lp ℂ 2 (Ultraspherical.measure lam)),
        Tendsto (fun s : Finset ι => R s (C lam alpha hlam ha f))
          atTop (nhds f) := by
  classical
  obtain ⟨ι, u, v, mu, hpos, hsum, hK, hdiag, hAdj⟩ :=
    exists_bilateral_singular_diagonal_coordinates_kummer
      lam alpha hlam ha
  refine ⟨ι, (fun s => singularCutoff u v mu s), ?_⟩
  intro f
  exact singularCutoff_strong_recovery
    (C lam alpha hlam ha) u v mu hpos hdiag f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.singularCutoff_strong_recovery
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_C_singularCutoff_strong_recovery

end GegenbauerFock.GeneralUltrasphericalFock
