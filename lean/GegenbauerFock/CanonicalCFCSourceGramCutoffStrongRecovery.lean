import GegenbauerFock.SingularDiagonalCoordinates
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# V007 — strong finite spectral-cutoff inversion of the source Gram

The exact genuine bounded Gram C* C acts diagonally with strictly
positive eigenvalues mu_i on a complete source Hilbert basis.
Finite-rank inverse filters 1 / mu_i are bounded for each finite
spectral set and recover every source in the strong Hilbert topology.

There is no uniform bounded inverse, and no claim of operator-norm
convergence or a strictly positive global spectral gap.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

private def sourceGramCutoff
    {ι : Type*} (lam : ℝ)
    (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (mu : ι → ℝ) (s : Finset ι) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  ∑ i ∈ s, ((mu i : ℂ)⁻¹) • rankOne ℂ (u i) (u i)

/-- The genuine source Gram admits strong finite-spectral-cutoff
reconstruction through strictly positive actual Gram eigenvalues. -/
theorem exists_sourceGram_cutoff_strong_recovery
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (R : Finset ι →
        Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)),
      ∀ (f : Lp ℂ 2 (Ultraspherical.measure lam)),
        Tendsto (fun s : Finset ι =>
          R s (gram lam alpha hlam ha f)) atTop (nhds f) := by
  classical
  obtain ⟨ι, u, v, mu, hpos, _hsummable, _hK, hC, hAdj⟩ :=
    exists_bilateral_singular_diagonal_coordinates_kummer
      lam alpha hlam ha
  have hdiag (f : Lp ℂ 2 (Ultraspherical.measure lam)) (i : ι) :
      u.repr (gram lam alpha hlam ha f) i =
        (mu i : ℂ) * u.repr f i := by
    have hsq : (Real.sqrt (mu i) : ℂ) *
        (Real.sqrt (mu i) : ℂ) = (mu i : ℂ) := by
      exact_mod_cast (Real.sq_sqrt (hpos i).le)
    change u.repr (C_adjoint lam alpha hlam ha
      (C lam alpha hlam ha f)) i = _
    rw [hAdj (C lam alpha hlam ha f) i, hC f i]
    rw [← mul_assoc, hsq]
  let R : Finset ι →
      Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam) :=
    fun s => sourceGramCutoff lam u mu s
  refine ⟨ι, R, ?_⟩
  intro f
  have hterm (i : ι) :
      (((mu i : ℂ)⁻¹) • rankOne ℂ (u i) (u i))
        (gram lam alpha hlam ha f) =
      u.repr f i • u i := by
    have hne : (mu i : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hpos i))
    calc
      (((mu i : ℂ)⁻¹) • rankOne ℂ (u i) (u i))
          (gram lam alpha hlam ha f) =
        ((mu i : ℂ)⁻¹ * u.repr (gram lam alpha hlam ha f) i)
          • u i := by
        simp only [ContinuousLinearMap.smul_apply,
          rankOne_apply, smul_smul, u.repr_apply_apply]
      _ = u.repr f i • u i := by
        rw [hdiag f i, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hsum : HasSum
      (fun i : ι =>
        (((mu i : ℂ)⁻¹) • rankOne ℂ (u i) (u i))
          (gram lam alpha hlam ha f)) f := by
    have heq :
        (fun i : ι =>
          (((mu i : ℂ)⁻¹) • rankOne ℂ (u i) (u i))
            (gram lam alpha hlam ha f)) =
        (fun i : ι => u.repr f i • u i) := by
      funext i
      exact hterm i
    rw [heq]
    exact u.hasSum_repr f
  simpa only [R, sourceGramCutoff, Finset.sum_apply] using hsum

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_sourceGram_cutoff_strong_recovery

end GegenbauerFock.GeneralUltrasphericalFock
