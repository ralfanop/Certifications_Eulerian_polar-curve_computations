import GegenbauerFock.GegenbauerIntrinsicEntireInverseInstability
import GegenbauerFock.FockApproximateNullNoStrongLimit

/-!
# V007 — genuine analytic Fock approximate-null sequence without source limit

The compact ultraspherical transform into actual Gaussian entire L²
is injective, but has unit source vectors whose entire Fock images
converge strongly to zero. No strong L² source limit exists. This
explicitly separates uniqueness from stable reconstruction.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Actual unit ultraspherical L² vectors with vanishing intrinsic
holomorphic Gaussian L² images and no strongly convergent source
subsequence. No nonzero kernel vector is asserted. -/
theorem C_intrinsicEntire_normalized_approximate_null_no_strong_limit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => C_intrinsicEntire lam alpha hlam ha (u n))
        atTop (nhds (0 : GaussianArea.entireGaussianL2Submodule alpha)) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ¬ Tendsto u atTop (nhds f)) := by
  obtain ⟨u, hunit, hcoeff, hnostrong⟩ :=
    C_exists_approximate_null_sequence_without_strong_limit
      lam alpha hlam ha
  refine ⟨u, hunit, ?_, hnostrong⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hn :
      (fun n : ℕ => ‖C_intrinsicEntire lam alpha hlam ha (u n)‖) =
      (fun n : ℕ => ‖C lam alpha hlam ha (u n)‖) := by
    funext n
    exact C_intrinsicEntire_norm lam alpha hlam ha (u n)
  rw [hn]
  exact tendsto_zero_iff_norm_tendsto_zero.mp hcoeff

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_normalized_approximate_null_no_strong_limit

end GegenbauerFock.GeneralUltrasphericalFock
