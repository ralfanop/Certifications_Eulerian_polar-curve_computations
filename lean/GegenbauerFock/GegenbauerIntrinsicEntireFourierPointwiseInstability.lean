import GegenbauerFock.GegenbauerIntrinsicEntireApproximateNullSequence
import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation

/-!
# V007 — unstable pointwise complex Fourier data despite exact uniqueness

The certified compact ultraspherical transform into the genuinely complete
intrinsic Gaussian Fock Hilbert space has normalized source vectors uₙ
whose entire analytic outputs tend strongly to zero, but whose source
vectors have no strongly convergent subsequence limit as a whole.

Continuity of the TRUE Fock coherent evaluation at every complex point
transfers this convergence to the actual complex-frequency Fourier–Bochner
integral, simultaneously in the quantified sense "for every z ∈ ℂ".
The theorem proves that uniqueness of infinite exact Fourier sampling
does NOT imply stability in source norm.

No finite-dimensional section, nonconstructive unproved integration
interchange, or false surjectivity assumption is introduced here.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Source unit vectors can have original complex Fourier–Bochner
integral data tending to zero at EVERY complex frequency, while the
source vectors have no strong limit. The same analytic output sequence
converges to zero in the full intrinsic Fock Hilbert norm. -/
theorem ultraspherical_fourierBochner_normalized_pointwise_null_no_strong_source_limit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ =>
        C_intrinsicEntire lam alpha hlam ha (u n))
        atTop (nhds (0 : GaussianArea.entireGaussianL2Submodule alpha)) ∧
      (∀ z : ℂ,
        Tendsto (fun n : ℕ =>
          ∫ v : ℝ, u n v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam))
          atTop (nhds (0 : ℂ))) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ¬ Tendsto u atTop (nhds f)) := by
  obtain ⟨u, hunit, hFock, hnostrong⟩ :=
    C_intrinsicEntire_normalized_approximate_null_no_strong_limit
      lam alpha hlam ha
  refine ⟨u, hunit, hFock, ?_, hnostrong⟩
  have hcoeff :
      Tendsto (fun n : ℕ => C lam alpha hlam ha (u n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hnorm := tendsto_zero_iff_norm_tendsto_zero.mp hFock
    have heq :
        (fun n : ℕ => ‖C lam alpha hlam ha (u n)‖) =
        (fun n : ℕ => ‖C_intrinsicEntire lam alpha hlam ha (u n)‖) := by
      funext n
      exact (C_intrinsicEntire_norm lam alpha hlam ha (u n)).symm
    rw [heq]
    exact hnorm
  intro z
  have hev :
      Tendsto (fun n : ℕ =>
        FockEvaluation.evaluation alpha ha z
          (C lam alpha hlam ha (u n)))
        atTop (nhds (0 : ℂ)) := by
    have h :=
      ((FockEvaluation.evaluation alpha ha z).continuous.tendsto
        (0 : InfiniteAnalysis.FockCoefficients)).comp hcoeff
    simpa only [map_zero] using h
  have hpoint :
      (fun n : ℕ =>
        ∫ v : ℝ, u n v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
      (fun n : ℕ =>
        FockEvaluation.evaluation alpha ha z
          (C lam alpha hlam ha (u n))) := by
    funext n
    exact (evaluatedOperator_eq_integral lam alpha hlam ha z (u n)).symm
  rw [hpoint]
  exact hev

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_normalized_pointwise_null_no_strong_source_limit

end GegenbauerFock.GeneralUltrasphericalFock
