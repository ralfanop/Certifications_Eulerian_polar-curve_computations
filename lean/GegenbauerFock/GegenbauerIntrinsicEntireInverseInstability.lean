import GegenbauerFock.GegenbauerIntrinsicEntireFockOperator
import GegenbauerFock.FockNoContinuousReconstruction
import GegenbauerFock.FockInverseInstability

/-!
# V007 — no stable reconstruction from genuine entire Gaussian Fock data

The Bargmann–Fock isometry identifies ℓ² with the independently defined
intrinsic entire Gaussian L² space, but the distinct compact
ultraspherical transform into that target has no stable inverse.
These statements are about the analytic codomain, not only ℓ².
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- No globally continuous, even nonlinear, reconstruction of the
ultraspherical source is possible from genuine entire Gaussian L² data. -/
theorem C_intrinsicEntire_no_continuous_global_reconstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ∃ r : GaussianArea.entireGaussianL2Submodule alpha →
        Lp ℂ 2 (Ultraspherical.measure lam),
      Continuous r ∧
        (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
          r (C_intrinsicEntire lam alpha hlam ha f) = f) := by
  rintro ⟨r, hc, hleft⟩
  apply C_no_continuous_global_reconstruction lam alpha hlam ha
  refine ⟨r ∘ (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha),
    hc.comp (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).continuous, ?_⟩
  intro f
  simpa only [Function.comp_apply, C_intrinsicEntire_apply] using hleft f

/-- Every finite proposed inverse constant fails on some genuine
ultraspherical L² vector, when measured in the true analytic output. -/
theorem C_intrinsicEntire_no_uniform_lower_norm_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      (K : ℝ) * ‖C_intrinsicEntire lam alpha hlam ha f‖ < ‖f‖ := by
  obtain ⟨f, hf⟩ := C_no_uniform_lower_norm_bound lam alpha hlam ha K
  refine ⟨f, ?_⟩
  simpa only [C_intrinsicEntire_norm] using hf

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_no_continuous_global_reconstruction
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_no_uniform_lower_norm_bound

end GegenbauerFock.GeneralUltrasphericalFock
