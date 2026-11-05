import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventZeroContinuousSpectrum
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventPointEigenvalues
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — zero belongs to the continuous spectrum of the actual Sturm resolvent

For lambda,t>0 the positive resolvent of the canonical CLOSED Sturm
operator acts on the full weighted real-L² Hilbert space. It is
injective, self-adjoint, has dense nonclosed proper range, and is not
invertible on the whole Hilbert space. Thus zero belongs to its
operator spectrum but is not an eigenvalue.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Zero is in the operator spectrum of the true bounded resolvent.
It is not invertible as a bounded endomorphism because it is not onto. -/
theorem sturmRealResolvent_zero_mem_spectrum
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (0 : ℝ) ∈ spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  apply spectrum.zero_mem ℝ
  intro hunit
  exact sturmRealResolvent_not_surjective lam t hlam ht
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2

/-- The exact zero continuous-spectrum criterion on weighted real L²:
spectral membership, trivial kernel, dense and proper image. -/
theorem sturmRealResolvent_zero_continuous_spectrum
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (0 : ℝ) ∈ spectrum ℝ
      (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    (sturmRealPositiveResolventFullCLM lam t hlam ht).ker = ⊥ ∧
    (sturmRealPositiveResolventFullCLM lam t hlam ht).range.topologicalClosure =
      (⊤ : Submodule ℝ (H lam)) ∧
    ¬ Function.Surjective (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  refine ⟨sturmRealResolvent_zero_mem_spectrum lam t hlam ht, ?_,
    sturmRealResolvent_dense_range lam t hlam ht,
    sturmRealResolvent_not_surjective lam t hlam ht⟩
  exact LinearMap.ker_eq_bot.mpr
    (sturmRealPositiveResolventFullCLM_injective_from_point_eigenvalues
      lam t hlam ht)

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_zero_mem_spectrum
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_zero_continuous_spectrum

end GegenbauerFock.Ultraspherical
