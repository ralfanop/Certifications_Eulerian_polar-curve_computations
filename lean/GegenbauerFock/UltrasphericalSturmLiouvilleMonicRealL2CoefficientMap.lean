import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2CoefficientSeparation

/-!
# V007 — injective full Gegenbauer coefficient analysis map

The explicit all-degree monic Gegenbauer eigenpolynomials give a
concrete, exact linear analysis map from the TRUE ultraspherical
weighted real L² Hilbert space into real coefficient sequences.
The previous kernel-certified separation of all scalar products
makes this infinite coefficient map injective without postulating
orthonormal normalization or the existence of a spectral basis.

The sequence target is the full product ℕ → ℝ, not yet ℓ²; the
later normalized Hilbert-basis construction will strengthen it.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Genuine infinite Gegenbauer coefficient analysis as a linear
map from actual weighted real L² into the space of sequences. -/
noncomputable def sturmMonicEigenCandidate_realL2_analysis
    (lam : ℝ) (hlam : 0 < lam) :
    SturmH lam →ₗ[ℝ] (ℕ → ℝ) :=
  LinearMap.pi fun n : ℕ =>
    innerSL ℝ (sturmRealPolynomialLp lam hlam
      (sturmMonicEigenCandidate lam n))

/-- The actual coefficient coordinates are the real L² inner
products with the explicit Sturm eigenpolynomials. -/
theorem sturmMonicEigenCandidate_realL2_analysis_apply
    (lam : ℝ) (hlam : 0 < lam)
    (f : SturmH lam) (n : ℕ) :
    sturmMonicEigenCandidate_realL2_analysis lam hlam f n =
      inner ℝ
        (sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n)) f := rfl

/-- Infinite Gegenbauer coefficients uniquely determine a genuine
weighted-real-L² function. No reconstruction hypothesis is used. -/
theorem sturmMonicEigenCandidate_realL2_analysis_injective
    (lam : ℝ) (hlam : 0 < lam) :
    Function.Injective (sturmMonicEigenCandidate_realL2_analysis lam hlam) := by
  intro f g hfg
  apply sturmMonicEigenCandidate_realL2_coefficients_injective
    lam hlam f g
  intro n
  have hn := congrArg (fun h : ℕ → ℝ => h n) hfg
  simpa only [sturmMonicEigenCandidate_realL2_analysis_apply,
    monicModes] using hn

/-- The exact infinite Gegenbauer analysis map has trivial kernel. -/
theorem sturmMonicEigenCandidate_realL2_analysis_ker_eq_bot
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmMonicEigenCandidate_realL2_analysis lam hlam).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (sturmMonicEigenCandidate_realL2_analysis_injective lam hlam)

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_analysis_apply
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_analysis_injective
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_analysis_ker_eq_bot

end GegenbauerFock.Ultraspherical
