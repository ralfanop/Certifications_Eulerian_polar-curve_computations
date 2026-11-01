import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealSpectralModes
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2CoefficientMap
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph

/-!
# V007 — exact full-L² coordinate diagonalization of the bounded Sturm resolvent

The previously certified true weighted-real-L² Gegenbauer coefficient
analysis is injective. The positive-shift resolvent is symmetric on
all of L² and sends each explicit degree-n monic mode to the scalar
(t+n(n+2λ))⁻¹ times itself. It follows that the coefficient of
R_t f is exactly this scalar times the coefficient of f, for
EVERY f in the Hilbert space, without a finite-degree truncation.

This is a rigorous diagonalization of the bounded resolvent in the
injective all-degree coefficient coordinates. Normalized Hilbert-basis
and weighted unbounded-domain statements remain separate.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The full bounded Sturm resolvent has exactly the Gegenbauer
spectral multiplier on every monic analysis coordinate, for every
real weighted-L² function f, not merely polynomial f. -/
theorem sturmMonicEigenCandidate_full_resolvent_inner_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) (n : ℕ) :
    inner ℝ
      (sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n))
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) =
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ *
      inner ℝ
        (sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n)) f := by
  let g : SturmH lam :=
    sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n)
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hsym :=
    sturmRealPositiveResolventFullCLM_inner_symmetric
      lam t hlam ht g f
  have hmode :=
    sturmMonicEigenCandidate_full_resolvent_diagonal
      lam t hlam ht n
  change R g =
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ • g at hmode
  rw [hmode, real_inner_smul_left] at hsym
  exact hsym.symm

/-- Exact action of the real-L² bounded resolvent on the
injective infinite Gegenbauer coefficient analysis map. -/
theorem sturmMonicEigenCandidate_realL2_analysis_resolvent_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) (n : ℕ) :
    sturmMonicEigenCandidate_realL2_analysis lam hlam
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) n =
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ *
      sturmMonicEigenCandidate_realL2_analysis lam hlam f n := by
  simpa only [sturmMonicEigenCandidate_realL2_analysis_apply] using
    sturmMonicEigenCandidate_full_resolvent_inner_diagonal
      lam t hlam ht f n

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_full_resolvent_inner_diagonal
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_analysis_resolvent_diagonal

end GegenbauerFock.Ultraspherical
