import GegenbauerFock.RealComplexPositiveSpectralAutomaticTraceClassBridge
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatNuclearProjectiveTrace

/-!
# V007 — concrete real Gegenbauer heat S1 versus positive complex CFC S1

For the GENUINE full weighted-real-L² Gegenbauer heat semigroup H_s,
for every lambda,s>0, the exact REAL projective nuclear norm already
equals its positive heat spectral sum.

This module instantiates the general real/complex automatic trace-class
bridge at that ACTUAL real heat operator. Given any positive bounded
COMPLEX operator whose complete eigenbasis has the same heat eigenvalues,
it DERIVES complex CFC IsTraceClass and its exact norm equality with
the real nuclear infimum. The more geometric variant instead assumes
a concrete basis-preserving real-linear intertwiner and commutation.

Neither variant asserts without proof that a selected complex CFC Gram
is the complexification of the real Sturm heat operator. A concrete
intertwiner, complete complex eigenbasis and positivity must be proved
separately when a specific complex operator is chosen.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

private abbrev RealHeatH (lam : ℝ) := Lp ℝ 2 (measure lam)

variable {HC : Type*}
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- Actual real heat eigenvalues in the canonical complete Gegenbauer
Hilbert basis (not an artificial diagonal model). -/
theorem sturmRealHeat_actual_complete_eigenbasis
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 ≤ s) (n : ℕ) :
    sturmRealHeatLimitCLM lam hlam s hs
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n) =
      Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n) := by
  have hb :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n =
        sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
    simp only [sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [hb]
  exact sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen
    lam hlam s hs n

/-- For any matched positive COMPLEX bounded heat-spectral operator,
the true complex CFC membership is constructed rather than assumed.
Its CFC trace norm equals the exact projective real nuclear norm of
the genuine Gegenbauer heat semigroup. -/
theorem sturmRealHeat_realS1_eq_complexCFC_autoClass_of_matching_spectrum
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s)
    (T : HC →L[ℂ] HC)
    (bC : HilbertBasis ℕ ℂ HC)
    (hTpos : 0 ≤ T)
    (hTmode : ∀ n : ℕ,
      T (bC n) =
        ((Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) : ℝ) : ℂ) •
          bC n) :
    ∃ hTclass : ProbabilisticTheory.IsTraceClass T,
      realNuclearInfimum
          (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) =
        ProbabilisticTheory.traceNorm T hTclass := by
  let bR := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let sigma : ℕ → ℝ :=
    fun n => Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hnonneg : ∀ n : ℕ, 0 ≤ sigma n :=
    fun n => (Real.exp_pos _).le
  have hsum : Summable sigma :=
    sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  have hR (n : ℕ) :
      sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) (bR n) =
        sigma n • bR n :=
    sturmRealHeat_actual_complete_eigenbasis lam s hlam (le_of_lt hs) n
  exact realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_sharedSpectrum
    (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs))
    T bR bC sigma hnonneg hsum hR hTmode hTpos

/-- A matching real-linear intertwiner between the ACTUAL real heat
operator and a positive complex operator automatically supplies the
complex CFC trace-class witness and the sharp cross-field S1 equality. -/
theorem sturmRealHeat_realS1_eq_complexCFC_autoClass_of_intertwining
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s)
    (T : HC →L[ℂ] HC)
    (bC : HilbertBasis ℕ ℂ HC)
    (J : RealHeatH lam →ₗ[ℝ] HC)
    (hJ : ∀ n : ℕ,
      J ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n) = bC n)
    (hcomm : ∀ x : RealHeatH lam,
      T (J x) =
        J (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) x))
    (hTpos : 0 ≤ T) :
    ∃ hTclass : ProbabilisticTheory.IsTraceClass T,
      realNuclearInfimum
          (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) =
        ProbabilisticTheory.traceNorm T hTclass := by
  let bR := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let sigma : ℕ → ℝ :=
    fun n => Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hnonneg : ∀ n : ℕ, 0 ≤ sigma n :=
    fun n => (Real.exp_pos _).le
  have hsum : Summable sigma :=
    sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  have hR (n : ℕ) :
      sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) (bR n) =
        sigma n • bR n :=
    sturmRealHeat_actual_complete_eigenbasis lam s hlam (le_of_lt hs) n
  exact realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_intertwining
    (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs))
    T bR bC J hJ hcomm sigma hnonneg hsum hR hTpos

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_actual_complete_eigenbasis
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_realS1_eq_complexCFC_autoClass_of_matching_spectrum
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_realS1_eq_complexCFC_autoClass_of_intertwining

end GegenbauerFock.Ultraspherical
