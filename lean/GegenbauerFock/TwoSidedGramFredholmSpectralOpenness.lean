import GegenbauerFock.TwoSidedGramEssentialSpectrumSingleton
import Mathlib.Analysis.Normed.Operator.Fredholm.Open

/-!
# V007 — closed Fredholm essential spectrum and local index constancy
in the spectral parameter

The non-Fredholm spectral locus is closed for any complex Hilbert-space
endomorphism: its complement is the inverse image of the open Fredholm
operator locus under the norm-continuous map z ↦ T - z I.
At every Fredholm spectral parameter the Fredholm index is locally
constant as a function of that complex parameter.

Applied to both concrete ultraspherical and Gaussian Fock Gram
operators, this gives a certified punctured-plane local statement.
It is distinct from perturbing the operator at a FIXED spectral
parameter, which was separately certified.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The Fredholm essential spectrum of ANY bounded complex Hilbert
space endomorphism is a closed subset of the complex plane. -/
theorem fredholmEssentialSpectrum_isClosed
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    IsClosed (fredholmEssentialSpectrum T) := by
  have hcont :
      Continuous (fun mu : ℂ => T - mu • (1 : H →L[ℂ] H)) := by
    fun_prop
  have hopen : IsOpen {S : H →L[ℂ] H | S.IsFredholm} :=
    ContinuousLinearMap.isOpen_setOfPred_isFredholm
  have hpre :
      IsOpen {mu : ℂ | (T - mu • (1 : H →L[ℂ] H)).IsFredholm} := by
    exact hopen.preimage hcont
  have hclosed :
      IsClosed ({mu : ℂ | (T - mu • (1 : H →L[ℂ] H)).IsFredholm}ᶜ) :=
    hpre.isClosed_compl
  simpa only [fredholmEssentialSpectrum, Set.compl_setOf] using hclosed

/-- Wherever T - mu I is Fredholm, the Fredholm index is locally
constant under changes of the complex spectral parameter mu. -/
theorem fredholmShift_index_locally_constant_in_parameter
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (mu : ℂ)
    (hf : ContinuousLinearMap.IsFredholm
      (T - mu • (1 : H →L[ℂ] H))) :
    ∀ᶠ nu : ℂ in 𝓝 mu,
      (T - nu • (1 : H →L[ℂ] H)).IsFredholm ∧
      (T - nu • (1 : H →L[ℂ] H)).index =
        (T - mu • (1 : H →L[ℂ] H)).index := by
  have hcont :
      ContinuousAt (fun z : ℂ => T - z • (1 : H →L[ℂ] H)) mu :=
    (by fun_prop : Continuous
      (fun z : ℂ => T - z • (1 : H →L[ℂ] H))).continuousAt
  exact hcont.tendsto.eventually
    (hf.eventually_nhds.and hf.eventually_nhds_index_eq)

/-- The source ultraspherical Gram has locally constant Fredholm index
in the punctured complex spectral plane. -/
theorem sourceGram_nonzero_parameter_fredholm_index_locally_constant
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ∀ᶠ nu : ℂ in 𝓝 mu,
      (gram lam alpha hlam ha -
        nu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).IsFredholm ∧
      (gram lam alpha hlam ha -
        nu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).index =
      (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).index := by
  exact fredholmShift_index_locally_constant_in_parameter
    (gram lam alpha hlam ha) mu
    (sourceGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu)

/-- The full Fock coefficient Gram has locally constant Fredholm index
in the punctured complex spectral plane. -/
theorem outputGram_nonzero_parameter_fredholm_index_locally_constant
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ∀ᶠ nu : ℂ in 𝓝 mu,
      (outputGram lam alpha hlam ha -
        nu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).IsFredholm ∧
      (outputGram lam alpha hlam ha -
        nu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).index =
      (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).index := by
  exact fredholmShift_index_locally_constant_in_parameter
    (outputGram lam alpha hlam ha) mu
    (outputGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu)

/-- Simultaneous local Fredholm-index constancy for the two
infinite-dimensional Gram operators at each nonzero complex parameter. -/
theorem two_sided_gram_nonzero_parameter_fredholm_index_locally_constant
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (∀ᶠ nu : ℂ in 𝓝 mu,
      (gram lam alpha hlam ha -
        nu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).IsFredholm ∧
      (gram lam alpha hlam ha -
        nu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).index =
      (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).index) ∧
    (∀ᶠ nu : ℂ in 𝓝 mu,
      (outputGram lam alpha hlam ha -
        nu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).IsFredholm ∧
      (outputGram lam alpha hlam ha -
        nu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).index =
      (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).index) :=
  ⟨sourceGram_nonzero_parameter_fredholm_index_locally_constant
      lam alpha hlam ha mu hmu,
    outputGram_nonzero_parameter_fredholm_index_locally_constant
      lam alpha hlam ha mu hmu⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fredholmEssentialSpectrum_isClosed
#print axioms GegenbauerFock.GeneralUltrasphericalFock.fredholmShift_index_locally_constant_in_parameter
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_parameter_fredholm_index_locally_constant
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_parameter_fredholm_index_locally_constant
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_parameter_fredholm_index_locally_constant

end GegenbauerFock.GeneralUltrasphericalFock
