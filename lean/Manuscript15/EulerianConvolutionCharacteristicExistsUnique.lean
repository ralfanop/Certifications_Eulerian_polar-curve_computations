import Manuscript15.EulerianConvolutionFourierGeometricDecay

/-!
# Manuscript 15 — existence and uniqueness of every Eulerian sinc-power law

Earlier genuinely operator-independent results construct the centered uniform
Borel probability measure μ_E and establish, for every n≥0, that the
ACTUAL n-fold additive convolution μ_E^{∗n} is a probability measure with
complex characteristic function (r_E(t):ℂ)^n.

The Fourier measure-extensionality theorem, already certified for these
convolution powers, yields full existence-and-uniqueness results in the
space of Borel probability measures. We formalize both the all-frequency
identity and its much stronger countable data-recovery version: even the
values of the characteristic function at rational frequencies uniquely
determine the probability law.

The construction does not rely on moments, B-spline densities,
Fourier inversion of a nonintegrable function, or any unverified claim
about physical realizations.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory

/-- For every natural order n, there exists exactly ONE real Borel
probability measure whose entire complex characteristic function is
the n-th power of the Eulerian sinc Fourier profile. -/
theorem eulerianConvolutionPower_existsUnique_probability (n : ℕ) :
    ∃! μ : Measure ℝ,
      IsProbabilityMeasure μ ∧
      ∀ t : ℝ, charFun μ t =
        (EulerianCert.FourierModes.rE t : ℂ) ^ n := by
  refine ⟨eulerianConvolutionPower n, ?_, ?_⟩
  · exact ⟨eulerianConvolutionPower_isProbability n,
      eulerianConvolutionPower_charFun n⟩
  · intro μ hμ
    letI : IsProbabilityMeasure μ := hμ.1
    exact finiteMeasure_eq_eulerianConvolutionPower_of_charFun n μ hμ.2

/-- Even the COUNTABLE set of characteristic values at rational
frequencies determines the genuine n-fold Eulerian uniform
convolution probability law uniquely; the law always exists. -/
theorem eulerianConvolutionPower_existsUnique_probability_from_rationals
    (n : ℕ) :
    ∃! μ : Measure ℝ,
      IsProbabilityMeasure μ ∧
      ∀ q : ℚ, charFun μ (q : ℝ) =
        (EulerianCert.FourierModes.rE (q : ℝ) : ℂ) ^ n := by
  refine ⟨eulerianConvolutionPower n, ?_, ?_⟩
  · exact ⟨eulerianConvolutionPower_isProbability n,
      fun q => eulerianConvolutionPower_charFun n (q : ℝ)⟩
  · intro μ hμ
    letI : IsProbabilityMeasure μ := hμ.1
    exact finiteMeasure_eq_eulerianConvolutionPower_of_charFun_rat n μ hμ.2

#print axioms Manuscript15.eulerianConvolutionPower_existsUnique_probability
#print axioms Manuscript15.eulerianConvolutionPower_existsUnique_probability_from_rationals

end Manuscript15
