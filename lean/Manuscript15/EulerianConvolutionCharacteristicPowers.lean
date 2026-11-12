import Manuscript15.UniformEulerianCharacteristicMeasure
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Manuscript 15 — all convolution powers of the genuine Eulerian uniform measure

The actual probability measure μ_E on [-1/2,1/2], identified in
UniformEulerianCharacteristicMeasure, has characteristic function
  charFun μ_E(t) = rE(t) = sinc(t/2).

Construct its n-fold ADDITIVE convolution distribution for every n≥0,
using the Dirac unit point mass δ₀ as the zero-fold convolution.
Each is a genuine Borel PROBABILITY MEASURE on ℝ. Independently
certified Mathlib Fourier-convolution multiplicativity implies
  charFun (μ_E^{∗n})(t) = (rE(t):ℂ)^n
for all n and t, without an assumption of density smoothness or
an unsupported explicit spline formula.

This exactly connects the Eulerian Fourier profiles of Manuscripts
11–13 with real n-fold probability convolutions. It does not yet
certify the endpoint B-spline formulas, high-order cusp asymptotics,
or probabilistic stability estimates of Manuscript 15.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory
open scoped MeasureTheory

/-- The genuine n-fold additive convolution of the actual centered
uniform interval probability measure. The n=0 distribution is δ₀. -/
noncomputable def eulerianConvolutionPower : ℕ → Measure ℝ
  | 0 => Measure.dirac (0 : ℝ)
  | n + 1 => eulerianUniformMeasure ∗ eulerianConvolutionPower n

/-- EVERY n-fold Eulerian uniform convolution, including n=0,
is an actual Borel probability measure with total mass one. -/
theorem eulerianConvolutionPower_isProbability (n : ℕ) :
    IsProbabilityMeasure (eulerianConvolutionPower n) := by
  induction n with
  | zero =>
      change IsProbabilityMeasure (Measure.dirac (0 : ℝ))
      infer_instance
  | succ n ih =>
      change IsProbabilityMeasure
        (eulerianUniformMeasure ∗ eulerianConvolutionPower n)
      letI : IsProbabilityMeasure (eulerianConvolutionPower n) := ih
      infer_instance

/-- Fourier transform of the actual n-fold uniform convolution
is EXACTLY the n-th complex power of the Eulerian sinc radius
for every real frequency and EVERY natural convolution order. -/
theorem eulerianConvolutionPower_charFun
    (n : ℕ) (t : ℝ) :
    charFun (eulerianConvolutionPower n) t =
      (EulerianCert.FourierModes.rE t : ℂ) ^ n := by
  induction n with
  | zero =>
      simp [eulerianConvolutionPower, charFun_dirac]
  | succ n ih =>
      letI : IsProbabilityMeasure (eulerianConvolutionPower n) :=
        eulerianConvolutionPower_isProbability n
      change charFun
        (eulerianUniformMeasure ∗ eulerianConvolutionPower n) t =
          (EulerianCert.FourierModes.rE t : ℂ) ^ (n + 1)
      rw [charFun_conv, eulerianUniformMeasure_charFun, ih]
      rw [pow_succ, mul_comm]

/-- The actual *measure*, not just its Fourier transform, at
convolution order one is exactly the original centered uniform
interval measure, by the Dirac convolution identity. -/
theorem eulerianConvolutionPower_one :
    eulerianConvolutionPower 1 = eulerianUniformMeasure := by
  simp [eulerianConvolutionPower]

/-- Exact identification of the n-fold Eulerian uniform
convolution distribution among ALL finite real Borel measures:
its entire complex characteristic function uniquely determines it. -/
theorem finiteMeasure_eq_eulerianConvolutionPower_of_charFun
    (n : ℕ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : ∀ t : ℝ,
      charFun ν t = (EulerianCert.FourierModes.rE t : ℂ) ^ n) :
    ν = eulerianConvolutionPower n := by
  letI : IsProbabilityMeasure (eulerianConvolutionPower n) :=
    eulerianConvolutionPower_isProbability n
  apply Measure.ext_of_charFun
  funext t
  exact (h t).trans (eulerianConvolutionPower_charFun n t).symm

/-- Exact one-fold normalization: the first convolution distribution
is the already-constructed genuine uniform centered interval measure
(up to the Dirac convolution unit). -/
theorem eulerianConvolutionPower_one_charFun (t : ℝ) :
    charFun (eulerianConvolutionPower 1) t =
      (EulerianCert.FourierModes.rE t : ℂ) := by
  simpa using eulerianConvolutionPower_charFun 1 t

#print axioms Manuscript15.eulerianConvolutionPower_isProbability
#print axioms Manuscript15.eulerianConvolutionPower_charFun
#print axioms Manuscript15.eulerianConvolutionPower_one_charFun
#print axioms Manuscript15.eulerianConvolutionPower_one
#print axioms Manuscript15.finiteMeasure_eq_eulerianConvolutionPower_of_charFun

end Manuscript15
