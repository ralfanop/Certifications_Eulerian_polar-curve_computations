import Mathlib

/-!
# General Gegenbauer/ultraspherical probability measure

For λ > 0, define the symmetric ultraspherical probability measure by
pushing forward the Mathlib Beta(λ + 1/2, λ + 1/2) probability law
under x ↦ 2x - 1.

This definition is a concrete measure, not an abstract unspecified
probability measure. A change-of-variables proof equating its
Lebesgue density with the classical Gamma-normalized
(1-u²)^(λ-1/2) profile remains a separate obligation.
Likewise the general even moments and symmetry must be
proved separately.

Mathlib's betaMeasure and its probability theorem already include
the analytic Gamma/Beta normalization proof.
-/

open MeasureTheory ProbabilityTheory

namespace GegenbauerFock.Ultraspherical

/-- The equal Beta shape parameters associated with ultraspherical λ. -/
def shape (lam : ℝ) : ℝ := lam + 1 / 2

/-- Affine change of variables transporting the beta law to [-1,1]. -/
def betaToInterval (x : ℝ) : ℝ := 2*x - 1

/-- Concrete general ultraspherical probability measure. -/
noncomputable def measure (lam : ℝ) : Measure ℝ :=
  (ProbabilityTheory.betaMeasure (shape lam) (shape lam)).map betaToInterval

theorem shape_pos (lam : ℝ) (hlam : 0 < lam) : 0 < shape lam := by
  unfold shape
  linarith

/-- Genuine normalization of the general-parameter measure. -/
theorem probability (lam : ℝ) (hlam : 0 < lam) :
    IsProbabilityMeasure (measure lam) := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.betaMeasure (shape lam) (shape lam)) :=
    ProbabilityTheory.isProbabilityMeasureBeta
      (shape_pos lam hlam) (shape_pos lam hlam)
  unfold measure
  infer_instance

theorem measure_univ (lam : ℝ) (hlam : 0 < lam) :
    measure lam Set.univ = 1 := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  exact IsProbabilityMeasure.measure_univ

/-- The probability normalization is also available as an actual
Bochner integral of the constant real function. -/
theorem integral_one (lam : ℝ) (hlam : 0 < lam) :
    (∫ _u : ℝ, (1 : ℝ) ∂(measure lam)) = 1 := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  simp

/-- The Mathlib symmetric Beta density is strictly positive
inside its support, for every positive ultraspherical λ. -/
theorem beta_density_pos (lam x : ℝ) (hlam : 0 < lam)
    (hx0 : 0 < x) (hx1 : x < 1) :
    0 < ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x :=
  ProbabilityTheory.betaPDFReal_pos hx0 hx1
    (shape_pos lam hlam) (shape_pos lam hlam)

#print axioms GegenbauerFock.Ultraspherical.shape_pos
#print axioms GegenbauerFock.Ultraspherical.probability
#print axioms GegenbauerFock.Ultraspherical.measure_univ
#print axioms GegenbauerFock.Ultraspherical.integral_one
#print axioms GegenbauerFock.Ultraspherical.beta_density_pos

end GegenbauerFock.Ultraspherical
