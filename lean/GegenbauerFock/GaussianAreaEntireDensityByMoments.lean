import GegenbauerFock.GaussianAreaPolarRadialCircleBridge
import GegenbauerFock.GaussianAreaRadialCircleMomentUniqueness
import GegenbauerFock.GaussianAreaTrueMomentKernel
import GegenbauerFock.GaussianAreaIntrinsicResidualCriterion

/-!
# V007 — eliminate the intrinsic Gaussian polynomial-projection residual

The exact polar Fubini and angular-to-circle-average transfer combine
with the positive radial Gamma moment to separate intrinsically entire
Gaussian L² functions by their *true planar* Gaussian moments.  This is
the analytical step absent from the Hilbert coefficient-space isometry.

This file must be compiled and axiom-audited against pinned Lean/Mathlib
before the concluding onto claim is used as a formal certificate.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Pull the (constant in z) real polar Jacobian/density through a
genuine normalized complex circle average. -/
theorem polar_gaussian_circleAverage_smul
    (alpha r : ℝ) (g : ℂ → ℂ) :
    Real.circleAverage
      (fun z : ℂ =>
        r • (((alpha / Real.pi) * Real.exp (-alpha * r ^ 2) : ℝ) • g z))
      0 r =
    ((r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2)) : ℝ) : ℂ) *
      Real.circleAverage g 0 r := by
  let c : ℂ :=
    ((r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2)) : ℝ) : ℂ)
  have heq :
      (fun z : ℂ =>
        r • (((alpha / Real.pi) * Real.exp (-alpha * r ^ 2) : ℝ) • g z)) =
      (fun z : ℂ => c • g z) := by
    funext z
    calc
      r • (((alpha / Real.pi) * Real.exp (-alpha * r ^ 2) : ℝ) • g z) =
          (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) • g z := by
        rw [smul_smul]
      _ = c • g z := by
        simp only [Complex.real_smul, smul_eq_mul, c]_nf
  rw [heq]
  simpa only [smul_eq_mul] using
    (Real.circleAverage_fun_smul (a := c) (f := g) (c := (0 : ℂ)) (R := r))

/-- An actual entire Gaussian area moment is precisely 2α times
the weighted radial integral of the Cauchy circle moments.
The factor is nonzero for every alpha>0. -/
theorem entire_planar_moment_eq_two_alpha_radial_circle
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) =
    ((2 * alpha : ℝ) : ℂ) *
      (∫ r in Set.Ioi (0 : ℝ),
        ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
          Real.circleAverage
            (fun z : ℂ =>
              entireRepresentative alpha x z * star (z ^ n)) 0 r) := by
  let g : ℂ → ℂ :=
    fun z => entireRepresentative alpha x z * star (z ^ n)
  have hcoeff (r : ℝ) :
      (2 * Real.pi) *
          (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) =
        (2 * alpha) * (r * Real.exp (-alpha * r ^ 2)) := by
    field_simp [Real.pi_ne_zero]
  calc
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) =
      (∫ r in Set.Ioi (0 : ℝ),
        (2 * Real.pi) •
          Real.circleAverage
            (fun z : ℂ =>
              r • (((alpha / Real.pi) * Real.exp (-alpha * r ^ 2) : ℝ) •
                g z)) 0 r) :=
      entireRepresentative_planar_moment_eq_radial_circleAverage alpha ha x n
    _ = (∫ r in Set.Ioi (0 : ℝ),
        ((2 * alpha : ℝ) : ℂ) *
          (((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
            Real.circleAverage g 0 r)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [polar_gaussian_circleAverage_smul]
      simp only [Complex.real_smul]
      have hc :
          ((2 * Real.pi : ℝ) : ℂ) *
              ((r * ((alpha / Real.pi) *
                Real.exp (-alpha * r ^ 2)) : ℝ) : ℂ) =
            ((2 * alpha : ℝ) : ℂ) *
              ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) := by
        exact_mod_cast hcoeff r
      rw [← mul_assoc, hc, mul_assoc]
    _ = ((2 * alpha : ℝ) : ℂ) *
        (∫ r in Set.Ioi (0 : ℝ),
          ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
            Real.circleAverage g 0 r) := by
      rw [integral_const_mul]

/-- No nonzero intrinsically entire Gaussian L² vector can have all
its actual planar Gaussian monomial moments equal to zero. -/
theorem intrinsicEntire_eq_zero_of_all_true_gaussian_moments_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha)
    (hz : ∀ n : ℕ,
      (∫ z : ℂ, entireRepresentative alpha x z * star (z ^ n)
        ∂gaussianAreaMeasure alpha) = 0) :
    x = 0 := by
  apply intrinsicGaussian_zero_of_radial_circleMoments_zero alpha ha x
  intro n
  have hplanar :
      (∫ z : ℂ,
        ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
          (entireRepresentative alpha x z * star (z ^ n))) = 0 := by
    calc
      (∫ z : ℂ,
        ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
          (entireRepresentative alpha x z * star (z ^ n))) =
        (∫ z : ℂ, entireRepresentative alpha x z * star (z ^ n)
          ∂gaussianAreaMeasure alpha) := by
          rw [gaussianArea_integral_eq_volume alpha ha]
          apply integral_congr_ae
          filter_upwards [] with z
          simp only [Complex.real_smul, Complex.ofReal_mul]
          ring
      _ = 0 := hz n
  rw [entire_planar_moment_eq_two_alpha_radial_circle alpha ha x n] at hplanar
  have htwo : ((2 * alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ha))
  exact (mul_eq_zero.mp hplanar).resolve_left htwo

/-- Every entire Gaussian L² class belongs to the closed Gaussian
holomorphic-polynomial span. This is the analytically nontrivial
direction of the full Bargmann-Fock coefficient isometry. -/
theorem intrinsicEntire_le_gaussianPolynomialClosure
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≤ gaussianPolynomialClosure alpha ha := by
  apply (intrinsicEntire_le_polynomialClosure_iff_analysis_unique alpha ha).2
  intro x hx hzero
  let y : entireGaussianL2Submodule alpha := ⟨x, hx⟩
  have hm : ∀ n : ℕ,
      (∫ z : ℂ, entireRepresentative alpha y z * star (z ^ n)
        ∂gaussianAreaMeasure alpha) = 0 :=
    (intrinsicAnalysis_zero_iff_all_integral_moments_zero alpha ha y).1 hzero
  have hy : y = 0 :=
    intrinsicEntire_eq_zero_of_all_true_gaussian_moments_zero alpha ha y hm
  exact (congrArg Subtype.val hy)

/-- The intrinsically defined complete holomorphic Gaussian Hilbert
subspace equals the closed span of the actual normalized monomials. -/
theorem intrinsicEntire_eq_gaussianPolynomialClosure
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha = gaussianPolynomialClosure alpha ha := by
  apply le_antisymm
  · exact intrinsicEntire_le_gaussianPolynomialClosure alpha ha
  · exact gaussianPolynomialClosure_le_entireGaussianL2Submodule alpha ha

#print axioms GegenbauerFock.GaussianArea.polar_gaussian_circleAverage_smul
#print axioms GegenbauerFock.GaussianArea.entire_planar_moment_eq_two_alpha_radial_circle
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_eq_zero_of_all_true_gaussian_moments_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_le_gaussianPolynomialClosure
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_eq_gaussianPolynomialClosure

end GegenbauerFock.GaussianArea
