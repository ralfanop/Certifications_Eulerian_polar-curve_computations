import GegenbauerFock.GaussianAreaActualL2Vectors
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# V007 — actual orthonormal family in weighted Gaussian L²(ℂ)

The previously constructed normalized complex monomials are genuine
weighted Gaussian L² vectors. The exact inner product of these
vectors is computed via Mathlib's L².inner_def, equality of the
a.e. representatives, the Radon–Nikodym density of the Gaussian
area measure, and the kernel-checked monomial integral.

This is a genuine Hilbert-space orthonormality claim, beyond the
finite formal Gram quadratic form. A surjective isometry onto
the full holomorphic Fock space still requires completeness/density
and a proof that the closed span is exactly the holomorphic subspace.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Real Gaussian density used in the normalized area measure. -/
private def gaussianDensity (alpha : ℝ) (z : ℂ) : ℝ :=
  (alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2)

/-- Convert the Gaussian weighted complex integral of any function
back to the genuine planar Lebesgue integral with explicit density. -/
theorem gaussianArea_integral_eq_volume
    (alpha : ℝ) (ha : 0 < alpha) (f : ℂ → ℂ) :
    (∫ z : ℂ, f z ∂gaussianAreaMeasure alpha) =
      (∫ z : ℂ, ((alpha / Real.pi : ℝ) : ℂ) *
        (f z * (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) ∂volume) := by
  have hmeas : Measurable (fun z : ℂ =>
      ENNReal.ofReal (gaussianDensity alpha z)) := by
    fun_prop
  have hfinite :
      ∀ᵐ z : ℂ ∂(volume : Measure ℂ),
        ENNReal.ofReal (gaussianDensity alpha z) < ⊤ := by
    filter_upwards [] with z
    simp
  rw [gaussianAreaMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  apply integral_congr_ae
  filter_upwards [] with z
  have hnonneg : 0 ≤ gaussianDensity alpha z := by
    dsimp [gaussianDensity]
    positivity
  rw [ENNReal.toReal_ofReal hnonneg, Complex.real_smul]
  dsimp [gaussianDensity]
  push_cast
  ring

/-- The normalized entire monomials are orthonormal in the
ACTUAL completed Gaussian weighted L² Hilbert space. -/
theorem inner_normalizedMonomialL2Vector
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    ⟪normalizedMonomialL2Vector alpha ha m,
      normalizedMonomialL2Vector alpha ha n⟫_ℂ =
      if m = n then (1 : ℂ) else 0 := by
  calc
    ⟪normalizedMonomialL2Vector alpha ha m,
      normalizedMonomialL2Vector alpha ha n⟫_ℂ =
    (∫ z : ℂ, normalizedMonomial alpha n z *
        star (normalizedMonomial alpha m z)
        ∂gaussianAreaMeasure alpha) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [normalizedMonomialL2Vector_ae alpha ha m,
         normalizedMonomialL2Vector_ae alpha ha n]
        with z hm hn
      rw [hm, hn]
      simp only [RCLike.inner_apply]
    _ = (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (normalizedMonomial alpha n z *
          star (normalizedMonomial alpha m z) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) := by
      rw [gaussianArea_integral_eq_volume alpha ha]
    _ = if n = m then (1 : ℂ) else 0 :=
      integral_normalized_monomial_pair_delta alpha ha n m
    _ = if m = n then (1 : ℂ) else 0 := by
      by_cases h : m = n
      · simp [h]
      · simp [h, Ne.symm h]

#print axioms GegenbauerFock.GaussianArea.gaussianArea_integral_eq_volume
#print axioms GegenbauerFock.GaussianArea.inner_normalizedMonomialL2Vector

end GegenbauerFock.GaussianArea
