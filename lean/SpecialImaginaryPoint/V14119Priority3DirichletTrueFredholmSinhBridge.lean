import SpecialImaginaryPoint.V14119Priority3DirichletInverseFredholmDerivativeTrace
import SpecialImaginaryPoint.V14119Priority3SpectralDetBridge
import SpecialImaginaryPoint.V14119Priority3OperatorCompression

/-!
# Priority 3 — genuine universal CFC-S₁ Dirichlet inverse Fredholm determinant = sinh quotient

Let A⁻¹ be the positive complex Dirichlet spectral inverse model
on the ACTUAL Hilbert space ℓ²(ℕ, ℂ), with eigenvalues
σ_n = 1/(π²(n+1)²). Its operator is already certified to belong to
the true CFC Schatten S₁ ideal.

This module bridges the actual infinite-dimensional universal
Hilbert-compression-limit Fredholm determinant to the independently
certified Euler–sinh spectral product, for ALL nonzero real x:

  det_F(I+x² A⁻¹) = sinh(x)/x.

This is not merely equality of auxiliary scalar products: at every
finite N, the determinant is that of the actual compressed bounded
Hilbert operator, and the infinite identity follows by uniqueness
of limits. The final two special-point corollaries bridge the same
actual operatorial determinant to the Eulerian Fourier profile r_E.

No identification with the differential Dirichlet inverse on
L²(0,1) or with a relative zeta determinant is claimed.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletTrueFredholmSinhBridge

open Filter Topology Set InnerProductSpace Matrix
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.OperatorCompression
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace

/-- Every finite compression of the actual Dirichlet inverse
has EXACTLY the previously certified scalar Dirichlet spectral product
as its true finite complex matrix Fredholm determinant. -/
theorem genuine_dirichlet_finite_compression_det_eq_scalar
    (N : ℕ) (t : ℝ) :
    finiteDeterminant N dirichletInverseS1 (t : ℂ) =
      (Manuscript14Dirichlet.finiteFredholm N t : ℂ) := by
  change Matrix.det
    (1 + (t : ℂ) • compressedCFC N dirichletInverseS1) = _
  rw [show compressedCFC N dirichletInverseS1 =
      compressedInverse N from rfl]
  change Matrix.det (finiteOperatorShift N t) = _
  rw [finiteOperatorShift_det]
  calc
    (∏ i : Fin N, 1 + (t : ℂ) * (σ i.val : ℂ)) =
        ∏ i : Fin N, ((Manuscript14Dirichlet.factor i.val t : ℝ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact factor_eq_real i.val t
    _ = (Manuscript14Dirichlet.finiteFredholm N t : ℂ) := by
      simp [Manuscript14Dirichlet.finiteFredholm,
        Fin.prod_univ_eq_prod_range]

/-- For every nonzero real x, the actual universal CFC-S₁
Fredholm determinant of the Dirichlet inverse spectral operator,
at real complex shift x², is exactly sinh(x)/x. -/
theorem genuine_dirichlet_fredholm_real_square_eq_sinh
    (x : ℝ) (hx : x ≠ 0) :
    fredholmDet dirichletInverseS1 ((x ^ 2 : ℝ) : ℂ) =
      ((Real.sinh x / x : ℝ) : ℂ) := by
  have hreal :=
    Manuscript14Priority3.finite_dirichlet_product_tendsto x hx
  have hcomplex :
      Tendsto
        (fun N : ℕ => finiteDeterminant N dirichletInverseS1 ((x ^ 2 : ℝ) : ℂ))
        atTop (𝓝 ((Real.sinh x / x : ℝ) : ℂ)) := by
    have hcast :=
      (Complex.continuous_ofReal.tendsto (Real.sinh x / x)).comp hreal
    simpa only [genuine_dirichlet_finite_compression_det_eq_scalar,
      Function.comp_def] using hcast
  exact tendsto_nhds_unique
    (finiteDeterminant_tendsto_fredholmDet
      dirichletInverseS1 ((x ^ 2 : ℝ) : ℂ)) hcomplex

/-- The actual Dirichlet inverse universal Fredholm determinant
coincides at real-square shifts with the Eulerian Fourier profile
on the corresponding imaginary axis. -/
theorem genuine_dirichlet_fredholm_real_square_eq_eulerian
    (x : ℝ) (hx : x ≠ 0) :
    fredholmDet dirichletInverseS1 ((x ^ 2 : ℝ) : ℂ) =
      Manuscript14Section67.rE (2 * ((x : ℂ) * Complex.I)) := by
  rw [genuine_dirichlet_fredholm_real_square_eq_sinh x hx]
  exact (Manuscript14Section67.rE_two_mul_I x hx).symm

/-- The exact genuine CFC-S₁ Dirichlet inverse Fredholm determinant
at the Eulerian special square a² coincides with r_E(z₀). -/
theorem genuine_dirichlet_fredholm_at_a_sq_eq_rE_z0 :
    fredholmDet dirichletInverseS1
      ((Manuscript14Section67.a ^ 2 : ℝ) : ℂ) =
        Manuscript14Section67.rE Manuscript14Section67.z0 := by
  rw [genuine_dirichlet_fredholm_real_square_eq_sinh
      Manuscript14Section67.a Manuscript14Section67.a_ne_zero]
  exact (Manuscript14Section67.rE_z0).symm

/-- The genuine CFC-S₁ Dirichlet inverse Fredholm determinant
at the Eulerian special square b² coincides with r_E(z₁). -/
theorem genuine_dirichlet_fredholm_at_b_sq_eq_rE_z1 :
    fredholmDet dirichletInverseS1
      ((Manuscript14Section67.b ^ 2 : ℝ) : ℂ) =
        Manuscript14Section67.rE Manuscript14Section67.z1 := by
  rw [genuine_dirichlet_fredholm_real_square_eq_sinh
      Manuscript14Section67.b Manuscript14Section67.b_ne_zero]
  exact (Manuscript14Section67.rE_z1).symm

#print axioms Manuscript14Priority3.DirichletTrueFredholmSinhBridge.genuine_dirichlet_finite_compression_det_eq_scalar
#print axioms Manuscript14Priority3.DirichletTrueFredholmSinhBridge.genuine_dirichlet_fredholm_real_square_eq_sinh
#print axioms Manuscript14Priority3.DirichletTrueFredholmSinhBridge.genuine_dirichlet_fredholm_real_square_eq_eulerian
#print axioms Manuscript14Priority3.DirichletTrueFredholmSinhBridge.genuine_dirichlet_fredholm_at_a_sq_eq_rE_z0
#print axioms Manuscript14Priority3.DirichletTrueFredholmSinhBridge.genuine_dirichlet_fredholm_at_b_sq_eq_rE_z1

end Manuscript14Priority3.DirichletTrueFredholmSinhBridge
