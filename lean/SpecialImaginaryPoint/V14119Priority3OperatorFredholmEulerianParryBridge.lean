import SpecialImaginaryPoint.V14119Priority3DirichletTrueFredholmSinhBridge
import SpecialImaginaryPoint.ParryThresholds

/-!
# Priority 3 — exact CFC-S₁ Fredholm operator realization of the Eulerian–Parry scalar

The distinguished scalar
  x_E = sqrt(2) sinh(1/sqrt(2))
used in the rigorously formalized Eulerian–Parry boundary problem
is EXACTLY the genuine universal Hilbert-compression-limit Fredholm
determinant of the positive CFC Schatten-S₁ Dirichlet inverse
spectral model on complex ℓ² at spectral parameter z=1/2:

  det_F(I + (1/2)A⁻¹) = x_E.

Furthermore, the two special values z=1/8 and z=1/2 of the same
actual operatorial Fredholm determinant obey an exact Eulerian
modular-duplication identity with factor cosh(1/sqrt(8)).

These are identities of a real trace-class Hilbert OPERATOR's
universal determinant, not scalar Euler products by definition.
The precise real rational enclosure and greedy Parry expansion
are separate pre-existing formalization obligations, and the
differential L²(0,1) realization is not assumed.
-/

noncomputable section

namespace Manuscript14Priority3.OperatorFredholmEulerianParryBridge

open Filter Topology Set InnerProductSpace
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace
open Manuscript14Priority3.DirichletTrueFredholmSinhBridge
open Manuscript14Section67

/-!
Alternative to Draft #261: centralize the transport of real-square
spectral parameters to complex shifts, and derive both special
values directly from the already proved operatorial Eulerian bridge.
No per-theorem rewriting of real-to-complex shifts is used.
-/

/-- Parameter transport for the actual CFC-S₁ Fredholm determinant.
This separates analytic operator theory from special-point arithmetic. -/
private theorem fredholm_at_parameter
    (x : ℝ) (hx : x ≠ 0) (s z : ℂ)
    (hs : ((x ^ 2 : ℝ) : ℂ) = s)
    (hz : 2 * ((x : ℂ) * Complex.I) = z) :
    fredholmDet dirichletInverseS1 s = rE z := by
  calc
    fredholmDet dirichletInverseS1 s =
        fredholmDet dirichletInverseS1 ((x ^ 2 : ℝ) : ℂ) := by rw [hs]
    _ = rE (2 * ((x : ℂ) * Complex.I)) :=
      genuine_dirichlet_fredholm_real_square_eq_eulerian x hx
    _ = rE z := congrArg rE hz

/-- Exact Eulerian special point z₀, from the common parameter-transport lemma. -/
theorem genuine_dirichlet_fredholm_eighth_eq_rE_z0 :
    fredholmDet dirichletInverseS1 (1 / 8 : ℂ) = rE z0 := by
  refine fredholm_at_parameter a a_ne_zero (1 / 8 : ℂ) z0 ?_ z0_eq.symm
  norm_num [a_sq]

/-- Exact Eulerian companion z₁, from the same parameter-transport lemma. -/
theorem genuine_dirichlet_fredholm_half_eq_rE_z1 :
    fredholmDet dirichletInverseS1 (1 / 2 : ℂ) = rE z1 := by
  refine fredholm_at_parameter b b_ne_zero (1 / 2 : ℂ) z1 ?_ z1_eq.symm
  norm_num [b_sq]

/-- The genuine Fredholm determinant at the half-shift equals the
distinguished Eulerian–Parry scalar, via the companion Fourier profile. -/
theorem genuine_dirichlet_fredholm_half_eq_eulerianParameter :
    fredholmDet dirichletInverseS1 (1 / 2 : ℂ) =
      ((Manuscript14Section11.eulerianParameter : ℝ) : ℂ) := by
  have hreal : Real.sinh b / b =
      Manuscript14Section11.eulerianParameter := by
    change Real.sinh b / b =
      Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2)
    rw [div_eq_mul_inv]
    have hb : b⁻¹ = Real.sqrt 2 := by
      simpa only [one_div] using one_div_b
    rw [hb, mul_comm]
    rfl
  calc
    fredholmDet dirichletInverseS1 (1 / 2 : ℂ) = rE z1 :=
      genuine_dirichlet_fredholm_half_eq_rE_z1
    _ = ((Real.sinh b / b : ℝ) : ℂ) := rE_z1
    _ = ((Manuscript14Section11.eulerianParameter : ℝ) : ℂ) :=
      congrArg (fun v : ℝ => (v : ℂ)) hreal

/-- Genuine operatorial Fredholm duplication between the two Eulerian
spectral parameters, using the established modular identity. -/
theorem genuine_dirichlet_fredholm_eulerian_duplication :
    fredholmDet dirichletInverseS1 (1 / 2 : ℂ) =
      ((Real.cosh a : ℝ) : ℂ) *
        fredholmDet dirichletInverseS1 (1 / 8 : ℂ) := by
  calc
    fredholmDet dirichletInverseS1 (1 / 2 : ℂ) = rE z1 :=
      genuine_dirichlet_fredholm_half_eq_rE_z1
    _ = ((Real.cosh a : ℝ) : ℂ) * rE z0 :=
      modular_duplication.2
    _ = ((Real.cosh a : ℝ) : ℂ) *
          fredholmDet dirichletInverseS1 (1 / 8 : ℂ) := by
      rw [genuine_dirichlet_fredholm_eighth_eq_rE_z0]

#print axioms Manuscript14Priority3.OperatorFredholmEulerianParryBridge.genuine_dirichlet_fredholm_half_eq_eulerianParameter
#print axioms Manuscript14Priority3.OperatorFredholmEulerianParryBridge.genuine_dirichlet_fredholm_eighth_eq_rE_z0
#print axioms Manuscript14Priority3.OperatorFredholmEulerianParryBridge.genuine_dirichlet_fredholm_half_eq_rE_z1
#print axioms Manuscript14Priority3.OperatorFredholmEulerianParryBridge.genuine_dirichlet_fredholm_eulerian_duplication

end Manuscript14Priority3.OperatorFredholmEulerianParryBridge
