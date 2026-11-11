import SpecialImaginaryPoint.V14119Priority3UniversalDirichletSinh
import SpecialImaginaryPoint.V14119Priority3UniversalFredholmEntire
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Priority 3 — analytic continuation of the genuine CFC-S₁ Dirichlet Fredholm identity

The certified REAL identity for the genuine ℓ² Dirichlet inverse
spectral operator,
    fredholmDet(A_D⁻¹,x²) = sinh(x)/x      (real x ≠ 0),
together with the independently certified universal Fredholm
ENTIRE theorem and the complex analytic identity theorem, implies

    z * fredholmDet(A_D⁻¹,z²) = sinh(z)   for EVERY z∈ℂ.

This form is ENTIRE on both sides and also proves equality at z=0
without a removable-singularity division. For z≠0 we recover the
full complex sinh(z)/z identity. The proof requires no prior
complex infinite Euler product and no zeta-regularization; it
extends the actual universal Hilbert trace-class determinant.

As before, the Dirichlet inverse is the certified ℓ² spectral
model; no identification with a differential realization on
L²(0,1) is asserted.
-/

noncomputable section

namespace Manuscript14Priority3.ComplexDirichletSinhEntire

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.UniversalDirichletSinh

/-- The real hyperbolic sine identity, written without division
on the complex side, for every NONZERO real x. -/
theorem dirichlet_sinh_complex_on_real_nonzero
    (x : ℝ) (hx : x ≠ 0) :
    (x : ℂ) * fredholmDet inverseTraceClass ((x : ℂ) ^ 2) =
      Complex.sinh (x : ℂ) := by
  have hsq : ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := by norm_cast
  rw [hsq, fredholmDet_true_dirichlet_inverse_sinh_quotient x hx]
  have hr : x * (Real.sinh x / x) = Real.sinh x := by
    field_simp [hx]
  calc
    (x : ℂ) * ((Real.sinh x / x : ℝ) : ℂ) =
      ((x * (Real.sinh x / x) : ℝ) : ℂ) := by norm_cast
    _ = ((Real.sinh x : ℝ) : ℂ) := by rw [hr]
    _ = Complex.sinh (x : ℂ) := Complex.ofReal_sinh x

/-- Holomorphic COMPLEX continuation of the TRUE CFC-S₁
Fredholm determinant identity, including z=0, by the
identity principle for entire functions. -/
theorem universal_dirichlet_sinh_entire_identity
    (z : ℂ) :
    z * fredholmDet inverseTraceClass (z ^ 2) =
      Complex.sinh z := by
  let f : ℂ → ℂ := fun w => w * fredholmDet inverseTraceClass (w ^ 2)
  let g : ℂ → ℂ := Complex.sinh
  have hdf : Differentiable ℂ f := by
    dsimp [f]
    exact differentiable_id.mul
      ((universal_fredholmDet_entire inverseTraceClass).comp
        (differentiable_id.pow 2))
  have hf : AnalyticOnNhd ℂ f Set.univ :=
    hdf.differentiableOn.analyticOnNhd isOpen_univ
  have hg : AnalyticOnNhd ℂ g Set.univ :=
    Complex.differentiable_sinh.differentiableOn.analyticOnNhd isOpen_univ
  let q : ℕ → ℂ :=
    fun n => (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ)
  have hq : Tendsto q atTop (𝓝 (0 : ℂ)) := by
    have hr : Tendsto (fun n : ℕ =>
        (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
  have hclosure :
      (0 : ℂ) ∈ closure ({w : ℂ | f w = g w} \ {(0 : ℂ)}) := by
    apply mem_closure_of_tendsto hq
    exact Filter.Eventually.of_forall (fun n : ℕ => by
      let x : ℝ := 1 / ((n : ℝ) + 1)
      have hx : x ≠ 0 := by dsimp [x]; positivity
      have hxcast : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      have hreal := dirichlet_sinh_complex_on_real_nonzero x hx
      refine ⟨?_, ?_⟩
      · change f (q n) = g (q n)
        simpa only [f, g, q, x] using hreal
      · change q n ≠ 0
        simpa only [q, x] using hxcast)
  have hEq : EqOn f g Set.univ :=
    hf.eqOn_of_preconnected_of_mem_closure hg
      isPreconnected_univ (Set.mem_univ (0 : ℂ)) hclosure
  exact hEq (Set.mem_univ z)

/-- For every NONZERO complex parameter, the genuine universal
Dirichlet inverse determinant is the full complex hyperbolic
sine quotient, with no assumption of real positivity. -/
theorem universal_dirichlet_sinh_quotient_complex
    (z : ℂ) (hz : z ≠ 0) :
    fredholmDet inverseTraceClass (z ^ 2) =
      Complex.sinh z / z := by
  apply (eq_div_iff hz).2
  rw [mul_comm]
  exact universal_dirichlet_sinh_entire_identity z

#print axioms Manuscript14Priority3.ComplexDirichletSinhEntire.dirichlet_sinh_complex_on_real_nonzero
#print axioms Manuscript14Priority3.ComplexDirichletSinhEntire.universal_dirichlet_sinh_entire_identity
#print axioms Manuscript14Priority3.ComplexDirichletSinhEntire.universal_dirichlet_sinh_quotient_complex

end Manuscript14Priority3.ComplexDirichletSinhEntire
