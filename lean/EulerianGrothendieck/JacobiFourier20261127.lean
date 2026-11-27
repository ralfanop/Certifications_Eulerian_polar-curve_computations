import EulerianGrothendieck.JacobiExpFrechet20261127
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.CStarAlgebra.Basic

noncomputable section
open MeasureTheory Set Filter NormedSpace
open scoped Topology InnerProductSpace ENNReal
namespace M12JacobiFourier
open M12BilateralJacobi M12ExpFrechet

section General
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormedAlgebra ℂ R]
  [CompleteSpace R] [StarRing R] [ContinuousStar R] [CStarRing R] [Nontrivial R]
  [StarModule ℝ R] [SMulCommClass ℝ ℂ R]

/-- Skew-adjoint subspace in a real/complex Banach star algebra. -/
def skewSpace (R : Type*) [NormedRing R] [NormedAlgebra ℝ R] [StarRing R] [StarModule ℝ R] : Submodule ℝ R where
  carrier := {A | star A = -A}
  zero_mem' := by
    change star (0:R) = -(0:R)
    simp
  add_mem' := by
    intro A C hA hC
    change star A = -A at hA
    change star C = -C at hC
    change star (A+C) = -(A+C)
    rw [star_add,hA,hC,neg_add]
  smul_mem' := by
    intro t A hA
    change star A = -A at hA
    change star (t • A) = -(t • A)
    rw [star_smul,star_trivial,hA,smul_neg]

theorem exp_unitary (A : R) (hA : star A = -A) :
    exp A ∈ unitary R := by
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr hA)

theorem skew_norm (A : R) (hA : star A = -A) : ‖exp A‖ = 1 :=
  CStarRing.norm_of_mem_unitary (exp_unitary A hA)

theorem skew_smul (A : R) (hA : star A = -A) (t : ℝ) :
    star (t • A) = -(t • A) := by
  rw [star_smul,star_trivial,hA,smul_neg]

theorem D_norm_le (A C : R) (hA : star A = -A) (hC : star C = -C) :
    ‖D A C‖ ≤ 1 := by
  unfold D
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := 1) (f := kernel A C)
    (fun s _ => by
      unfold kernel
      calc
        _ ≤ ‖exp ((1-s) • A)‖ * ‖exp (s • C)‖ :=
          ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ R _ _
        _ = 1 := by rw [skew_norm _ (skew_smul A hA (1-s)),skew_norm _ (skew_smul C hC s),one_mul])
  simpa using h

def generator (t : ℝ) : (skewSpace R) →L[ℝ] R := t • (skewSpace R).subtypeL

theorem generator_apply (t : ℝ) (A : (skewSpace R)) :
    generator (R := R) t A = t • (A : R) := rfl

theorem generator_skew (t : ℝ) (A : (skewSpace R)) :
    star (generator t A) = -(generator t A) :=
  skew_smul A A.property t

theorem generator_norm (t : ℝ) : ‖generator t‖ ≤ |t| := by
  unfold generator
  rw [norm_smul,Real.norm_eq_abs]
  simpa using mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le (skewSpace R)) (abs_nonneg t)

def integrand (w : ℝ → ℂ) (A : (skewSpace R)) (t : ℝ) : R :=
  w t • exp (generator t A)

def integrandD (w : ℝ → ℂ) (A : (skewSpace R)) (t : ℝ) : (skewSpace R) →L[ℝ] R :=
  w t • (D (generator t A) (generator t A)).comp (generator t)

theorem integrand_hasFDerivAt (w : ℝ → ℂ) (A : (skewSpace R)) (t : ℝ) :
    HasFDerivAt (fun X : (skewSpace R) => integrand w X t) (integrandD w A t) A := by
  exact ((exp_hasFDerivAt (generator t A)).comp A (generator t).hasFDerivAt).const_smul (w t)

theorem integrandD_bound (w : ℝ → ℂ) (A : (skewSpace R)) (t : ℝ) :
    ‖integrandD w A t‖ ≤ ‖w t‖ * |t| := by
  unfold integrandD
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖D (generator t A) (generator t A)‖ * ‖generator t‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * |t| := mul_le_mul (D_norm_le _ _ (generator_skew t A) (generator_skew t A))
      (generator_norm t) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Fourier calculus with w = Fourier transform divided by 2π.
The measurable Fourier density and its first absolute moment are the
analytic input. The operator differentiation is derived, not assumed. -/
def fourierOp (w : ℝ → ℂ) (A : (skewSpace R)) : R :=
  ∫ t, integrand w A t

theorem fourier_hasFDerivAt (w : ℝ → ℂ) (A : (skewSpace R))
    (hm : ∀ X : (skewSpace R), AEStronglyMeasurable (integrand w X) volume)
    (hi : Integrable (integrand w A) volume)
    (hdm : AEStronglyMeasurable (integrandD w A) volume)
    (hmoment : Integrable (fun t : ℝ => ‖w t‖ * |t|) volume) :
    HasFDerivAt (fourierOp w) (∫ t, integrandD w A t) A := by
  unfold fourierOp
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Set.univ) (F' := integrandD w) (bound := fun t => ‖w t‖ * |t|)
    univ_mem (Eventually.of_forall hm) hi hdm
    (Eventually.of_forall fun t X _ => integrandD_bound w X t)
    hmoment (Eventually.of_forall fun t X _ => integrand_hasFDerivAt w X t)

end General

set_option synthInstance.maxHeartbeats 1000000 in
theorem jacobi_skew (u : Bonds) : star (Complex.I • J u) = -(Complex.I • J u) := by
  rw [star_smul,(J_selfAdjoint u).star_eq,Complex.star_def,Complex.conj_I]
  ext x k
  change (-Complex.I)*J u x k = -(Complex.I*J u x k)
  ring

/-- Direct specialization of the unitary identity to the actual Jacobi generator. -/
theorem jacobi_unitary (u : Bonds) (t : ℝ) :
    exp (((t:ℂ)*Complex.I) • J u) ∈ unitary Op := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  apply skewAdjoint.mem_iff.mpr
  rw [star_smul,(J_selfAdjoint u).star_eq]
  ext x k
  simp [Complex.star_def,Complex.conj_I,mul_assoc]

end M12JacobiFourier

#print axioms M12JacobiFourier.exp_unitary
#print axioms M12JacobiFourier.skew_norm
#print axioms M12JacobiFourier.skew_smul
#print axioms M12JacobiFourier.D_norm_le
#print axioms M12JacobiFourier.generator_apply
#print axioms M12JacobiFourier.generator_skew
#print axioms M12JacobiFourier.generator_norm
#print axioms M12JacobiFourier.integrand_hasFDerivAt
#print axioms M12JacobiFourier.integrandD_bound
#print axioms M12JacobiFourier.fourier_hasFDerivAt
#print axioms M12JacobiFourier.jacobi_skew
#print axioms M12JacobiFourier.jacobi_unitary
