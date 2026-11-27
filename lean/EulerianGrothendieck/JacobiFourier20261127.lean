import EulerianGrothendieck.JacobiExpFrechet20261127
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.CStarAlgebra.Basic

noncomputable section
open MeasureTheory Set Filter NormedSpace
open scoped Topology InnerProductSpace ENNReal
namespace M12JacobiFourier
open M12BilateralJacobi M12ExpFrechet

section General
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
  [CompleteSpace R] [StarRing R] [ContinuousStar R] [CStarRing R] [Nontrivial R]
  [StarModule ℝ R]

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
  rw [Unitary.mem_iff,NormedSpace.star_exp,hA]
  have hp : A ∈ Metric.eball (0:R) (expSeries ℝ R).radius :=
    (expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _
  have hn : -A ∈ Metric.eball (0:R) (expSeries ℝ R).radius :=
    (expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _
  have h₁ := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (Commute.refl A).neg_left hn hp
  have h₂ := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (Commute.refl A).neg_right hp hn
  rw [neg_add_cancel,exp_zero] at h₁
  rw [add_neg_cancel,exp_zero] at h₂
  exact ⟨h₁.symm,h₂.symm⟩

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
  skew_smul (A : R) A.property t

theorem generator_norm (t : ℝ) : ‖generator (R := R) t‖ ≤ |t| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg t)
  intro A
  rw [generator_apply]
  change ‖t • (A : R)‖ ≤ |t| * ‖(A : R)‖
  simpa only [Real.norm_eq_abs] using norm_smul_le t (A : R)

def integrand (w : ℝ → R) (A : (skewSpace R)) (t : ℝ) : R :=
  w t * exp (generator t A)

def integrandD (w : ℝ → R) (A : (skewSpace R)) (t : ℝ) : (skewSpace R) →L[ℝ] R :=
  (ContinuousLinearMap.mulLeftRight ℝ R (w t) 1).comp
    ((D (generator t A) (generator t A)).comp (generator t))

theorem integrand_hasFDerivAt (w : ℝ → R) (A : (skewSpace R)) (t : ℝ) :
    HasFDerivAt (fun X : (skewSpace R) => integrand w X t) (integrandD w A t) A := by
  have h₁ := (exp_hasFDerivAt (generator t A)).comp A
    (generator (R := R) t).hasFDerivAt
  have h₂ := (ContinuousLinearMap.mulLeftRight ℝ R (w t) 1).hasFDerivAt.comp A h₁
  simpa only [Function.comp_def,ContinuousLinearMap.mulLeftRight_apply,mul_one,integrand,integrandD] using h₂

theorem integrandD_bound (w : ℝ → R) (A : (skewSpace R)) (t : ℝ) :
    ‖integrandD w A t‖ ≤ ‖w t‖ * |t| := by
  unfold integrandD
  have h₁ : ‖ContinuousLinearMap.mulLeftRight ℝ R (w t) 1‖ ≤ ‖w t‖ := by
    simpa using ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ R (w t) 1
  have h₂ : ‖(D (generator t A) (generator t A)).comp (generator t)‖ ≤ |t| := by
    calc
      _ ≤ ‖D (generator t A) (generator t A)‖ * ‖generator t‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * |t| := mul_le_mul (D_norm_le _ _ (generator_skew t A) (generator_skew t A))
        (generator_norm (R := R) t) (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul h₁ h₂ (norm_nonneg _) (norm_nonneg _))

/-- Fourier calculus with algebra-valued weight w (the intended weight is the central scalar embedding of the Fourier transform divided by 2π).
The measurable Fourier density and its first absolute moment are the
analytic input. The operator differentiation is derived, not assumed. -/
def fourierOp (w : ℝ → R) (A : (skewSpace R)) : R :=
  ∫ t, integrand w A t

theorem fourier_hasFDerivAt (w : ℝ → R) (A : (skewSpace R))
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
  let A : Op := ((t:ℂ)*Complex.I) • J u
  change exp A ∈ unitary Op
  have hA : star A = -A := by
    dsimp [A]
    rw [star_smul,(J_selfAdjoint u).star_eq]
    ext x k
    change (star ((t:ℂ)*Complex.I))*J u x k = -(((t:ℂ)*Complex.I)*J u x k)
    simp [Complex.star_def,Complex.conj_I,mul_assoc]
  rw [Unitary.mem_iff,NormedSpace.star_exp,hA]
  have hp : A ∈ Metric.eball (0:Op) (expSeries ℂ Op).radius :=
    (expSeries_radius_eq_top ℂ Op).symm ▸ edist_lt_top _ _
  have hn : -A ∈ Metric.eball (0:Op) (expSeries ℂ Op).radius :=
    (expSeries_radius_eq_top ℂ Op).symm ▸ edist_lt_top _ _
  have h₁ := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    (Commute.refl A).neg_left hn hp
  have h₂ := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    (Commute.refl A).neg_right hp hn
  rw [neg_add_cancel,exp_zero] at h₁
  rw [add_neg_cancel,exp_zero] at h₂
  exact ⟨h₁.symm,h₂.symm⟩

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
