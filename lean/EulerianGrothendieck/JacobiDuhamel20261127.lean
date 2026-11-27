import EulerianGrothendieck.JacobiFrechet20261127
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! M12 Lemma 5.12: Duhamel's exact operator difference identity.
No commutation between the endpoints is assumed. This integrates the
actual derivative of exp((1-s)A) exp(s C) on the real unit interval. -/
noncomputable section
open MeasureTheory Set NormedSpace
namespace M12Duhamel
section General
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

def path (A C : R) (s : ℝ) : R :=
  exp ((1-s) • A) * exp (s • C)

def density (A C X : R) (s : ℝ) : R :=
  exp ((1-s) • A) * X * exp (s • C)

theorem exp_line_deriv (A : R) (s : ℝ) :
    HasDerivAt (fun t : ℝ => exp (t • A)) (exp (s • A) * A) s :=
  hasDerivAt_exp_smul_const A s

theorem exp_line_continuous (A : R) : Continuous (fun t : ℝ => exp (t • A)) :=
  continuous_iff_continuousAt.mpr (fun s => (exp_line_deriv A s).continuousAt)

theorem path_derivative (A C : R) (s : ℝ) :
    HasDerivAt (path A C) (density A C (C-A) s) s := by
  have h₁ : HasDerivAt (fun t : ℝ => 1-t) (-1) s := by
    have h := (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id' s)
    change HasDerivAt ((fun _ : ℝ => (1:ℝ)) - (fun t : ℝ => t)) (-1) s
    simpa only [zero_sub] using h
  have h₂ := (exp_line_deriv A (1-s)).scomp s h₁
  have h₃ : HasDerivAt (fun t : ℝ => exp (t • C)) (C * exp (s • C)) s :=
    hasDerivAt_exp_smul_const' C s
  have h₄ := h₂.mul h₃
  have he : (-1:ℝ) • (exp ((1-s) • A)*A) * exp (s • C) +
      exp ((1-s) • A)*(C*exp (s • C)) = density A C (C-A) s := by
    rw [neg_smul,one_smul]
    unfold density
    noncomm_ring
  rw [← he]
  exact h₄

theorem density_continuous (A C X : R) : Continuous (density A C X) := by
  unfold density
  exact (((exp_line_continuous A).comp (continuous_const.sub continuous_id)).mul
    continuous_const).mul (exp_line_continuous C)

theorem density_integrable (A C X : R) :
    IntervalIntegrable (density A C X) volume 0 1 :=
  (density_continuous A C X).intervalIntegrable 0 1

theorem difference (A C : R) :
    exp C - exp A = ∫ s in (0:ℝ)..1, density A C (C-A) s := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := path A C) (f' := density A C (C-A)) (a := 0) (b := 1)
    (fun s _ => path_derivative A C s) (density_integrable A C (C-A))
  have h0 : path A C 0 = exp A := by simp [path,exp_zero]
  have h1 : path A C 1 = exp C := by simp [path,exp_zero]
  rw [h0,h1] at h
  exact h.symm

theorem density_smul (A C X : R) (h s : ℝ) :
    density A C (h • X) s = h • density A C X s := by
  unfold density
  rw [mul_smul_comm,smul_mul_assoc]

theorem difference_scaled (A X : R) (h : ℝ) :
    exp (A+h • X) - exp A =
      h • (∫ s in (0:ℝ)..1, density A (A+h • X) X s) := by
  rw [difference,add_sub_cancel_left]
  calc
    _ = ∫ s in (0:ℝ)..1, h • density A (A+h • X) X s := by
      apply intervalIntegral.integral_congr
      intro s _
      exact density_smul _ _ _ _ _
    _ = _ := (density_integrable A (A+h • X) X).integral_smul h

end General

open M12BilateralJacobi

theorem jacobi_difference (u v : Bonds) :
    exp (J v) - exp (J u) =
      ∫ s in (0:ℝ)..1, density (J u) (J v) (J v-J u) s :=
  difference (J u) (J v)

theorem jacobi_bond_difference (u : Bonds) (m : ℤ) (h : ℝ) :
    exp (J u+h • M12JacobiFrechet.bond m) - exp (J u) =
      h • (∫ s in (0:ℝ)..1,
        density (J u) (J u+h • M12JacobiFrechet.bond m)
          (M12JacobiFrechet.bond m) s) :=
  difference_scaled (J u) (M12JacobiFrechet.bond m) h

end M12Duhamel
#print axioms M12Duhamel.exp_line_deriv
#print axioms M12Duhamel.exp_line_continuous
#print axioms M12Duhamel.path_derivative
#print axioms M12Duhamel.density_continuous
#print axioms M12Duhamel.density_integrable
#print axioms M12Duhamel.difference
#print axioms M12Duhamel.density_smul
#print axioms M12Duhamel.difference_scaled
#print axioms M12Duhamel.jacobi_difference
#print axioms M12Duhamel.jacobi_bond_difference
