import SpecialImaginaryPoint.V14119Priority3FredholmPerturbationReciprocal
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Priority 3 — true scalar Fredholm reciprocal perturbation modulus

Let f_T(z) = det_F(I+zT) denote the actual Hilbert-compression-limit
Fredholm determinant of an arbitrary complex CFC Schatten-S₁ operator T.

On the quantitatively certified zero-free trace-norm perturbation
region, both f_T(z) and f_(T+R)(z) are nonzero. The exact field identity
for the difference of their reciprocals, combined with the genuinely
infinite-dimensional Fredholm trace-norm estimate, gives a rigorous
modulus-of-continuity estimate for the SCALAR determinant reciprocal.

The statement concerns f_T⁻¹ as a scalar function, not an operator
inverse, and does not assume normality, positivity or selfadjointness.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmReciprocalVariation

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.QuantitativeFredholmNonvanishing
open Manuscript14Priority3.FredholmPerturbationReciprocal

/-- Exact nonasymptotic variation estimate of the TRUE scalar
universal Fredholm reciprocal, involving actual determinant moduli. -/
theorem universalFredholm_reciprocal_traceNorm_variation
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall :
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) <
        ‖fredholmDet T z‖) :
    ‖(fredholmDet (T + R) z)⁻¹ - (fredholmDet T z)⁻¹‖ ≤
      ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖))) /
        (‖fredholmDet (T + R) z‖ * ‖fredholmDet T z‖) := by
  have hE : 0 ≤ (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) :=
    mul_nonneg (mul_nonneg (norm_nonneg z) (norm_nonneg R)) (Real.exp_pos _).le
  have hbold : fredholmDet T z ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_le_of_lt hE hsmall)
  have hbnew : fredholmDet (T + R) z ≠ 0 :=
    universalFredholm_nonzero_of_traceNorm_perturbation T R z hsmall
  have hb := fredholmDet_add_traceNorm_bound T R z
  have heq :
      ‖(fredholmDet (T + R) z)⁻¹ - (fredholmDet T z)⁻¹‖ =
      ‖fredholmDet (T + R) z - fredholmDet T z‖ /
        (‖fredholmDet (T + R) z‖ * ‖fredholmDet T z‖) := by
    simpa only [dist_eq_norm] using (dist_inv_inv₀ hbnew hbold)
  rw [heq]
  exact div_le_div_of_nonneg_right hb
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A fully a posteriori bound depending only on the OLD genuine
determinant modulus and the certified trace-norm error. In particular,
the bound is finite whenever the strict perturbation margin holds. -/
theorem universalFredholm_reciprocal_explicit_stability
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall :
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) <
        ‖fredholmDet T z‖) :
    ‖(fredholmDet (T + R) z)⁻¹ - (fredholmDet T z)⁻¹‖ ≤
      ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖))) /
        ((‖fredholmDet T z‖ -
            ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)))) *
          ‖fredholmDet T z‖) := by
  have hE : 0 ≤ (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) :=
    mul_nonneg (mul_nonneg (norm_nonneg z) (norm_nonneg R)) (Real.exp_pos _).le
  have hgap : 0 < ‖fredholmDet T z‖ -
      ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖))) := by
    linarith
  have hden :
      (‖fredholmDet T z‖ -
          ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)))) *
        ‖fredholmDet T z‖ ≤
      ‖fredholmDet (T + R) z‖ * ‖fredholmDet T z‖ :=
    mul_le_mul_of_nonneg_right
      (universalFredholm_perturbation_modulus_lower_bound T R z)
      (norm_nonneg _)
  calc
    ‖(fredholmDet (T + R) z)⁻¹ - (fredholmDet T z)⁻¹‖ ≤
        ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖))) /
          (‖fredholmDet (T + R) z‖ * ‖fredholmDet T z‖) :=
      universalFredholm_reciprocal_traceNorm_variation T R z hsmall
    _ ≤
        ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖))) /
          ((‖fredholmDet T z‖ -
            ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)))) *
          ‖fredholmDet T z‖) :=
      div_le_div_of_nonneg_left hE
        (mul_pos hgap (lt_of_le_of_lt hE hsmall)) hden

#print axioms Manuscript14Priority3.FredholmReciprocalVariation.universalFredholm_reciprocal_traceNorm_variation
#print axioms Manuscript14Priority3.FredholmReciprocalVariation.universalFredholm_reciprocal_explicit_stability

end Manuscript14Priority3.FredholmReciprocalVariation
