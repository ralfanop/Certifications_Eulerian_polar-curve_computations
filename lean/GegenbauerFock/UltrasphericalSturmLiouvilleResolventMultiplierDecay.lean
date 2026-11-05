import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueGrowth
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Decay of ultraspherical Sturm resolvent multipliers

For positive ultraspherical parameter lam and positive resolvent
shift t, the exact degree-n spectral multiplier is strictly positive
and vanishes as the polynomial degree tends to infinity. The lower
bound on its denominator is obtained from the previously certified
growth estimate for the concrete Sturm eigenvalues.

This is the scalar decay input for a separate operator-norm
finite-rank approximation argument; it does not by itself assert
compactness of the actual closed Sturm resolvent.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Filter

/-- Positivity of every exact Gegenbauer positive-shift resolvent
spectral multiplier. -/
theorem sturmResolventMultiplier_pos
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    0 < (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ := by
  apply inv_pos.mpr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnl : 0 ≤ (n : ℝ) + 2 * lam := by positivity
  have hp : 0 ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) :=
    mul_nonneg hn hnl
  linarith

/-- The degree-n denominator dominates n and therefore escapes
to positive infinity; the actual spectral multiplier tends to zero. -/
theorem sturmResolventMultiplier_tendsto_zero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto (fun n : ℕ =>
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹)
      atTop (nhds 0) := by
  have hdegree (n : ℕ) :
      (n : ℝ) ≤ t + (n : ℝ) * ((n : ℝ) + 2 * lam) := by
    have h := sturmEigenvalue_le_neg_degree lam hlam n
    dsimp [sturmEigenvalue] at h
    linarith
  have hnat :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun n : ℕ =>
        t + (n : ℝ) * ((n : ℝ) + 2 * lam)) atTop atTop :=
    (tendsto_atTop_mono hdegree) hnat
  exact tendsto_inv_atTop_zero.comp hden

#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_pos
#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_tendsto_zero

end GegenbauerFock.Ultraspherical
