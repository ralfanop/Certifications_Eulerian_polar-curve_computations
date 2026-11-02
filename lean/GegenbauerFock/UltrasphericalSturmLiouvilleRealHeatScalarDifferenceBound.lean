import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# V007 — uniform scalar Yosida/heat difference quotient domination

For every nonnegative frequency w and positive time s, the heat
difference quotient satisfies
   |s⁻¹ (exp(-s*w) - 1)| ≤ w.
This pointwise spectral bound is precisely the dominating multiplier
used to extend finite-spectral-core right derivatives to the full
closed Sturm graph domain by Parseval and dominated convergence.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- Sharp elementary bound for the right heat difference quotient
of every nonnegative Gegenbauer spectral frequency. -/
theorem sturmRealHeat_scalar_difference_quotient_abs_le
    (omega s : ℝ) (homega : 0 ≤ omega) (hs : 0 < s) :
    |s⁻¹ * (Real.exp (-s * omega) - 1)| ≤ omega := by
  have hproduct : 0 ≤ s * omega := mul_nonneg hs.le homega
  have hExpLe : Real.exp (-s * omega) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hExpGe : -(s * omega) ≤ Real.exp (-s * omega) - 1 := by
    have h := Real.add_one_le_exp (-s * omega)
    linarith
  have hinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hnegative : Real.exp (-s * omega) - 1 ≤ 0 := by
    linarith
  have hL :
      s⁻¹ * (-(s * omega)) ≤
        s⁻¹ * (Real.exp (-s * omega) - 1) :=
    mul_le_mul_of_nonneg_left hExpGe hinv
  have hR :
      s⁻¹ * (Real.exp (-s * omega) - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hinv hnegative
  apply abs_le.mpr
  constructor
  · calc
      -omega = s⁻¹ * (-(s * omega)) := by
        field_simp [ne_of_gt hs]
        ring
      _ ≤ s⁻¹ * (Real.exp (-s * omega) - 1) := hL
  · exact hR.trans homega

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_scalar_difference_quotient_abs_le

end GegenbauerFock.Ultraspherical
