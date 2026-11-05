import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# V007 — a time-uniform scalar majorant for the heat difference quotient

For omega>=0 and s>0, the heat multiplier satisfies
  0 <= ((exp(-s*omega)-1)/s + omega) <= omega.
This is the essential frequency-wise domination for the graph-domain
Parseval argument identifying the unbounded heat generator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- Nonnegative error of the exponential difference quotient, with a
sharp, time-independent upper bound by the spectral frequency omega. -/
theorem sturmRealHeat_scalar_slope_error_bounded
    (omega s : ℝ) (homega : 0 ≤ omega) (hs : 0 < s) :
    0 ≤ (Real.exp (-s * omega) - 1) / s + omega ∧
      (Real.exp (-s * omega) - 1) / s + omega ≤ omega := by
  have hprod : 0 ≤ s * omega := mul_nonneg hs.le homega
  have harg : -s * omega ≤ 0 := by nlinarith
  have hupper : Real.exp (-s * omega) ≤ 1 :=
    Real.exp_le_one_iff.mpr harg
  have hlower : -s * omega + 1 ≤ Real.exp (-s * omega) :=
    Real.add_one_le_exp (-s * omega)
  have hquotlower : -omega ≤ (Real.exp (-s * omega) - 1) / s := by
    apply (le_div_iff₀ hs).2
    nlinarith [hlower]
  have hquotupper : (Real.exp (-s * omega) - 1) / s ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hupper) hs.le
  constructor <;> linarith

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_scalar_slope_error_bounded

end GegenbauerFock.Ultraspherical
