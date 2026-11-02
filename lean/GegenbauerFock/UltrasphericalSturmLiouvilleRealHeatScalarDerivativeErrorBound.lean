import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarDifferenceBound

/-!
# V007 — sharp spectral error domination for the heat-generator derivative

The bounded heat difference quotient q_s(ω)=s⁻¹(exp(-sω)-1)
satisfies -ω ≤ q_s(ω) ≤ 0 whenever s>0 and ω≥0.
Consequently 0 ≤ q_s(ω)+ω ≤ ω, and therefore
  |q_s(ω)+ω| ≤ ω.
This gives the precise square-summable majorant ω_n² |c_n|²
on the canonical closed Sturm domain for the forward generator
dominated-convergence proof in genuine weighted L².
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- The scalar error between the right heat quotient and its Sturm
spectral derivative is dominated by the spectral frequency itself. -/
theorem sturmRealHeat_scalar_derivative_error_abs_le
    (omega s : ℝ) (homega : 0 ≤ omega) (hs : 0 < s) :
    |s⁻¹ * (Real.exp (-s * omega) - 1) + omega| ≤ omega := by
  have habs :=
    sturmRealHeat_scalar_difference_quotient_abs_le omega s homega hs
  have hqLower :
      -omega ≤ s⁻¹ * (Real.exp (-s * omega) - 1) :=
    (abs_le.mp habs).1
  have hexp : Real.exp (-s * omega) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have hw : 0 ≤ s * omega := mul_nonneg hs.le homega
      linarith)
  have hqUpper :
      s⁻¹ * (Real.exp (-s * omega) - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs.le) (by linarith)
  apply abs_le.mpr
  constructor <;> linarith

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_scalar_derivative_error_abs_le

end GegenbauerFock.Ultraspherical
