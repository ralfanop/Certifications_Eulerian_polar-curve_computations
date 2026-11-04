import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexLpDecomposition
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# V007 — the genuine real-to-complex weighted L2 embedding is isometric

The canonical inclusion J : L²(nu_lambda;R) -> L²(nu_lambda;C)
is a real-linear map on the ACTUAL ultraspherical weighted L² spaces.
Its norm is exactly preserved. The proof is quantitative and avoids any
assumed real/complex basis identification:

* pointwise Complex.ofRealCLM has operator norm one;
* pointwise Complex.reCLM has operator norm one;
* the Lp composition construction contracts according to these norms;
* realPart(J f) = f, already kernel-certified.

Thus two opposite bounds yield the exact equality ||J f||=||f||.
The injection is immediate from its certified left inverse.
No claim of coincidence with the unrelated complex Fock Gram is made.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory
private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Norm preservation on EVERY genuine weighted real-L2 vector. -/
theorem realToComplexLp_norm_eq
    (lam : ℝ) (f : HR lam) :
    ‖realToComplexLp lam f‖ = ‖f‖ := by
  have hupper :
      ‖realToComplexLp lam f‖ ≤ ‖f‖ := by
    calc
      ‖realToComplexLp lam f‖ =
          ‖Complex.ofRealCLM.compLp f‖ := rfl
      _ ≤ ‖Complex.ofRealCLM‖ * ‖f‖ :=
          Complex.ofRealCLM.norm_compLp_le f
      _ = ‖f‖ := by rw [Complex.ofRealCLM_norm, one_mul]
  have hlower :
      ‖f‖ ≤ ‖realToComplexLp lam f‖ := by
    calc
      ‖f‖ =
          ‖complexLpRe lam (realToComplexLp lam f)‖ := by
            rw [complexLpRe_realToComplexLp]
      _ = ‖Complex.reCLM.compLp (realToComplexLp lam f)‖ := rfl
      _ ≤ ‖Complex.reCLM‖ * ‖realToComplexLp lam f‖ :=
          Complex.reCLM.norm_compLp_le _
      _ = ‖realToComplexLp lam f‖ := by
            rw [Complex.reCLM_norm, one_mul]
  exact le_antisymm hupper hlower

/-- The concrete real-to-complex L2 map is injective: applying
the real-component projection gives a left inverse. -/
theorem realToComplexLp_injective (lam : ℝ) :
    Function.Injective (realToComplexLp lam) := by
  intro f g heq
  have hf := congrArg (complexLpRe lam) heq
  simpa only [complexLpRe_realToComplexLp] using hf

#print axioms GegenbauerFock.Ultraspherical.realToComplexLp_norm_eq
#print axioms GegenbauerFock.Ultraspherical.realToComplexLp_injective

end GegenbauerFock.Ultraspherical
