import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! Frozen M16.6 §13, thm:dirac-maxwell-obstruction-164.
Actual compact continuous linear operators on a complex Hilbert space.
No self-adjointness is imposed. This is a Fredholm-alternative gate,
not the full Atkinson index-invariance theorem or the determinant construction. -/
namespace Manuscript16.V166CompactFredholmAlternative

open Module End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Every nonzero exceptional scalar is an actual eigenvalue, and conversely. -/
theorem nonzero_exceptional_iff_eigenvalue
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (μ : ℂ) (hμ : μ ≠ 0) :
    HasEigenvalue K.toLinearMap μ ↔ μ ∈ spectrum ℂ K :=
  hK.hasEigenvalue_iff_mem_spectrum hμ

/-- Away from exceptional scalars, the actual shifted bounded operator is a unit. -/
theorem shifted_isUnit_of_not_eigenvalue
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (μ : ℂ) (hμ : μ ≠ 0)
    (h : ¬ HasEigenvalue K.toLinearMap μ) :
    IsUnit (μ • (1 : E →L[ℂ] E) - K) :=
  spectrum.mem_resolventSet_iff.mp
    ((hK.hasEigenvalue_or_mem_resolventSet hμ).resolve_left h)

/-- The nonzero scalar shift has finite-dimensional kernel, without normality. -/
theorem shifted_finite_kernel
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (μ : ℂ) (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (μ • (1 : E →L[ℂ] E) - K).ker := by
  have heq : (μ • (1 : E →L[ℂ] E) - K).ker = eigenspace K.toLinearMap μ := by
    ext x
    rw [mem_eigenspace_iff]
    change μ • x - K x = 0 ↔ K x = μ • x
    exact sub_eq_zero.trans eq_comm
  rw [heq]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK μ hμ

/-- Even outside the small-norm Neumann regime, absence of an eigenvalue implies
a quantitative bounded-below statement (the constant need not be explicit). -/
theorem shift_antilipschitz_of_not_eigenvalue
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (μ : ℂ) (hμ : μ ≠ 0)
    (h : ¬ HasEigenvalue K.toLinearMap μ) :
    ∃ C, AntilipschitzWith C (K - μ • (1 : E →L[ℂ] E)) :=
  hK.antilipschitz_of_not_hasEigenvalue hμ h

end Manuscript16.V166CompactFredholmAlternative

#print axioms Manuscript16.V166CompactFredholmAlternative.nonzero_exceptional_iff_eigenvalue
#print axioms Manuscript16.V166CompactFredholmAlternative.shifted_isUnit_of_not_eigenvalue
#print axioms Manuscript16.V166CompactFredholmAlternative.shifted_finite_kernel
#print axioms Manuscript16.V166CompactFredholmAlternative.shift_antilipschitz_of_not_eigenvalue
