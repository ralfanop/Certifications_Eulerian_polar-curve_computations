import GegenbauerFock.OutputGramSpectrum

/-!
# V007: the zero spectral sector of the actual output Gram

The coefficient-side Gram is CC†. Its zero eigenspace is precisely
ker(C†), equivalently the orthogonal complement of the range of C.
This is a genuine infinite-dimensional Hilbert-space identity, derived
using the adjoint laws already in pinned Mathlib.

In particular NO density-of-range assumption is made: the statement
isolates the zero-mode obstruction that a later density proof must
eliminate.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Exact equality of the closed kernels ker(CC†) = ker(C†) in
the true Fock coefficient Hilbert space. -/
theorem outputGram_ker_eq_C_adjoint_ker
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (outputGram lam alpha hlam ha).ker =
      (C_adjoint lam alpha hlam ha).ker := by
  change ((C lam alpha hlam ha).comp
    (C lam alpha hlam ha).adjoint).ker =
      (C lam alpha hlam ha).adjoint.ker
  exact (C lam alpha hlam ha).ker_self_comp_adjoint

/-- The null eigenspace of CC† is exactly the kernel of the genuine
Hilbert adjoint of C. -/
theorem outputGram_zero_eigenspace_eq_C_adjoint_ker
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    eigenspace (outputGram lam alpha hlam ha).toLinearMap 0 =
      (C_adjoint lam alpha hlam ha).ker := by
  rw [eigenspace_zero]
  exact outputGram_ker_eq_C_adjoint_ker lam alpha hlam ha

/-- The zero eigenspace on the Fock side is precisely the
orthogonal complement of the concrete source-side image of C:
this is the exact missing density-of-range obstruction. -/
theorem outputGram_zero_eigenspace_eq_orthogonal_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    eigenspace (outputGram lam alpha hlam ha).toLinearMap 0 =
      (C lam alpha hlam ha).rangeᗮ := by
  rw [outputGram_zero_eigenspace_eq_C_adjoint_ker]
  exact (C lam alpha hlam ha).orthogonal_range.symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_ker_eq_C_adjoint_ker
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_zero_eigenspace_eq_C_adjoint_ker
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_zero_eigenspace_eq_orthogonal_range

end GegenbauerFock.GeneralUltrasphericalFock
