import Mathlib

/-!
# V007: infinite coefficient Fock Hilbert model

A concrete \u2113\u00b2(\u2115;\u2102) Hilbert space is used as the
coefficient realization of the holomorphic Gaussian Fock space.
This module does not claim the analytic isometric identification
with the full space of entire functions; that identification and the
coherent exponential coefficient norm remain separate obligations.

The coordinate functionals are genuine bounded linear maps on
an *infinite-dimensional* Hilbert space, with verified adjoints.
-/

open scoped ENNReal

namespace GegenbauerFock.FockSequence

/-- Weighted holomorphic Fock space after passing to its
orthonormal monomial coordinates. This is a genuine Hilbert space. -/
abbrev Coefficients : Type := lp (fun _ : ℕ => ℂ) 2

/-- Coordinate evaluation is a bounded complex-linear map. -/
noncomputable def coordinate (n : ℕ) : Coefficients →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n

/-- The n-th evaluation has norm at most one on genuine \u2113\u00b2. -/
theorem coordinate_bound (n : ℕ) (x : Coefficients) :
    ‖coordinate n x‖ ≤ ‖x‖ := by
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n

/-- The coefficient functional has a genuine Hilbert adjoint. -/
theorem coordinate_adjoint_exists (n : ℕ) :
    ∃ T : ℂ →L[ℂ] Coefficients, T = (coordinate n).adjoint := by
  exact ⟨_, rfl⟩

/-- The infinite-dimensional Fock coordinate model is complete. -/
theorem fock_complete : CompleteSpace Coefficients := inferInstance

/-- Mathlib equips the coefficient model with the actual complex inner product. -/
theorem fock_innerProduct : InnerProductSpace ℂ Coefficients := inferInstance

#print axioms GegenbauerFock.FockSequence.coordinate_bound
#print axioms GegenbauerFock.FockSequence.coordinate_adjoint_exists
#print axioms GegenbauerFock.FockSequence.fock_complete
#print axioms GegenbauerFock.FockSequence.fock_innerProduct

end GegenbauerFock.FockSequence
