import GegenbauerFock.NonzeroSourceSpectralCompleteness
import GegenbauerFock.UltrasphericalComplexWeierstrass

/-!
# V007 — unconditional completeness of the nonzero source singular spectrum

The earlier compact spectral theorem established completeness of all
eigenspaces, including the zero sector. The polynomial density and
complex Weierstrass argument subsequently established injectivity of
the actual infinite-dimensional Gegenbauer--Fock operator.

This module combines those independently checked results to eliminate
the zero sector *without any additional density hypothesis*. It proves
the source-side nonzero spectral completeness only: density of the
range of C on the Fock side, normalized eigenbasis enumeration and
trace-eigenvalue summability are separate obligations.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The zero eigenspace of the actual compact source Gram integral
operator vanishes unconditionally for every positive lambda, alpha. -/
theorem gramIntegralOperator_zero_eigenspace_bot
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap (0 : ℂ) =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :=
  gramIntegralOperator_zero_eigenspace_bot_of_C_injective
    lam alpha hlam ha (C_injective lam alpha hlam ha)

/-- The actual ultraspherical source L² is generated densely by the
nonzero compact Gram eigenspaces, with no injectivity or polynomial
density hypothesis in the theorem statement. -/
theorem gramIntegralOperator_nonzero_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
      if mu = 0 then
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      else
        eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :=
  gramIntegralOperator_nonzero_eigenspaces_complete_of_C_injective
    lam alpha hlam ha (C_injective lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_zero_eigenspace_bot
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_nonzero_eigenspaces_complete

end GegenbauerFock.GeneralUltrasphericalFock
