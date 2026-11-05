import GegenbauerFock.TwoSidedSingularSpectralCompleteness
import GegenbauerFock.ConcreteFockCompact

/-!
# V007 — genuine compact quasiaffinity

The actual Gegenbauer--Fock analysis operator from the ultraspherical
L² source to the complete infinite Gaussian-Fock coefficient Hilbert
space is a compact quasiaffinity: a compact bounded linear map which
is injective and has dense image.

This combines three previously independent kernel-checked results:
summable coefficient rows imply compactness; complex polynomial
Weierstrass density implies injectivity; and analytic uniqueness of
the entire coherent reconstruction implies dense range.

Dense range is NOT identified with surjectivity. In particular,
compactness alone never yields a continuous inverse in infinite
dimension.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Actual C is compact, one-to-one, and has dense range. These
assertions apply to the full infinite-dimensional Hilbert operator,
not to finite truncations or a formal coefficient sequence. -/
theorem C_compact_injective_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (C lam alpha hlam ha) ∧
      Function.Injective (C lam alpha hlam ha) ∧
      (C lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  exact ⟨C_compact lam alpha hlam ha,
    C_injective lam alpha hlam ha,
    C_dense_range_unconditional lam alpha hlam ha⟩

/-- The compact quasiaffinity has trivial kernels on both sides.
We do not strengthen dense range to a closed or surjective range. -/
theorem C_compact_two_sided_kernel_free
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (C lam alpha hlam ha) ∧
      Function.Injective (C lam alpha hlam ha) ∧
      Function.Injective (C_adjoint lam alpha hlam ha) := by
  exact ⟨C_compact lam alpha hlam ha,
    C_injective lam alpha hlam ha,
    C_adjoint_injective_unconditional lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_compact_injective_dense_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_compact_two_sided_kernel_free

end GegenbauerFock.GeneralUltrasphericalFock
