import GegenbauerFock.CompactQuasiaffinity
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# V007 — the compact dense-range Fock transform is not onto

A compact bounded linear operator C on two Hilbert spaces cannot be
bijective if its target is infinite-dimensional: otherwise the Banach
bounded inverse theorem would make the target identity compact,
forcing finite dimensionality.

The target is the actual infinite complex coefficient space lp(ℕ,2),
whose standard coordinate vectors form an infinite linearly
independent family. Combined with the certified dense-range theorem,
this identifies the precise functional-analytic nature of C:
injective and dense but NOT surjective.

This file is a candidate until its pinned Lean build and #print axioms
pass. It does not modify any previously certified module.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual Gaussian-Fock coefficient Hilbert space is not
finite-dimensional over ℂ, as witnessed by the standard ℓ² basis. -/
theorem fockCoefficients_not_finiteDimensional :
    ¬ FiniteDimensional ℂ InfiniteAnalysis.FockCoefficients := by
  intro hfinite
  letI : FiniteDimensional ℂ InfiniteAnalysis.FockCoefficients := hfinite
  let b : HilbertBasis ℕ ℂ InfiniteAnalysis.FockCoefficients := default
  have hlin : LinearIndependent ℂ (fun n : ℕ => b n) :=
    b.orthonormal.linearIndependent
  exact (Module.Finite.not_linearIndependent_of_infinite
    (fun n : ℕ => b n)) hlin

/-- General compact-injective obstruction to surjectivity with an
infinite-dimensional codomain. This proof is formulated abstractly to
avoid unfolding the ultraspherical integral operator while invoking
the Banach bounded-inverse theorem. -/
private theorem compact_injective_not_surjective
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F)
    (hcompact : IsCompactOperator T)
    (hinj : Function.Injective T)
    (hinfinite : ¬ FiniteDimensional ℂ F) :
    ¬ Function.Surjective T := by
  intro hsurj
  have hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : T.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let e : E ≃L[ℂ] F := ContinuousLinearEquiv.ofBijective T hker hrange
  have hcompact' : IsCompactOperator (T ∘ (e.symm : F →L[ℂ] E)) :=
    hcompact.comp_clm (e.symm : F →L[ℂ] E)
  have hcomp_id : (T ∘ (e.symm : F →L[ℂ] E)) = (id : F → F) := by
    funext y
    exact e.apply_symm_apply y
  rw [hcomp_id] at hcompact'
  exact hinfinite (FiniteDimensional.of_isCompactOperator_id hcompact')

/-- C has dense image but cannot be surjective. If it were onto,
the Banach inverse theorem would make the identity on ℓ² compact,
forcing its infinite-dimensional coefficient space to be finite. -/
theorem C_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (C lam alpha hlam ha) :=
  compact_injective_not_surjective
    (C lam alpha hlam ha)
    (C_compact lam alpha hlam ha)
    (C_injective lam alpha hlam ha)
    fockCoefficients_not_finiteDimensional

/-- The actual compact quasiaffinity has a proper, dense image.
These assertions remain different: dense does not mean closed or onto. -/
theorem C_proper_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) ∧
      ¬ Function.Surjective (C lam alpha hlam ha) :=
  ⟨C_dense_range_unconditional lam alpha hlam ha,
    C_not_surjective lam alpha hlam ha⟩

/-- The concrete Fock transform has non-closed image: it is dense,
but not equal to the full output Hilbert space. -/
theorem C_range_not_closed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ IsClosed
      ((C lam alpha hlam ha).range :
        Set InfiniteAnalysis.FockCoefficients) := by
  intro hclosed
  have htop : (C lam alpha hlam ha).range =
      (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
    calc
      (C lam alpha hlam ha).range =
          (C lam alpha hlam ha).range.topologicalClosure :=
        (hclosed.submodule_topologicalClosure_eq).symm
      _ = ⊤ := C_dense_range_unconditional lam alpha hlam ha
  exact C_not_surjective lam alpha hlam ha
    (LinearMap.range_eq_top.mp htop)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fockCoefficients_not_finiteDimensional
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_not_surjective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_proper_dense_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_range_not_closed

end GegenbauerFock.GeneralUltrasphericalFock
