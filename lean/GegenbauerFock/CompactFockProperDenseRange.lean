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
  let b : HilbertBasis ℕ ℂ InfiniteAnalysis.FockCoefficients := default
  have hlin : LinearIndependent ℂ (fun n : ℕ => b n) :=
    b.orthonormal.linearIndependent
  exact (Module.Finite.not_linearIndependent_of_infinite
    (fun n : ℕ => b n)) hlin

/-- C has dense image but cannot be surjective. If it were onto,
its certified injectivity and the Banach inverse theorem would give a
continuous linear inverse, making the identity on infinite ℓ² compact. -/
theorem C_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (C lam alpha hlam ha) := by
  intro hsurj
  have hker : (C lam alpha hlam ha).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (C_injective lam alpha hlam ha)
  have hrange : (C lam alpha hlam ha).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let e := ContinuousLinearEquiv.ofBijective
    (C lam alpha hlam ha) hker hrange
  have hcompact : IsCompactOperator
      ((C lam alpha hlam ha) ∘
        (e.symm : InfiniteAnalysis.FockCoefficients →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))) :=
    (C_compact lam alpha hlam ha).comp_clm e.symm
  have hidentity : IsCompactOperator
      (id : InfiniteAnalysis.FockCoefficients →
        InfiniteAnalysis.FockCoefficients) := by
    convert hcompact using 1
    funext F
    exact (e.apply_symm_apply F).symm
  have hfinite : FiniteDimensional ℂ InfiniteAnalysis.FockCoefficients :=
    FiniteDimensional.of_isCompactOperator_id hidentity
  exact fockCoefficients_not_finiteDimensional hfinite

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
