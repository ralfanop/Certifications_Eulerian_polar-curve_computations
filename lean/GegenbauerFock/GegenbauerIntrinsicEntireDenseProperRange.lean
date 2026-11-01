import GegenbauerFock.GegenbauerIntrinsicEntireCompactQuasiaffinity
import GegenbauerFock.CompactFockProperDenseRange
import Mathlib.Topology.Algebra.Module.Basic

/-!
# V007 — compact ultraspherical transform has proper dense nonclosed range
# in the genuine entire Gaussian Fock Hilbert space

The onto Bargmann–Fock realization is an isometry between ℓ² and the
entire Gaussian L² space. In contrast, the ultraspherical transform
remains compact and injective, with proper dense (hence nonclosed)
range. This separates Hilbert-space completeness of the *target*
from invertibility of the *ultraspherical source transform*.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine coefficient-space ultraspherical transform has a dense
range as a plain function between the two Hilbert spaces. -/
theorem C_denseRange_as_function
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    DenseRange (C lam alpha hlam ha) := by
  change Dense ((C lam alpha hlam ha).range :
    Set InfiniteAnalysis.FockCoefficients)
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (C_dense_range_unconditional lam alpha hlam ha)

/-- The ultraspherical transform into actual entire Gaussian L² has
dense range, although it is not surjective. -/
theorem C_intrinsicEntire_denseRange
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    DenseRange (C_intrinsicEntire lam alpha hlam ha) := by
  have he :
      DenseRange
        (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha) :=
    (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).surjective.denseRange
  have hc : DenseRange
      ((GaussianArea.coefficientIntrinsicEntireEquiv alpha ha) ∘
        (C lam alpha hlam ha)) :=
    he.comp (C_denseRange_as_function lam alpha hlam ha)
      (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).continuous
  exact hc

/-- The image is dense but not closed in the true intrinsic
holomorphic Gaussian L² topology. -/
theorem C_intrinsicEntire_range_not_closed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ IsClosed ((C_intrinsicEntire lam alpha hlam ha).range :
      Set (GaussianArea.entireGaussianL2Submodule alpha)) := by
  intro hclosed
  have hcl :
      closure (Set.range (C_intrinsicEntire lam alpha hlam ha)) =
        Set.univ :=
    (C_intrinsicEntire_denseRange lam alpha hlam ha).closure_range
  have hfull :
      ((C_intrinsicEntire lam alpha hlam ha).range :
        Set (GaussianArea.entireGaussianL2Submodule alpha)) = Set.univ :=
    hclosed.closure_eq.symm.trans hcl
  apply C_intrinsicEntire_not_surjective lam alpha hlam ha
  intro y
  have hy : y ∈
      ((C_intrinsicEntire lam alpha hlam ha).range :
        Set (GaussianArea.entireGaussianL2Submodule alpha)) := by
    rw [hfull]
    trivial
  exact hy

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_denseRange_as_function
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_denseRange
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_range_not_closed

end GegenbauerFock.GeneralUltrasphericalFock
