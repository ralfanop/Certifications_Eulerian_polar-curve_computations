import GegenbauerFock.TwoSidedGramProperDenseRange
import Mathlib.Topology.Algebra.Module.Basic

/-!
# V007 — nonclosed ranges for the actual source and output Grams

Both genuine compact positive Grams G=C†C and H=CC† have
proper dense images, as proved separately in the preceding
kernel-certified candidates. A dense linear subspace which is
also closed would be the whole Hilbert space, contradicting
nonsurjectivity. Thus neither Gram image is closed.

Together with the zero-eigenspace results, this identifies
zero as a continuous spectral point (and not a genuine
eigenvalue) for both source and coefficient Hilbert spaces.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem gram_range_not_closed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ IsClosed ((gram lam alpha hlam ha).range :
      Set (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  intro hclosed
  have htop : (gram lam alpha hlam ha).range =
      (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    calc
      (gram lam alpha hlam ha).range =
          (gram lam alpha hlam ha).range.topologicalClosure :=
        (hclosed.submodule_topologicalClosure_eq).symm
      _ = ⊤ := gram_dense_range lam alpha hlam ha
  exact gram_not_surjective lam alpha hlam ha
    (LinearMap.range_eq_top.mp htop)

theorem outputGram_range_not_closed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ IsClosed ((outputGram lam alpha hlam ha).range :
      Set InfiniteAnalysis.FockCoefficients) := by
  intro hclosed
  have htop : (outputGram lam alpha hlam ha).range =
      (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
    calc
      (outputGram lam alpha hlam ha).range =
          (outputGram lam alpha hlam ha).range.topologicalClosure :=
        (hclosed.submodule_topologicalClosure_eq).symm
      _ = ⊤ := outputGram_dense_range lam alpha hlam ha
  exact outputGram_not_surjective lam alpha hlam ha
    (LinearMap.range_eq_top.mp htop)

theorem two_sided_gram_nonclosed_ranges
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (¬ IsClosed ((gram lam alpha hlam ha).range :
      Set (Lp ℂ 2 (Ultraspherical.measure lam)))) ∧
    (¬ IsClosed ((outputGram lam alpha hlam ha).range :
      Set InfiniteAnalysis.FockCoefficients)) :=
  ⟨gram_range_not_closed lam alpha hlam ha,
   outputGram_range_not_closed lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_range_not_closed
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_range_not_closed
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonclosed_ranges

end GegenbauerFock.GeneralUltrasphericalFock
