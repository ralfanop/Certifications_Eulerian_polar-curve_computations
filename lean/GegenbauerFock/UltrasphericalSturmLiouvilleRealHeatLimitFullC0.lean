import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitModeContinuity
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatStrongContinuityDensity
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# V007 — strong C₀ continuity of the genuine weighted-real-L² heat limit

The contractive limit heat operators H_s act on the *entire* real
weighted L² and have an explicit diagonal action on each normalized
Gegenbauer mode. The modes form a true Hilbert basis, giving density
of their real linear span. The mode time-continuity and contractive
density principle now give time-zero strong continuity for ALL
vectors of the genuine L².

Combined with the independently formalized positive-time semigroup law,
this establishes the strongly continuous limiting contraction semigroup.
Identification of its infinitesimal generator with the canonical graph
closure is a further, distinct obligation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every vector of the actual weighted real L² has a continuous
heat-limit orbit as time approaches zero from the right. -/
theorem sturmRealHeatLimitNonnegativeExtended_allL2_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    Tendsto
      (fun s : ℝ => sturmRealHeatLimitNonnegativeExtended lam hlam s f)
      (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  let v : ℕ → SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let b : HilbertBasis ℕ ℝ (SturmH lam) :=
    sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let D : Submodule ℝ (SturmH lam) :=
    Submodule.span ℝ (Set.range v)
  let T : ℝ → SturmH lam →L[ℝ] SturmH lam :=
    sturmRealHeatLimitNonnegativeExtended lam hlam
  have hnorm (s : ℝ) (_hs : 0 ≤ s) : ‖T s‖ ≤ 1 :=
    sturmRealHeatLimitNonnegativeExtended_opNorm_le lam hlam s
  have hb (n : ℕ) : b n = v n := by
    dsimp [b, v, sturmMonicEigenCandidate_realL2_hilbertBasis]
    exact congrFun
      (HilbertBasis.coe_mkOfOrthogonalEqBot
        (sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam)
        (sturmMonicEigenCandidate_realL2_normalized_orthogonal_eq_bot lam hlam)) n
  have hrange : Set.range b = Set.range v := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hb n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, hb n⟩
  have hdense : Dense (D : Set (SturmH lam)) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    change (Submodule.span ℝ (Set.range v)).topologicalClosure = ⊤
    rw [← hrange]
    exact b.dense_span
  have hconv (d : SturmH lam) (hd : d ∈ D) :
      Tendsto (fun s : ℝ => T s d) (𝓝[≥] (0 : ℝ)) (𝓝 d) := by
    change d ∈ Submodule.span ℝ (Set.range v) at hd
    obtain ⟨a, ha⟩ :=
      Finsupp.mem_span_range_iff_exists_finsupp.mp hd
    have hsum : (∑ n ∈ a.support, (a n) • v n) = d := ha
    have hterm (n : ℕ) :
        Tendsto (fun s : ℝ => (a n) • (T s (v n)))
          (𝓝[≥] (0 : ℝ)) (𝓝 ((a n) • v n)) :=
      (sturmRealHeatLimitNonnegativeExtended_mode_tendsto_zero
        lam hlam n).const_smul (a n)
    have hfinite :
        Tendsto
          (fun s : ℝ => ∑ n ∈ a.support, (a n) • (T s (v n)))
          (𝓝[≥] (0 : ℝ))
          (𝓝 (∑ n ∈ a.support, (a n) • v n)) := by
      induction a.support using Finset.induction_on with
      | empty => simp
      | @insert n F hn ih =>
          simp only [Finset.sum_insert hn]
          exact (hterm n).add ih
    have hfun :
        (fun s : ℝ => T s d) =
        (fun s : ℝ => ∑ n ∈ a.support, (a n) • (T s (v n))) := by
      funext s
      rw [← hsum]
      simp only [map_sum, map_smul]
    rw [hfun, ← hsum]
    exact hfinite
  exact strongContinuityAtZero_of_contractions_on_dense
    T hnorm (D : Set (SturmH lam)) hdense hconv f

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitNonnegativeExtended_allL2_tendsto_zero

end GegenbauerFock.Ultraspherical
