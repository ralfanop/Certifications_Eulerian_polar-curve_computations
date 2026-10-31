import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaFiniteSpanLimit
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaStrongLimitDensityPrinciple
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialContractive
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# V007 — existence of the strong Yosida heat-semigroup limit on all real L²

The explicitly constructed normalized Gegenbauer eigenmodes form a true
complete Hilbert basis of the weighted real L². The bounded Yosida
semigroups S_t(s) are contractive for every s≥0, uniformly in t.

The independently kernel-checked finite-sum convergence, plus
completeness and density, therefore gives the existence of a strong
limit of S_{k+1}(s) f for EVERY f∈L² at every fixed s≥0.

This theorem constructs the limit as an existential; the semigroup law
of the limit and identification of its unbounded generator are separate.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every weighted-real-L² vector has a strong Yosida exponential
limit along the positive integer shifts t=k+1, for fixed s≥0. -/
theorem sturmRealYosidaExponential_allL2_strong_limit_exists
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam) :
    ∃ y : SturmH lam,
      Tendsto
        (fun k : ℕ =>
          sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
            (by positivity : 0 < (k : ℝ) + 1) s f)
        atTop (𝓝 y) := by
  let v : ℕ → SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let b : HilbertBasis ℕ ℝ (SturmH lam) :=
    sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let S : Submodule ℝ (SturmH lam) :=
    Submodule.span ℝ (Set.range v)
  let T : ℕ → SturmH lam →L[ℝ] SturmH lam :=
    fun k => sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
      (by positivity : 0 < (k : ℝ) + 1) s
  have hnorm (k : ℕ) : ‖T k‖ ≤ 1 :=
    sturmRealYosidaExponential_opNorm_le_one
      lam ((k : ℝ) + 1) hlam
      (by positivity : 0 < (k : ℝ) + 1) s hs
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
      exact ⟨n, hb n⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hb n).symm⟩
  have hdense : Dense (S : Set (SturmH lam)) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    change (Submodule.span ℝ (Set.range v)).topologicalClosure = ⊤
    rw [← hrange]
    exact b.dense_span
  have hconv (d : SturmH lam) (hd : d ∈ S) :
      ∃ y : SturmH lam, Tendsto (fun k : ℕ => T k d) atTop (𝓝 y) := by
    change d ∈ Submodule.span ℝ (Set.range v) at hd
    obtain ⟨a, ha⟩ :=
      Finsupp.mem_span_range_iff_exists_finsupp.mp hd
    have hx :
        sturmRealGegenbauerFiniteVector lam hlam a.support (fun n => a n) =
          d := by
      change (∑ n ∈ a.support, (a n) • v n) = d
      exact ha
    refine ⟨sturmRealGegenbauerFiniteHeatVector lam hlam
      a.support (fun n => a n) s, ?_⟩
    change Tendsto (fun k : ℕ =>
      sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
        (by positivity : 0 < (k : ℝ) + 1) s d) atTop _
    rw [← hx]
    exact sturmRealYosidaExponential_finiteGegenbauer_tendsto
      lam hlam a.support (fun n => a n) s
  exact strongLimit_of_uniform_contractions_on_dense
    T hnorm (S : Set (SturmH lam)) hdense hconv f

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_allL2_strong_limit_exists

end GegenbauerFock.Ultraspherical
