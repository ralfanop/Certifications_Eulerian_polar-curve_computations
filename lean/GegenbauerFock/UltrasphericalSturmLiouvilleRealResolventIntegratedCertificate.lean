import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventFullSpectrum
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventInverseOnRange
import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventQuadraticNormError

/-!
# V007 — integrated kernel certificate for the canonical closed Sturm resolvent

This module imports together the independent operator-domain, exact
real-spectrum, finite-rank compact-approximation, and inverse-on-range
theorems. It records a complete spectral dichotomy for genuine weighted
real L², and a single compactness-and-spectrum certificate suitable
for citing as one result in the V007 manuscript.

It does not change V097, V170, or the closed operator's definition.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every real spectral value of the actual compact resolvent is either
the non-eigenvalue zero, or a strictly positive Gegenbauer eigenvalue.
The first alternative explicitly excludes eigenvectors at zero. -/
theorem sturmRealClosedResolvent_spectral_dichotomy
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (r : ℝ)
    (hs : r ∈ spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht)) :
    (r = 0 ∧ ¬ ∃ f : SturmH lam, f ≠ 0 ∧
      sturmRealPositiveResolventFullCLM lam t hlam ht f = r • f) ∨
      (∃ n : ℕ, r = (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ ∧
        0 < r) := by
  rcases (sturmRealClosedResolvent_mem_spectrum_iff
    lam t hlam ht r).mp hs with hzero | ⟨n, hn⟩
  · left
    refine ⟨hzero, ?_⟩
    rintro ⟨f, hf, heig⟩
    have hRf : sturmRealPositiveResolventFullCLM lam t hlam ht f = 0 := by
      rw [hzero] at heig
      simpa using heig
    exact (sturmRealPositiveResolventFullCLM_zero_not_eigenvalue
      lam t hlam ht) ⟨f, hf, hRf⟩
  · right
    refine ⟨n, hn, ?_⟩
    rw [hn]
    exact sturmResolventMultiplier_pos lam t hlam ht n

/-- Integrated operator certificate for the canonical closure's genuine
positive resolvent on the entire complete weighted real L² space. -/
theorem sturmRealClosedResolvent_compact_spectrum_and_exact_cutoffs
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsCompactOperator (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    (spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      ({0} : Set ℝ) ∪
        Set.range (fun n : ℕ =>
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹)) ∧
    (∀ N : ℕ,
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
        sturmRealResolventFiniteRankTruncation lam t hlam N‖ =
        (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹) ∧
    ((sturmRealPositiveResolventFullCLM lam t hlam ht).range.topologicalClosure =
      (⊤ : Submodule ℝ (SturmH lam))) ∧
    ¬ IsClosed ((sturmRealPositiveResolventFullCLM lam t hlam ht).range :
      Set (SturmH lam)) := by
  refine ⟨sturmRealClosedResolvent_isCompactOperator lam t hlam ht,
    sturmRealClosedResolvent_spectrum_eq lam t hlam ht, ?_,
    sturmRealResolvent_dense_range lam t hlam ht,
    sturmRealResolvent_range_not_closed lam t hlam ht⟩
  intro N
  exact sturmRealClosedResolvent_finite_tail_norm_eq lam t hlam ht N

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_spectral_dichotomy
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_compact_spectrum_and_exact_cutoffs
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_inverse_on_range_discontinuous_at_zero

end GegenbauerFock.Ultraspherical
