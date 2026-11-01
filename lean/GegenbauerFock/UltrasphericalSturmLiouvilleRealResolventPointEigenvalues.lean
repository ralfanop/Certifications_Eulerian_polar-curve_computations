import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay

/-!
# V007 — exact real point spectrum of the genuine closed Sturm resolvent

For the actual closed Sturm operator on the complete weighted-real-L²
space, its positive-shift bounded resolvent has exactly the positive
degree-n Gegenbauer multipliers as point eigenvalues. In particular,
zero is NOT an eigenvalue, even though the multipliers tend to zero.
The proof uses the certified actual normalized Gegenbauer Hilbert
basis and its exact resolvent coordinate formula.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact classification of the real point eigenvalues of the
everywhere-defined true closed Sturm positive resolvent. -/
theorem sturmRealPositiveResolventFullCLM_point_eigenvalue_iff
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (r : ℝ) :
    (∃ f : H lam, f ≠ 0 ∧
      sturmRealPositiveResolventFullCLM lam t hlam ht f = r • f) ↔
    ∃ n : ℕ, r = (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ := by
  constructor
  · rintro ⟨f, hf, heig⟩
    let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
    have hnonzero : ∃ n : ℕ, (b.repr f) n ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hz : b.repr f = 0 := by
        ext n
        exact hall n
      exact hf (b.repr.injective (by simpa only [map_zero] using hz))
    obtain ⟨n, hn⟩ := hnonzero
    have hcoord :=
      sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
        lam t hlam ht f n
    rw [heig, map_smul] at hcoord
    change r * (b.repr f) n =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ * (b.repr f) n at hcoord
    have hfactor :
        (r - (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) *
          (b.repr f) n = 0 := by
      calc
        _ = r * (b.repr f) n -
            (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ *
              (b.repr f) n := by ring
        _ = 0 := sub_eq_zero.mpr hcoord
    exact ⟨n, sub_eq_zero.mp
      ((mul_eq_zero.mp hfactor).resolve_right hn)⟩
  · rintro ⟨n, rfl⟩
    refine ⟨sturmMonicEigenCandidate_realL2_normalized lam hlam n,
      ?_, ?_⟩
    · intro hz
      have hnorm := sturmMonicEigenCandidate_realL2_normalized_norm
        lam hlam n
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    · exact sturmMonicRealHilbertBasis_full_resolvent_eigen
        lam t hlam ht n

/-- Zero is excluded from the point spectrum of the actual bounded
real-L² Sturm resolvent, regardless of shift t > 0. -/
theorem sturmRealPositiveResolventFullCLM_zero_not_eigenvalue
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ¬ ∃ f : H lam, f ≠ 0 ∧
      sturmRealPositiveResolventFullCLM lam t hlam ht f = 0 := by
  rintro ⟨f, hf, hRf⟩
  have hpoint :
      ∃ f : H lam, f ≠ 0 ∧
        sturmRealPositiveResolventFullCLM lam t hlam ht f =
          (0 : ℝ) • f := by
    refine ⟨f, hf, ?_⟩
    simpa only [zero_smul] using hRf
  obtain ⟨n, hn⟩ :=
    (sturmRealPositiveResolventFullCLM_point_eigenvalue_iff
      lam t hlam ht 0).mp hpoint
  have hpos := sturmResolventMultiplier_pos lam t hlam ht n
  rw [← hn] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- The genuine closed Sturm positive resolvent is injective on
the entire weighted-real-L² Hilbert space. It cannot annihilate any
nonzero source, although its eigenvalues accumulate at zero. -/
theorem sturmRealPositiveResolventFullCLM_injective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Injective (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  intro f g hfg
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  by_contra hne
  have hdiff : f - g ≠ (0 : H lam) := by
    intro hz
    exact hne (sub_eq_zero.mp hz)
  have hzero : R (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  exact (sturmRealPositiveResolventFullCLM_zero_not_eigenvalue
    lam t hlam ht) ⟨f - g, hdiff, hzero⟩

/-- Every real point eigenvalue of the genuine closed Sturm
positive resolvent is strictly positive. -/
theorem sturmRealPositiveResolventFullCLM_point_eigenvalue_pos
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (r : ℝ)
    (hpoint : ∃ f : H lam, f ≠ 0 ∧
      sturmRealPositiveResolventFullCLM lam t hlam ht f = r • f) :
    0 < r := by
  obtain ⟨n, rfl⟩ :=
    (sturmRealPositiveResolventFullCLM_point_eigenvalue_iff
      lam t hlam ht r).mp hpoint
  exact sturmResolventMultiplier_pos lam t hlam ht n

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_point_eigenvalue_iff
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_zero_not_eigenvalue
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_injective
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_point_eigenvalue_pos

end GegenbauerFock.Ultraspherical
