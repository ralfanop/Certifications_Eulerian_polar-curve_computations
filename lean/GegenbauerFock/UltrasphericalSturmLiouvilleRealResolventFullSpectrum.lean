import GegenbauerFock.UltrasphericalSturmLiouvilleResolventCompactExact
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventZeroSpectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# V007 — complete spectrum of the genuine canonical closed Sturm resolvent

The exact compactness theorem and the Fredholm alternative identify
each nonzero real spectral point with a point eigenvalue. The prior
all-degree Gegenbauer eigenvalue classification then determines the
whole spectrum. The only extra point is zero, already certified as a
continuous spectral point for the true closed positive resolvent.

No assumed resolvent, finite-dimensional substitute or extra axiom.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Fredholm eigenvalue criterion in the actual Gegenbauer–Sturm
real weighted L² Hilbert space, with explicit closed-resolvent eigenvalues. -/
theorem sturmRealClosedResolvent_hasEigenvalue_iff
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (r : ℝ) :
    Module.End.HasEigenvalue
      (sturmRealPositiveResolventFullCLM lam t hlam ht :
        Module.End ℝ (SturmH lam)) r ↔
      ∃ n : ℕ, r = (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ := by
  constructor
  · intro heig
    obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector heig
    apply (sturmRealPositiveResolventFullCLM_point_eigenvalue_iff
      lam t hlam ht r).mp
    refine ⟨f, hf.2, ?_⟩
    exact hf.apply_eq_smul
  · intro h
    obtain ⟨f, hf, hRf⟩ :=
      (sturmRealPositiveResolventFullCLM_point_eigenvalue_iff
        lam t hlam ht r).mpr h
    apply Module.End.hasEigenvalue_of_hasEigenvector
    apply (Module.End.hasEigenvector_iff).mpr
    refine ⟨(Module.End.mem_eigenspace_iff).mpr ?_, hf⟩
    exact hRf

/-- A real scalar belongs to the full operator spectrum exactly if
it is zero or one of the positive Gegenbauer spectral multipliers. -/
theorem sturmRealClosedResolvent_mem_spectrum_iff
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (r : ℝ) :
    r ∈ spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) ↔
      r = 0 ∨
        ∃ n : ℕ, r = (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ := by
  let R : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  have hcompact : IsCompactOperator R :=
    sturmRealClosedResolvent_isCompactOperator lam t hlam ht
  constructor
  · intro hs
    by_cases hzero : r = 0
    · exact Or.inl hzero
    · right
      have heig : Module.End.HasEigenvalue (R : Module.End ℝ (SturmH lam)) r :=
        (hcompact.hasEigenvalue_iff_mem_spectrum hzero).mpr hs
      exact (sturmRealClosedResolvent_hasEigenvalue_iff
        lam t hlam ht r).mp heig
  · rintro (hzero | ⟨n, hn⟩)
    · subst r
      exact sturmRealResolvent_zero_mem_spectrum lam t hlam ht
    · have hnonzero : r ≠ 0 := by
        rw [hn]
        exact ne_of_gt (sturmResolventMultiplier_pos lam t hlam ht n)
      have heig : Module.End.HasEigenvalue (R : Module.End ℝ (SturmH lam)) r :=
        (sturmRealClosedResolvent_hasEigenvalue_iff
          lam t hlam ht r).mpr ⟨n, hn⟩
      exact (hcompact.hasEigenvalue_iff_mem_spectrum hnonzero).mp heig

/-- Exact full real spectrum of the compact canonical positive
resolvent: the degree-n eigenvalue sequence together with zero. -/
theorem sturmRealClosedResolvent_spectrum_eq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      ({0} : Set ℝ) ∪
        Set.range (fun n : ℕ =>
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) := by
  ext r
  rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · intro hs
    rcases (sturmRealClosedResolvent_mem_spectrum_iff
      lam t hlam ht r).mp hs with hzero | ⟨n, hn⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨n, hn.symm⟩
  · rintro (hzero | ⟨n, hn⟩)
    · exact (sturmRealClosedResolvent_mem_spectrum_iff
        lam t hlam ht r).mpr (Or.inl hzero)
    · exact (sturmRealClosedResolvent_mem_spectrum_iff
        lam t hlam ht r).mpr (Or.inr ⟨n, hn.symm⟩)

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_hasEigenvalue_iff
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_mem_spectrum_iff
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_spectrum_eq

end GegenbauerFock.Ultraspherical
