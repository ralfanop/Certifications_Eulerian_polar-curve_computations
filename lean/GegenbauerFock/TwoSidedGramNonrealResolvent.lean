import GegenbauerFock.TwoSidedGramNegativeResolvent

/-!
# V007 — nonreal parameters are resolvent points for both concrete Grams

The two compact positive selfadjoint Grams act on distinct complex
Hilbert spaces, yet their entire scalar resolvent sets coincide.
A nonreal complex scalar cannot belong to either operator spectrum:
every spectral value has zero imaginary part.

The statement is global, and makes no inference from finite-dimensional
approximations or a surjective Gegenbauer–Fock coefficient transform.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- All genuinely nonreal complex parameters are simultaneously
resolvent parameters for both actual Gram operators. -/
theorem two_sided_gram_nonreal_mem_resolventSet
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu.im ≠ 0) :
    mu ∈ resolventSet ℂ (gram lam alpha hlam ha) ∧
      mu ∈ resolventSet ℂ (outputGram lam alpha hlam ha) := by
  have hnot : mu ∉ spectrum ℂ (gram lam alpha hlam ha) := by
    intro hm
    have hr : (mu.re : ℂ) = mu :=
      ((two_sided_gram_spectra_nonnegative_real lam alpha hlam ha).1 mu hm).1
    have hi : mu.im = 0 := by
      have h := congrArg Complex.im hr
      simpa using h.symm
    exact hmu hi
  have hres : mu ∈ resolventSet ℂ (gram lam alpha hlam ha) := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
  exact ⟨hres,
    (two_sided_gram_resolventSet_eq lam alpha hlam ha) ▸ hres⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonreal_mem_resolventSet

end GegenbauerFock.GeneralUltrasphericalFock
