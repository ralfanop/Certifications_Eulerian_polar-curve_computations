import GegenbauerFock.UltrasphericalBetaMoments

/-!
# V007: pointwise reflection invariance of the symmetric Beta density

The normalized symmetric Beta(shape λ, shape λ) density is invariant
under x ↦ 1-x on the whole real line, including the zero-density
region outside (0,1).  This is the measure-theoretic symmetry input
for the as-yet unproved vanishing of general ultraspherical odd moments.
-/

namespace GegenbauerFock.Ultraspherical

/-- Reflection invariance of the actual symmetric Beta density
at every real x, without an interior support restriction. -/
theorem symmetricBetaPDFReal_reflection_all
    (lam x : ℝ) :
    ProbabilityTheory.betaPDFReal (shape lam) (shape lam) (1-x) =
      ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact beta_density_reflection lam x hx.1 hx.2
  · have hy : ¬ (0 < 1-x ∧ 1-x < 1) := by
      intro h
      apply hx
      constructor <;> linarith [h.1,h.2]
    simp [ProbabilityTheory.betaPDFReal, hx, hy]

#print axioms GegenbauerFock.Ultraspherical.symmetricBetaPDFReal_reflection_all

end GegenbauerFock.Ultraspherical
