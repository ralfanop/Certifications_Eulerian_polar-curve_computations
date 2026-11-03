import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatNuclearMass
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearClass

/-!
# V007 — real 1-nuclear class of the actual positive-time Gegenbauer heat operator

For every lambda>0 and s>0, the actual full weighted-real-L² heat
semigroup element admits a REAL nuclear rank-one operator series whose
projective cost is summable. This is not a scalar-only spectral result:
the representing series converges in operator norm to the actual H_s.

The positive orthogonal expansion supplies a sharp explicit nuclear
witness, with rank-one norm mass equal to the genuine basis trace.
No equivalence with a separately defined complex CFC Schatten ideal is
asserted or used.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

/-- The actual strictly positive-time Gegenbauer heat semigroup belongs
to the real Hilbert rank-one nuclear class, on all weighted real L². -/
theorem sturmRealHeat_has_real_nuclear_rank_one_series
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    HasRealNuclearRankOneSeries
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) := by
  exact
    (sturmRealHeat_has_positive_real_nuclear_expansion
      lam s hlam hs).toRealNuclearRankOneSeries

/-- Nuclearity together with exact mass of the positive rank-one
decomposition, computed against the genuine complete Hilbert basis. -/
theorem sturmRealHeat_nuclear_rank_one_mass_certificate
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    HasRealNuclearRankOneSeries
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) ∧
    (∑' n : ℕ,
      ‖Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖) =
    (∑' n : ℕ,
      inner ℝ
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
        (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)
          ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n))) := by
  exact ⟨sturmRealHeat_has_real_nuclear_rank_one_series lam s hlam hs,
    sturmRealHeat_positive_nuclear_mass_eq_actual_basis_trace lam s hlam hs⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_has_real_nuclear_rank_one_series
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_nuclear_rank_one_mass_certificate

end GegenbauerFock.Ultraspherical
