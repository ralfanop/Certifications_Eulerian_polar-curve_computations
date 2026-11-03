import GegenbauerFock.RealHilbertPositiveDiagonalTraceNorm
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatPositiveNuclear

/-!
# V007 — exact real projective S1 norm of the genuine positive-time heat operator

For lambda > 0 and s > 0 the genuine full weighted-real-L2 Gegenbauer
heat operator is positive diagonal with summable eigenvalues.

This module upgrades an explicit positive nuclear representation to the
INFIMUM over ALL admissible real-Hilbert rank-one representations,
using the already kernel-certified abstract diagonal theorem. It is
not a formal comparison with a distinct complex CFC/Physlib S1 API.

No change to the pinned Lean/Mathlib or the Sturm resolvent proofs.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

/-- The actual full real-L2 Gegenbauer heat operator at positive time
has projective nuclear norm exactly equal to its spectral heat trace. -/
theorem sturmRealHeat_realNuclearInfimum_eq_spectralTrace
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    realNuclearInfimum (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) =
      ∑' n : ℕ, Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let beta : ℕ → ℝ :=
    fun n => Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hsum : Summable beta :=
    sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  have hpositive : ∀ n : ℕ, 0 ≤ beta n :=
    fun n => (Real.exp_pos _).le
  have hexpansion :
      sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) =
        ∑' n : ℕ, beta n • rankOne ℝ (b n) (b n) := by
    simpa only [b, beta,
      sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot] using
        sturmRealHeat_positive_nuclear_operator_tsum_eq lam s hlam hs
  have hdiag : ∀ n : ℕ,
      inner ℝ (b n)
        (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) (b n)) = beta n := by
    intro n
    exact sturmRealHeat_actual_basis_inner_diagonal
      lam s hlam (le_of_lt hs) n
  exact realHilbert_positiveDiagonal_nuclearInfimum_eq_trace
    b (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs))
    beta hsum hpositive hexpansion hdiag

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_realNuclearInfimum_eq_spectralTrace

end GegenbauerFock.Ultraspherical
