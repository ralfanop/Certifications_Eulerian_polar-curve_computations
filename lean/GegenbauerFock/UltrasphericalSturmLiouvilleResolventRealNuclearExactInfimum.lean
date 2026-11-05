import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearDualLower

/-!
# V007 — exact real nuclear projective infimum (canonical certified bridge)

The earlier finite-rank-series experiment is superseded by the
kernel-checked general continuous-linear-functional proof in
`UltrasphericalSturmLiouvilleResolventRealNuclearDualLower`.
We expose compatible statement names here without repeating the
proof or depending on an unrelated experimental finite-sum module.

These are results about the intrinsic real-Hilbert projective nuclear
infimum of the ACTUAL Sturm resolvent, not an asserted equivalence to
a separate complex CFC trace-class API.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every absolutely summable real rank-one series obeys the uniform
coefficient-one finite-coordinate trace inequality. -/
theorem realHilbertFiniteTrace_rankOne_tsum_abs_le
    (b : HilbertBasis ℕ ℝ H) (N : ℕ)
    (u v : ℕ → H) (β : ℕ → ℝ)
    (hs : Summable (fun k : ℕ => ‖β k‖ * ‖u k‖ * ‖v k‖)) :
    |∑ n ∈ Finset.range N,
      inner ℝ (b n)
        ((∑' k : ℕ, β k • rankOne ℝ (u k) (v k)) (b n))| ≤
      ∑' k : ℕ, ‖β k‖ * ‖u k‖ * ‖v k‖ := by
  have hc :
      (∑' k : ℕ, ‖β k‖ * ‖u k‖ * ‖v k‖) ∈
        RealNuclearCosts
          (∑' k : ℕ, β k • rankOne ℝ (u k) (v k)) :=
    ⟨u, v, β, hs, rfl, rfl⟩
  exact realHilbertFiniteTrace_abs_le_nuclearCost b N _ hc

/-- Uniform lower bound, valid for every admissible real projective
nuclear cost of any bounded real-Hilbert operator. -/
theorem realHilbertFiniteTrace_le_all_realNuclearCosts
    (b : HilbertBasis ℕ ℝ H) (N : ℕ)
    (T : H →L[ℝ] H) {c : ℝ}
    (hc : c ∈ RealNuclearCosts T) :
    |∑ n ∈ Finset.range N, inner ℝ (b n) (T (b n))| ≤ c :=
  realHilbertFiniteTrace_abs_le_nuclearCost b N T hc

/-- Every admissible nuclear cost of the actual closed real Sturm
resolvent dominates its full spectral trace. -/
theorem sturmRealClosedResolvent_spectralTrace_le_all_nuclearCosts
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    {c : ℝ}
    (hc : c ∈ RealNuclearCosts
      (sturmRealPositiveResolventFullCLM lam t hlam ht)) :
    sturmResolventSpectralTrace lam t ≤ c :=
  sturmRealClosedResolvent_spectralTrace_le_allNuclearCosts lam t hlam ht hc

/-- The exact intrinsic real projective nuclear norm equals the
spectral trace of the true full-L² canonical Sturm resolvent. -/
theorem sturmRealClosedResolvent_realNuclearInfimum_eq_spectralTrace
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    realNuclearInfimum (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      sturmResolventSpectralTrace lam t :=
  sturmRealClosedResolvent_nuclearInfimum_eq_spectralTrace lam t hlam ht

#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_rankOne_tsum_abs_le
#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_le_all_realNuclearCosts
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_spectralTrace_le_all_nuclearCosts
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_realNuclearInfimum_eq_spectralTrace

end GegenbauerFock.Ultraspherical
