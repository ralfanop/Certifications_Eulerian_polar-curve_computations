import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearFiniteDual
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealSchattenBasis
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# V007 — all-representation trace duality and the real Sturm S₁ norm

The intended conclusion is the REVERSE bound for the genuine nuclear
projective norm infimum. The key intermediate result uniformly bounds
every finite Hilbert diagonal trace against the cost of ANY admissible
real-Hilbert rank-one series.

No change to Mathlib/Lean pins and no use of axioms or 'sorry'.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Continuous real-linear functional: trace compressed to the first
N vectors of a genuine complete real Hilbert basis. -/
noncomputable def realHilbertFiniteTraceCLM
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) :
    (H →L[ℝ] H) →L[ℝ] ℝ :=
  ∑ n ∈ Finset.range N,
    (innerSL ℝ (b n)).comp
      (ContinuousLinearMap.apply ℝ H (b n))

theorem realHilbertFiniteTraceCLM_apply
    (b : HilbertBasis ℕ ℝ H) (N : ℕ)
    (T : H →L[ℝ] H) :
    realHilbertFiniteTraceCLM b N T =
      ∑ n ∈ Finset.range N, inner ℝ (b n) (T (b n)) := by
  simp only [realHilbertFiniteTraceCLM,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Every admissible nuclear rank-one series has finite Hilbert trace
bounded by its WHOLE projective cost, with constant exactly 1,
uniformly in the cutoff N. -/
theorem realHilbertFiniteTrace_abs_le_nuclearCost
    (b : HilbertBasis ℕ ℝ H) (N : ℕ)
    (T : H →L[ℝ] H) {c : ℝ}
    (hc : c ∈ RealNuclearCosts T) :
    |∑ n ∈ Finset.range N, inner ℝ (b n) (T (b n))| ≤ c := by
  rcases hc with ⟨u, v, β, hcost, hT, rfl⟩
  let Φ : (H →L[ℝ] H) →L[ℝ] ℝ := realHilbertFiniteTraceCLM b N
  let A : ℕ → (H →L[ℝ] H) :=
    fun k => β k • rankOne ℝ (u k) (v k)
  have hA : Summable A := by
    apply Summable.of_norm
    convert hcost using 1
    funext k
    rw [norm_smul, norm_rankOne]
    ring
  have hterm (k : ℕ) :
      ‖Φ (A k)‖ ≤ ‖β k‖ * ‖u k‖ * ‖v k‖ := by
    have htrace :
        |Φ (rankOne ℝ (u k) (v k))| ≤ ‖u k‖ * ‖v k‖ := by
      rw [realHilbertFiniteTraceCLM_apply]
      exact realHilbertFiniteTrace_rankOne_abs_le b N (u k) (v k)
    have hscal : Φ (A k) =
        β k • Φ (rankOne ℝ (u k) (v k)) := by
      change Φ (β k • rankOne ℝ (u k) (v k)) = _
      rw [map_smul]
    rw [hscal, norm_smul, Real.norm_eq_abs]
    calc
      ‖β k‖ * |Φ (rankOne ℝ (u k) (v k))| ≤
          ‖β k‖ * (‖u k‖ * ‖v k‖) :=
        mul_le_mul_of_nonneg_left htrace (norm_nonneg _)
      _ = ‖β k‖ * ‖u k‖ * ‖v k‖ := by ring
  have hΦnorm : Summable (fun k : ℕ => ‖Φ (A k)‖) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · exact hterm
    · exact hcost
  have hΦ : Summable (fun k : ℕ => Φ (A k)) :=
    Summable.of_norm hΦnorm
  have hcommute : Φ T = ∑' k : ℕ, Φ (A k) := by
    rw [hT]
    exact Φ.map_tsum hA
  have hsumBound :
      (∑' k : ℕ, ‖Φ (A k)‖) ≤
        ∑' k : ℕ, ‖β k‖ * ‖u k‖ * ‖v k‖ :=
    hΦnorm.tsum_le_tsum hterm hcost
  calc
    |∑ n ∈ Finset.range N, inner ℝ (b n) (T (b n))| =
        ‖Φ T‖ := by
          rw [realHilbertFiniteTraceCLM_apply]
          exact (Real.norm_eq_abs _).symm
    _ = ‖∑' k : ℕ, Φ (A k)‖ := by rw [hcommute]
    _ ≤ ∑' k : ℕ, ‖Φ (A k)‖ :=
      norm_tsum_le_tsum_norm hΦnorm
    _ ≤ ∑' k : ℕ, ‖β k‖ * ‖u k‖ * ‖v k‖ := hsumBound

/-- For the ACTUAL real closed Sturm resolvent, all projective
nuclear representation costs dominate the exact spectral trace. -/
theorem sturmRealClosedResolvent_spectralTrace_le_allNuclearCosts
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    {c : ℝ}
    (hc : c ∈ RealNuclearCosts
      (sturmRealPositiveResolventFullCLM lam t hlam ht)) :
    sturmResolventSpectralTrace lam t ≤ c := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hn (N : ℕ) : (∑ n ∈ Finset.range N, β n) ≤ c := by
    have h := realHilbertFiniteTrace_abs_le_nuclearCost b N
      (sturmRealPositiveResolventFullCLM lam t hlam ht) hc
    have hdiag :
        (∑ n ∈ Finset.range N,
          inner ℝ (b n)
            (sturmRealPositiveResolventFullCLM lam t hlam ht (b n))) =
        ∑ n ∈ Finset.range N, β n := by
      apply Finset.sum_congr rfl
      intro n _
      exact sturmRealPositiveResolvent_basis_inner_diagonal lam t hlam ht n
    rw [hdiag] at h
    have hβ : 0 ≤ ∑ n ∈ Finset.range N, β n := by
      apply Finset.sum_nonneg
      intro n _
      exact le_of_lt (sturmResolventMultiplier_pos lam t hlam ht n)
    rwa [abs_of_nonneg hβ] at h
  have hs : Summable β := sturmResolventMultiplier_summable lam t hlam ht
  unfold sturmResolventSpectralTrace
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall hn)

/-- Exact equality: the true full-space real Sturm resolvent's
projective 1-nuclear norm is its certified positive spectral trace. -/
theorem sturmRealClosedResolvent_nuclearInfimum_eq_spectralTrace
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    realNuclearInfimum (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      sturmResolventSpectralTrace lam t := by
  apply le_antisymm
  · exact sturmRealClosedResolvent_nuclearInfimum_le_spectralTrace lam t hlam ht
  · unfold realNuclearInfimum
    have hclass :
        HasRealNuclearRankOneSeries
          (sturmRealPositiveResolventFullCLM lam t hlam ht) :=
      sturmRealClosedResolvent_has_real_nuclear_rank_one_series lam t hlam ht
    rcases hclass with ⟨u,v,β,hs,hT⟩
    have hnonempty :
        (RealNuclearCosts
          (sturmRealPositiveResolventFullCLM lam t hlam ht)).Nonempty :=
      ⟨∑' n : ℕ, ‖β n‖ * ‖u n‖ * ‖v n‖, ⟨u,v,β,hs,hT,rfl⟩⟩
    apply le_csInf hnonempty
    intro c hc
    exact sturmRealClosedResolvent_spectralTrace_le_allNuclearCosts lam t hlam ht hc

#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTraceCLM_apply
#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_abs_le_nuclearCost
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_spectralTrace_le_allNuclearCosts
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_nuclearInfimum_eq_spectralTrace

end GegenbauerFock.Ultraspherical
