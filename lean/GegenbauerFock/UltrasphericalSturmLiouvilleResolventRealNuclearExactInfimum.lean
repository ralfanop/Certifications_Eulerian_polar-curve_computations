import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearFiniteSumDual
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealSchattenBasis
import Mathlib.Topology.Order.OrderClosed

/-!
# V007 — sharp real nuclear projective norm of the actual closed Sturm resolvent

The finite Fourier trace dual estimate is passed to every summable
rank-one representation by continuity of the finite trace in operator
norm. Passing to all Gegenbauer modes gives the universal projective
nuclear lower bound, which matches the already kernel-certified upper
bound. This is the real-Hilbert projective nuclear S1 model, not an
unproved complex CFC/Physlib identification.

The declarations are CANDIDATES until exact-SHA compilation and
#print axioms checks succeed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A uniform coefficient-one finite Fourier trace bound for any
operator-norm absolutely summable REAL rank-one series. -/
theorem realHilbertFiniteTrace_rankOne_tsum_abs_le
    (b : HilbertBasis ℕ ℝ H) (N : ℕ)
    (u v : ℕ → H) (β : ℕ → ℝ)
    (hs : Summable (fun k : ℕ => ‖β k‖ * ‖u k‖ * ‖v k‖)) :
    |∑ n ∈ Finset.range N,
      inner ℝ (b n)
        ((∑' k : ℕ, β k • rankOne ℝ (u k) (v k)) (b n))| ≤
      ∑' k : ℕ, ‖β k‖ * ‖u k‖ * ‖v k‖ := by
  let ops : ℕ → (H →L[ℝ] H) :=
    fun k => β k • rankOne ℝ (u k) (v k)
  let cost : ℕ → ℝ :=
    fun k => ‖β k‖ * ‖u k‖ * ‖v k‖
  have hOp : Summable ops := by
    apply Summable.of_norm
    convert hs using 1
    funext k
    exact (by
      dsimp [ops, cost]
      rw [norm_smul, norm_rankOne] :
        ‖ops k‖ = ‖β k‖ * ‖u k‖ * ‖v k‖)
  let F : (H →L[ℝ] H) → ℝ := fun A =>
    |∑ n ∈ Finset.range N, inner ℝ (b n) (A (b n))|
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hleft :
      Tendsto
        (fun K : ℕ => F (∑ k ∈ Finset.range K, ops k))
        atTop (nhds (F (∑' k : ℕ, ops k))) :=
    (hF.tendsto _).comp hOp.hasSum.tendsto_sum_nat
  have hright :
      Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, cost k)
        atTop (nhds (∑' k : ℕ, cost k)) :=
    hs.hasSum.tendsto_sum_nat
  have hbound (K : ℕ) :
      F (∑ k ∈ Finset.range K, ops k) ≤
        ∑ k ∈ Finset.range K, cost k := by
    exact realHilbertFiniteTrace_rankOne_finset_sum_abs_le
      b N (Finset.range K) u v β
  have hlim := le_of_tendsto_of_tendsto' hleft hright hbound
  simpa only [F, ops, cost] using hlim

/-- Each admissible projective nuclear cost dominates every finite
Fourier trace of the same concrete real bounded operator. -/
theorem realHilbertFiniteTrace_le_all_realNuclearCosts
    (b : HilbertBasis ℕ ℝ H) (N : ℕ)
    (T : H →L[ℝ] H) {c : ℝ}
    (hc : c ∈ RealNuclearCosts T) :
    |∑ n ∈ Finset.range N, inner ℝ (b n) (T (b n))| ≤ c := by
  obtain ⟨u, v, β, hs, hseries, rfl⟩ := hc
  rw [hseries]
  exact realHilbertFiniteTrace_rankOne_tsum_abs_le b N u v β hs

/-- The spectral trace is a lower bound for EVERY admissible real
nuclear decomposition cost of the actual canonical closed resolvent. -/
theorem sturmRealClosedResolvent_spectralTrace_le_all_nuclearCosts
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    {c : ℝ}
    (hc : c ∈ RealNuclearCosts
      (sturmRealPositiveResolventFullCLM lam t hlam ht)) :
    sturmResolventSpectralTrace lam t ≤ c := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range N, β n) ≤ c := by
    have hbound :=
      realHilbertFiniteTrace_le_all_realNuclearCosts b N
        (sturmRealPositiveResolventFullCLM lam t hlam ht) hc
    have hdiag :
        (∑ n ∈ Finset.range N,
          inner ℝ (b n)
            (sturmRealPositiveResolventFullCLM lam t hlam ht (b n))) =
        ∑ n ∈ Finset.range N, β n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sturmRealPositiveResolvent_basis_inner_diagonal lam t hlam ht n
    rw [hdiag] at hbound
    have hp : 0 ≤ (∑ n ∈ Finset.range N, β n) := by
      apply Finset.sum_nonneg
      intro n hn
      exact le_of_lt (sturmResolventMultiplier_pos lam t hlam ht n)
    simpa only [abs_of_nonneg hp] using hbound
  have hs : Summable β := sturmResolventMultiplier_summable lam t hlam ht
  unfold sturmResolventSpectralTrace
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall hfinite)

/-- Exact REAL projective nuclear S1 norm of the actual weighted-L2
closed Sturm–Liouville resolvent, computed as the infimum over ALL
admissible rank-one expansions (not one distinguished mass). -/
theorem sturmRealClosedResolvent_realNuclearInfimum_eq_spectralTrace
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    realNuclearInfimum (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      sturmResolventSpectralTrace lam t := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hnonempty : (RealNuclearCosts R).Nonempty := by
    obtain ⟨u, v, β, hs, hseries⟩ :=
      sturmRealClosedResolvent_has_real_nuclear_rank_one_series lam t hlam ht
    refine ⟨∑' n : ℕ, ‖β n‖ * ‖u n‖ * ‖v n‖, ?_⟩
    exact ⟨u, v, β, hs, hseries, rfl⟩
  apply le_antisymm
  · exact sturmRealClosedResolvent_nuclearInfimum_le_spectralTrace lam t hlam ht
  · unfold realNuclearInfimum
    exact le_csInf hnonempty
      (fun c hc =>
        sturmRealClosedResolvent_spectralTrace_le_all_nuclearCosts
          lam t hlam ht hc)

#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_rankOne_tsum_abs_le
#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_le_all_realNuclearCosts
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_spectralTrace_le_all_nuclearCosts
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_realNuclearInfimum_eq_spectralTrace

end GegenbauerFock.Ultraspherical
