import GegenbauerFock.RealNuclearTwoOrthonormalAllCostsDual

/-!
# V007 — real nuclear S1 from one complete source and an incomplete target family

The source family b is a Hilbert basis. The output singular vectors c
are only ORTHONORMAL; they may fail to be complete and may have proper
closed span. Given nonnegative summable sigma with
T(b_n) = sigma_n c_n, the actual bounded T equals its operator-norm
summable rank-one singular expansion, is nuclear, and has exact
projective nuclear norm equal to sum sigma_n.

No global unitary sending b to c is assumed or constructed. The theorem
covers weighted injective unilateral nuclear shifts, for which no such
unitary exists. It does not assert that EVERY nuclear operator admits
this one-complete-source presentation when zero singular modes occur.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Operator-norm singular rank-one expansion, requiring only an
orthonormal target family, not a second complete Hilbert basis. -/
theorem realOneFullSourceSingular_operator_tsum_eq
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (c : ℕ → H) (hc : Orthonormal ℝ c)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 ≤ sigma n)
    (hs : Summable sigma)
    (heig : ∀ n, T (b n) = sigma n • c n) :
    T = ∑' n : ℕ, sigma n • rankOne ℝ (c n) (b n) := by
  have hsOp : Summable (fun n : ℕ =>
      sigma n • rankOne ℝ (c n) (b n)) := by
    apply Summable.of_norm
    have hn (n : ℕ) :
        ‖sigma n • rankOne ℝ (c n) (b n)‖ = sigma n := by
      rw [norm_smul, norm_rankOne, hc.norm_eq_one n,
        b.orthonormal.norm_eq_one n]
      simp only [one_mul, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (hpos n)]
    exact hs.congr (fun n => (hn n).symm)
  apply ContinuousLinearMap.ext
  intro x
  have hTsum :
      HasSum (fun n : ℕ =>
        (inner ℝ (b n) x) • (sigma n • c n)) (T x) := by
    have hrec := (b.hasSum_repr x).mapL T
    convert hrec using 1
    funext n
    simp only [HilbertBasis.repr_apply_apply, map_smul, heig]
  have hEval :
      (∑' n : ℕ, sigma n • rankOne ℝ (c n) (b n)) x =
        ∑' n : ℕ, (sigma n • rankOne ℝ (c n) (b n)) x :=
    (ContinuousLinearMap.apply ℝ H x).map_tsum hsOp
  calc
    T x = ∑' n : ℕ, (inner ℝ (b n) x) • (sigma n • c n) :=
      hTsum.tsum_eq.symm
    _ = ∑' n : ℕ, (sigma n • rankOne ℝ (c n) (b n)) x := by
      apply tsum_congr
      intro n
      change (inner ℝ (b n) x) • (sigma n • c n) =
        sigma n • ((inner ℝ (b n) x) • c n)
      exact smul_comm (inner ℝ (b n) x) (sigma n) (c n)
    _ = (∑' n : ℕ, sigma n • rankOne ℝ (c n) (b n)) x :=
      hEval.symm

/-- An arbitrary real Hilbert operator with a complete source basis,
possibly INCOMPLETE target orthonormal singular family, and summable
nonnegative singular values is nuclear with exact projective S1 norm.
The cost infimum ranges over every admissible real rank-one series. -/
theorem realOneFullSourceSingular_nuclear_exact_trace
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (c : ℕ → H) (hc : Orthonormal ℝ c)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 ≤ sigma n)
    (hs : Summable sigma)
    (heig : ∀ n, T (b n) = sigma n • c n) :
    HasRealNuclearRankOneSeries T ∧
      realNuclearInfimum T = ∑' n : ℕ, sigma n := by
  have hseries : T = ∑' n : ℕ, sigma n • rankOne ℝ (c n) (b n) :=
    realOneFullSourceSingular_operator_tsum_eq T b c hc sigma hpos hs heig
  have hterm (n : ℕ) :
      ‖sigma n‖ * ‖c n‖ * ‖b n‖ = sigma n := by
    rw [hc.norm_eq_one n, b.orthonormal.norm_eq_one n,
      Real.norm_eq_abs, abs_of_nonneg (hpos n)]
    ring
  have hcost : Summable (fun n : ℕ =>
      ‖sigma n‖ * ‖c n‖ * ‖b n‖) :=
    hs.congr (fun n => (hterm n).symm)
  have hclass : HasRealNuclearRankOneSeries T :=
    ⟨c, b, sigma, hcost, hseries⟩
  have hmem : (∑' n : ℕ, sigma n) ∈ RealNuclearCosts T := by
    refine ⟨c, b, sigma, hcost, hseries, ?_⟩
    exact (tsum_congr hterm).symm
  have hupper : realNuclearInfimum T ≤ ∑' n : ℕ, sigma n :=
    realNuclearInfimum_le_cost T hmem
  have hlower (cost : ℝ) (hmemc : cost ∈ RealNuclearCosts T) :
      (∑' n : ℕ, sigma n) ≤ cost := by
    have hfinite (N : ℕ) :
        (∑ n ∈ Finset.range N, sigma n) ≤ cost := by
      have hh :=
        realTwoOrthonormalFiniteTrace_abs_le_nuclearCost
          b c b.orthonormal hc N T hmemc
      have hd (n : ℕ) : inner ℝ (c n) (T (b n)) = sigma n := by
        rw [heig n, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hc.norm_eq_one n]
        ring
      have hsum :
          (∑ n ∈ Finset.range N, inner ℝ (c n) (T (b n))) =
            ∑ n ∈ Finset.range N, sigma n :=
        Finset.sum_congr rfl (fun n _ => hd n)
      rw [hsum] at hh
      have hp : 0 ≤ ∑ n ∈ Finset.range N, sigma n :=
        Finset.sum_nonneg (fun n _ => hpos n)
      simpa only [abs_of_nonneg hp] using hh
    exact le_of_tendsto hs.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hfinite)
  have heq :
      realNuclearInfimum T = ∑' n : ℕ, sigma n :=
    le_antisymm hupper
      (le_csInf ⟨∑' n : ℕ, sigma n, hmem⟩ hlower)
  exact ⟨hclass, heq⟩

#print axioms GegenbauerFock.Ultraspherical.realOneFullSourceSingular_operator_tsum_eq
#print axioms GegenbauerFock.Ultraspherical.realOneFullSourceSingular_nuclear_exact_trace

end GegenbauerFock.Ultraspherical
