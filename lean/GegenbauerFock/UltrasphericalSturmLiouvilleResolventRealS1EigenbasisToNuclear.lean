import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealS1SpectralBridge

/-!
# V007 — universal real positive eigenbasis S₁ -> nuclear operator bridge

This file is NOT specific to Sturm/Gegenbauer. For any complete REAL
Hilbert space with a countable Hilbert eigenbasis, a bounded operator
with nonnegative summable eigenvalues is proven to be an actual
operator-norm summable positive rank-one nuclear series.

The final theorem computes the projective nuclear norm by a
basis-independent universal infimum. This is a general equivalence for
POSITIVE DIAGONALIZABLE REAL trace-class operators only; it is not a
claim for arbitrary nonselfadjoint operators or an independent CFC abs
implementation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace MeasureTheory Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- If T is diagonal on a complete real Hilbert basis and its
nonnegative eigenvalues are summable, the ACTUAL T is the
operator-norm sum of those rank-one orthogonal projections.
No abstract polar/CFC decomposition is assumed. -/
theorem realPositiveEigenSummable_operator_tsum_eq
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    (hs : Summable σ)
    (heig : ∀ n, T (b n) = σ n • b n) :
    T = ∑' n : ℕ, σ n • rankOne ℝ (b n) (b n) := by
  have hsOp : Summable (fun n : ℕ =>
      σ n • rankOne ℝ (b n) (b n)) := by
    apply Summable.of_norm
    have hn (n : ℕ) :
        ‖σ n • rankOne ℝ (b n) (b n)‖ = σ n := by
      rw [norm_smul, norm_rankOne, b.orthonormal.norm_eq_one n]
      simp only [one_mul, mul_one, Real.norm_eq_abs, abs_of_nonneg (hσ n)]
    exact hs.congr (fun n => (hn n).symm)
  apply ContinuousLinearMap.ext
  intro x
  have hTsum :
      HasSum (fun n : ℕ =>
        (inner ℝ (b n) x) • (σ n • b n)) (T x) := by
    have hrec := (b.hasSum_repr x).mapL T
    convert hrec using 1
    funext n
    simp only [HilbertBasis.repr_apply_apply, map_smul, heig]
  have hEval :
      (∑' n : ℕ, σ n • rankOne ℝ (b n) (b n)) x =
        ∑' n : ℕ, (σ n • rankOne ℝ (b n) (b n)) x :=
    (ContinuousLinearMap.apply ℝ H x).map_tsum hsOp
  calc
    T x = ∑' n : ℕ, (inner ℝ (b n) x) • (σ n • b n) :=
      hTsum.tsum_eq.symm
    _ = ∑' n : ℕ, (σ n • rankOne ℝ (b n) (b n)) x := by
      apply tsum_congr
      intro n
      change (inner ℝ (b n) x) • (σ n • b n) =
        σ n • ((inner ℝ (b n) x) • b n)
      exact smul_comm (inner ℝ (b n) x) (σ n) (b n)
    _ = (∑' n : ℕ, σ n • rankOne ℝ (b n) (b n)) x :=
      hEval.symm

/-- General positive real spectral S₁ criterion implies a genuine
operator-norm-convergent positive nuclear rank-one witness. -/
theorem HasRealPositiveS1Eigenbasis.toPositiveRealNuclearExpansion
    {T : H →L[ℝ] H}
    (hT : HasRealPositiveS1Eigenbasis T) :
    HasRealPositiveNuclearExpansion T := by
  obtain ⟨b, σ, hσ, hs, heig⟩ := hT
  exact ⟨b, σ, b.orthonormal, hσ, hs,
    realPositiveEigenSummable_operator_tsum_eq T b σ hσ hs heig⟩

/-- For ANY complete real Hilbert space admitting a positive
summable eigenbasis, the universal projective nuclear infimum is
exactly the positive eigenvalue sum. This is not merely the mass
of one spectral witness. -/
theorem HasRealPositiveS1Eigenbasis.exists_projective_norm_eq_eigenSum
    {T : H →L[ℝ] H}
    (hT : HasRealPositiveS1Eigenbasis T) :
    ∃ (b : HilbertBasis ℕ ℝ H) (σ : ℕ → ℝ),
      (∀ n, 0 ≤ σ n) ∧ Summable σ ∧
      (∀ n, T (b n) = σ n • b n) ∧
      realNuclearInfimum T = ∑' n : ℕ, σ n := by
  obtain ⟨b, σ, hσ, hs, heig⟩ := hT
  have hseries :
      T = ∑' n : ℕ, σ n • rankOne ℝ (b n) (b n) :=
    realPositiveEigenSummable_operator_tsum_eq T b σ hσ hs heig
  have hterm (n : ℕ) :
      ‖σ n‖ * ‖b n‖ * ‖b n‖ = σ n := by
    rw [b.orthonormal.norm_eq_one n, Real.norm_eq_abs,
      abs_of_nonneg (hσ n)]
    ring
  have hcost : Summable (fun n : ℕ =>
      ‖σ n‖ * ‖b n‖ * ‖b n‖) :=
    hs.congr (fun n => (hterm n).symm)
  have hmem : (∑' n : ℕ, σ n) ∈ RealNuclearCosts T := by
    refine ⟨b, b, σ, hcost, hseries, ?_⟩
    exact (tsum_congr hterm).symm
  have hupper : realNuclearInfimum T ≤ ∑' n : ℕ, σ n :=
    realNuclearInfimum_le_cost T hmem
  have hlower (c : ℝ) (hc : c ∈ RealNuclearCosts T) :
      (∑' n : ℕ, σ n) ≤ c := by
    have hfinite (N : ℕ) : (∑ n ∈ Finset.range N, σ n) ≤ c := by
      have hh := realHilbertFiniteTrace_abs_le_nuclearCost b N T hc
      have hd (n : ℕ) : inner ℝ (b n) (T (b n)) = σ n := by
        rw [heig n, real_inner_smul_right,
          real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one n]
        ring
      have hsum :
          (∑ n ∈ Finset.range N, inner ℝ (b n) (T (b n))) =
          ∑ n ∈ Finset.range N, σ n :=
        Finset.sum_congr rfl (fun n _ => hd n)
      rw [hsum] at hh
      have hp : 0 ≤ ∑ n ∈ Finset.range N, σ n :=
        Finset.sum_nonneg (fun n _ => hσ n)
      simpa only [abs_of_nonneg hp] using hh
    exact le_of_tendsto hs.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hfinite)
  have hnonempty : (RealNuclearCosts T).Nonempty :=
    ⟨∑' n : ℕ, σ n, hmem⟩
  have hEq : realNuclearInfimum T = ∑' n : ℕ, σ n :=
    le_antisymm hupper (le_csInf hnonempty hlower)
  exact ⟨b, σ, hσ, hs, heig, hEq⟩

#print axioms GegenbauerFock.Ultraspherical.realPositiveEigenSummable_operator_tsum_eq
#print axioms GegenbauerFock.Ultraspherical.HasRealPositiveS1Eigenbasis.toPositiveRealNuclearExpansion
#print axioms GegenbauerFock.Ultraspherical.HasRealPositiveS1Eigenbasis.exists_projective_norm_eq_eigenSum

end GegenbauerFock.Ultraspherical
