import GegenbauerFock.RealCompactGramPositiveSingularBasisBridge
import GegenbauerFock.RealNuclearGramPositiveSupportS1

/-!
# V007 — complete source Gram basis including zero modes

Given a full orthonormal eigenbasis of the REAL Gram T†T with
nonnegative eigenvalues, summability of their square roots gives
an operator-norm convergent rank-one expansion of T itself, and
a genuine nuclear representation. Zero eigenvalues are allowed,
and no complete target basis, global unitary or defect equality
is required.

This is a conditional theorem: the arbitrary-compact Gram spectral
basis and general equivalence with singular S1 remain separate goals.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem realGram_fullBasis_image_norm_eq_sqrt_v007
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 ≤ mu n)
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n)
    (n : ℕ) :
    ‖T (b n)‖ = Real.sqrt (mu n) := by
  have hsq := realGram_eigenvector_norm_sq_v007
    T (mu n) (b n) (heig n)
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa [b.orthonormal.norm_eq_one n, Real.sq_sqrt (hmu n)]
    using hsq

/-- Rank-one series converges in operator norm even when T has kernel. -/
theorem realGram_fullBasis_rankOne_summable_v007
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 ≤ mu n)
    (hs : Summable (fun n => Real.sqrt (mu n)))
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n) :
    Summable (fun n : ℕ => rankOne ℝ (T (b n)) (b n)) := by
  apply Summable.of_norm
  have hn (n : ℕ) :
      ‖rankOne ℝ (T (b n)) (b n)‖ = Real.sqrt (mu n) := by
    rw [norm_rankOne, b.orthonormal.norm_eq_one n, mul_one]
    exact realGram_fullBasis_image_norm_eq_sqrt_v007
      T b mu hmu heig n
  exact hs.congr (fun n => (hn n).symm)

/-- Actual operator reconstruction from a full source Gram basis. -/
theorem realGram_fullBasis_operator_tsum_eq_v007
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 ≤ mu n)
    (hs : Summable (fun n => Real.sqrt (mu n)))
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n) :
    T = ∑' n : ℕ, rankOne ℝ (T (b n)) (b n) := by
  have hsOp : Summable (fun n : ℕ => rankOne ℝ (T (b n)) (b n)) :=
    realGram_fullBasis_rankOne_summable_v007 T b mu hmu hs heig
  apply ContinuousLinearMap.ext
  intro x
  have hTsum :
      HasSum (fun n : ℕ =>
        (inner ℝ (b n) x) • T (b n)) (T x) := by
    have hrec := (b.hasSum_repr x).mapL T
    convert hrec using 1
    funext n
    simp only [HilbertBasis.repr_apply_apply, map_smul]
  have hEval :
      (∑' n : ℕ, rankOne ℝ (T (b n)) (b n)) x =
        ∑' n : ℕ, (rankOne ℝ (T (b n)) (b n)) x :=
    (ContinuousLinearMap.apply ℝ H x).map_tsum hsOp
  calc
    T x = ∑' n : ℕ, (inner ℝ (b n) x) • T (b n) :=
      hTsum.tsum_eq.symm
    _ = ∑' n : ℕ, (rankOne ℝ (T (b n)) (b n)) x := by
      apply tsum_congr
      intro n
      rfl
    _ = (∑' n : ℕ, rankOne ℝ (T (b n)) (b n)) x :=
      hEval.symm

/-- The exact real operator is nuclear; its universal projective
rank-one cost is at most the sum of the singular amplitudes.
The reverse lower bound remains a separate support-duality step. -/
theorem realGram_fullBasis_nuclear_upper_v007
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (mu : ℕ → ℝ) (hmu : ∀ n, 0 ≤ mu n)
    (hs : Summable (fun n => Real.sqrt (mu n)))
    (heig : ∀ n, (T.adjoint ∘L T) (b n) = mu n • b n) :
    HasRealNuclearRankOneSeries T ∧
      realNuclearInfimum T ≤ ∑' n : ℕ, Real.sqrt (mu n) := by
  let u : ℕ → H := fun n => T (b n)
  let v : ℕ → H := fun n => b n
  let beta : ℕ → ℝ := fun _ => 1
  have hnorm (n : ℕ) : ‖u n‖ = Real.sqrt (mu n) :=
    realGram_fullBasis_image_norm_eq_sqrt_v007 T b mu hmu heig n
  have hterm (n : ℕ) :
      ‖beta n‖ * ‖u n‖ * ‖v n‖ = Real.sqrt (mu n) := by
    simp only [beta, u, v, Real.norm_eq_abs, abs_one,
      one_mul, b.orthonormal.norm_eq_one n, mul_one]
    exact hnorm n
  have hcost : Summable (fun n : ℕ =>
      ‖beta n‖ * ‖u n‖ * ‖v n‖) :=
    hs.congr (fun n => (hterm n).symm)
  have hseries :
      T = ∑' n : ℕ, beta n • rankOne ℝ (u n) (v n) := by
    simpa only [beta, u, v, one_smul] using
      realGram_fullBasis_operator_tsum_eq_v007 T b mu hmu hs heig
  have hN : HasRealNuclearRankOneSeries T :=
    ⟨u, v, beta, hcost, hseries⟩
  have hMass :
      (∑' n : ℕ, Real.sqrt (mu n)) ∈ RealNuclearCosts T := by
    refine ⟨u, v, beta, hcost, hseries, ?_⟩
    exact (tsum_congr hterm).symm
  exact ⟨hN, realNuclearInfimum_le_cost T hMass⟩

#print axioms GegenbauerFock.Ultraspherical.realGram_fullBasis_image_norm_eq_sqrt_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_fullBasis_rankOne_summable_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_fullBasis_operator_tsum_eq_v007
#print axioms GegenbauerFock.Ultraspherical.realGram_fullBasis_nuclear_upper_v007

end GegenbauerFock.Ultraspherical
