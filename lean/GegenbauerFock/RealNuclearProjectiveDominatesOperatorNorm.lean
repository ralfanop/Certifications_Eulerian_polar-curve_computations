import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearNorm

/-!
# V007 — general real projective nuclear norm dominates operator norm

This proof is about EVERY real-Hilbert nuclear operator, not only
positive, self-adjoint, or diagonalizable operators. Each admissible
rank-one series has projective cost at least its operator norm.
Taking the universal infimum gives the sharp contractive inclusion
of the real projective nuclear class into bounded Hilbert operators.

A nuclear witness is explicitly required: `sInf ∅` is not used to
define a norm on all bounded nonnuclear operators.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every admissible nuclear representation cost dominates the true
bounded-operator norm of T, even for nonnormal real-Hilbert T. -/
theorem RealNuclearCosts.opNorm_le
    (T : H →L[ℝ] H) {c : ℝ}
    (hc : c ∈ RealNuclearCosts T) :
    ‖T‖ ≤ c := by
  rcases hc with ⟨u, v, β, hs, hT, rfl⟩
  have hOp : Summable (fun n : ℕ =>
      β n • rankOne ℝ (u n) (v n)) := by
    apply Summable.of_norm
    convert hs using 1
    funext n
    rw [norm_smul, norm_rankOne]
    ring
  have hNormOp : Summable (fun n : ℕ =>
      ‖β n • rankOne ℝ (u n) (v n)‖) := by
    convert hs using 1
    funext n
    rw [norm_smul, norm_rankOne]
    ring
  rw [hT]
  calc
    ‖∑' n : ℕ, β n • rankOne ℝ (u n) (v n)‖ ≤
        ∑' n : ℕ, ‖β n • rankOne ℝ (u n) (v n)‖ :=
      norm_tsum_le_tsum_norm hNormOp
    _ = ∑' n : ℕ, ‖β n‖ * ‖u n‖ * ‖v n‖ := by
      apply tsum_congr
      intro n
      rw [norm_smul, norm_rankOne]
      ring

/-- The projective infimum is nonnegative on every genuinely nuclear
real bounded operator. -/
theorem realNuclearInfimum_nonneg_of_witness
    (T : H →L[ℝ] H) (hT : HasRealNuclearRankOneSeries T) :
    0 ≤ realNuclearInfimum T := by
  obtain ⟨u, v, β, hs, hsum⟩ := hT
  unfold realNuclearInfimum
  apply le_csInf
    (⟨∑' n : ℕ, ‖β n‖ * ‖u n‖ * ‖v n‖,
      ⟨u, v, β, hs, hsum, rfl⟩⟩ :
      (RealNuclearCosts T).Nonempty)
  intro c hc
  exact RealNuclearCosts.nonneg T hc

/-- Sharp norm comparison for ALL real nuclear Hilbert operators:
operator norm is bounded by the universal nuclear projective infimum. -/
theorem realNuclearInfimum_opNorm_le_of_witness
    (T : H →L[ℝ] H) (hT : HasRealNuclearRankOneSeries T) :
    ‖T‖ ≤ realNuclearInfimum T := by
  obtain ⟨u, v, β, hs, hsum⟩ := hT
  unfold realNuclearInfimum
  apply le_csInf
    (⟨∑' n : ℕ, ‖β n‖ * ‖u n‖ * ‖v n‖,
      ⟨u, v, β, hs, hsum, rfl⟩⟩ :
      (RealNuclearCosts T).Nonempty)
  intro c hc
  exact RealNuclearCosts.opNorm_le T hc

#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.opNorm_le
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_nonneg_of_witness
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_opNorm_le_of_witness

end GegenbauerFock.Ultraspherical
