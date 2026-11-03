import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearNorm

/-!
# V007 — projective real nuclear S₁ norm dominates operator norm

For ANY real Hilbert nuclear rank-one series representing an ACTUAL
bounded operator, the series' projective cost bounds the operator norm.
The infimum of ALL admissible costs thus dominates the operator norm.

In particular, the infimum is nondegenerate on the class of REAL
nuclear operators, independently of positivity or selfadjointness.
The infimum is NOT proposed as a finite norm on arbitrary nonnuclear
operators, since the cost set can then be empty.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every admissible projective real nuclear representation of a
bounded operator has cost at least its actual operator norm. -/
theorem RealNuclearCosts.opNorm_le
    (T : H →L[ℝ] H) {c : ℝ}
    (hc : c ∈ RealNuclearCosts T) :
    ‖T‖ ≤ c := by
  obtain ⟨u, v, beta, hs, hseries, rfl⟩ := hc
  have hterm (n : ℕ) :
      ‖beta n • rankOne ℝ (u n) (v n)‖ =
        ‖beta n‖ * ‖u n‖ * ‖v n‖ := by
    rw [norm_smul, norm_rankOne]
    ring
  have hnorms :
      Summable (fun n : ℕ =>
        ‖beta n • rankOne ℝ (u n) (v n)‖) :=
    hs.congr (fun n => (hterm n).symm)
  calc
    ‖T‖ = ‖∑' n : ℕ, beta n • rankOne ℝ (u n) (v n)‖ := by
      rw [hseries]
    _ ≤ ∑' n : ℕ, ‖beta n • rankOne ℝ (u n) (v n)‖ :=
      norm_tsum_le_tsum_norm hnorms
    _ = ∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖ :=
      tsum_congr hterm

/-- For any genuinely NUCLEAR bounded real Hilbert operator,
its universal projective S₁ infimum dominates its operator norm. -/
theorem realNuclearInfimum_opNorm_le
    (T : H →L[ℝ] H)
    (hT : HasRealNuclearRankOneSeries T) :
    ‖T‖ ≤ realNuclearInfimum T := by
  obtain ⟨u, v, beta, hs, hseries⟩ := hT
  have hnonempty : (RealNuclearCosts T).Nonempty := by
    refine ⟨∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖, ?_⟩
    exact ⟨u, v, beta, hs, hseries, rfl⟩
  unfold realNuclearInfimum
  exact le_csInf hnonempty (fun c hc => RealNuclearCosts.opNorm_le T hc)

/-- General nondegeneracy: an actual NONZERO real nuclear operator
has strictly positive projective nuclear norm, without requiring a
selfadjoint, normal or positive spectral decomposition. -/
theorem realNuclearInfimum_pos_of_nuclear_ne_zero
    (T : H →L[ℝ] H)
    (hT : HasRealNuclearRankOneSeries T)
    (hneq : T ≠ 0) :
    0 < realNuclearInfimum T := by
  have hpos : 0 < ‖T‖ := norm_pos_iff.mpr hneq
  exact lt_of_lt_of_le hpos (realNuclearInfimum_opNorm_le T hT)

/-- Zero projective nuclear infimum forces any nuclear bounded
real Hilbert operator to be exactly the zero operator. -/
theorem realNuclearInfimum_zero_implies_operator_zero
    (T : H →L[ℝ] H)
    (hT : HasRealNuclearRankOneSeries T)
    (hzero : realNuclearInfimum T = 0) :
    T = 0 := by
  have h := realNuclearInfimum_opNorm_le T hT
  rw [hzero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg T))

#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.opNorm_le
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_opNorm_le
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_pos_of_nuclear_ne_zero
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_zero_implies_operator_zero

end GegenbauerFock.Ultraspherical
