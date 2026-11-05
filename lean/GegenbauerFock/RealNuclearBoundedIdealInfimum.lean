import GegenbauerFock.RealNuclearBoundedRightIdeal

/-!
# V007 — exact coefficient-one bounded two-sided nuclear ideal norm bound

The real nuclear projective norm is the infimum of ALL admissible
rank-one representation costs. A prior kernel-checked theorem transfers
every such cost under arbitrary bounded two-sided multiplication.
This module upgrades that cost-by-cost estimate to the actual
universal projective nuclear norm for every nuclear T:

  nuclearInfimum(A ∘ T ∘ B)
    ≤ ‖A‖ ‖B‖ nuclearInfimum(T).

This handles zero and strictly positive multiplier norms separately;
no positivity, normality or unitary polar decomposition is required.
The infimum is used only for genuinely nuclear T, so the empty-cost
case does not silently give a spurious trace norm.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The universal REAL nuclear projective trace norm obeys the sharp
two-sided ideal inequality under arbitrary bounded operators. -/
theorem realNuclearInfimum_bounded_two_sided_le
    (A B T : H →L[ℝ] H)
    (hT : HasRealNuclearRankOneSeries T) :
    realNuclearInfimum
      (realNuclearBoundedLeftCLM A
        (realNuclearBoundedRightCLM B T)) ≤
      (‖A‖ * ‖B‖) * realNuclearInfimum T := by
  let target :=
    realNuclearBoundedLeftCLM A (realNuclearBoundedRightCLM B T)
  let k : ℝ := ‖A‖ * ‖B‖
  have hk0 : 0 ≤ k := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨u, v, beta, hs, hseries⟩ := hT
  have hnonempty : (RealNuclearCosts T).Nonempty :=
    ⟨∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖,
      ⟨u, v, beta, hs, hseries, rfl⟩⟩
  change realNuclearInfimum target ≤ k * realNuclearInfimum T
  by_cases hk : 0 < k
  · have hdiv :
        realNuclearInfimum target / k ≤ realNuclearInfimum T := by
      change realNuclearInfimum target / k ≤ sInf (RealNuclearCosts T)
      apply le_csInf hnonempty
      intro c hc
      obtain ⟨c', hc', hbound⟩ :=
        RealNuclearCosts.bounded_two_sided A B T hc
      have hle : realNuclearInfimum target ≤ c' :=
        realNuclearInfimum_le_cost target hc'
      have hbound' : realNuclearInfimum target ≤ c * k := by
        calc
          realNuclearInfimum target ≤ c' := hle
          _ ≤ (‖A‖ * ‖B‖) * c := hbound
          _ = c * k := by dsimp [k]; ring
      exact (div_le_iff₀ hk).mpr hbound'
    calc
      realNuclearInfimum target ≤ realNuclearInfimum T * k :=
        (div_le_iff₀ hk).mp hdiv
      _ = k * realNuclearInfimum T := mul_comm _ _
  · have hkzero : k = 0 :=
      le_antisymm (le_of_not_gt hk) hk0
    obtain ⟨c, hc⟩ := hnonempty
    obtain ⟨c', hc', hbound⟩ :=
      RealNuclearCosts.bounded_two_sided A B T hc
    have hle : realNuclearInfimum target ≤ c' :=
      realNuclearInfimum_le_cost target hc'
    calc
      realNuclearInfimum target ≤ c' := hle
      _ ≤ k * c := hbound
      _ = k * realNuclearInfimum T := by simp [hkzero]

#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_bounded_two_sided_le

end GegenbauerFock.Ultraspherical
