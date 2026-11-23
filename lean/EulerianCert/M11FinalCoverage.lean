import EulerianCert.FourierSeries
import EulerianCert.Bracket

/-!
Manuscript 11, frozen author source 2026-11-23, Proposition 3.4 and Remark 3.16.
Proofs in this file concern original M11 statements, not classical Plancherel/Pythagoras
or numerical FLINT/Arb certifications.
-/

open Real Set
open EulerianCert.FourierModes
open EulerianCert.FourierSeries

noncomputable section

namespace EulerianCert.M11FinalCoverage

/-- Proposition 3.4: each summand of `S N θ - S N π` is nonnegative. -/
private lemma truncation_gap_sum (N : ℕ) (θ : ℝ) :
    S N θ - S N π =
      ∑ n ∈ Finset.range N,
        (cE n + (-1 : ℝ) ^ n * cE n * Real.cos ((n + 1 : ℝ) * θ)) := by
  let F : ℕ → ℝ → ℝ :=
    fun n x => A (n + 1) * Real.cos ((n + 1 : ℝ) * x)
  have hs (x : ℝ) :
      S N x = A 0 / 2 + ∑ n ∈ Finset.range N, F n x := rfl
  calc
    S N θ - S N π =
        ∑ n ∈ Finset.range N, (F n θ - F n π) := by
      rw [hs θ, hs π, Finset.sum_sub_distrib]
      abel
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [F]
      rw [A_succ_eq]
      rw [term_pi (c := cE) n]
      ring

/-- The missing equality clause of Proposition 3.4: for a nonconstant truncation,
`S_N(θ) = S_N(π)` on `[-π,π]` forces exactly one of the two endpoints. -/
theorem S_min_eq_only_endpoints (N : ℕ) (hN : 1 ≤ N) (θ : ℝ)
    (hθ : θ ∈ Icc (-π) π) (heq : S N θ = S N π) :
    θ = -π ∨ θ = π := by
  have hnonneg : ∀ n ∈ Finset.range N,
      0 ≤ cE n + (-1 : ℝ) ^ n * cE n * Real.cos ((n + 1 : ℝ) * θ) := by
    intro n hn
    linarith [term_ge cE_nonneg n θ]
  have hfirst := Finset.single_le_sum (f := fun n : ℕ =>
      cE n + (-1 : ℝ) ^ n * cE n * Real.cos ((n + 1 : ℝ) * θ))
      hnonneg (Finset.mem_range.mpr hN)
  have hsum : (∑ n ∈ Finset.range N,
      (cE n + (-1 : ℝ) ^ n * cE n * Real.cos ((n + 1 : ℝ) * θ))) = 0 := by
    rw [← truncation_gap_sum]
    linarith
  rw [hsum] at hfirst
  have hmul : cE 0 * (1 + Real.cos θ) ≤ 0 := by
    simpa [mul_add] using hfirst
  have hcosge : 0 ≤ 1 + Real.cos θ := by
    linarith [Real.neg_one_le_cos θ]
  have hzero : 1 + Real.cos θ = 0 := by
    by_contra hne
    have hgt : 0 < 1 + Real.cos θ := lt_of_le_of_ne hcosge (Ne.symm hne)
    have := mul_pos (cE_pos 0) hgt
    linarith
  have hcos : Real.cos θ = -1 := by linarith
  have hmem : |θ| ∈ Icc (0 : ℝ) π :=
    ⟨abs_nonneg _, (abs_le.mpr hθ)⟩
  have hpimem : (π : ℝ) ∈ Icc (0 : ℝ) π := ⟨le_of_lt Real.pi_pos, le_rfl⟩
  have hcosabs : Real.cos |θ| = Real.cos π := by
    simpa [Real.cos_abs, Real.cos_pi] using hcos
  have habs : |θ| = π := Real.injOn_cos hmem hpimem hcosabs
  rcases le_total 0 θ with hpos | hneg
  · right
    simpa [abs_of_nonneg hpos] using habs
  · left
    rw [abs_of_nonpos hneg] at habs
    linarith

/-- Proposition 3.4: the zeroth truncation is constant. -/
theorem S_zero_constant (θ : ℝ) : S 0 θ = S 0 π := by
  simp [S]

/-- The exact small-order equality asserted in Remark 3.16. -/
theorem c3_eq_c5 :
    Bracket.cn 3 1 = (1 : ℝ) / 2 ∧ Bracket.cn 5 2 = (1 : ℝ) / 2 := by
  have h31 : Bracket.E 3 1 = 4 := by decide +kernel
  have h30 : Bracket.E 3 0 = 1 := by decide +kernel
  have h52 : Bracket.E 5 2 = 66 := by decide +kernel
  have h51 : Bracket.E 5 1 = 26 := by decide +kernel
  constructor
  · norm_num [Bracket.cn, h31, h30]
  · norm_num [Bracket.cn, h52, h51]

end EulerianCert.M11FinalCoverage
