import V033AllDegreeTheorem

/-! # Manuscript 12, Corollary 5.2 (Jacobi normalisation)

For every fixed degree `n = j+1 ≥ 1` the off-diagonal Jacobi entries of the variance-one law
of `Y_M`, `a_n^{[M]} = √(12 β_n^{[M]}/M)`, satisfy
`a_n^{[M]} = √n [1 - 3(n-1)/(10M) + O_n(M^{-2})]`.
Proved from the certified Theorem 5.1 (`canonical_two_term`), for the canonical Hankel
quotient `β_n^{[M]}`, and hence for every monic Lanczos family. -/

noncomputable section
namespace V033.UniformSum
open Polynomial Finset

/-- `|√u - t| ≤ |u - t²|/t` for `u ≥ 0`, `t > 0`. -/
theorem abs_sqrt_sub_le (u t : ℝ) (hu : 0 ≤ u) (ht : 0 < t) :
    |Real.sqrt u - t| ≤ |u - t^2| / t := by
  have hs : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hpos : 0 < Real.sqrt u + t := by linarith
  have hprod : (Real.sqrt u - t) * (Real.sqrt u + t) = u - t^2 := by
    have := Real.sq_sqrt hu
    nlinarith [this]
  rw [le_div_iff₀ ht]
  calc |Real.sqrt u - t| * t ≤ |Real.sqrt u - t| * (Real.sqrt u + t) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |u - t^2| := by rw [← hprod, abs_mul, abs_of_pos hpos]

set_option maxHeartbeats 2000000 in
/-- **Corollary 5.2.** -/
theorem jacobi_normalisation (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
      (Gram.hankel (rawFunctional M) (j+1)).det ≠ 0 ∧
      |Real.sqrt (12 / (M:ℝ) * canonicalCoefficient M j) -
          Real.sqrt (j+1) * (1 - 3 * (j:ℝ) / (10 * M))| ≤ C / (M:ℝ)^2 := by
  obtain ⟨C, hC, N, hN0, hN⟩ := canonical_two_term j
  set n : ℝ := (j:ℝ) + 1 with hn
  have hn1 : 1 ≤ n := by rw [hn]; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hn0 : (0:ℝ) ≤ n := by linarith
  -- K bounds |u - t²| M²
  set K : ℝ := 12 * C + n * (j:ℝ)^2 with hK
  have hK0 : 0 < K := by
    rw [hK]; have : 0 ≤ n * (j:ℝ)^2 := by positivity
    linarith
  obtain ⟨N2, hN2⟩ := exists_nat_gt (4 * K)
  refine ⟨2 * K, by linarith, max (max N N2) (j+1), by omega, ?_⟩
  intro M hM
  have hMN : N ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hM)
  have hMN2 : N2 ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hM)
  have hMj : j + 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hd, hb⟩ := hN M hMN
  refine ⟨hd, ?_⟩
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMj' : (j:ℝ) + 1 ≤ M := by exact_mod_cast hMj
  have hMK : 4 * K < M := lt_of_lt_of_le hN2 (by exact_mod_cast hMN2)
  set β := canonicalCoefficient M j
  set u := 12 / (M:ℝ) * β with hu
  set t := Real.sqrt n * (1 - 3 * (j:ℝ) / (10 * M)) with ht
  have hsn : 1 ≤ Real.sqrt n := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn1
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  have hfrac : 3 * (j:ℝ) / (10 * M) ≤ 3/10 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hfrac0 : 0 ≤ 3 * (j:ℝ) / (10 * M) := by positivity
  have ht7 : 7/10 ≤ t := by
    rw [ht]; nlinarith
  -- |u - t²| ≤ K/M²
  have hut : |u - t^2| ≤ K / (M:ℝ)^2 := by
    have e1 : u - t^2 = 12 / (M:ℝ) * (β - (n * M / 12 - n * j / 20)) -
        n * (9 * (j:ℝ)^2 / (100 * (M:ℝ)^2)) := by
      rw [hu, ht, mul_pow, hsq]
      field_simp
      ring
    rw [e1]
    have hb' : |β - (n * M / 12 - n * j / 20)| ≤ C / M := by
      have : n * M / 12 - n * j / 20 = ((j+1:ℝ) * M / 12 - (j+1:ℝ) * j / 20) := by rw [hn]
      rw [this]; exact hb
    calc |12 / (M:ℝ) * (β - (n * M / 12 - n * j / 20)) - n * (9 * (j:ℝ)^2 / (100 * (M:ℝ)^2))|
        ≤ |12 / (M:ℝ) * (β - (n * M / 12 - n * j / 20))| +
            |n * (9 * (j:ℝ)^2 / (100 * (M:ℝ)^2))| := abs_sub _ _
      _ = 12 / (M:ℝ) * |β - (n * M / 12 - n * j / 20)| +
            n * (9 * (j:ℝ)^2 / (100 * (M:ℝ)^2)) := by
          rw [abs_mul, abs_of_pos (div_pos (by norm_num) hMpos),
            abs_of_nonneg (mul_nonneg hn0 (by positivity))]
      _ ≤ 12 / (M:ℝ) * (C / M) + n * (9 * (j:ℝ)^2 / (100 * (M:ℝ)^2)) := by
          gcongr
      _ ≤ K / (M:ℝ)^2 := by
          rw [hK, show 12 / (M:ℝ) * (C / M) + n * (9 * (j:ℝ)^2 / (100 * (M:ℝ)^2)) =
              (12 * C + n * (9 * (j:ℝ)^2 / 100)) / (M:ℝ)^2 by field_simp]
          exact div_le_div_of_nonneg_right
            (by nlinarith [sq_nonneg (j:ℝ), mul_nonneg hn0 (sq_nonneg (j:ℝ))]) (by positivity)
  -- u ≥ 0 for M large
  have hM1 : (1:ℝ) ≤ M := by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hKM : K / (M:ℝ)^2 ≤ 1/4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hMK, hM1]
  have hu0 : 0 ≤ u := by
    have h1 := (abs_le.mp (le_trans hut hKM)).1
    have h7 := mul_le_mul ht7 ht7 (by norm_num) (by linarith)
    have ht2 : (49/100:ℝ) ≤ t^2 := by rw [sq]; linarith
    linarith
  calc |Real.sqrt u - t| ≤ |u - t^2| / t := abs_sqrt_sub_le u t hu0 (by linarith)
    _ ≤ (K / (M:ℝ)^2) / (7/10) := by
        apply div_le_div₀ (by positivity) hut (by norm_num) ht7
    _ = (10/7) * (K / (M:ℝ)^2) := by ring
    _ ≤ 2 * K / (M:ℝ)^2 := by
        have hKM0 : 0 ≤ K / (M:ℝ)^2 := div_nonneg hK0.le (by positivity)
        rw [mul_div_assoc]
        linarith

/-- Corollary 5.2 for every monic Lanczos family of the moment functional of `S_M`. -/
theorem jacobi_normalisation_lanczos
    (P : ℕ → ℕ → ℝ[X]) (β : ℕ → ℕ → ℝ)
    (h : ∀ M : ℕ, 0 < M → Gram.IsLanczosFamily (rawFunctional M) (P M) (β M)) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
      |Real.sqrt (12 / (M:ℝ) * β M (j+1)) -
          Real.sqrt (j+1) * (1 - 3 * (j:ℝ) / (10 * M))| ≤ C / (M:ℝ)^2 := by
  obtain ⟨C, hC, N, hN0, hN⟩ := jacobi_normalisation j
  refine ⟨C, hC, N, hN0, ?_⟩
  intro M hM
  obtain ⟨hd, hb⟩ := hN M hM
  have hm : 0 < M := lt_of_lt_of_le hN0 hM
  rw [(h M hm).coefficient_as_determinants j hd]
  exact hb

end V033.UniformSum
