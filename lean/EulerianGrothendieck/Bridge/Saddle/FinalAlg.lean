import Bridge.Saddle.Deriv

/-!
# Lemma 5.5, part 15: the algebra that turns the expansions of `I_r` into the `C²` bound

Abstract statement (`final_bounds`): if `Y_r = N_r + O(ε⁵)` with
`N₀ = 1 + ε²η + ε⁴p`, `N₁ = εg₁₁ + ε³g₁₃`, `N₂ = g₂₀ + ε²g₂₂ + ε⁴g₂₄`, bounded coefficients and the
cancellation identities of `Coeffs`, then
* `Y₀ - 1 - ε²η = O(ε⁴)`;
* `-ε⁻¹Y₁/Y₀ + L1 - ε²η' = O(ε³)`;
* `ε⁻²(Y₂/Y₀ - (Y₁/Y₀)² - g₂₀) + L2 - ε²η'' = O(ε³)`,
with explicit constants.
-/

open Complex

namespace EulerianBridge.Saddle

theorem nmul {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

theorem npow {e : ℝ} (he : 0 ≤ e) (k : ℕ) : ‖(e:ℂ) ^ k‖ = e ^ k := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]

/-- The exact remainder `R` with `F_N + ε²(L2 - ε²η'')N₀² = ε⁶ R`. -/
def Rrem (E η p g13 g20 g22 g24 L2 η2 : ℂ) : ℂ :=
  ((g24 * η + g22 * p - g13 ^ 2 - 2 * g20 * η * p) + L2 * (η ^ 2 + 2 * p) - 2 * η2 * η) +
    E ^ 2 * ((g24 * p - g20 * p ^ 2) + 2 * L2 * η * p - η2 * (η ^ 2 + 2 * p)) +
    E ^ 4 * (L2 * p ^ 2 - 2 * η2 * η * p) - E ^ 6 * (η2 * p ^ 2)

theorem exact_identity (E η p g11 g13 g20 g22 g24 L2 η2 : ℂ)
    (i22 : g22 - g20 * η - g11 ^ 2 + L2 = 0)
    (i24 : g24 + g22 * η - g20 * p - 2 * g11 * g13 - g20 * η ^ 2 + 2 * L2 * η - η2 = 0) :
    ((g20 + E ^ 2 * g22 + E ^ 4 * g24) * (1 + E ^ 2 * η + E ^ 4 * p) - (E * g11 + E ^ 3 * g13) ^ 2 -
      g20 * (1 + E ^ 2 * η + E ^ 4 * p) ^ 2) + E ^ 2 * (L2 - E ^ 2 * η2) * (1 + E ^ 2 * η + E ^ 4 * p) ^ 2 =
      E ^ 6 * Rrem E η p g13 g20 g22 g24 L2 η2 := by
  unfold Rrem
  linear_combination E ^ 2 * i22 + E ^ 4 * i24

theorem norm_Rrem_le {e K : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK : 1 ≤ K)
    {η p g13 g20 g22 g24 L2 η2 : ℂ} (hη : ‖η‖ ≤ K) (hp : ‖p‖ ≤ K) (h13 : ‖g13‖ ≤ K)
    (h20 : ‖g20‖ ≤ K) (h22 : ‖g22‖ ≤ K) (h24 : ‖g24‖ ≤ K) (hL2 : ‖L2‖ ≤ K) (hη2 : ‖η2‖ ≤ K) :
    ‖Rrem (e:ℂ) η p g13 g20 g22 g24 L2 η2‖ ≤ 21 * K ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have k2 : K ^ 2 ≤ K ^ 3 := by nlinarith
  have hE2 : ‖(e:ℂ) ^ 2‖ ≤ 1 := by rw [npow he0]; exact pow_le_one₀ he0 he1
  have hE4 : ‖(e:ℂ) ^ 4‖ ≤ 1 := by rw [npow he0]; exact pow_le_one₀ he0 he1
  have hE6 : ‖(e:ℂ) ^ 6‖ ≤ 1 := by rw [npow he0]; exact pow_le_one₀ he0 he1
  have n2 : ‖(2:ℂ)‖ = 2 := by norm_num
  -- the pieces
  have a1 : ‖g24 * η + g22 * p - g13 ^ 2 - 2 * g20 * η * p‖ ≤ 5 * K ^ 3 := by
    have t1 := nmul h24 hη
    have t2 := nmul h22 hp
    have t3 : ‖g13 ^ 2‖ ≤ K * K := by rw [sq]; exact nmul h13 h13
    have t4 : ‖2 * g20 * η * p‖ ≤ 2 * K * K * K := nmul (nmul (nmul (le_of_eq n2) h20) hη) hp
    have := norm_sub_le (g24 * η + g22 * p - g13 ^ 2) (2 * g20 * η * p)
    have := norm_sub_le (g24 * η + g22 * p) (g13 ^ 2)
    have := norm_add_le (g24 * η) (g22 * p)
    nlinarith
  have a2 : ‖L2 * (η ^ 2 + 2 * p)‖ ≤ 3 * K ^ 3 := by
    have : ‖η ^ 2 + 2 * p‖ ≤ K * K + 2 * K := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [sq]; exact nmul hη hη
      · exact nmul (le_of_eq n2) hp
    have := nmul hL2 this
    nlinarith
  have a3 : ‖2 * η2 * η‖ ≤ 2 * K ^ 3 := by
    have := nmul (nmul (le_of_eq n2) hη2) hη
    nlinarith
  have b1 : ‖(g24 * p - g20 * p ^ 2) + 2 * L2 * η * p - η2 * (η ^ 2 + 2 * p)‖ ≤ 7 * K ^ 3 := by
    have t1 := nmul h24 hp
    have t2 : ‖g20 * p ^ 2‖ ≤ K * (K * K) := nmul h20 (by rw [sq]; exact nmul hp hp)
    have t3 : ‖2 * L2 * η * p‖ ≤ 2 * K * K * K := nmul (nmul (nmul (le_of_eq n2) hL2) hη) hp
    have t4 : ‖η2 * (η ^ 2 + 2 * p)‖ ≤ K * (K * K + 2 * K) := by
      refine nmul hη2 ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      · rw [sq]; exact nmul hη hη
      · exact nmul (le_of_eq n2) hp
    have := norm_sub_le ((g24 * p - g20 * p ^ 2) + 2 * L2 * η * p) (η2 * (η ^ 2 + 2 * p))
    have := norm_add_le (g24 * p - g20 * p ^ 2) (2 * L2 * η * p)
    have := norm_sub_le (g24 * p) (g20 * p ^ 2)
    nlinarith
  have c1 : ‖L2 * p ^ 2 - 2 * η2 * η * p‖ ≤ 3 * K ^ 3 := by
    have t1 : ‖L2 * p ^ 2‖ ≤ K * (K * K) := nmul hL2 (by rw [sq]; exact nmul hp hp)
    have t2 : ‖2 * η2 * η * p‖ ≤ 2 * K * K * K := nmul (nmul (nmul (le_of_eq n2) hη2) hη) hp
    have := norm_sub_le (L2 * p ^ 2) (2 * η2 * η * p)
    nlinarith
  have d1 : ‖η2 * p ^ 2‖ ≤ K ^ 3 := by
    have := nmul hη2 (show ‖p ^ 2‖ ≤ K * K by rw [sq]; exact nmul hp hp)
    nlinarith
  unfold Rrem
  have e1 := nmul hE2 b1
  have e2 := nmul hE4 c1
  have e3 := nmul hE6 d1
  have s1 := norm_add_le ((g24 * η + g22 * p - g13 ^ 2 - 2 * g20 * η * p) + L2 * (η ^ 2 + 2 * p))
    (-(2 * η2 * η))
  have s0 := norm_add_le (g24 * η + g22 * p - g13 ^ 2 - 2 * g20 * η * p) (L2 * (η ^ 2 + 2 * p))
  rw [norm_neg] at s1
  rw [← sub_eq_add_neg] at s1
  have z1 := norm_sub_le (((g24 * η + g22 * p - g13 ^ 2 - 2 * g20 * η * p) + L2 * (η ^ 2 + 2 * p) -
      2 * η2 * η) + (e:ℂ) ^ 2 * ((g24 * p - g20 * p ^ 2) + 2 * L2 * η * p - η2 * (η ^ 2 + 2 * p)) +
      (e:ℂ) ^ 4 * (L2 * p ^ 2 - 2 * η2 * η * p)) ((e:ℂ) ^ 6 * (η2 * p ^ 2))
  have z2 := norm_add_le (((g24 * η + g22 * p - g13 ^ 2 - 2 * g20 * η * p) + L2 * (η ^ 2 + 2 * p) -
      2 * η2 * η) + (e:ℂ) ^ 2 * ((g24 * p - g20 * p ^ 2) + 2 * L2 * η * p - η2 * (η ^ 2 + 2 * p)))
      ((e:ℂ) ^ 4 * (L2 * p ^ 2 - 2 * η2 * η * p))
  have z3 := norm_add_le ((g24 * η + g22 * p - g13 ^ 2 - 2 * g20 * η * p) + L2 * (η ^ 2 + 2 * p) -
      2 * η2 * η) ((e:ℂ) ^ 2 * ((g24 * p - g20 * p ^ 2) + 2 * L2 * η * p - η2 * (η ^ 2 + 2 * p)))
  linarith

/-- Common setting of the three final estimates. -/
structure FinalData (e K Cρ : ℝ) (Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2 : ℂ) : Prop where
  he0 : 0 < e
  he1 : e ≤ 1
  hK : 1 ≤ K
  hC : 0 ≤ Cρ
  hη : ‖η‖ ≤ K
  hp : ‖p‖ ≤ K
  h11 : ‖g11‖ ≤ K
  h13 : ‖g13‖ ≤ K
  h20 : ‖g20‖ ≤ K
  h22 : ‖g22‖ ≤ K
  h24 : ‖g24‖ ≤ K
  hL2 : ‖L2‖ ≤ K
  hη1 : ‖η1‖ ≤ K
  hη2 : ‖η2‖ ≤ K
  hY0 : ‖Y0 - (1 + (e:ℂ) ^ 2 * η + (e:ℂ) ^ 4 * p)‖ ≤ Cρ * e ^ 5
  hY1 : ‖Y1 - ((e:ℂ) * g11 + (e:ℂ) ^ 3 * g13)‖ ≤ Cρ * e ^ 5
  hY2 : ‖Y2 - (g20 + (e:ℂ) ^ 2 * g22 + (e:ℂ) ^ 4 * g24)‖ ≤ Cρ * e ^ 5
  hsmall : ‖Y0 - 1‖ ≤ 1 / 2
  i11 : g11 = L1
  i13 : g13 = g11 * η - η1
  i22 : g22 - g20 * η - g11 ^ 2 + L2 = 0
  i24 : g24 + g22 * η - g20 * p - 2 * g11 * g13 - g20 * η ^ 2 + 2 * L2 * η - η2 = 0

theorem FinalData.Y0_ne {e K Cρ : ℝ} {Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2 : ℂ}
    (D : FinalData e K Cρ Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2) : 1 / 2 ≤ ‖Y0‖ := by
  have := norm_sub_norm_le (1:ℂ) Y0
  rw [norm_one, norm_sub_rev] at this
  linarith [D.hsmall]

theorem final_a {e K Cρ : ℝ} {Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2 : ℂ}
    (D : FinalData e K Cρ Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2) :
    ‖Y0 - 1 - (e:ℂ) ^ 2 * η‖ ≤ (K + Cρ) * e ^ 4 := by
  have he0 := D.he0
  have hK0 : 0 ≤ K := by linarith [D.hK]
  have : Y0 - 1 - (e:ℂ) ^ 2 * η = (Y0 - (1 + (e:ℂ) ^ 2 * η + (e:ℂ) ^ 4 * p)) + (e:ℂ) ^ 4 * p := by ring
  rw [this]
  have h1 := nmul (le_of_eq (npow he0.le 4)) D.hp
  have h5 : e ^ 5 ≤ e ^ 4 := pow_le_pow_of_le_one he0.le D.he1 (by norm_num)
  calc _ ≤ Cρ * e ^ 5 + e ^ 4 * K := (norm_add_le _ _).trans (add_le_add D.hY0 h1)
    _ ≤ (K + Cρ) * e ^ 4 := by nlinarith [D.hC]

set_option maxHeartbeats 2000000 in
theorem final_b {e K Cρ : ℝ} {Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2 : ℂ}
    (D : FinalData e K Cρ Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2) :
    ‖-((e:ℂ)⁻¹ * (Y1 / Y0)) + L1 - (e:ℂ) ^ 2 * η1‖ ≤ 2 * (3 * K ^ 2 + Cρ + 2 * K * Cρ) * e ^ 3 := by
  have he0 := D.he0
  have he1 := D.he1
  have hK0 : 0 ≤ K := by linarith [D.hK]
  have hC := D.hC
  have hE : ‖(e:ℂ)‖ = e := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0]
  have hE0 : (e:ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  have hY0n := D.Y0_ne
  have hY0ne : Y0 ≠ 0 := by intro h; rw [h, norm_zero] at hY0n; linarith
  have ek : ∀ k : ℕ, e ^ k ≤ 1 := fun k => pow_le_one₀ he0.le he1
  have hnum : -((e:ℂ)⁻¹ * (Y1 / Y0)) + L1 - (e:ℂ) ^ 2 * η1 =
      ((e:ℂ) ^ 4 * (L1 * p - η1 * η) - (e:ℂ) ^ 6 * (η1 * p) -
        (e:ℂ)⁻¹ * (Y1 - ((e:ℂ) * g11 + (e:ℂ) ^ 3 * g13)) +
        (L1 - (e:ℂ) ^ 2 * η1) * (Y0 - (1 + (e:ℂ) ^ 2 * η + (e:ℂ) ^ 4 * p))) / Y0 := by
    rw [eq_div_iff hY0ne, D.i13, D.i11]
    field_simp
    ring
  rw [hnum, norm_div]
  have hL1 : ‖L1‖ ≤ K := D.i11 ▸ D.h11
  have t1 : ‖(e:ℂ) ^ 4 * (L1 * p - η1 * η)‖ ≤ e ^ 4 * (K * K + K * K) :=
    nmul (le_of_eq (npow he0.le 4)) ((norm_sub_le _ _).trans (add_le_add (nmul hL1 D.hp) (nmul D.hη1 D.hη)))
  have t2 : ‖(e:ℂ) ^ 6 * (η1 * p)‖ ≤ e ^ 6 * (K * K) := nmul (le_of_eq (npow he0.le 6)) (nmul D.hη1 D.hp)
  have t3 : ‖(e:ℂ)⁻¹ * (Y1 - ((e:ℂ) * g11 + (e:ℂ) ^ 3 * g13))‖ ≤ Cρ * e ^ 4 := by
    rw [norm_mul, norm_inv, hE]
    calc e⁻¹ * ‖_‖ ≤ e⁻¹ * (Cρ * e ^ 5) := mul_le_mul_of_nonneg_left D.hY1 (by positivity)
      _ = Cρ * e ^ 4 := by field_simp
  have t4 : ‖(L1 - (e:ℂ) ^ 2 * η1) * (Y0 - (1 + (e:ℂ) ^ 2 * η + (e:ℂ) ^ 4 * p))‖ ≤ (K + K) * (Cρ * e ^ 5) := by
    refine nmul ((norm_sub_le _ _).trans (add_le_add hL1 ?_)) D.hY0
    calc ‖(e:ℂ) ^ 2 * η1‖ ≤ e ^ 2 * K := nmul (le_of_eq (npow he0.le 2)) D.hη1
      _ ≤ 1 * K := by gcongr; exact ek 2
      _ = K := one_mul K
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)) t4)
  have e43 : e ^ 4 ≤ e ^ 3 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
  have e53 : e ^ 5 ≤ e ^ 3 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
  have e63 : e ^ 6 ≤ e ^ 3 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
  have hKK : 0 ≤ K * K := mul_nonneg hK0 hK0
  have hKC : 0 ≤ K * Cρ := mul_nonneg hK0 hC
  have h1 : e ^ 4 * (K * K + K * K) ≤ 2 * K ^ 2 * e ^ 3 := by
    have := mul_le_mul_of_nonneg_right e43 (add_nonneg hKK hKK); nlinarith
  have h2 : e ^ 6 * (K * K) ≤ K ^ 2 * e ^ 3 := by
    have := mul_le_mul_of_nonneg_right e63 hKK; nlinarith
  have h3 : Cρ * e ^ 4 ≤ Cρ * e ^ 3 := mul_le_mul_of_nonneg_left e43 hC
  have h4 : (K + K) * (Cρ * e ^ 5) ≤ 2 * K * Cρ * e ^ 3 := by
    have := mul_le_mul_of_nonneg_left e53 hKC; nlinarith
  have hfin : (3 * K ^ 2 + Cρ + 2 * K * Cρ) * e ^ 3 ≥ 0 := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith

set_option maxHeartbeats 4000000 in
theorem final_c {e K Cρ : ℝ} {Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2 : ℂ}
    (D : FinalData e K Cρ Y0 Y1 Y2 η p g11 g13 g20 g22 g24 L1 L2 η1 η2) :
    ‖(((e:ℂ) ^ 2)⁻¹ * (Y2 / Y0 - (Y1 / Y0) ^ 2 - g20) + L2 - (e:ℂ) ^ 2 * η2)‖ ≤
      4 * (21 * K ^ 3 + Cρ * (10 * K + 2 * Cρ + 6 * K ^ 2 + K * Cρ) + 2 * K * Cρ * (6 * K + Cρ)) * e ^ 3 := by
  have he0 := D.he0
  have he1 := D.he1
  have hK := D.hK
  have hK0 : 0 ≤ K := by linarith
  have hC := D.hC
  have hE0 : (e:ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  have hY0n := D.Y0_ne
  have hY0ne : Y0 ≠ 0 := by intro h; rw [h, norm_zero] at hY0n; linarith
  have ek : ∀ k : ℕ, e ^ k ≤ 1 := fun k => pow_le_one₀ he0.le he1
  have hEk : ∀ k : ℕ, ‖(e:ℂ) ^ k‖ = e ^ k := fun k => npow he0.le k
  -- abbreviations as opaque variables
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℂ, N0 = 1 + (e:ℂ) ^ 2 * η + (e:ℂ) ^ 4 * p := ⟨_, rfl⟩
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℂ, N1 = (e:ℂ) * g11 + (e:ℂ) ^ 3 * g13 := ⟨_, rfl⟩
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℂ, N2 = g20 + (e:ℂ) ^ 2 * g22 + (e:ℂ) ^ 4 * g24 := ⟨_, rfl⟩
  have hY0 : ‖Y0 - N0‖ ≤ Cρ * e ^ 5 := hN0 ▸ D.hY0
  have hY1 : ‖Y1 - N1‖ ≤ Cρ * e ^ 5 := hN1 ▸ D.hY1
  have hY2 : ‖Y2 - N2‖ ≤ Cρ * e ^ 5 := hN2 ▸ D.hY2
  have nN0 : ‖N0‖ ≤ 3 * K := by
    rw [hN0]
    have := (norm_add_le _ _).trans (add_le_add ((norm_add_le (1:ℂ) ((e:ℂ) ^ 2 * η)).trans
      (add_le_add (le_of_eq norm_one) (nmul (le_of_eq (hEk 2)) D.hη))) (nmul (le_of_eq (hEk 4)) D.hp))
    have := ek 2; have := ek 4
    nlinarith
  have nN1 : ‖N1‖ ≤ 2 * K := by
    rw [hN1]
    have := (norm_add_le _ _).trans (add_le_add (nmul (le_of_eq (hEk 1)) D.h11) (nmul (le_of_eq (hEk 3)) D.h13))
    rw [pow_one] at this
    have := ek 1; have := ek 3
    rw [pow_one] at *
    nlinarith
  have nN2 : ‖N2‖ ≤ 3 * K := by
    rw [hN2]
    have := (norm_add_le _ _).trans (add_le_add ((norm_add_le g20 ((e:ℂ) ^ 2 * g22)).trans
      (add_le_add D.h20 (nmul (le_of_eq (hEk 2)) D.h22))) (nmul (le_of_eq (hEk 4)) D.h24))
    have := ek 2; have := ek 4
    nlinarith
  have hρ5 : Cρ * e ^ 5 ≤ Cρ := by have := ek 5; nlinarith
  have nY0 : ‖Y0‖ ≤ 3 * K + Cρ := by have := norm_le_norm_add_norm_sub' Y0 N0; linarith
  have nY1 : ‖Y1‖ ≤ 2 * K + Cρ := by have := norm_le_norm_add_norm_sub' Y1 N1; linarith
  have hR := norm_Rrem_le he0.le he1 hK D.hη D.hp D.h13 D.h20 D.h22 D.h24 D.hL2 D.hη2
  have hex := exact_identity (e:ℂ) η p g11 g13 g20 g22 g24 L2 η2 D.i22 D.i24
  rw [← hN0, ← hN1, ← hN2] at hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ, R = Rrem (e:ℂ) η p g13 g20 g22 g24 L2 η2 := ⟨_, rfl⟩
  rw [← hRdef] at hex hR
  obtain ⟨D1, hD1⟩ : ∃ D1 : ℂ, D1 = (Y2 - N2) * Y0 + N2 * (Y0 - N0) - (Y1 - N1) * (Y1 + N1) -
      g20 * ((Y0 - N0) * (Y0 + N0)) := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ D2 : ℂ, D2 = (Y0 - N0) * (Y0 + N0) := ⟨_, rfl⟩
  have hnum : ((e:ℂ) ^ 2)⁻¹ * (Y2 / Y0 - (Y1 / Y0) ^ 2 - g20) + L2 - (e:ℂ) ^ 2 * η2 =
      ((e:ℂ) ^ 4 * R + ((e:ℂ) ^ 2)⁻¹ * D1 + (L2 - (e:ℂ) ^ 2 * η2) * D2) / Y0 ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hY0ne)]
    have h6 : (e:ℂ) ^ 4 * R = ((e:ℂ) ^ 2)⁻¹ * ((e:ℂ) ^ 6 * R) := by field_simp
    rw [h6, ← hex, hD1, hD2]
    field_simp
    ring
  rw [hnum, norm_div, norm_pow]
  have hY02 : 1 / 4 ≤ ‖Y0‖ ^ 2 := by nlinarith
  have nD1 : ‖D1‖ ≤ Cρ * e ^ 5 * (10 * K + 2 * Cρ + 6 * K ^ 2 + K * Cρ) := by
    rw [hD1]
    have t1 := nmul hY2 nY0
    have t2 := nmul nN2 hY0
    have t3 := nmul hY1 ((norm_add_le Y1 N1).trans (add_le_add nY1 nN1))
    have t4 := nmul D.h20 (nmul hY0 ((norm_add_le Y0 N0).trans (add_le_add nY0 nN0)))
    have := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)
    have hCe : 0 ≤ Cρ * e ^ 5 := by positivity
    nlinarith
  have nD2 : ‖D2‖ ≤ Cρ * e ^ 5 * (6 * K + Cρ) := by
    rw [hD2]
    have := nmul hY0 ((norm_add_le Y0 N0).trans (add_le_add nY0 nN0))
    nlinarith
  have t1 : ‖(e:ℂ) ^ 4 * R‖ ≤ e ^ 4 * (21 * K ^ 3) := nmul (le_of_eq (hEk 4)) hR
  have t2 : ‖((e:ℂ) ^ 2)⁻¹ * D1‖ ≤ Cρ * (10 * K + 2 * Cρ + 6 * K ^ 2 + K * Cρ) * e ^ 3 := by
    rw [norm_mul, norm_inv, hEk 2]
    calc (e ^ 2)⁻¹ * ‖D1‖ ≤ (e ^ 2)⁻¹ * (Cρ * e ^ 5 * (10 * K + 2 * Cρ + 6 * K ^ 2 + K * Cρ)) :=
          mul_le_mul_of_nonneg_left nD1 (by positivity)
      _ = Cρ * (10 * K + 2 * Cρ + 6 * K ^ 2 + K * Cρ) * e ^ 3 := by field_simp
  have t3 : ‖(L2 - (e:ℂ) ^ 2 * η2) * D2‖ ≤ (K + K) * (Cρ * e ^ 5 * (6 * K + Cρ)) := by
    refine nmul ((norm_sub_le _ _).trans (add_le_add D.hL2 ?_)) nD2
    calc ‖(e:ℂ) ^ 2 * η2‖ ≤ e ^ 2 * K := nmul (le_of_eq (hEk 2)) D.hη2
      _ ≤ 1 * K := by gcongr; exact ek 2
      _ = K := one_mul K
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)
  have e43 : e ^ 4 ≤ e ^ 3 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
  have e53 : e ^ 5 ≤ e ^ 3 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
  have hK3 : 0 ≤ 21 * K ^ 3 := by positivity
  have hQ : 0 ≤ 2 * K * Cρ * (6 * K + Cρ) := by positivity
  have h1 : e ^ 4 * (21 * K ^ 3) ≤ 21 * K ^ 3 * e ^ 3 := by
    have := mul_le_mul_of_nonneg_right e43 hK3; linarith
  have h2 : (K + K) * (Cρ * e ^ 5 * (6 * K + Cρ)) ≤ 2 * K * Cρ * (6 * K + Cρ) * e ^ 3 := by
    have := mul_le_mul_of_nonneg_left e53 hQ
    have : (K + K) * (Cρ * e ^ 5 * (6 * K + Cρ)) = 2 * K * Cρ * (6 * K + Cρ) * e ^ 5 := by ring
    linarith
  rw [div_le_iff₀ (by linarith)]
  have hpos : 0 ≤ (21 * K ^ 3 + Cρ * (10 * K + 2 * Cρ + 6 * K ^ 2 + K * Cρ) +
      2 * K * Cρ * (6 * K + Cρ)) * e ^ 3 := by positivity
  nlinarith

end EulerianBridge.Saddle
