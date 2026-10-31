import Bridge.Saddle.IrExp

/-!
# Lemma 5.5, part 12: the coefficients of the expansion and their cancellation identities

As functions of the tilt `s` (with `κ = κ₂(s)`):
* `etaS = (κ₄/κ₂² - 5κ₃²/(3κ₂³))/8` (eq. (67)), its `s`-derivatives `etaS1`, `etaS2`;
* the `x`-derivatives `eta1 = etaS1/κ₂`, `eta2 = (eta1)'/κ₂` (since `ds/dx = 1/κ₂`);
* `L1 = κ₃/(2κ₂²) = (½ log v)'`, `L2 = (L1)'/κ₂ = (½ log v)''`;
* the Gaussian coefficients `G_{rj}` with `N_0 = 1 + ε²G₀₂ + ε⁴G₀₄`, `N_1 = εG₁₁ + ε³G₁₃`,
  `N_2 = G₂₀ + ε²G₂₂ + ε⁴G₂₄`, and the five identities
  `G₀₂ = η`, `G₁₁ = L1`, `G₁₃ = G₁₁η - η'`, `G₂₂ - G₂₀η - G₁₁² + L2 = 0`,
  `G₂₄ + G₂₂η - G₂₀G₀₄ - 2G₁₁G₁₃ - G₂₀η² + 2L2η - η'' = 0`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-! ## Real coefficient functions of `s` -/

/-- `η(s) = (κ₄/κ₂² - 5κ₃²/(3κ₂³))/8`, eq. (67). -/
noncomputable def etaS (s : ℝ) : ℝ := (κ 4 s / κ 2 s ^ 2 - 5 * κ 3 s ^ 2 / (3 * κ 2 s ^ 3)) / 8

noncomputable def etaS1 (s : ℝ) : ℝ :=
  (κ 5 s / κ 2 s ^ 2 - 16 / 3 * κ 3 s * κ 4 s / κ 2 s ^ 3 + 5 * κ 3 s ^ 3 / κ 2 s ^ 4) / 8

noncomputable def etaS2 (s : ℝ) : ℝ :=
  (κ 6 s / κ 2 s ^ 2 - 2 * κ 5 s * κ 3 s / κ 2 s ^ 3
    - 16 / 3 * ((κ 4 s * κ 4 s + κ 3 s * κ 5 s) / κ 2 s ^ 3 - 3 * κ 3 s * κ 4 s * κ 3 s / κ 2 s ^ 4)
    + 5 * (3 * κ 3 s ^ 2 * κ 4 s / κ 2 s ^ 4 - 4 * κ 3 s ^ 3 * κ 3 s / κ 2 s ^ 5)) / 8

/-- `η'(x)` as a function of `s = s(x)`. -/
noncomputable def eta1 (s : ℝ) : ℝ := etaS1 s / κ 2 s

/-- `η''(x)` as a function of `s = s(x)`. -/
noncomputable def eta2 (s : ℝ) : ℝ := (etaS2 s * κ 2 s - etaS1 s * κ 3 s) / κ 2 s ^ 2 / κ 2 s

/-- `(½ log v)'` as a function of `s`. -/
noncomputable def L1 (s : ℝ) : ℝ := κ 3 s / (2 * κ 2 s ^ 2)

/-- `(½ log v)''` as a function of `s`. -/
noncomputable def L2 (s : ℝ) : ℝ := (κ 4 s * κ 2 s - 2 * κ 3 s ^ 2) / (2 * κ 2 s ^ 3) / κ 2 s

theorem κ2_ne (s : ℝ) : κ 2 s ≠ 0 := (κ_two_pos s).ne'

theorem hasDerivAt_etaS (s : ℝ) : HasDerivAt etaS (etaS1 s) s := by
  have h2 := hasDerivAt_κ 2 s; have h3 := hasDerivAt_κ 3 s; have h4 := hasDerivAt_κ 4 s
  have hk := κ2_ne s
  have hd1 : (κ 2 ^ 2) s ≠ 0 := by simp only [Pi.pow_apply]; exact pow_ne_zero 2 hk
  have hd2 : (fun y => 3 * (κ 2 ^ 3) y) s ≠ 0 := by
    simp only [Pi.pow_apply]; exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hk)
  have h := (((h4.div (h2.pow 2) hd1).sub
    (((h3.pow 2).const_mul 5).div ((h2.pow 3).const_mul 3) hd2)).div_const 8)
  convert h using 1
  all_goals first
    | (funext x; simp only [etaS, Pi.pow_apply, Pi.div_apply, Pi.sub_apply]; ring)
    | (simp only [etaS1, Pi.pow_apply, Pi.div_apply, Pi.sub_apply, Pi.mul_apply]; field_simp; ring)

theorem hasDerivAt_etaS1 (s : ℝ) : HasDerivAt etaS1 (etaS2 s) s := by
  have h2 := hasDerivAt_κ 2 s; have h3 := hasDerivAt_κ 3 s; have h4 := hasDerivAt_κ 4 s
  have h5 := hasDerivAt_κ 5 s
  have hk := κ2_ne s
  have hA := h5.div (h2.pow 2) (by simp only [Pi.pow_apply]; exact pow_ne_zero 2 hk)
  have hB := (((h3.const_mul (16 / 3 : ℝ)).mul h4)).div (h2.pow 3)
    (by simp only [Pi.pow_apply]; exact pow_ne_zero 3 hk)
  have hC := ((h3.pow 3).const_mul (5 : ℝ)).div (h2.pow 4)
    (by simp only [Pi.pow_apply]; exact pow_ne_zero 4 hk)
  have h := ((hA.sub hB).add hC).div_const 8
  convert h using 1
  all_goals first
    | (funext x; simp only [etaS1, Pi.pow_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply,
        Pi.mul_apply]; ring)
    | (simp only [etaS2, Pi.pow_apply, Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply];
       field_simp; ring)

theorem hasDerivAt_eta1 (s : ℝ) :
    HasDerivAt eta1 ((etaS2 s * κ 2 s - etaS1 s * κ 3 s) / κ 2 s ^ 2) s :=
  (hasDerivAt_etaS1 s).div (hasDerivAt_κ 2 s) (κ2_ne s)

theorem hasDerivAt_L1 (s : ℝ) :
    HasDerivAt L1 ((κ 4 s * κ 2 s - 2 * κ 3 s ^ 2) / (2 * κ 2 s ^ 3)) s := by
  have h2 := hasDerivAt_κ 2 s; have h3 := hasDerivAt_κ 3 s
  have hk := κ2_ne s
  have h := h3.div ((h2.pow 2).const_mul 2)
    (by simp only [Pi.pow_apply]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hk))
  convert h using 1
  all_goals first
    | (funext x; simp only [L1, Pi.pow_apply, Pi.div_apply])
    | (simp only [Pi.pow_apply, Pi.div_apply, Pi.mul_apply]; field_simp; ring)

/-! ## The Gaussian coefficients -/

/-- `κ` as a complex number. -/
noncomputable def kc (s : ℝ) : ℂ := (κ 2 s : ℂ)

noncomputable def G02 (s : ℝ) : ℂ := ac 4 s * (3 / kc s ^ 2) + ac 3 s ^ 2 / 2 * (-15 / kc s ^ 3)

noncomputable def G04 (s : ℝ) : ℂ :=
  ac 6 s * (-15 / kc s ^ 3) + (ac 3 s * ac 5 s + ac 4 s ^ 2 / 2) * (105 / kc s ^ 4) +
    ac 3 s ^ 2 * ac 4 s / 2 * (-945 / kc s ^ 5) + ac 3 s ^ 4 / 24 * (10395 / kc s ^ 6)

noncomputable def G11 (s : ℝ) : ℂ := ac 3 s * (3 / kc s ^ 2)

noncomputable def G13 (s : ℝ) : ℂ :=
  ac 5 s * (-15 / kc s ^ 3) + ac 3 s * ac 4 s * (105 / kc s ^ 4) + ac 3 s ^ 3 / 6 * (-945 / kc s ^ 5)

noncomputable def G20 (s : ℝ) : ℂ := -1 / kc s

noncomputable def G22 (s : ℝ) : ℂ := ac 4 s * (-15 / kc s ^ 3) + ac 3 s ^ 2 / 2 * (105 / kc s ^ 4)

noncomputable def G24 (s : ℝ) : ℂ :=
  ac 6 s * (105 / kc s ^ 4) + (ac 3 s * ac 5 s + ac 4 s ^ 2 / 2) * (-945 / kc s ^ 5) +
    ac 3 s ^ 2 * ac 4 s / 2 * (10395 / kc s ^ 6) + ac 3 s ^ 4 / 24 * (-135135 / kc s ^ 7)

theorem μ_even (κ0 : ℝ) (n : ℕ) (hn : Even n) :
    μ κ0 n = ((-1) ^ (n / 2) * ((n - 1 : ℕ)‼ : ℝ) / κ0 ^ (n / 2) : ℝ) := by
  simp only [μ, if_pos hn]

theorem μ_eval (κ0 : ℝ) :
    μ κ0 0 = 1 ∧ μ κ0 2 = ((-1 / κ0 : ℝ) : ℂ) ∧ μ κ0 4 = ((3 / κ0 ^ 2 : ℝ) : ℂ) ∧
    μ κ0 6 = ((-15 / κ0 ^ 3 : ℝ) : ℂ) ∧ μ κ0 8 = ((105 / κ0 ^ 4 : ℝ) : ℂ) ∧
    μ κ0 10 = ((-945 / κ0 ^ 5 : ℝ) : ℂ) ∧ μ κ0 12 = ((10395 / κ0 ^ 6 : ℝ) : ℂ) ∧
    μ κ0 14 = ((-135135 / κ0 ^ 7 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [μ_even κ0 _ (by decide)] <;> norm_num [Nat.doubleFactorial]

theorem μ_odd (κ0 : ℝ) (n : ℕ) (hn : Odd n) : μ κ0 n = 0 := by
  simp [μ, Nat.not_even_iff_odd.mpr hn]

theorem Nexp_zero (s e : ℝ) : Nexp s e 0 = 1 + (e:ℂ) ^ 2 * G02 s + (e:ℂ) ^ 4 * G04 s := by
  obtain ⟨m0, m2, m4, m6, m8, m10, m12, m14⟩ := μ_eval (κ 2 s)
  simp only [Nexp, Finset.sum_range_succ, Finset.sum_range_zero, τc]
  simp only [zero_add, m0, m4, m6, m8, m10, m12, μ_odd (κ 2 s) 3 (by decide),
    μ_odd (κ 2 s) 5 (by decide), μ_odd (κ 2 s) 7 (by decide), μ_odd (κ 2 s) 9 (by decide),
    μ_odd (κ 2 s) 1 (by decide), μ_odd (κ 2 s) 11 (by decide)]
  simp only [G02, G04, kc]; push_cast; ring

theorem Nexp_one (s e : ℝ) : Nexp s e 1 = (e:ℂ) * G11 s + (e:ℂ) ^ 3 * G13 s := by
  obtain ⟨m0, m2, m4, m6, m8, m10, m12, m14⟩ := μ_eval (κ 2 s)
  simp only [Nexp, Finset.sum_range_succ, Finset.sum_range_zero, τc]
  simp only [m4, m6, m8, m10, μ_odd (κ 2 s) 1 (by decide), μ_odd (κ 2 s) 13 (by decide),
    μ_odd (κ 2 s) 5 (by decide), μ_odd (κ 2 s) 7 (by decide), μ_odd (κ 2 s) 9 (by decide),
    μ_odd (κ 2 s) 11 (by decide), show (1:ℕ) + 0 = 1 from rfl, show (1:ℕ) + 3 = 4 from rfl,
    show (1:ℕ) + 4 = 5 from rfl, show (1:ℕ) + 5 = 6 from rfl, show (1:ℕ) + 6 = 7 from rfl,
    show (1:ℕ) + 7 = 8 from rfl, show (1:ℕ) + 8 = 9 from rfl, show (1:ℕ) + 9 = 10 from rfl,
    show (1:ℕ) + 10 = 11 from rfl, show (1:ℕ) + 12 = 13 from rfl]
  simp only [G11, G13, kc]; push_cast; ring

theorem Nexp_two (s e : ℝ) : Nexp s e 2 = G20 s + (e:ℂ) ^ 2 * G22 s + (e:ℂ) ^ 4 * G24 s := by
  obtain ⟨m0, m2, m4, m6, m8, m10, m12, m14⟩ := μ_eval (κ 2 s)
  simp only [Nexp, Finset.sum_range_succ, Finset.sum_range_zero, τc]
  simp only [m2, m6, m8, m10, m12, m14, μ_odd (κ 2 s) 3 (by decide), μ_odd (κ 2 s) 5 (by decide),
    μ_odd (κ 2 s) 7 (by decide), μ_odd (κ 2 s) 9 (by decide), μ_odd (κ 2 s) 11 (by decide),
    μ_odd (κ 2 s) 13 (by decide), show (2:ℕ) + 0 = 2 from rfl, show (2:ℕ) + 3 = 5 from rfl,
    show (2:ℕ) + 4 = 6 from rfl, show (2:ℕ) + 5 = 7 from rfl, show (2:ℕ) + 6 = 8 from rfl,
    show (2:ℕ) + 7 = 9 from rfl, show (2:ℕ) + 8 = 10 from rfl, show (2:ℕ) + 9 = 11 from rfl,
    show (2:ℕ) + 10 = 12 from rfl, show (2:ℕ) + 12 = 14 from rfl]
  simp only [G20, G22, G24, kc]; push_cast; ring

/-! ## The cancellation identities -/

theorem ac_eq (n : ℕ) (s : ℝ) : ac n s = ((κ n s / n ! : ℝ) : ℂ) := by
  rw [ac, κc_ofReal]; push_cast; ring

theorem id_G02 (s : ℝ) : G02 s = (etaS s : ℂ) := by
  have hk : (κ 2 s : ℂ) ≠ 0 := by exact_mod_cast κ2_ne s
  simp only [G02, kc, ac_eq, etaS, Nat.factorial]
  push_cast
  field_simp
  ring

theorem id_G11 (s : ℝ) : G11 s = (L1 s : ℂ) := by
  have hk : (κ 2 s : ℂ) ≠ 0 := by exact_mod_cast κ2_ne s
  simp only [G11, kc, ac_eq, L1, Nat.factorial]
  push_cast
  field_simp
  ring

theorem id_G13 (s : ℝ) : G13 s = G11 s * (etaS s : ℂ) - (eta1 s : ℂ) := by
  have hk : (κ 2 s : ℂ) ≠ 0 := by exact_mod_cast κ2_ne s
  simp only [G13, G11, kc, ac_eq, etaS, eta1, etaS1, Nat.factorial]
  push_cast
  field_simp
  ring

theorem id_G22 (s : ℝ) : G22 s - G20 s * (etaS s : ℂ) - G11 s ^ 2 + (L2 s : ℂ) = 0 := by
  have hk : (κ 2 s : ℂ) ≠ 0 := by exact_mod_cast κ2_ne s
  simp only [G22, G20, G11, kc, ac_eq, etaS, L2, Nat.factorial]
  push_cast
  field_simp
  ring

theorem id_G24 (s : ℝ) :
    G24 s + G22 s * (etaS s : ℂ) - G20 s * G04 s - 2 * G11 s * G13 s - G20 s * (etaS s : ℂ) ^ 2 +
      2 * (L2 s : ℂ) * (etaS s : ℂ) - (eta2 s : ℂ) = 0 := by
  have hk : (κ 2 s : ℂ) ≠ 0 := by exact_mod_cast κ2_ne s
  simp only [G24, G22, G20, G04, G11, G13, kc, ac_eq, etaS, L2, eta2, etaS1, etaS2, Nat.factorial]
  push_cast
  field_simp
  ring

end EulerianBridge.Saddle
