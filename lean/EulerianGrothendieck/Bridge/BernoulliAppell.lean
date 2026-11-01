import Bridge.Appell

/-!
# Proposition 4.1: dual Bernoulli conventions

Manuscript V173, Section 4, eqs. (57)–(64).

With `op` from `Bridge.Appell` (formal operators `f(D)` on polynomials):
* (58) `𝒜 = M(D)` is the averaging operator `(𝒜p)(x) = ∫_0^1 p(x+t) dt` (`Appell.op_Mser_integral`);
* (59) `𝒜⁻¹ = D/(e^D - 1)`; (60) `M(-D)⁻¹ = D/(1 - e^{-D})`; (61) `M(-D)⁻¹ - M(D)⁻¹ = D`;
* `B_n := 𝒜⁻¹(x^n)` is Mathlib's Bernoulli polynomial `Polynomial.bernoulli n`;
* (62) `∫_0^1 B_n(x+t) dt = x^n`;
* (63)–(64) the Taylor coefficients of `z/(1-e^{-z})` and `z/(e^z-1)` through `z^{10}`.
-/

open Finset
open scoped Nat

namespace EulerianBridge.BernoulliAppell

open EulerianBridge.Appell

/-- The averaging operator `𝒜 = M(D)` on `ℚ[x]`. -/
noncomputable abbrev avg : Polynomial ℚ →ₗ[ℚ] Polynomial ℚ := op (Mser ℚ)

/-- `z/(e^z - 1) = ∑ B_n z^n/n!` (Mathlib's `bernoulli`, `B₁ = -1/2`). -/
noncomputable def bernSer : PowerSeries ℚ := PowerSeries.mk fun n => bernoulli n / n !

/-- `z/(1 - e^{-z}) = ∑ B'_n z^n/n!` (Mathlib's `bernoulli'`, `B'₁ = +1/2`). -/
noncomputable def bernSer' : PowerSeries ℚ := PowerSeries.mk fun n => bernoulli' n / n !

/-- `M(-z)`. -/
noncomputable def MserNeg : PowerSeries ℚ := PowerSeries.rescale (-1 : ℚ) (Mser ℚ)

theorem exp_sub_one_ne_zero : PowerSeries.exp ℚ - 1 ≠ 0 := by
  intro h0
  have := congrArg (PowerSeries.coeff 1) h0
  simp [PowerSeries.coeff_exp] at this

theorem bernSer_mul_Mser : bernSer * Mser ℚ = 1 := by
  have h := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hb : bernoulliPowerSeries ℚ = bernSer := by
    ext n; simp [bernoulliPowerSeries, bernSer]
  rw [hb, ← X_mul_Mser] at h
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ))
  calc PowerSeries.X * (bernSer * Mser ℚ) = bernSer * (PowerSeries.X * Mser ℚ) := by ring
    _ = PowerSeries.X * 1 := by rw [h, mul_one]

theorem rescale_neg_exp_mul_exp : PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) * PowerSeries.exp ℚ = 1 := by
  have := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) (-1) 1
  rw [show PowerSeries.rescale (1:ℚ) (PowerSeries.exp ℚ) = PowerSeries.exp ℚ by simp] at this
  rw [this]; simp

theorem X_mul_MserNeg_mul_exp : PowerSeries.X * MserNeg * PowerSeries.exp ℚ = PowerSeries.exp ℚ - 1 := by
  have h1 := congrArg (PowerSeries.rescale (-1 : ℚ)) (X_mul_Mser (K := ℚ))
  rw [map_mul, PowerSeries.rescale_X, map_sub, map_one] at h1
  have hneg : -(PowerSeries.X * MserNeg) = PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) - 1 := by
    rw [← h1, MserNeg, map_neg, map_one, neg_one_mul, neg_mul]
  calc PowerSeries.X * MserNeg * PowerSeries.exp ℚ
      = -((PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) - 1) * PowerSeries.exp ℚ) := by
        rw [← hneg]; ring
    _ = PowerSeries.exp ℚ - 1 := by rw [sub_mul, rescale_neg_exp_mul_exp]; ring

theorem bernSer'_mul_MserNeg : bernSer' * MserNeg = 1 := by
  have h := bernoulli'PowerSeries_mul_exp_sub_one ℚ
  have hb : bernoulli'PowerSeries ℚ = bernSer' := by
    ext n; simp [bernoulli'PowerSeries, bernSer']
  rw [hb] at h
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ))
  apply mul_right_cancel₀ exp_sub_one_ne_zero
  calc PowerSeries.X * (bernSer' * MserNeg) * (PowerSeries.exp ℚ - 1)
      = bernSer' * (PowerSeries.exp ℚ - 1) * (PowerSeries.X * MserNeg) := by ring
    _ = PowerSeries.X * PowerSeries.exp ℚ * (PowerSeries.X * MserNeg) := by rw [h]
    _ = PowerSeries.X * (PowerSeries.X * MserNeg * PowerSeries.exp ℚ) := by ring
    _ = PowerSeries.X * 1 * (PowerSeries.exp ℚ - 1) := by rw [X_mul_MserNeg_mul_exp]; ring

theorem bernSer'_sub_bernSer : bernSer' - bernSer = PowerSeries.X := by
  ext n
  simp only [bernSer', bernSer, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_X]
  rcases eq_or_ne n 1 with rfl | hn
  · simp [bernoulli_one]; norm_num
  · rw [bernoulli_eq_bernoulli'_of_ne_one hn, if_neg hn]; ring

/-! ## Operator statements -/

/-- Eq. (59): `𝒜` is invertible with `𝒜⁻¹ = D/(e^D - 1)`. -/
theorem avg_inverse :
    (op bernSer).comp avg = LinearMap.id ∧ avg.comp (op bernSer) = LinearMap.id :=
  ⟨op_comp_eq_id bernSer_mul_Mser, op_comp_eq_id (by rw [mul_comm]; exact bernSer_mul_Mser)⟩

/-- Eq. (60): `M(-D)⁻¹ = D/(1 - e^{-D})`. -/
theorem MnegD_inverse :
    (op bernSer').comp (op MserNeg) = LinearMap.id ∧ (op MserNeg).comp (op bernSer') = LinearMap.id :=
  ⟨op_comp_eq_id bernSer'_mul_MserNeg, op_comp_eq_id (by rw [mul_comm]; exact bernSer'_mul_MserNeg)⟩

/-- Eq. (61): `M(-D)⁻¹ - M(D)⁻¹ = D`. -/
theorem inverse_difference : op bernSer' - op bernSer = (Polynomial.derivative : Polynomial ℚ →ₗ[ℚ] _) := by
  rw [← op_sub, bernSer'_sub_bernSer, op_X]

/-- `𝒜⁻¹(x^n)` is the ordinary Bernoulli polynomial `B_n`. -/
theorem op_bernSer_X_pow (n : ℕ) : op bernSer (Polynomial.X ^ n) = Polynomial.bernoulli n := by
  rw [op_apply, Polynomial.natDegree_X_pow, Polynomial.bernoulli]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [pow_D_apply, Polynomial.iterate_derivative_X_pow_eq_smul, smul_smul, Polynomial.smul_X_eq_monomial]
  congr 1
  simp only [bernSer, PowerSeries.coeff_mk]
  have hfac : (k ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- `𝒜 B_n = x^n`. -/
theorem avg_bernoulli (n : ℕ) : avg (Polynomial.bernoulli n) = Polynomial.X ^ n := by
  rw [← op_bernSer_X_pow, ← LinearMap.comp_apply, avg_inverse.2, LinearMap.id_apply]

/-- Eq. (62): `∫_0^1 B_n(x+t) dt = x^n` for real `x`. -/
theorem integral_bernoulli (n : ℕ) (x : ℝ) :
    ∫ t in (0:ℝ)..1, ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).eval (x + t) = x ^ n := by
  rw [← op_Mser_integral, ← map_Mser (algebraMap ℚ ℝ), ← op_map, avg_bernoulli]
  simp

/-! ## Eqs. (63)–(64): Taylor coefficients through `z^{10}` -/

theorem b5 : bernoulli' 5 = 0 := bernoulli'_odd_eq_zero ⟨2, rfl⟩ (by norm_num)
theorem b7 : bernoulli' 7 = 0 := bernoulli'_odd_eq_zero ⟨3, rfl⟩ (by norm_num)
theorem b9 : bernoulli' 9 = 0 := bernoulli'_odd_eq_zero ⟨4, rfl⟩ (by norm_num)

theorem b6 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, b5]
  norm_num [Nat.choose]

theorem b8 : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, b5, b6, b7]
  norm_num [Nat.choose]

theorem b10 : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, b5, b6, b7, b8, b9]
  norm_num [Nat.choose]

/-- The coefficients of (63): `z/(1-e^{-z}) = 1 + z/2 + z²/12 - z⁴/720 + z⁶/30240 - z⁸/1209600 + z¹⁰/47900160 + ⋯`. -/
theorem bernSer'_coeffs :
    (List.range 11).map (fun n => PowerSeries.coeff n bernSer') =
      [1, 1/2, 1/12, 0, -1/720, 0, 1/30240, 0, -1/1209600, 0, 1/47900160] := by
  simp only [bernSer', PowerSeries.coeff_mk]
  simp [List.range_succ, bernoulli'_two, bernoulli'_four, b5, b6, b7, b8, b9, b10, Nat.factorial]
  norm_num

/-- The coefficients of (64): `z/(e^z-1)` differs only in the linear term. -/
theorem bernSer_coeffs :
    (List.range 11).map (fun n => PowerSeries.coeff n bernSer) =
      [1, -1/2, 1/12, 0, -1/720, 0, 1/30240, 0, -1/1209600, 0, 1/47900160] := by
  have h : ∀ n, PowerSeries.coeff n bernSer = PowerSeries.coeff n bernSer' - if n = 1 then 1 else 0 := by
    intro n
    have := congrArg (PowerSeries.coeff n) bernSer'_sub_bernSer
    rw [map_sub, PowerSeries.coeff_X] at this
    linarith
  simp only [h]
  have h' := bernSer'_coeffs
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq] at h' ⊢
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, -⟩ := h'
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  norm_num

end EulerianBridge.BernoulliAppell
