import PrivateApex.EvenAsymptotics

/-!
PRIVATE: Manuscript 15, Section 7.3 -- eighth-order exponential enclosure of `sin u / u`.

For `0 ≤ u ≤ 1`, with `q(u) = u²/6 + u⁴/180 + u⁶/2835` (the first three terms of the classical
Taylor series of `-log(sin u/u)`):

  `exp(-q(u) - u⁸/1000) ≤ sin u / u ≤ exp(-q(u) + u⁸/1000)`.

Consequently, for the weight `x² |sinc x|^(N+2)` of `IntegralBound`, with `M = N + 2`,

  `u² e^(-Mu²/6) Plow(M,u) ≤ weight N u ≤ u² e^(-Mu²/6) Pup(M,u)`      (`0 ≤ u ≤ 1`),

where `Pup`, `Plow` are explicit polynomials.  These are the pointwise inputs of the
second-order Laplace expansion in `OddSecondOrder`.
-/
noncomputable section
namespace PrivateApex
open Real
open EulerianCert.LocalLimit (nonneg_of_deriv_nonneg)
open EulerianCert.CentralSlope (sin_ge7 exp_le_quad exp_ge_cubic nonneg_of_deriv_nonpos_left)

theorem cos_le8 {y : ℝ} (hy : 0 ≤ y) :
    cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 + y ^ 8 / 40320 := by
  have := nonneg_of_deriv_nonneg
    (f := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 + y ^ 8 / 40320 - cos y)
    (f' := fun y => -y + y ^ 3 / 6 - y ^ 5 / 120 + y ^ 7 / 5040 + sin y)
    (fun x => by
      have := (((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_pow 6 x).div_const 720)).add
        ((hasDerivAt_pow 8 x).div_const 40320)).sub (hasDerivAt_cos x)
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := sin_ge7 hx; linarith) hy
  linarith

theorem sin_le9 {y : ℝ} (hy : 0 ≤ y) :
    sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 + y ^ 9 / 362880 := by
  have := nonneg_of_deriv_nonneg
    (f := fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 + y ^ 9 / 362880 - sin y)
    (f' := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 + y ^ 8 / 40320 - cos y)
    (fun x => by
      have := (((((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
        ((hasDerivAt_pow 5 x).div_const 120)).sub ((hasDerivAt_pow 7 x).div_const 5040)).add
        ((hasDerivAt_pow 9 x).div_const 362880)).sub (hasDerivAt_sin x)
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := cos_le8 hx; linarith) hy
  linarith

theorem exp_le_quartic {x : ℝ} (hx : x ≤ 0) :
    exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
  have := nonneg_of_deriv_nonpos_left
    (f := fun x => 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 - exp x)
    (f' := fun x => 1 + x + x ^ 2 / 2 + x ^ 3 / 6 - exp x)
    (fun y => by
      have := (((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id' y)).add
        ((hasDerivAt_pow 2 y).div_const 2)).add ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub (Real.hasDerivAt_exp y)
      convert this using 1; push_cast; ring)
    (by simp) (fun y hy => by have := exp_ge_cubic hy; linarith) hx
  linarith

theorem sinc_le_poly8 {u : ℝ} (h0 : 0 ≤ u) :
    sinc u ≤ 1 - u ^ 2 / 6 + u ^ 4 / 120 - u ^ 6 / 5040 + u ^ 8 / 362880 := by
  rcases h0.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [sinc_of_ne_zero h.ne', div_le_iff₀ h]
    exact (sin_le9 h0).trans (le_of_eq (by ring))

theorem poly6_le_sinc {u : ℝ} (h0 : 0 ≤ u) :
    1 - u ^ 2 / 6 + u ^ 4 / 120 - u ^ 6 / 5040 ≤ sinc u := by
  rcases h0.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [sinc_of_ne_zero h.ne', le_div_iff₀ h]
    exact (le_of_eq (by ring)).trans (sin_ge7 h0)

/-- `sin u / u ≤ exp(-u²/6 - u⁴/180 - u⁶/2835 + u⁸/1000)` for `0 ≤ u ≤ 1`. -/
theorem sinc_upper8 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    sinc u ≤ exp (-(u ^ 2 / 6 + u ^ 4 / 180 + u ^ 6 / 2835) + u ^ 8 / 1000) := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u ^ 2 := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hv1 : v ≤ 1 := by rw [hv]; exact pow_le_one₀ h0 h1
  have e4 : u ^ 4 = v ^ 2 := by rw [hv]; ring
  have e6 : u ^ 6 = v ^ 3 := by rw [hv]; ring
  have e8 : u ^ 8 = v ^ 4 := by rw [hv]; ring
  have hs := sinc_le_poly8 h0
  rw [e4, e6, e8, ← hv] at hs
  rw [e4, e6, e8, ← hv]
  have n2 : 0 ≤ v ^ 2 := pow_nonneg hv0 2
  have n3 : 0 ≤ v ^ 3 := pow_nonneg hv0 3
  have n4 : 0 ≤ v ^ 4 := pow_nonneg hv0 4
  have q41 : v ^ 4 ≤ v := by
    calc v ^ 4 ≤ v ^ 1 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
      _ = v := pow_one v
  have hy : -(v / 6 + v ^ 2 / 180 + v ^ 3 / 2835) + v ^ 4 / 1000 ≤ 0 := by linarith
  refine hs.trans (le_trans ?_ (exp_ge_cubic hy))
  have q5 : v ^ 5 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n5 : 0 ≤ v ^ 5 := pow_nonneg hv0 5
  have q6 : v ^ 6 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n6 : 0 ≤ v ^ 6 := pow_nonneg hv0 6
  have q7 : v ^ 7 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n7 : 0 ≤ v ^ 7 := pow_nonneg hv0 7
  have q8 : v ^ 8 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n8 : 0 ≤ v ^ 8 := pow_nonneg hv0 8
  have q9 : v ^ 9 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n9 : 0 ≤ v ^ 9 := pow_nonneg hv0 9
  have q10 : v ^ 10 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n10 : 0 ≤ v ^ 10 := pow_nonneg hv0 10
  have q11 : v ^ 11 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n11 : 0 ≤ v ^ 11 := pow_nonneg hv0 11
  have q12 : v ^ 12 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n12 : 0 ≤ v ^ 12 := pow_nonneg hv0 12
  nlinarith

/-- `exp(-u²/6 - u⁴/180 - u⁶/2835 - u⁸/1000) ≤ sin u / u` for `0 ≤ u ≤ 1`. -/
theorem sinc_lower8 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    exp (-(u ^ 2 / 6 + u ^ 4 / 180 + u ^ 6 / 2835) - u ^ 8 / 1000) ≤ sinc u := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u ^ 2 := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hv1 : v ≤ 1 := by rw [hv]; exact pow_le_one₀ h0 h1
  have e4 : u ^ 4 = v ^ 2 := by rw [hv]; ring
  have e6 : u ^ 6 = v ^ 3 := by rw [hv]; ring
  have e8 : u ^ 8 = v ^ 4 := by rw [hv]; ring
  have hs := poly6_le_sinc h0
  rw [e4, e6, ← hv] at hs
  rw [e4, e6, e8, ← hv]
  have n2 : 0 ≤ v ^ 2 := pow_nonneg hv0 2
  have n3 : 0 ≤ v ^ 3 := pow_nonneg hv0 3
  have n4 : 0 ≤ v ^ 4 := pow_nonneg hv0 4
  have hy : -(v / 6 + v ^ 2 / 180 + v ^ 3 / 2835) - v ^ 4 / 1000 ≤ 0 := by linarith
  refine (exp_le_quartic hy).trans (le_trans ?_ hs)
  have q5 : v ^ 5 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n5 : 0 ≤ v ^ 5 := pow_nonneg hv0 5
  have q6 : v ^ 6 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n6 : 0 ≤ v ^ 6 := pow_nonneg hv0 6
  have q7 : v ^ 7 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n7 : 0 ≤ v ^ 7 := pow_nonneg hv0 7
  have q8 : v ^ 8 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n8 : 0 ≤ v ^ 8 := pow_nonneg hv0 8
  have q9 : v ^ 9 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n9 : 0 ≤ v ^ 9 := pow_nonneg hv0 9
  have q10 : v ^ 10 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n10 : 0 ≤ v ^ 10 := pow_nonneg hv0 10
  have q11 : v ^ 11 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n11 : 0 ≤ v ^ 11 := pow_nonneg hv0 11
  have q12 : v ^ 12 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n12 : 0 ≤ v ^ 12 := pow_nonneg hv0 12
  have q13 : v ^ 13 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n13 : 0 ≤ v ^ 13 := pow_nonneg hv0 13
  have q14 : v ^ 14 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n14 : 0 ≤ v ^ 14 := pow_nonneg hv0 14
  have q15 : v ^ 15 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n15 : 0 ≤ v ^ 15 := pow_nonneg hv0 15
  have q16 : v ^ 16 ≤ v ^ 4 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have n16 : 0 ≤ v ^ 16 := pow_nonneg hv0 16
  nlinarith

/-- The upper polynomial factor. -/
def Pup (M u : ℝ) : ℝ :=
  1 - M / 180 * u ^ 4 - M / 2835 * u ^ 6 + M / 1000 * u ^ 8 +
    M ^ 2 / 2 * (u ^ 4 / 180 + u ^ 6 / 2835) ^ 2

/-- The lower polynomial factor. -/
def Plow (M u : ℝ) : ℝ :=
  1 - M / 180 * u ^ 4 - M / 2835 * u ^ 6 - M / 1000 * u ^ 8 +
    M ^ 2 / 2 * (u ^ 4 / 180) ^ 2 - M ^ 3 / 6 * (7 / 1000) ^ 3 * u ^ 12

theorem Pup_nonneg {M : ℝ} (hM : 0 ≤ M) (u : ℝ) : 0 ≤ Pup M u := by
  unfold Pup
  have h8 : 0 ≤ M * u ^ 8 := mul_nonneg hM (by positivity)
  nlinarith [sq_nonneg (1 - M * (u ^ 4 / 180 + u ^ 6 / 2835))]

/-- `weight N u ≤ u² e^(-Mu²/6) Pup(M,u)` for `0 ≤ u ≤ 1`, `M = N + 2`. -/
theorem weight_le_Pup (N : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    weight N u ≤ u ^ 2 * exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Pup ((N : ℝ) + 2) u := by
  have hM : (0 : ℝ) ≤ (N : ℝ) + 2 := by positivity
  have hs := sinc_upper8 h0 h1
  have hs0 : 0 ≤ sinc u := (exp_pos _).le.trans (sinc_lower8 h0 h1)
  have hpow : |sinc u| ^ (N + 2) ≤
      exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Pup ((N : ℝ) + 2) u := by
    rw [abs_of_nonneg hs0]
    calc sinc u ^ (N + 2)
        ≤ (exp (-(u ^ 2 / 6 + u ^ 4 / 180 + u ^ 6 / 2835) + u ^ 8 / 1000)) ^ (N + 2) :=
          pow_le_pow_left₀ hs0 hs _
      _ = exp (-(((N : ℝ) + 2) / 6) * u ^ 2) *
          exp (-(((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 - u ^ 8 / 1000))) := by
          rw [← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
      _ ≤ exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Pup ((N : ℝ) + 2) u := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          have n4 : 0 ≤ u ^ 4 := pow_nonneg h0 4
          have n6 : 0 ≤ u ^ 6 := pow_nonneg h0 6
          have n8 : 0 ≤ u ^ 8 := pow_nonneg h0 8
          have hu8 : u ^ 8 ≤ u ^ 4 := pow_le_pow_of_le_one h0 h1 (by norm_num)
          have hz0 : 0 ≤ ((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 - u ^ 8 / 1000) :=
            mul_nonneg hM (by linarith)
          have hzy : ((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 - u ^ 8 / 1000) ≤
              ((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835) :=
            mul_le_mul_of_nonneg_left (by linarith) hM
          have hsq := pow_le_pow_left₀ hz0 hzy 2
          have he := exp_le_quad
            (x := -(((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 - u ^ 8 / 1000))) (by linarith)
          unfold Pup
          nlinarith [he, hsq]
  unfold weight
  calc u ^ 2 * |sinc u| ^ (N + 2)
      ≤ u ^ 2 * (exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Pup ((N : ℝ) + 2) u) :=
        mul_le_mul_of_nonneg_left hpow (sq_nonneg u)
    _ = u ^ 2 * exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Pup ((N : ℝ) + 2) u := by ring

/-- `u² e^(-Mu²/6) Plow(M,u) ≤ weight N u` for `0 ≤ u ≤ 1`, `M = N + 2`. -/
theorem Plow_le_weight (N : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    u ^ 2 * exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Plow ((N : ℝ) + 2) u ≤ weight N u := by
  have hM : (0 : ℝ) ≤ (N : ℝ) + 2 := by positivity
  have hs := sinc_lower8 h0 h1
  have hs0 : 0 ≤ sinc u := (exp_pos _).le.trans hs
  have hpow : exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Plow ((N : ℝ) + 2) u ≤
      |sinc u| ^ (N + 2) := by
    rw [abs_of_nonneg hs0]
    calc exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Plow ((N : ℝ) + 2) u
        ≤ exp (-(((N : ℝ) + 2) / 6) * u ^ 2) *
          exp (-(((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000))) := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          have n4 : 0 ≤ u ^ 4 := pow_nonneg h0 4
          have n6 : 0 ≤ u ^ 6 := pow_nonneg h0 6
          have n8 : 0 ≤ u ^ 8 := pow_nonneg h0 8
          have hu6 : u ^ 6 ≤ u ^ 4 := pow_le_pow_of_le_one h0 h1 (by norm_num)
          have hu8 : u ^ 8 ≤ u ^ 4 := pow_le_pow_of_le_one h0 h1 (by norm_num)
          have hw0 : 0 ≤ u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000 := by positivity
          have hw1 : u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000 ≤ 7 / 1000 * u ^ 4 := by linarith
          have hw2 : u ^ 4 / 180 ≤ u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000 := by linarith
          have hz0 : 0 ≤ ((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000) :=
            mul_nonneg hM hw0
          have hz1 : ((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000) ≤
              ((N : ℝ) + 2) * (7 / 1000 * u ^ 4) := mul_le_mul_of_nonneg_left hw1 hM
          have hz2 : ((N : ℝ) + 2) * (u ^ 4 / 180) ≤
              ((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000) :=
            mul_le_mul_of_nonneg_left hw2 hM
          have hcu := pow_le_pow_left₀ hz0 hz1 3
          have hsq := pow_le_pow_left₀ (mul_nonneg hM (by positivity : (0 : ℝ) ≤ u ^ 4 / 180))
            hz2 2
          have he := exp_ge_cubic
            (x := -(((N : ℝ) + 2) * (u ^ 4 / 180 + u ^ 6 / 2835 + u ^ 8 / 1000))) (by linarith)
          unfold Plow
          nlinarith [he, hcu, hsq]
      _ = (exp (-(u ^ 2 / 6 + u ^ 4 / 180 + u ^ 6 / 2835) - u ^ 8 / 1000)) ^ (N + 2) := by
          rw [← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
      _ ≤ sinc u ^ (N + 2) := pow_le_pow_left₀ (exp_pos _).le hs _
  unfold weight
  calc u ^ 2 * exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Plow ((N : ℝ) + 2) u
      = u ^ 2 * (exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * Plow ((N : ℝ) + 2) u) := by ring
    _ ≤ u ^ 2 * |sinc u| ^ (N + 2) := mul_le_mul_of_nonneg_left hpow (sq_nonneg u)

#print axioms sinc_upper8
#print axioms sinc_lower8
#print axioms weight_le_Pup
#print axioms Plow_le_weight
end PrivateApex
