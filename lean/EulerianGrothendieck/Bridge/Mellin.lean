import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Section 6: the hyperbolic quotient and its Mellin moments

Manuscript V173, Proposition 6.2, Theorem 6.3, Corollaries 6.4–6.5 (printed (149)–(163)).

* `qE t = r_E(2it)/r_E(4it) = sech t = e^t M(2t)/M(4t)` for real `t`;
* `∫_0^∞ t^{s-1} sech t dt = 2Γ(s)β(s)` for real `s > 1`;
* `∫_0^∞ t^{s-1} sech² t dt = 2^{2-s}Γ(s)η(s-1)` for real `s > 2`;
* the three moments `2β(2)`, `4β(3) = π³/8` and `9ζ(3)/8`;
* `d_E = 8/π³ = 1/∫_0^∞ t² q_E(t) dt`, and the polygamma form
  `β(3) = -(7/8)ζ(3) - (1/64)ψ''(1/4)` with `ψ''(1/4) := -2∑_{n≥0}(n+1/4)^{-3}`.

The Dirichlet series are defined as the (absolutely convergent) sums
`β(s) = ∑ (-1)^n (2n+1)^{-s}`, `η(s) = ∑ (-1)^n (n+1)^{-s}`, `ζ(s) = ∑ (n+1)^{-s}`.
-/

open Real MeasureTheory Set Filter Topology

namespace EulerianBridge.Mellin

noncomputable def sech (t : ℝ) : ℝ := 1 / cosh t

/-- The real restriction of the Eulerian profile on the imaginary axis: `r_E(iy) = sinh(y/2)/(y/2)`. -/
noncomputable def rEi (y : ℝ) : ℝ := if y = 0 then 1 else sinh (y / 2) / (y / 2)

/-- Definition 6.1: `q_E(t) = r_E(2it)/r_E(4it)`. -/
noncomputable def qE (t : ℝ) : ℝ := rEi (2 * t) / rEi (4 * t)

/-- `M(z) = (e^z - 1)/z`, `M(0) = 1` (eq. (57)), on the real line. -/
noncomputable def Mfun (x : ℝ) : ℝ := if x = 0 then 1 else (exp x - 1) / x

/-- Proposition 6.2: `q_E = sech = e^t M(2t)/M(4t)`. -/
theorem qE_eq_sech (t : ℝ) : qE t = sech t ∧ sech t = exp t * Mfun (2 * t) / Mfun (4 * t) := by
  by_cases ht : t = 0
  · subst ht; simp [qE, rEi, sech, Mfun]
  have h2 : (2 * t) ≠ 0 := by positivity
  have h4 : (4 * t) ≠ 0 := by positivity
  have hc : cosh t ≠ 0 := (cosh_pos t).ne'
  have hs : sinh t ≠ 0 := by
    intro h; exact ht (sinh_injective (h.trans sinh_zero.symm))
  constructor
  · simp only [qE, rEi, h2, h4, if_false, sech]
    rw [show 2 * t / 2 = t by ring, show 4 * t / 2 = 2 * t by ring, sinh_two_mul]
    field_simp
  · simp only [sech, Mfun, h2, h4, if_false]
    set E := exp t with hE
    have hEp : 0 < E := exp_pos t
    have e2 : exp (2 * t) = E ^ 2 := by rw [hE, ← exp_nat_mul]; push_cast; ring_nf
    have e4 : exp (4 * t) = E ^ 4 := by rw [hE, ← exp_nat_mul]; push_cast; ring_nf
    have en : exp (-t) = E⁻¹ := by rw [hE, exp_neg]
    have hE1 : E ^ 2 - 1 ≠ 0 := by
      intro h0; apply h2; rw [← e2] at h0
      have := exp_eq_one_iff (2 * t) |>.mp (by linarith); exact this
    have hE2 : E ^ 2 + 1 ≠ 0 := by positivity
    rw [cosh_eq, en, e2, e4]
    rw [show E ^ 4 - 1 = (E ^ 2 - 1) * (E ^ 2 + 1) by ring]
    field_simp
    ring

/-! ## Exponential expansions -/

theorem norm_neg_exp_lt_one {t : ℝ} (ht : 0 < t) : ‖-exp (-(2 * t))‖ < 1 := by
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem pow_neg_exp (t : ℝ) (n : ℕ) : (-exp (-(2 * t))) ^ n = (-1:ℝ) ^ n * exp (-(2 * n * t)) := by
  rw [neg_pow, ← exp_nat_mul]; ring_nf

/-- `sech t = 2 ∑ (-1)^n e^{-(2n+1)t}` for `t > 0` (eq. (157), first part). -/
theorem hasSum_sech {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => 2 * ((-1:ℝ) ^ n * exp (-((2 * n + 1) * t)))) (sech t) := by
  have hg := (hasSum_geometric_of_norm_lt_one (norm_neg_exp_lt_one ht)).mul_left (2 * exp (-t))
  convert hg using 1
  · funext n
    rw [pow_neg_exp, show -((2 * (n:ℝ) + 1) * t) = -t + -(2 * n * t) by ring, exp_add]
    ring
  · unfold sech
    set E := exp t with hE
    have hEp : 0 < E := exp_pos t
    have en : exp (-t) = E⁻¹ := by rw [hE, exp_neg]
    have e2 : exp (-(2 * t)) = (E ^ 2)⁻¹ := by rw [exp_neg, hE, ← exp_nat_mul]; push_cast; ring_nf
    rw [cosh_eq, en, e2, ← hE]
    have k1 : (1:ℝ) - -(E^2)⁻¹ = (E^2+1)/E^2 := by field_simp; ring
    have k2 : (E + E⁻¹)/2 = (E^2+1)/(2*E) := by field_simp
    rw [k1, k2]
    field_simp

/-- `sech² t = -4 ∑ n (-e^{-2t})^n` for `t > 0`, i.e. `4 ∑_{n≥1} (-1)^{n-1} n e^{-2nt}`. -/
theorem hasSum_sech_sq {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => -4 * ((n:ℝ) * (-1:ℝ) ^ n * exp (-(2 * n * t)))) (sech t ^ 2) := by
  have hg := (hasSum_coe_mul_geometric_of_norm_lt_one (norm_neg_exp_lt_one ht)).mul_left (-4)
  convert hg using 1
  · funext n
    rw [pow_neg_exp]; ring
  · unfold sech
    set E := exp t with hE
    have hEp : 0 < E := exp_pos t
    have en : exp (-t) = E⁻¹ := by rw [hE, exp_neg]
    have e2 : exp (-(2 * t)) = (E ^ 2)⁻¹ := by rw [exp_neg, hE, ← exp_nat_mul]; push_cast; ring_nf
    rw [cosh_eq, en, e2, ← hE]
    have k1 : (1:ℝ) - -(E^2)⁻¹ = (E^2+1)/E^2 := by field_simp; ring
    have k2 : (E + E⁻¹)/2 = (E^2+1)/(2*E) := by field_simp
    rw [k1, k2]
    field_simp
    ring

/-! ## Dirichlet series -/

noncomputable def dirichletBeta (s : ℝ) : ℝ := ∑' n : ℕ, (-1:ℝ) ^ n / (2 * n + 1) ^ s
noncomputable def dirichletEta (s : ℝ) : ℝ := ∑' n : ℕ, (-1:ℝ) ^ n / ((n:ℝ) + 1) ^ s
noncomputable def zeta (s : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ s

theorem summable_odd_rpow {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ => 1 / (2 * (n:ℝ) + 1) ^ s) := by
  have h := (Real.summable_one_div_nat_rpow.mpr hs)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((summable_nat_add_iff 1).mpr h)
  rw [one_div_le_one_div (by positivity) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]

theorem summable_nat_rpow {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ s) := by
  have h := (Real.summable_one_div_nat_rpow.mpr hs)
  have := (summable_nat_add_iff 1).mpr h
  simpa using this

/-! ## Theorem 6.3 -/

theorem integral_term {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫ t in Ioi (0:ℝ), t ^ (s - 1) * exp (-(r * t)) = Gamma s / r ^ s := by
  rw [integral_rpow_mul_exp_neg_mul_Ioi hs hr, div_rpow (by norm_num) hr.le, one_rpow]
  ring

theorem integrableOn_term {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := r) (by linarith) le_rfl hr
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [rpow_one]; ring_nf

/-- Theorem 6.3, eq. (152): `∫_0^∞ t^{s-1} sech t dt = 2Γ(s)β(s)` for `s > 1`. -/
theorem mellin_sech {s : ℝ} (hs : 1 < s) :
    ∫ t in Ioi (0:ℝ), t ^ (s - 1) * sech t = 2 * Gamma s * dirichletBeta s := by
  have hs0 : 0 < s := by linarith
  set f : ℕ → ℝ → ℝ := fun n t => t ^ (s - 1) * (2 * ((-1:ℝ) ^ n * exp (-((2 * n + 1) * t))))
  have hpt : ∀ t ∈ Ioi (0:ℝ), t ^ (s - 1) * sech t = ∑' n, f n t := by
    intro t ht
    rw [(hasSum_sech ht).tsum_eq.symm, ← tsum_mul_left]
  have hint : ∀ n, IntegrableOn (f n) (Ioi 0) := by
    intro n
    have := (integrableOn_term hs0 (by positivity : (0:ℝ) < 2 * n + 1)).const_mul (2 * (-1:ℝ) ^ n)
    refine IntegrableOn.congr_fun this (fun t _ => by simp only [f]; ring) measurableSet_Ioi
  have hnorm : ∀ n, ∫⁻ t in Ioi (0:ℝ), ‖f n t‖ₑ = ENNReal.ofReal (2 * Gamma s / (2 * n + 1) ^ s) := by
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    congr 1
    rw [show (2 * Gamma s / (2 * (n:ℝ) + 1) ^ s) = 2 * (Gamma s / (2 * n + 1) ^ s) by ring,
      ← integral_term hs0 (by positivity), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    simp only [f, norm_mul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_pos (exp_pos _), abs_of_pos (rpow_pos_of_pos ht' _), abs_two]
    ring
  have hsum : Summable (fun n : ℕ => 2 * Gamma s / (2 * (n:ℝ) + 1) ^ s) := by
    have := (summable_odd_rpow hs).mul_left (2 * Gamma s)
    refine this.congr (fun n => by ring)
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_tsum]
  · have : ∀ n, ∫ t in Ioi (0:ℝ), f n t = 2 * Gamma s * ((-1:ℝ) ^ n / (2 * n + 1) ^ s) := by
      intro n
      have e : (fun t => f n t) = fun t => (2 * (-1:ℝ) ^ n) * (t ^ (s - 1) * exp (-((2 * n + 1) * t))) := by
        funext t; simp only [f]; ring
      rw [e, integral_const_mul, integral_term hs0 (by positivity)]
      ring
    simp_rw [this]
    rw [tsum_mul_left, dirichletBeta]
  · exact fun n => (hint n).aestronglyMeasurable
  · simp_rw [hnorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top

/-- Theorem 6.3, eq. (153): `∫_0^∞ t^{s-1} sech² t dt = 2^{2-s}Γ(s)η(s-1)` for `s > 2`. -/
theorem mellin_sech_sq {s : ℝ} (hs : 2 < s) :
    ∫ t in Ioi (0:ℝ), t ^ (s - 1) * sech t ^ 2 = 2 ^ (2 - s) * Gamma s * dirichletEta (s - 1) := by
  have hs0 : 0 < s := by linarith
  set f : ℕ → ℝ → ℝ := fun n t => t ^ (s - 1) * (-4 * ((n:ℝ) * (-1:ℝ) ^ n * exp (-(2 * n * t))))
  have hpt : ∀ t ∈ Ioi (0:ℝ), t ^ (s - 1) * sech t ^ 2 = ∑' n, f n t := by
    intro t ht
    rw [(hasSum_sech_sq ht).tsum_eq.symm, ← tsum_mul_left]
  have hval : ∀ n : ℕ, ∫ t in Ioi (0:ℝ), f n t = -4 * (n * (-1:ℝ) ^ n) * (Gamma s / (2 * n) ^ s) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp [f]
    have hpos : (0:ℝ) < 2 * n := by positivity
    have e : (fun t => f n t) = fun t => (-4 * (n * (-1:ℝ) ^ n)) * (t ^ (s - 1) * exp (-((2 * n) * t))) := by
      funext t; simp only [f]; ring_nf
    rw [e, integral_const_mul, integral_term hs0 hpos]
  have hint : ∀ n, IntegrableOn (f n) (Ioi 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp [f]
    have hpos : (0:ℝ) < 2 * n := by positivity
    have := (integrableOn_term hs0 hpos).const_mul (-4 * (n * (-1:ℝ) ^ n))
    refine IntegrableOn.congr_fun this (fun t _ => by simp only [f]; ring_nf) measurableSet_Ioi
  have hsumN : Summable (fun n : ℕ => 4 * n * (Gamma s / (2 * n) ^ s)) := by
    -- 4 n Γ(s)(2n)^{-s} = 4·2^{-s}Γ(s) · n^{1-s}, and s - 1 > 1
    have h := (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < s - 1)).mul_left (4 * Gamma s / 2 ^ s)
    refine h.congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp [Real.zero_rpow (by linarith : s ≠ 0), Real.zero_rpow (by linarith : s - 1 ≠ 0)]
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    rw [mul_rpow (by norm_num) hn'.le, rpow_sub hn', rpow_one]
    have : (0:ℝ) < (n:ℝ) ^ s := rpow_pos_of_pos hn' s
    have : (0:ℝ) < (2:ℝ) ^ s := rpow_pos_of_pos (by norm_num) s
    field_simp
  have hnorm : ∀ n, ∫⁻ t in Ioi (0:ℝ), ‖f n t‖ₑ = ENNReal.ofReal (4 * n * (Gamma s / (2 * n) ^ s)) := by
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    congr 1
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp [f]
    have hpos : (0:ℝ) < 2 * n := by positivity
    rw [show 4 * (n:ℝ) * (Gamma s / (2 * n) ^ s) = (4 * n) * (Gamma s / (2 * n) ^ s) by ring,
      ← integral_term hs0 hpos, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    simp only [f, norm_mul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_pos (exp_pos _), abs_of_pos (rpow_pos_of_pos ht' _), Nat.abs_cast]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 4)]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_tsum]
  · simp_rw [hval]
    -- ∑ -4 n (-1)^n Γ/(2n)^s = 2^{2-s} Γ ∑ (-1)^m/(m+1)^{s-1}
    have hshift : ∑' n : ℕ, -4 * ((n:ℝ) * (-1:ℝ) ^ n) * (Gamma s / (2 * n) ^ s)
        = ∑' m : ℕ, -4 * (((m + 1 : ℕ):ℝ) * (-1:ℝ) ^ (m + 1)) * (Gamma s / (2 * ((m + 1 : ℕ):ℝ)) ^ s) := by
      rw [tsum_eq_zero_add']
      · simp
      · have hs : Summable (fun n : ℕ => -4 * ((n:ℝ) * (-1:ℝ) ^ n) * (Gamma s / (2 * n) ^ s)) := by
          apply Summable.of_norm
          refine hsumN.congr (fun n => ?_)
          have hG : (0:ℝ) < Gamma s := Gamma_pos_of_pos hs0
          have hp : (0:ℝ) ≤ (2 * (n:ℝ)) ^ s := rpow_nonneg (by positivity) s
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos hG, abs_of_nonneg hp,
            abs_pow]
          norm_num
        exact (summable_nat_add_iff 1).mpr hs
    rw [hshift, dirichletEta, ← tsum_mul_left]
    congr 1
    funext m
    have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
    push_cast
    rw [mul_rpow (by norm_num) hm.le, rpow_sub (by norm_num : (0:ℝ) < 2), rpow_two,
      rpow_sub hm, rpow_one, pow_succ]
    have h1 : (0:ℝ) < ((m:ℝ) + 1) ^ s := rpow_pos_of_pos hm s
    have h2 : (0:ℝ) < (2:ℝ) ^ s := rpow_pos_of_pos (by norm_num) s
    field_simp
    ring
  · exact fun n => (hint n).aestronglyMeasurable
  · simp_rw [hnorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumN]
    exact ENNReal.ofReal_ne_top

/-! ## The special moments (eqs. (154)–(156)) and Corollaries 6.4–6.5 -/

/-- Catalan's constant, `β(2) = ∑ (-1)^n/(2n+1)^2`. -/
theorem moment_one : ∫ t in Ioi (0:ℝ), t * qE t = 2 * dirichletBeta 2 := by
  have h := mellin_sech (s := 2) (by norm_num)
  rw [show (2:ℝ) - 1 = 1 by norm_num, show (2:ℝ) = (1:ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial] at h
  norm_num at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [(qE_eq_sech t).1]

/-- `β(3) = π³/32`, from Mathlib's `hasSum_L_function_mod_four_eval_three`. -/
theorem dirichletBeta_three : dirichletBeta 3 = π ^ 3 / 32 := by
  have h := hasSum_L_function_mod_four_eval_three
  -- the summand vanishes at even `n` and equals `(-1)^k/(2k+1)^3` at `n = 2k+1`
  have hodd : HasSum (fun k : ℕ => (1:ℝ) / ((2 * k + 1 : ℕ):ℝ) ^ 3 * Real.sin (π * ((2 * k + 1 : ℕ):ℝ) / 2))
      (π ^ 3 / 32) := by
    have hev : ∀ n : ℕ, n ∉ Set.range (fun k : ℕ => 2 * k + 1) →
        (1:ℝ) / (n:ℝ) ^ 3 * Real.sin (π * n / 2) = 0 := by
      intro n hn
      have : Even n := by
        rcases Nat.even_or_odd n with he | ⟨k, hk⟩
        · exact he
        · exact absurd ⟨k, hk.symm⟩ hn
      obtain ⟨k, hk⟩ := this
      rw [hk]; push_cast
      rw [show π * ((k:ℝ) + k) / 2 = (k:ℤ) * π by push_cast; ring, Real.sin_int_mul_pi]; simp
    exact (Function.Injective.hasSum_iff (fun a b h => by simpa using h) hev).mpr h
  unfold dirichletBeta
  rw [← hodd.tsum_eq]
  congr 1
  funext k
  push_cast
  rw [show π * (2 * (k:ℝ) + 1) / 2 = π / 2 + k * π by ring, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  rw [show ((2 * (k:ℝ) + 1)) ^ (3:ℝ) = (2 * (k:ℝ) + 1) ^ (3:ℕ) by norm_cast]
  ring

/-- Eq. (155): `∫_0^∞ t² q_E(t) dt = 4β(3) = π³/8`. -/
theorem moment_two : ∫ t in Ioi (0:ℝ), t ^ 2 * qE t = 4 * dirichletBeta 3 ∧ 4 * dirichletBeta 3 = π ^ 3 / 8 := by
  refine ⟨?_, by rw [dirichletBeta_three]; ring⟩
  have h := mellin_sech (s := 3) (by norm_num)
  rw [show (3:ℝ) - 1 = 2 by norm_num, show (3:ℝ) = (2:ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial] at h
  norm_num at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [(qE_eq_sech t).1]

/-! ## Odd zeta-type sums with natural exponents -/

theorem summable_inv_cube : Summable (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 3) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  simpa using this

theorem summable_of_le_inv_cube {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hle : ∀ n, g n ≤ 1 / ((n:ℝ) + 1) ^ 3) :
    Summable g := Summable.of_nonneg_of_le h0 hle summable_inv_cube

theorem inv_cube_le {a : ℝ} (n : ℕ) (ha : (n:ℝ) + 1 ≤ a) : 1 / a ^ 3 ≤ 1 / ((n:ℝ) + 1) ^ 3 := by
  have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have ha0 : 0 < a := by linarith
  rw [one_div_le_one_div (by positivity) (by positivity)]
  exact pow_le_pow_left₀ h1.le ha 3

theorem summable_odd_cube : Summable (fun k : ℕ => 1 / (2 * (k:ℝ) + 1) ^ 3) :=
  summable_of_le_inv_cube (fun k => by positivity)
    (fun k => inv_cube_le k (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]))

theorem rpow_three_nat (x : ℝ) : x ^ (3:ℝ) = x ^ (3:ℕ) := by
  rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, rpow_natCast]

theorem zeta_three_nat : zeta 3 = ∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ 3 := by
  unfold zeta; simp_rw [rpow_three_nat]

theorem eta_three_nat : dirichletEta 3 = ∑' n : ℕ, (-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 3 := by
  unfold dirichletEta; simp_rw [rpow_three_nat]

theorem beta_three_nat : dirichletBeta 3 = ∑' n : ℕ, (-1:ℝ) ^ n / (2 * (n:ℝ) + 1) ^ 3 := by
  unfold dirichletBeta; simp_rw [rpow_three_nat]

/-- `∑_{k} 1/(2k+2)^3 = ζ(3)/8`. -/
theorem even_cube_sum : ∑' k : ℕ, 1 / (2 * (k:ℝ) + 2) ^ 3 = 1 / 8 * zeta 3 := by
  rw [zeta_three_nat, ← tsum_mul_left]
  congr 1; funext k
  have : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [show 2 * (k:ℝ) + 2 = 2 * ((k:ℝ) + 1) by ring]
  field_simp
  ring

theorem summable_even_cube : Summable (fun k : ℕ => 1 / (2 * (k:ℝ) + 2) ^ 3) :=
  summable_of_le_inv_cube (fun k => by positivity)
    (fun k => inv_cube_le k (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]))

/-- `∑_{k} 1/(2k+1)^3 = (7/8) ζ(3)`. -/
theorem odd_cube_sum : ∑' k : ℕ, 1 / (2 * (k:ℝ) + 1) ^ 3 = 7 / 8 * zeta 3 := by
  set F : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 1) ^ 3 with hF
  have he : (fun k : ℕ => F (2 * k)) = fun k : ℕ => 1 / (2 * (k:ℝ) + 1) ^ 3 := by
    funext k; simp only [hF]; push_cast; rfl
  have ho : (fun k : ℕ => F (2 * k + 1)) = fun k : ℕ => 1 / (2 * (k:ℝ) + 2) ^ 3 := by
    funext k; simp only [hF]; push_cast; ring_nf
  have hsplit := tsum_even_add_odd (f := F) (he ▸ summable_odd_cube) (ho ▸ summable_even_cube)
  rw [he, ho, even_cube_sum] at hsplit
  have hz : ∑' k, F k = zeta 3 := zeta_three_nat.symm
  rw [hz] at hsplit
  linarith

/-- `η(3) = (3/4) ζ(3)`. -/
theorem dirichletEta_three : dirichletEta 3 = 3 / 4 * zeta 3 := by
  set F : ℕ → ℝ := fun n => (-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 3 with hF
  have he : (fun k : ℕ => F (2 * k)) = fun k : ℕ => 1 / (2 * (k:ℝ) + 1) ^ 3 := by
    funext k; simp only [hF]; rw [pow_mul]; push_cast; norm_num
  have ho : (fun k : ℕ => F (2 * k + 1)) = fun k : ℕ => -(1 / (2 * (k:ℝ) + 2) ^ 3) := by
    funext k; simp only [hF]; rw [pow_succ, pow_mul]; push_cast; norm_num; ring_nf
  have hsplit := tsum_even_add_odd (f := F) (he ▸ summable_odd_cube) (ho ▸ summable_even_cube.neg)
  rw [he, ho, tsum_neg, even_cube_sum, odd_cube_sum] at hsplit
  have hz : ∑' k, F k = dirichletEta 3 := eta_three_nat.symm
  rw [hz] at hsplit
  linarith

/-- Eq. (156): `∫_0^∞ t³ q_E(t)² dt = (9/8) ζ(3)`. -/
theorem moment_three_sq : ∫ t in Ioi (0:ℝ), t ^ 3 * qE t ^ 2 = 9 / 8 * zeta 3 := by
  have h := mellin_sech_sq (s := 4) (by norm_num)
  have hG : Gamma 4 = 6 := by
    rw [show (4:ℝ) = (3:ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
  rw [hG, show (4:ℝ) - 1 = 3 by norm_num, show (2:ℝ) - 4 = -2 by norm_num, dirichletEta_three,
    Real.rpow_neg (by norm_num), show (2:ℝ) ^ (2:ℝ) = 4 by norm_num] at h
  have hl : ∫ t in Ioi (0:ℝ), t ^ 3 * qE t ^ 2 = ∫ t in Ioi (0:ℝ), t ^ (3:ℝ) * sech t ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [(qE_eq_sech t).1, rpow_three_nat]
  rw [hl, h]
  ring

/-! ## Corollary 6.4 with the polygamma form -/

/-- `ψ''(1/4) := -2 ∑_{n≥0} (n + 1/4)^{-3}` (the series stated in the manuscript). -/
noncomputable def psi2Quarter : ℝ := -2 * ∑' n : ℕ, 1 / ((n:ℝ) + 1 / 4) ^ 3

theorem summable_41 : Summable (fun n : ℕ => 1 / (4 * (n:ℝ) + 1) ^ 3) :=
  summable_of_le_inv_cube (fun k => by positivity)
    (fun k => inv_cube_le k (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]))

theorem summable_43 : Summable (fun n : ℕ => 1 / (4 * (n:ℝ) + 3) ^ 3) :=
  summable_of_le_inv_cube (fun k => by positivity)
    (fun k => inv_cube_le k (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]))

/-- `β(3) = -(7/8) ζ(3) - ψ''(1/4)/64` (Corollary 6.4). -/
theorem beta_three_polygamma : dirichletBeta 3 = -(7 / 8) * zeta 3 - psi2Quarter / 64 := by
  set S1 := ∑' n : ℕ, 1 / (4 * (n:ℝ) + 1) ^ 3
  set S3 := ∑' n : ℕ, 1 / (4 * (n:ℝ) + 3) ^ 3
  set F : ℕ → ℝ := fun k => 1 / (2 * (k:ℝ) + 1) ^ 3 with hF
  set G : ℕ → ℝ := fun k => (-1:ℝ) ^ k / (2 * (k:ℝ) + 1) ^ 3 with hG
  have he : (fun k : ℕ => F (2 * k)) = fun n : ℕ => 1 / (4 * (n:ℝ) + 1) ^ 3 := by
    funext k; simp only [hF]; push_cast; ring_nf
  have ho : (fun k : ℕ => F (2 * k + 1)) = fun n : ℕ => 1 / (4 * (n:ℝ) + 3) ^ 3 := by
    funext k; simp only [hF]; push_cast; ring_nf
  have ge : (fun k : ℕ => G (2 * k)) = fun n : ℕ => 1 / (4 * (n:ℝ) + 1) ^ 3 := by
    funext k; simp only [hG]; rw [pow_mul]; push_cast; norm_num; ring_nf
  have go : (fun k : ℕ => G (2 * k + 1)) = fun n : ℕ => -(1 / (4 * (n:ℝ) + 3) ^ 3) := by
    funext k; simp only [hG]; rw [pow_succ, pow_mul]; push_cast; norm_num; ring_nf
  have hO := tsum_even_add_odd (f := F) (he ▸ summable_41) (ho ▸ summable_43)
  have hB := tsum_even_add_odd (f := G) (ge ▸ summable_41) (go ▸ summable_43.neg)
  rw [he, ho] at hO
  rw [ge, go, tsum_neg] at hB
  have hO' : ∑' k, F k = 7 / 8 * zeta 3 := odd_cube_sum
  have hB' : ∑' k, G k = dirichletBeta 3 := beta_three_nat.symm
  rw [hO'] at hO
  rw [hB'] at hB
  have hpsi : psi2Quarter / 64 = -2 * S1 := by
    have h64 : ∑' n : ℕ, 1 / ((n:ℝ) + 1 / 4) ^ 3 = ∑' n : ℕ, 64 * (1 / (4 * (n:ℝ) + 1) ^ 3) := by
      congr 1; funext n
      have : (0:ℝ) < 4 * n + 1 := by positivity
      have : (0:ℝ) < n + 1 / 4 := by positivity
      field_simp; ring
    unfold psi2Quarter; rw [h64, tsum_mul_left]; ring
  rw [hpsi]
  linarith

/-- `β(3) = π³/32`, `(7/8)ζ(3) + β(3) = 2∑(4n+1)^{-3}` — Corollary 6.5's two numerical inputs are now
the two certified identities `dirichletBeta_three` and `beta_three_polygamma`. -/
theorem zeta_three_polygamma : 7 / 8 * zeta 3 = -π ^ 3 / 32 - psi2Quarter / 64 := by
  have := beta_three_polygamma; rw [dirichletBeta_three] at this; linarith

end EulerianBridge.Mellin
