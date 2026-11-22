import EulerianCert.EulerianFourier
import PrivateApex.IntegralBound
import PrivateApex.ConsecutiveSlopes

/-!
PRIVATE: Manuscript 15, Section 7 -- the odd central slopes through their Fourier integral.

With `N = n + 1` even, the Fourier representation of the odd central slope proved in
`EulerianCert.EulerianFourier.central_slope_integral`,

  `s_n = (N/2π) ∫_ℝ r_E(t)^N (1 - cos t) dt`,       `r_E(t) = sinc(t/2)`,

is rewritten as  `s_n = (4N/π) ∫_0^∞ u² (sin u/u)^(N+2) du`  (`slopeQ_odd_eq_integral`).
The integral estimate of `IntegralBound` and the constant of `TailConstants` then give,
for the actual Eulerian numbers and without any assumed bound,

  `0 < s_n`  for every odd `n ≥ 3`,     `s_n ≤ analyticMajorant N / 2`,
  `s_n < 1`  for every odd `n ≥ 73`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PrivateApex
open Real Set MeasureTheory Filter Topology
open EulerianCert.Bracket

local notation "rE" => EulerianCert.FourierModes.rE

theorem sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, sinc_neg]

theorem weight_abs (N : ℕ) (x : ℝ) : weight N |x| = weight N x := by
  unfold weight; rw [sq_abs, sinc_abs]

/-- `1 - cos t = 2 (t/2)² sinc(t/2)²`. -/
theorem one_sub_cos_eq_sinc (t : ℝ) : 1 - cos t = 2 * (t / 2) ^ 2 * sinc (t / 2) ^ 2 := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp
  · have h2 : t / 2 ≠ 0 := div_ne_zero h two_ne_zero
    rw [sinc_of_ne_zero h2]
    have hcos : cos t = 1 - 2 * sin (t / 2) ^ 2 := by
      have h3 := cos_two_mul (t / 2)
      have h4 := sin_sq_add_cos_sq (t / 2)
      rw [show 2 * (t / 2) = t by ring] at h3
      linarith
    rw [hcos]
    field_simp
    ring

/-- For even `D`: `r_E(t)^D (1 - cos t) = 2 (t/2)² |sinc(t/2)|^(D+2)`. -/
theorem rE_pow_mul_eq_weight {D : ℕ} (hD : Even D) (t : ℝ) :
    rE t ^ D * (1 - cos t) = 2 * weight D (t / 2) := by
  have hE : Even (D + 2) := hD.add even_two
  have hr : rE t = sinc (t / 2) := rfl
  unfold weight
  rw [hE.pow_abs, hr, one_sub_cos_eq_sinc, pow_add]
  ring

/-- `∫_ℝ r_E(t)^D (1 - cos t) dt = 8 ∫_0^∞ u² |sinc u|^(D+2) du` for even `D`. -/
theorem integral_rE_eq_weight {D : ℕ} (hD : Even D) :
    ∫ t : ℝ, rE t ^ D * (1 - cos t) = 8 * ∫ x in Ioi (0 : ℝ), weight D x := by
  have h1 : (fun t : ℝ => rE t ^ D * (1 - cos t)) = fun t => 2 * weight D (t / 2) := by
    funext t; exact rE_pow_mul_eq_weight hD t
  have h2 : ∫ x : ℝ, weight D x = 2 * ∫ x in Ioi (0 : ℝ), weight D x := by
    rw [← integral_comp_abs (f := weight D)]
    congr 1; funext x; exact (weight_abs D x).symm
  rw [h1, integral_const_mul, Measure.integral_comp_div (weight D) 2, h2, smul_eq_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-- The real value of `slopeQ (2j+1)` is the central slope `s_n` in the form used by
`EulerianCert.EulerianFourier.central_slope_integral` and `EulerianCert.CentralSlope.slope`. -/
theorem slopeQ_odd_cast (j : ℕ) :
    ((slopeQ (2 * j + 1) : ℚ) : ℝ) = ((2 * j + 1 : ℕ) + 1 : ℝ) *
      ((E (2 * j + 1) j : ℝ) / (2 * j + 1).factorial -
        (E (2 * j + 1) (j - 1) : ℝ) / (2 * j + 1).factorial) := by
  rw [slopeQ_odd]
  push_cast
  ring

/-- Real form of the identity between consecutive slopes: with `N = n + 1`, `n = 2m ≥ 4`,
`t_n = 2 N² / ((N+1)(N+3)) · s_{n+1}`. -/
theorem slopeQ_even_cast {m : ℕ} (hm : 2 ≤ m) :
    ((slopeQ (2 * m) : ℚ) : ℝ) =
      2 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
        ((((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 3)) *
        ((slopeQ (2 * m + 1) : ℚ) : ℝ) := by
  rw [slopeQ_even_eq hm]
  push_cast
  ring

/-- **Odd central slope as a positive half-line integral**: for odd `n = 2j+1 ≥ 3`, `N = n+1`,
`s_n = (4N/π) ∫_0^∞ u² |sin u/u|^(N+2) du`. -/
theorem slopeQ_odd_eq_integral {j : ℕ} (hj : 1 ≤ j) :
    ((slopeQ (2 * j + 1) : ℚ) : ℝ) =
      4 * ((2 * j + 2 : ℕ) : ℝ) / π * ∫ x in Ioi (0 : ℝ), weight (2 * j + 2) x := by
  have h := EulerianCert.EulerianFourier.central_slope_integral hj
  have hI := integral_rE_eq_weight (D := 2 * j + 2) ⟨j + 1, by ring⟩
  rw [slopeQ_odd_cast, h, show 2 * j + 1 + 1 = 2 * j + 2 from rfl, hI]
  push_cast
  ring

/-- **Even central slope as a positive half-line integral**: for even `n = 2m ≥ 4`, `N = n+1`,
`t_n = (8N²/(π(N+3))) ∫_0^∞ u² |sin u/u|^(N+3) du`. -/
theorem slopeQ_even_eq_integral {m : ℕ} (hm : 2 ≤ m) :
    ((slopeQ (2 * m) : ℚ) : ℝ) =
      8 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 / (π * (((2 * m + 1 : ℕ) : ℝ) + 3)) *
        ∫ x in Ioi (0 : ℝ), weight (2 * m + 2) x := by
  rw [slopeQ_even_cast hm, slopeQ_odd_eq_integral (by omega : 1 ≤ m)]
  have hpi := pi_pos
  have h1 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) + 3 := by positivity
  push_cast
  field_simp
  ring

/-- The half-line integral is strictly positive. -/
theorem weight_integral_pos (N : ℕ) (hN : 2 ≤ N) : 0 < ∫ x in Ioi (0 : ℝ), weight N x := by
  have hc : Continuous (weight N) := by unfold weight; fun_prop
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun x => weight_nonneg N x)) (weight_integrable_half N hN)]
  have hopen : IsOpen (Function.support (weight N) ∩ Ioi (0 : ℝ)) :=
    hc.isOpen_support.inter isOpen_Ioi
  have hne : (Function.support (weight N) ∩ Ioi (0 : ℝ)).Nonempty := by
    refine ⟨1, ?_, by simp⟩
    rw [Function.mem_support]
    have hs : sinc (1 : ℝ) ≠ 0 := by
      rw [sinc_of_ne_zero one_ne_zero, div_one]
      exact (sin_pos_of_pos_of_lt_pi one_pos (by linarith [pi_gt_three])).ne'
    unfold weight
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (abs_ne_zero.mpr hs))
  exact hopen.measure_pos volume hne

/-- `0 < s_n` for every odd `n ≥ 3`. -/
theorem slopeQ_odd_pos {j : ℕ} (hj : 1 ≤ j) : 0 < slopeQ (2 * j + 1) := by
  have h : (0 : ℝ) < ((slopeQ (2 * j + 1) : ℚ) : ℝ) := by
    rw [slopeQ_odd_eq_integral hj]
    have hN : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
    exact mul_pos (div_pos (by positivity) pi_pos) (weight_integral_pos _ (by omega))
  exact_mod_cast h

theorem gauss_integral_eq (N : ℕ) :
    ∫ x in Ioi (0 : ℝ), gauss N x =
      √π / (4 * (((N : ℝ) + 2) / 6) * √(((N : ℝ) + 2) / 6)) := by
  unfold gauss
  exact gaussian_half_integral (((N : ℝ) + 2) / 6) (by positivity)

theorem sq_aux {N p a sp sa : ℝ} (hsp : 0 < sp) (hsa : 0 < sa)
    (hpp : sp * sp = p) (haa : sa * sa = a) :
    (4 * N / p * (sp / (4 * a * sa))) ^ 2 = N ^ 2 / (p * a ^ 3) := by
  subst hpp haa
  field_simp

/-- `(4N/π) · √π / (4 a √a) = √(216 N² / (π (N+2)³))` with `a = (N+2)/6`. -/
theorem gauss_term_eq {N : ℝ} (hN : 0 < N) :
    4 * N / π * (√π / (4 * ((N + 2) / 6) * √((N + 2) / 6))) =
      √(216 * N ^ 2 / (π * (N + 2) ^ 3)) := by
  have ha : 0 < (N + 2) / 6 := by positivity
  have hsp : 0 < √π := sqrt_pos.mpr pi_pos
  have hsa : 0 < √((N + 2) / 6) := sqrt_pos.mpr ha
  have hL : 0 ≤ 4 * N / π * (√π / (4 * ((N + 2) / 6) * √((N + 2) / 6))) := by positivity
  rw [← sqrt_sq hL, sq_aux hsp hsa (mul_self_sqrt pi_pos.le) (mul_self_sqrt ha.le)]
  congr 1
  have hpi := pi_pos
  field_simp
  ring

/-- `(4N/π) / ((N-1) π^(N-1)) = 4N / ((N-1) π^N)`. -/
theorem tail_term_eq (N : ℕ) (hN : 2 ≤ N) :
    4 * (N : ℝ) / π * (1 / (((N : ℝ) - 1) * π ^ (N - 1))) =
      4 * (N : ℝ) / (((N : ℝ) - 1) * π ^ N) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hpi := pi_pos
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    push_cast; linarith
  rw [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- **Analytic majorant for the actual odd slopes**: `s_n ≤ analyticMajorant N / 2`, `N = n+1`. -/
theorem slopeQ_odd_le_majorant {j : ℕ} (hj : 1 ≤ j) :
    ((slopeQ (2 * j + 1) : ℚ) : ℝ) ≤ analyticMajorant (2 * j + 2) / 2 := by
  have hN2 : 2 ≤ 2 * j + 2 := by omega
  have hNpos : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
  have hle := weight_integral_le (2 * j + 2) hN2
  rw [gauss_integral_eq, tail_half_integral _ hN2] at hle
  rw [slopeQ_odd_eq_integral hj]
  calc 4 * ((2 * j + 2 : ℕ) : ℝ) / π * ∫ x in Ioi (0 : ℝ), weight (2 * j + 2) x
      ≤ 4 * ((2 * j + 2 : ℕ) : ℝ) / π *
          (√π / (4 * ((((2 * j + 2 : ℕ) : ℝ) + 2) / 6) * √((((2 * j + 2 : ℕ) : ℝ) + 2) / 6)) +
            1 / ((((2 * j + 2 : ℕ) : ℝ) - 1) * π ^ (2 * j + 2 - 1))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = √(216 * ((2 * j + 2 : ℕ) : ℝ) ^ 2 / (π * (((2 * j + 2 : ℕ) : ℝ) + 2) ^ 3)) +
          4 * ((2 * j + 2 : ℕ) : ℝ) / ((((2 * j + 2 : ℕ) : ℝ) - 1) * π ^ (2 * j + 2)) := by
        rw [mul_add, gauss_term_eq hNpos, tail_term_eq _ hN2]
    _ = analyticMajorant (2 * j + 2) / 2 := by
        unfold analyticMajorant
        ring

/-- **Uniform tail bound for the actual odd slopes**: `s_n < 1` for every odd `n = 2j+1 ≥ 73`. -/
theorem slopeQ_odd_lt_one {j : ℕ} (hj : 36 ≤ j) : slopeQ (2 * j + 1) < 1 := by
  have h1 := slopeQ_odd_le_majorant (j := j) (by omega)
  have h2 := analyticMajorant_lt_two (2 * j + 2) (by omega)
  have h : ((slopeQ (2 * j + 1) : ℚ) : ℝ) < 1 := by linarith
  exact_mod_cast h

/-- **Tail of the even family**: `0 < t_n < 2` for every even `n = 2m ≥ 72`, from
`t_n < 2 s_{n+1}` and `s_{n+1} < 1`. -/
theorem slopeQ_even_tail {m : ℕ} (hm : 36 ≤ m) : 0 < slopeQ (2 * m) ∧ slopeQ (2 * m) < 2 := by
  have hpos := slopeQ_odd_pos (j := m) (by omega)
  have hlt := slopeQ_odd_lt_one hm
  refine ⟨slopeQ_even_pos (by omega) hpos, ?_⟩
  have := slopeQ_even_lt_two_mul (m := m) (by omega) hpos
  linarith

/-- `0 < t_n` for every even `n ≥ 4`. -/
theorem slopeQ_even_pos' {m : ℕ} (hm : 2 ≤ m) : 0 < slopeQ (2 * m) :=
  slopeQ_even_pos hm (slopeQ_odd_pos (by omega))

#print axioms slopeQ_odd_eq_integral
#print axioms slopeQ_even_eq_integral
#print axioms slopeQ_odd_pos
#print axioms slopeQ_odd_le_majorant
#print axioms slopeQ_odd_lt_one
#print axioms slopeQ_even_tail
#print axioms slopeQ_even_pos'
end PrivateApex
