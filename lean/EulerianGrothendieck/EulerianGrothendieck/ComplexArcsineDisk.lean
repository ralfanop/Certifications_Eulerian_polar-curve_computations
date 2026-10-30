import EulerianGrothendieck.FiniteSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-! # Task D: the sharp complex Lipschitz constant of `arcsin` on `D_B = {|z - i| ≤ 1/2}`

Branch.  `sqrtOneSub z = (1 - z²)^{1/2}` (principal power) and
`H0 z = -i log(i z + (1 - z²)^{1/2})` (principal logarithm).  On the open upper half-plane,
which contains `D_B`, both principal branches are holomorphic: `1 - z²` and
`i z + (1 - z²)^{1/2}` lie in the slit plane.  We prove `sin (H0 z) = z` (for every `z`) and
`H0' = (1 - z²)^{-1/2}` on the upper half-plane, so `H0` is the holomorphic branch of `arcsin`
near `D_B`.

Main results (namespace `EulerianGrothendieck.ArcsinDisk`):
* `sin_H0`: `sin (H0 z) = z`;
* `hasDerivAt_H0`: `H0' z = 1/(1 - z²)^{1/2}` for `Im z > 0`;
* `sup_norm_deriv_H0`: `sup_{z ∈ D_B} |H0'(z)| = 2/√5`, attained at `z = i/2`;
* `H0_lipschitz`: `|H0 z - H0 w| ≤ (2/√5)|z - w|` on `D_B` (mean value inequality on the
  convex disc);
* `H0_lipschitz_sharp`: every Lipschitz constant of `H0` on `D_B` is `≥ 2/√5`
  (difference quotients at `i/2` along points of the disc). -/

noncomputable section
open Complex Filter Topology
namespace EulerianGrothendieck.ArcsinDisk

def sqrtOneSub (z : ℂ) : ℂ := (1 - z ^ 2) ^ (1/2 : ℂ)

/-- The holomorphic branch of `arcsin` near `D_B`. -/
def H0 (z : ℂ) : ℂ := -I * log (I * z + sqrtOneSub z)

/-- `D_B = {z : |z - i| ≤ 1/2}`. -/
def diskB : Set ℂ := Metric.closedBall I (1/2)

theorem sqrtOneSub_sq (z : ℂ) : sqrtOneSub z ^ 2 = 1 - z ^ 2 := by
  unfold sqrtOneSub
  rw [one_div, Complex.cpow_ofNat_inv_pow]

theorem cpow_half_re_nonneg (w : ℂ) : 0 ≤ (w ^ (1/2 : ℂ)).re := by
  by_cases hw : w = 0
  · rw [hw, Complex.zero_cpow (by norm_num)]; simp
  · rw [Complex.cpow_def_of_ne_zero hw, Complex.exp_re]
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_mem_Icc
    have h12 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
    have him : (Complex.log w * (1/2 : ℂ)).im = Complex.arg w / 2 := by
      rw [h12, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.log_im]
      ring
    rw [him]
    constructor
    · have := Complex.neg_pi_lt_arg w; linarith
    · have := Complex.arg_le_pi w; linarith

theorem one_sub_sq_re (z : ℂ) : (1 - z ^ 2).re = 1 - z.re ^ 2 + z.im ^ 2 := by
  simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re]
  ring

theorem one_sub_sq_im (z : ℂ) : (1 - z ^ 2).im = -(2 * z.re * z.im) := by
  simp only [Complex.sub_im, Complex.one_im, pow_two, Complex.mul_im]
  ring

theorem one_sub_sq_mem_slitPlane {z : ℂ} (hz : 0 < z.im) : 1 - z ^ 2 ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hx : z.re = 0
  · left
    rw [one_sub_sq_re, hx]; positivity
  · right
    rw [one_sub_sq_im]
    have : z.re * z.im ≠ 0 := mul_ne_zero hx hz.ne'
    intro h; apply this; linarith

theorem sqrtOneSub_ne_zero {z : ℂ} (hz : 0 < z.im) : sqrtOneSub z ≠ 0 := by
  intro h
  have h2 := sqrtOneSub_sq z
  rw [h, zero_pow two_ne_zero] at h2
  exact Complex.slitPlane_ne_zero (one_sub_sq_mem_slitPlane hz) h2.symm

/-- `(i z + s)(s - i z) = 1` with `s = (1 - z²)^{1/2}`. -/
theorem branch_product (z : ℂ) : (I * z + sqrtOneSub z) * (sqrtOneSub z - I * z) = 1 := by
  have h := sqrtOneSub_sq z
  linear_combination h - z ^ 2 * I_sq

/-- `i z + (1 - z²)^{1/2}` lies in the slit plane, for every `z`. -/
theorem branch_mem_slitPlane (z : ℂ) : I * z + sqrtOneSub z ∈ slitPlane := by
  have hab : (I * z + sqrtOneSub z) * (sqrtOneSub z - I * z) = 1 := branch_product z
  have hsum : sqrtOneSub z = ((I * z + sqrtOneSub z) + (sqrtOneSub z - I * z)) / 2 := by ring
  have hnn : 0 ≤ (sqrtOneSub z).re := cpow_half_re_nonneg (1 - z ^ 2)
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = I * z + sqrtOneSub z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = sqrtOneSub z - I * z := ⟨_, rfl⟩
  rw [← hA, ← hB] at hab hsum
  rw [← hA, Complex.mem_slitPlane_iff]
  by_contra hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  -- the number `A = i z + s` is a negative real number
  have hreal : A = ((A.re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, him]
  have hr0 : A.re ≠ 0 := by
    intro h0
    rw [hreal, h0, Complex.ofReal_zero, zero_mul] at hab
    exact zero_ne_one hab
  have hrneg : A.re < 0 := lt_of_le_of_ne hre hr0
  have hb : B = (((A.re)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, ← hreal]
    exact (inv_eq_of_mul_eq_one_right hab).symm
  have hBre : B.re = (A.re)⁻¹ := by rw [hb, Complex.ofReal_re]
  have hs : (sqrtOneSub z).re = (A.re + (A.re)⁻¹) / 2 := by
    rw [hsum, ← hBre, Complex.div_ofNat_re, Complex.add_re]
  have hneg : (A.re + (A.re)⁻¹) / 2 < 0 := by
    have : (A.re)⁻¹ < 0 := inv_lt_zero.mpr hrneg
    linarith
  rw [hs] at hnn
  linarith

theorem branch_ne_zero (z : ℂ) : I * z + sqrtOneSub z ≠ 0 :=
  Complex.slitPlane_ne_zero (branch_mem_slitPlane z)

/-- `H0` inverts the sine: `sin (H0 z) = z` (for every `z`; in particular on `D_B`). -/
theorem sin_H0 (z : ℂ) : Complex.sin (H0 z) = z := by
  have hne := branch_ne_zero z
  have hexp : Complex.exp (I * H0 z) = I * z + sqrtOneSub z := by
    unfold H0
    rw [show I * (-I * Complex.log (I * z + sqrtOneSub z)) = Complex.log (I * z + sqrtOneSub z) by
      linear_combination (-Complex.log (I * z + sqrtOneSub z)) * I_sq]
    exact Complex.exp_log hne
  have hexp' : Complex.exp (-(H0 z) * I) = sqrtOneSub z - I * z := by
    have h1 : Complex.exp (-(H0 z) * I) = (Complex.exp (I * H0 z))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [h1, hexp]
    exact inv_eq_of_mul_eq_one_right (branch_product z)
  rw [Complex.sin, show H0 z * I = I * H0 z by ring, hexp, hexp']
  linear_combination (-z) * I_sq

/-- `H0'(z) = (1 - z²)^{-1/2}` on the open upper half-plane. -/
theorem hasDerivAt_H0 {z : ℂ} (hz : 0 < z.im) : HasDerivAt H0 (1 / sqrtOneSub z) z := by
  have hw := one_sub_sq_mem_slitPlane hz
  have hs0 := sqrtOneSub_ne_zero hz
  have hw0 : (1 - z ^ 2) ≠ 0 := Complex.slitPlane_ne_zero hw
  have h1 : HasDerivAt (fun z : ℂ => 1 - z ^ 2) (-(2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).const_sub 1)
    simpa using this
  have h2 : HasDerivAt sqrtOneSub ((1/2 : ℂ) * (1 - z ^ 2) ^ ((1/2 : ℂ) - 1) * (-(2 * z))) z :=
    h1.cpow_const hw
  have hpow : (1 - z ^ 2) ^ ((1/2 : ℂ) - 1) = sqrtOneSub z / (1 - z ^ 2) := by
    rw [Complex.cpow_sub _ _ hw0, Complex.cpow_one]; rfl
  rw [hpow] at h2
  have h3 : HasDerivAt (fun z : ℂ => I * z + sqrtOneSub z)
      (I + (1/2 : ℂ) * (sqrtOneSub z / (1 - z ^ 2)) * (-(2 * z))) z := by
    have := ((hasDerivAt_id z).const_mul I).add h2
    simpa using this
  have h4 := (h3.clog (branch_mem_slitPlane z)).const_mul (-I)
  have hb := branch_ne_zero z
  have hsq := sqrtOneSub_sq z
  have hderiv : -I * ((I + (1/2 : ℂ) * (sqrtOneSub z / (1 - z ^ 2)) * (-(2 * z))) /
      (I * z + sqrtOneSub z)) = 1 / sqrtOneSub z := by
    rw [← hsq]
    have e1 : (1/2 : ℂ) * (sqrtOneSub z / sqrtOneSub z ^ 2) * (-(2 * z)) = -(z / sqrtOneSub z) := by
      field_simp <;> ring
    have e2 : I + -(z / sqrtOneSub z) = (I * sqrtOneSub z - z) / sqrtOneSub z := by
      field_simp <;> ring
    have e3 : -I * (I * sqrtOneSub z - z) = I * z + sqrtOneSub z := by
      linear_combination (-(sqrtOneSub z)) * I_sq
    rw [e1, e2, div_div, ← mul_div_assoc, e3, mul_comm (sqrtOneSub z) (I * z + sqrtOneSub z),
      ← div_div, div_self hb]
  exact h4.congr_deriv hderiv

theorem diskB_im {z : ℂ} (hz : z ∈ diskB) : 1/2 ≤ z.im := by
  unfold diskB at hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have h := Complex.abs_im_le_norm (z - I)
  have him : (z - I).im = z.im - 1 := by simp
  rw [him] at h
  have := abs_le.mp (h.trans hz)
  linarith [this.1]

theorem diskB_coords {z : ℂ} (hz : z ∈ diskB) : z.re ^ 2 + (z.im - 1) ^ 2 ≤ 1/4 := by
  unfold diskB at hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have h2 : ‖z - I‖ ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im] at h2
  nlinarith

/-- `|1 - z²| ≥ 5/4` on `D_B` (manuscript (eg:eq:lipschitz)). -/
theorem norm_one_sub_sq_ge {z : ℂ} (hz : z ∈ diskB) : 5/4 ≤ ‖1 - z ^ 2‖ := by
  have hb := EulerianGrothendieck.arcsin_disk_realpart_bound z.re z.im (diskB_coords hz)
  have hre := one_sub_sq_re z
  have := Complex.re_le_norm (1 - z ^ 2)
  nlinarith [sq_nonneg (z.im - 1/2)]

theorem norm_sqrtOneSub_sq (z : ℂ) : ‖sqrtOneSub z‖ ^ 2 = ‖1 - z ^ 2‖ := by
  rw [← norm_pow, sqrtOneSub_sq]

theorem sqrt5_div_two_eq : Real.sqrt 5 / 2 = Real.sqrt (5/4) := by
  rw [Real.sqrt_div' _ (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem norm_deriv_le {z : ℂ} (hz : z ∈ diskB) : ‖1 / sqrtOneSub z‖ ≤ 2 / Real.sqrt 5 := by
  have hs0 := sqrtOneSub_ne_zero (lt_of_lt_of_le (by norm_num) (diskB_im hz))
  have hpos : 0 < ‖sqrtOneSub z‖ := norm_pos_iff.mpr hs0
  have hge : Real.sqrt 5 / 2 ≤ ‖sqrtOneSub z‖ := by
    have h1 := norm_one_sub_sq_ge hz
    rw [← norm_sqrtOneSub_sq] at h1
    rw [sqrt5_div_two_eq]
    calc Real.sqrt (5/4) ≤ Real.sqrt (‖sqrtOneSub z‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = ‖sqrtOneSub z‖ := Real.sqrt_sq (norm_nonneg _)
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [norm_div, norm_one, div_le_div_iff₀ hpos h5]
  linarith

theorem half_I_mem : (I / 2 : ℂ) ∈ diskB := by
  unfold diskB
  rw [Metric.mem_closedBall, Complex.dist_eq]
  have : I / 2 - I = -(I / 2) := by ring
  rw [this, norm_neg, norm_div, Complex.norm_I]
  norm_num

theorem sqrtOneSub_half_I : sqrtOneSub (I / 2) = (Real.sqrt 5 / 2 : ℝ) := by
  unfold sqrtOneSub
  have h : (1 - (I / 2) ^ 2 : ℂ) = ((5/4 : ℝ) : ℂ) := by
    rw [div_pow, I_sq]; push_cast; ring
  have h12 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [h, h12, ← Complex.ofReal_cpow (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, sqrt5_div_two_eq]

theorem norm_deriv_half_I : ‖1 / sqrtOneSub (I / 2)‖ = 2 / Real.sqrt 5 := by
  rw [sqrtOneSub_half_I, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), one_div_div]

theorem deriv_H0 {z : ℂ} (hz : z ∈ diskB) : deriv H0 z = 1 / sqrtOneSub z :=
  (hasDerivAt_H0 (lt_of_lt_of_le (by norm_num) (diskB_im hz))).deriv

/-- **`sup_{z ∈ D_B} |H0'(z)| = 2/√5`**, attained at `z = i/2`. -/
theorem sup_norm_deriv_H0 :
    IsGreatest ((fun z => ‖deriv H0 z‖) '' diskB) (2 / Real.sqrt 5) := by
  constructor
  · refine ⟨I / 2, half_I_mem, ?_⟩
    show ‖deriv H0 (I / 2)‖ = 2 / Real.sqrt 5
    rw [deriv_H0 half_I_mem, norm_deriv_half_I]
  · rintro r ⟨z, hz, rfl⟩
    show ‖deriv H0 z‖ ≤ 2 / Real.sqrt 5
    rw [deriv_H0 hz]
    exact norm_deriv_le hz

theorem sSup_norm_deriv_H0 : sSup ((fun z => ‖deriv H0 z‖) '' diskB) = 2 / Real.sqrt 5 :=
  sup_norm_deriv_H0.csSup_eq

/-- Lipschitz upper bound on the convex disc `D_B`, by the mean value inequality. -/
theorem H0_lipschitz {z w : ℂ} (hz : z ∈ diskB) (hw : w ∈ diskB) :
    ‖H0 z - H0 w‖ ≤ 2 / Real.sqrt 5 * ‖z - w‖ := by
  have hconv : Convex ℝ diskB := convex_closedBall _ _
  exact hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := H0) (f' := fun x => 1 / sqrtOneSub x)
    (fun x hx => (hasDerivAt_H0 (lt_of_lt_of_le (by norm_num) (diskB_im hx))).hasDerivWithinAt)
    (fun x hx => norm_deriv_le hx) hw hz

/-- **Sharpness**: every Lipschitz constant of `H0` on `D_B` is at least `2/√5`. -/
theorem H0_lipschitz_sharp {L : ℝ}
    (hL : ∀ z ∈ diskB, ∀ w ∈ diskB, ‖H0 z - H0 w‖ ≤ L * ‖z - w‖) : 2 / Real.sqrt 5 ≤ L := by
  have hd : HasDerivAt H0 (1 / sqrtOneSub (I / 2)) (I / 2) :=
    hasDerivAt_H0 (by norm_num)
  -- the real path `h ↦ i/2 + i h`
  have hg : HasDerivAt (fun h : ℝ => I / 2 + I * (h : ℂ)) I 0 := by
    have := (((hasDerivAt_id (0:ℝ)).ofReal_comp).const_mul I).const_add (I / 2)
    simpa using this
  have hd' : HasDerivAt H0 (1 / sqrtOneSub (I / 2)) (I / 2 + I * ((0:ℝ) : ℂ)) := by
    simpa using hd
  have hcomp : HasDerivAt (fun h : ℝ => H0 (I / 2 + I * (h : ℂ))) (1 / sqrtOneSub (I / 2) * I) 0 :=
    HasDerivAt.comp (h₂ := H0) (h := fun h : ℝ => I / 2 + I * (h : ℂ)) (0:ℝ) hd' hg
  have hslope := hcomp.tendsto_slope_zero_right
  have hnorm := (continuous_norm.tendsto _).comp hslope
  have key : ‖1 / sqrtOneSub (I / 2) * I‖ ≤ L := by
    apply le_of_tendsto hnorm
    have hmem : ∀ᶠ h in 𝓝[>] (0:ℝ), h < 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with h hh using hh.2
    filter_upwards [self_mem_nhdsWithin, hmem] with h hpos h1
    have hpos' : 0 < h := hpos
    simp only [Function.comp, zero_add, Complex.ofReal_zero, mul_zero, add_zero]
    have hz : I / 2 + I * (h : ℂ) ∈ diskB := by
      unfold diskB
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have : I / 2 + I * (h : ℂ) - I = ((h - 1/2 : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]; constructor <;> linarith
    have hb := hL _ hz (I / 2) half_I_mem
    have hdist : I / 2 + I * (h : ℂ) - I / 2 = I * (h : ℂ) := by ring
    rw [hdist, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos'] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos', inv_mul_le_iff₀ hpos']
    linarith
  rwa [norm_mul, Complex.norm_I, mul_one, norm_deriv_half_I] at key

/-- The sharp Lipschitz constant: `2/√5` is the least `L` with
`|H0 z - H0 w| ≤ L|z - w|` on `D_B`. -/
theorem H0_lipschitz_constant :
    IsLeast {L : ℝ | ∀ z ∈ diskB, ∀ w ∈ diskB, ‖H0 z - H0 w‖ ≤ L * ‖z - w‖} (2 / Real.sqrt 5) :=
  ⟨fun z hz w hw => H0_lipschitz hz hw, fun _ hL => H0_lipschitz_sharp hL⟩

end EulerianGrothendieck.ArcsinDisk
