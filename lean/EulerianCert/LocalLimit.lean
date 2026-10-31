/-
# V001 §3.11, Eqs. (82)–(83): the Gaussian local limit law for the Eulerian distribution

With `D = n + 1`, `x_{n,k} = k/(n+1)`, `p_{n,k} = E(n,k−1)/n!` and
`G_D(x) = √(6/(πD)) exp(−6D(x − ½)²)` (module `Combinatorics`), we prove
* an explicit-rate local limit theorem: there is `K` with
  `|p_{n,k} − G_D(x_{n,k})| ≤ K D^{−3/2}` for all `n ≥ 1`, `k ≥ 1`;
* **Eq. (82)**: `p_{n,k} ∼ G_D(x_{n,k})` uniformly for `(k − D/2)/√D` in compact sets.
The proof is the Laplace method on the Fourier inversion formula (81) of `EulerianFourier`,
with the Taylor bounds `y − y³/6 ≤ sin y ≤ y − y³/6 + y⁵/120` (`y ≥ 0`) giving
`e^{−t²/24 − t⁴/288} ≤ r_E(t) ≤ e^{−t²/24 + t⁴/1920}` for `|t| ≤ 1`, `|r_E(t)| ≤ 24/25` for
`|t| ≥ 1`, and Mathlib's Fourier transform of the Gaussian.
-/
import EulerianCert.EulerianFourier
import EulerianCert.Combinatorics
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecificLimits.Normed

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace EulerianCert.LocalLimit

local notation "rE" => EulerianCert.FourierModes.rE

/-! ### Taylor inequalities -/

/-- `f(0) = 0` and `f' ≥ 0` on `[0, ∞)` give `f ≥ 0` on `[0, ∞)`. -/
lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [interior_Ici] at hy
    rw [(hf y).deriv]
    exact hd y (le_of_lt hy)
  have := hmono (Set.self_mem_Ici) hx hx
  rwa [h0] at this

lemma sin_ge {y : ℝ} (hy : 0 ≤ y) : y - y ^ 3 / 6 ≤ Real.sin y := by
  have := nonneg_of_deriv_nonneg (f := fun y => Real.sin y - y + y ^ 3 / 6)
    (f' := fun y => Real.cos y - 1 + y ^ 2 / 2)
    (fun x => by
      have := ((hasDerivAt_sin x).sub (hasDerivAt_id' x)).add ((hasDerivAt_pow 3 x).div_const 6)
      convert this using 1; push_cast; ring)
    (by simp) (fun x _ => by have := one_sub_sq_div_two_le_cos (x := x); linarith) hy
  linarith

lemma cos_le {y : ℝ} (hy : 0 ≤ y) : Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
  have := nonneg_of_deriv_nonneg (f := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
    (f' := fun y => -y + y ^ 3 / 6 + Real.sin y)
    (fun x => by
      have := ((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 4 x).div_const 24)).sub (hasDerivAt_cos x))
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := sin_ge hx; linarith) hy
  linarith

lemma sin_le {y : ℝ} (hy : 0 ≤ y) : Real.sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 120 := by
  have := nonneg_of_deriv_nonneg (f := fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y)
    (f' := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
    (fun x => by
      have := ((((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
        ((hasDerivAt_pow 5 x).div_const 120)).sub (hasDerivAt_sin x))
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := cos_le hx; linarith) hy
  linarith

/-! ### Bounds for `r_E(t) = sin(t/2)/(t/2)` -/

lemma rE_eq_abs (t : ℝ) (ht : t ≠ 0) : rE t = Real.sin (|t| / 2) / (|t| / 2) := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [← EulerianCert.FourierModes.rE_neg, EulerianCert.FourierModes.rE_of_ne_zero (by linarith),
      abs_of_neg h]
    field_simp
  · rw [EulerianCert.FourierModes.rE_of_ne_zero ht, abs_of_pos h]; field_simp

lemma rE_ge (t : ℝ) : 1 - t ^ 2 / 24 ≤ rE t := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [EulerianCert.FourierModes.rE]
  · rw [rE_eq_abs t h]
    have hy : 0 < |t| / 2 := by positivity
    rw [le_div_iff₀ hy]
    have := sin_ge hy.le
    have : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith

lemma rE_le (t : ℝ) : rE t ≤ 1 - t ^ 2 / 24 + t ^ 4 / 1920 := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [EulerianCert.FourierModes.rE]
  · rw [rE_eq_abs t h]
    have hy : 0 < |t| / 2 := by positivity
    rw [div_le_iff₀ hy]
    have := sin_le hy.le
    have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
    have h4 : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← pow_mul]
    nlinarith

lemma rE_nonneg {t : ℝ} (ht : |t| ≤ 2 * π) : 0 ≤ rE t := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [EulerianCert.FourierModes.rE]
  · rw [rE_eq_abs t h]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith))
      (by positivity)

/-- `e^{−a} ≤ 1 − y` for `a = y + 2y²`, `0 ≤ y ≤ 1/2`. -/
lemma exp_le_one_sub {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) : Real.exp (-(y + 2 * y ^ 2)) ≤ 1 - y := by
  have h := Real.add_one_le_exp (y + 2 * y ^ 2)
  have hpos : 0 < y + 2 * y ^ 2 + 1 := by positivity
  rw [Real.exp_neg]
  calc (Real.exp (y + 2 * y ^ 2))⁻¹ ≤ (y + 2 * y ^ 2 + 1)⁻¹ := inv_anti₀ hpos h
    _ ≤ 1 - y := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) (by linarith : (0 : ℝ) ≤ 1 - 2 * y)]

lemma rE_lower_exp {t : ℝ} (ht : |t| ≤ 1) : Real.exp (-(t ^ 2 / 24 + t ^ 4 / 288)) ≤ rE t := by
  have ht2 : t ^ 2 ≤ 1 := by
    have := sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2; simpa using this
  have := exp_le_one_sub (y := t ^ 2 / 24) (by positivity) (by linarith)
  have e : t ^ 2 / 24 + 2 * (t ^ 2 / 24) ^ 2 = t ^ 2 / 24 + t ^ 4 / 288 := by ring
  rw [e] at this
  exact this.trans (rE_ge t)

lemma rE_upper_exp (t : ℝ) : rE t ≤ Real.exp (-(t ^ 2 / 24) + t ^ 4 / 1920) := by
  have := Real.add_one_le_exp (-(t ^ 2 / 24) + t ^ 4 / 1920)
  linarith [rE_le t]

lemma abs_rE_le_far {t : ℝ} (ht : 1 ≤ |t|) : |rE t| ≤ 24 / 25 := by
  by_cases h2 : |t| ≤ 2 * π
  · rw [abs_of_nonneg (rE_nonneg h2)]
    refine (rE_le t).trans ?_
    have hs1 : 1 ≤ t ^ 2 := by
      have := mul_le_mul ht ht zero_le_one (abs_nonneg _); rwa [one_mul, ← sq, sq_abs] at this
    have hs2 : t ^ 2 ≤ 79 := by
      have h2' : |t| ≤ 7 := h2.trans (by linarith [pi_lt_d2])
      have := mul_le_mul h2' h2' (abs_nonneg _) (by norm_num)
      rw [← sq, sq_abs] at this; linarith
    have : t ^ 4 = (t ^ 2) ^ 2 := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hs2)]
  · push Not at h2
    have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
    refine (EulerianCert.EulerianFourier.abs_rE_le t ht0).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pi_gt_three]

/-! ### Pointwise comparison with the Gaussian -/

/-- The dominating function of `|r_E^D − e^{−Dt²/24}|`. -/
def H (D : ℕ) (t : ℝ) : ℝ :=
  (D : ℝ) / 288 * (t ^ 4 * Real.exp (-((D : ℝ) / 48) * t ^ 2)) +
    (24 / 25 : ℝ) ^ (D - 2) * (8 * (4 + t ^ 2)⁻¹) +
    Real.exp (-((D : ℝ) / 48)) * Real.exp (-((D : ℝ) / 48) * t ^ 2)

lemma H_terms_nonneg (D : ℕ) (t : ℝ) :
    0 ≤ (D : ℝ) / 288 * (t ^ 4 * Real.exp (-((D : ℝ) / 48) * t ^ 2)) ∧
    0 ≤ (24 / 25 : ℝ) ^ (D - 2) * (8 * (4 + t ^ 2)⁻¹) ∧
    0 ≤ Real.exp (-((D : ℝ) / 48)) * Real.exp (-((D : ℝ) / 48) * t ^ 2) :=
  ⟨by positivity, by positivity, by positivity⟩

lemma pointwise {D : ℕ} (hD : 2 ≤ D) (t : ℝ) :
    |rE t ^ D - Real.exp (-((D : ℝ) / 24) * t ^ 2)| ≤ H D t := by
  obtain ⟨h1, h2, h3⟩ := H_terms_nonneg D t
  set g := Real.exp (-((D : ℝ) / 24) * t ^ 2)
  have hDr : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  by_cases ht : |t| ≤ 1
  · have ht2 : t ^ 2 ≤ 1 := by
      have := sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2; simpa using this
    have ht4 : t ^ 4 ≤ t ^ 2 := by
      rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring]
      exact mul_le_of_le_one_right (sq_nonneg t) ht2
    set a := (D : ℝ) * t ^ 4 / 288
    set b := (D : ℝ) * t ^ 4 / 1920
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have hab : b ≤ a := by
      simp only [a, b]; apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
    -- the two exponential bounds for `r_E^D`
    have hlow : g * Real.exp (-a) ≤ rE t ^ D := by
      have := pow_le_pow_left₀ (Real.exp_pos _).le (rE_lower_exp ht) D
      rw [← Real.exp_nat_mul] at this
      refine le_trans (le_of_eq ?_) this
      simp only [g, a]; rw [← Real.exp_add]; congr 1; ring
    have hup : rE t ^ D ≤ g * Real.exp b := by
      have := pow_le_pow_left₀ (rE_nonneg (ht.trans (by linarith [pi_gt_three])))
        (rE_upper_exp t) D
      rw [← Real.exp_nat_mul] at this
      refine this.trans (le_of_eq ?_)
      simp only [g, b]; rw [← Real.exp_add]; congr 1; ring
    have hgb : g * Real.exp b ≤ Real.exp (-((D : ℝ) / 48) * t ^ 2) := by
      simp only [g, b]; rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left ht4 hDr]
    have hg48 : g ≤ Real.exp (-((D : ℝ) / 48) * t ^ 2) := by
      simp only [g]; apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg t]
    have hE1 : Real.exp b - 1 ≤ b * Real.exp b := by
      have := Real.add_one_le_exp (-b)
      have hpos := Real.exp_pos b
      have : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have hE2 : 1 - Real.exp (-a) ≤ a := by linarith [Real.add_one_le_exp (-a)]
    have hgpos : 0 < g := Real.exp_pos _
    rw [abs_le]
    constructor
    · -- `g − r^D ≤ g (1 − e^{−a}) ≤ a g`
      have : g - rE t ^ D ≤ a * Real.exp (-((D : ℝ) / 48) * t ^ 2) := by
        have := mul_le_mul_of_nonneg_left hE2 hgpos.le
        nlinarith [mul_le_mul_of_nonneg_left hg48 ha]
      have e : a * Real.exp (-((D : ℝ) / 48) * t ^ 2) =
          (D : ℝ) / 288 * (t ^ 4 * Real.exp (-((D : ℝ) / 48) * t ^ 2)) := by simp only [a]; ring
      unfold H; linarith
    · -- `r^D − g ≤ g (e^b − 1) ≤ b g e^b`
      have : rE t ^ D - g ≤ a * Real.exp (-((D : ℝ) / 48) * t ^ 2) := by
        have h5 : rE t ^ D - g ≤ g * (Real.exp b - 1) := by nlinarith
        have h6 : g * (Real.exp b - 1) ≤ b * (g * Real.exp b) := by
          have := mul_le_mul_of_nonneg_left hE1 hgpos.le; nlinarith
        have h7 : b * (g * Real.exp b) ≤ a * Real.exp (-((D : ℝ) / 48) * t ^ 2) :=
          mul_le_mul hab hgb (by positivity) ha
        linarith
      have e : a * Real.exp (-((D : ℝ) / 48) * t ^ 2) =
          (D : ℝ) / 288 * (t ^ 4 * Real.exp (-((D : ℝ) / 48) * t ^ 2)) := by simp only [a]; ring
      unfold H; linarith
  · push Not at ht
    have hr := abs_rE_le_far ht.le
    have hr2 : |rE t| ^ (1 + 1) ≤ 8 * (4 + t ^ 2)⁻¹ :=
      EulerianCert.EulerianFourier.pow_rE_le (n := 1) le_rfl t
    have hpow : |rE t| ^ D ≤ (24 / 25 : ℝ) ^ (D - 2) * (8 * (4 + t ^ 2)⁻¹) := by
      rw [show D = (D - 2) + (1 + 1) by omega, pow_add, show D - 2 + (1 + 1) - 2 = D - 2 by omega]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hr _) hr2 (by positivity) (by positivity)
    have ht2 : 1 ≤ t ^ 2 := by
      have := mul_le_mul ht.le ht.le zero_le_one (abs_nonneg _); rwa [one_mul, ← sq, sq_abs] at this
    have hg : g ≤ Real.exp (-((D : ℝ) / 48)) * Real.exp (-((D : ℝ) / 48) * t ^ 2) := by
      simp only [g]; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    calc |rE t ^ D - g| ≤ |rE t ^ D| + |g| := abs_sub _ _
      _ = |rE t| ^ D + g := by rw [abs_pow, abs_of_pos (Real.exp_pos _)]
      _ ≤ H D t := by unfold H; linarith

/-! ### Gaussian integrals -/

lemma integrable_pow4_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => t ^ 4 * Real.exp (-b * t ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 4) (by norm_num)
  refine this.congr (Eventually.of_forall (fun t => ?_))
  beta_reduce
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `M₄ = ∫ s⁴ e^{−s²} ds`. -/
def M4 : ℝ := ∫ s : ℝ, s ^ 4 * Real.exp (-1 * s ^ 2)

lemma integral_pow4_gauss {b : ℝ} (hb : 0 < b) :
    ∫ t : ℝ, t ^ 4 * Real.exp (-b * t ^ 2) = M4 / (b ^ 2 * √b) := by
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  have h := Measure.integral_comp_mul_left (fun s : ℝ => s ^ 4 * Real.exp (-1 * s ^ 2)) (√b)
  have e : (fun x : ℝ => (√b * x) ^ 4 * Real.exp (-1 * (√b * x) ^ 2)) =
      fun x => b ^ 2 * (x ^ 4 * Real.exp (-b * x ^ 2)) := by
    funext x
    have : √b ^ 2 = b := Real.sq_sqrt hb.le
    rw [mul_pow, mul_pow, show √b ^ 4 = (√b ^ 2) ^ 2 by ring, this]; ring_nf
  rw [e, integral_const_mul, abs_of_pos (inv_pos.mpr hsb), smul_eq_mul] at h
  unfold M4
  rw [eq_div_iff (by positivity)]
  calc (∫ t : ℝ, t ^ 4 * Real.exp (-b * t ^ 2)) * (b ^ 2 * √b)
      = (b ^ 2 * ∫ t : ℝ, t ^ 4 * Real.exp (-b * t ^ 2)) * √b := by ring
    _ = ((√b)⁻¹ * ∫ s : ℝ, s ^ 4 * Real.exp (-1 * s ^ 2)) * √b := by rw [h]
    _ = ∫ s : ℝ, s ^ 4 * Real.exp (-1 * s ^ 2) := by field_simp

/-- `∫ 8/(4 + t²) dt`. -/
def J8 : ℝ := ∫ t : ℝ, 8 * (4 + t ^ 2)⁻¹

lemma integrable_J8 : Integrable (fun t : ℝ => 8 * (4 + t ^ 2)⁻¹) := by
  have := (integrable_inv_one_add_sq.comp_mul_left' (show (1 / 2 : ℝ) ≠ 0 by norm_num)).const_mul 2
  refine this.congr (Eventually.of_forall (fun t => ?_))
  beta_reduce
  field_simp
  ring

lemma integrable_H {D : ℕ} (hD : 1 ≤ D) : Integrable (H D) := by
  have hb : (0 : ℝ) < (D : ℝ) / 48 := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    positivity
  unfold H
  exact (((integrable_pow4_gauss hb).const_mul _).add (integrable_J8.const_mul _)).add
    ((integrable_exp_neg_mul_sq hb).const_mul _)

lemma integral_H {D : ℕ} (hD : 1 ≤ D) :
    ∫ t, H D t = (D : ℝ) / 288 * (M4 / (((D : ℝ) / 48) ^ 2 * √((D : ℝ) / 48))) +
      (24 / 25 : ℝ) ^ (D - 2) * J8 + Real.exp (-((D : ℝ) / 48)) * √(π / ((D : ℝ) / 48)) := by
  have hb : (0 : ℝ) < (D : ℝ) / 48 := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    positivity
  unfold H
  have i1 : Integrable (fun t : ℝ => (D : ℝ) / 288 * (t ^ 4 * Real.exp (-((D : ℝ) / 48) * t ^ 2))) :=
    (integrable_pow4_gauss hb).const_mul _
  have i2 : Integrable (fun t : ℝ => (24 / 25 : ℝ) ^ (D - 2) * (8 * (4 + t ^ 2)⁻¹)) :=
    integrable_J8.const_mul _
  have i3 : Integrable (fun t : ℝ => Real.exp (-((D : ℝ) / 48)) *
      Real.exp (-((D : ℝ) / 48) * t ^ 2)) := (integrable_exp_neg_mul_sq hb).const_mul _
  have i12 : Integrable (fun t : ℝ => (D : ℝ) / 288 * (t ^ 4 * Real.exp (-((D : ℝ) / 48) * t ^ 2)) +
      (24 / 25 : ℝ) ^ (D - 2) * (8 * (4 + t ^ 2)⁻¹)) := i1.add i2
  have e1 : ∫ t : ℝ, (D : ℝ) / 288 * (t ^ 4 * Real.exp (-((D : ℝ) / 48) * t ^ 2)) =
      (D : ℝ) / 288 * (M4 / (((D : ℝ) / 48) ^ 2 * √((D : ℝ) / 48))) := by
    rw [integral_const_mul, integral_pow4_gauss hb]
  have e2 : ∫ t : ℝ, (24 / 25 : ℝ) ^ (D - 2) * (8 * (4 + t ^ 2)⁻¹) = (24 / 25 : ℝ) ^ (D - 2) * J8 :=
    integral_const_mul _ _
  have e3 : ∫ t : ℝ, Real.exp (-((D : ℝ) / 48)) * Real.exp (-((D : ℝ) / 48) * t ^ 2) =
      Real.exp (-((D : ℝ) / 48)) * √(π / ((D : ℝ) / 48)) := by
    rw [integral_const_mul, integral_gaussian]
  rw [integral_add i12 i3, integral_add i1 i2, e1, e2, e3]

/-- `∫ e^{−bt²} cos(tu) dt = √(π/b) e^{−u²/(4b)}`. -/
lemma gauss_cos {b : ℝ} (hb : 0 < b) (u : ℝ) :
    ∫ t : ℝ, Real.exp (-b * t ^ 2) * Real.cos (t * u) = √(π / b) * Real.exp (-u ^ 2 / (4 * b)) := by
  have hbc : 0 < (b : ℂ).re := by simpa using hb
  have h := fourierIntegral_gaussian hbc (u : ℂ)
  have hint : Integrable (fun x : ℝ => Complex.exp (Complex.I * u * x) * Complex.exp (-b * x ^ 2)) := by
    refine (integrable_exp_neg_mul_sq hb).mono' ?_ (Eventually.of_forall (fun x => ?_))
    · exact (by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (Complex.I * u * x) * Complex.exp (-b * x ^ 2)).aestronglyMeasurable
    · rw [norm_mul, show Complex.I * (u : ℂ) * (x : ℂ) = ((u * x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp]
      apply le_of_eq; congr 1
      rw [show -(b : ℂ) * (x : ℂ) ^ 2 = ((-b * x ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hre := congrArg Complex.re h
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint] at hre
  have lhs : ∀ x : ℝ, Complex.reCLM (Complex.exp (Complex.I * u * x) * Complex.exp (-b * x ^ 2)) =
      Real.exp (-b * x ^ 2) * Real.cos (x * u) := by
    intro x
    rw [Complex.reCLM_apply, show Complex.I * (u : ℂ) * (x : ℂ) = ((x * u : ℝ) : ℂ) * Complex.I by
      push_cast; ring, show -(b : ℂ) * (x : ℂ) ^ 2 = ((-b * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
    ring
  simp_rw [lhs] at hre
  rw [hre]
  have hpb : (0 : ℝ) ≤ π / b := by positivity
  rw [show ((π : ℂ) / (b : ℂ)) = ((π / b : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hpb,
    show -(u : ℂ) ^ 2 / (4 * (b : ℂ)) = ((-u ^ 2 / (4 * b) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re, Real.sqrt_eq_rpow]

/-! ### The error integral is `O(D^{−3/2})` -/

lemma pow_mul_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ c, ∀ D : ℕ, (D : ℝ) ^ 2 * r ^ D ≤ c := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (by rwa [abs_of_nonneg hr0])
  obtain ⟨c, hc⟩ := h.bddAbove_range
  exact ⟨c, fun D => hc ⟨D, rfl⟩⟩

lemma M4_nonneg : 0 ≤ M4 := integral_nonneg (fun s => by positivity)

lemma J8_nonneg : 0 ≤ J8 := integral_nonneg (fun s => by positivity)

theorem error_bound : ∃ K, ∀ D : ℕ, 2 ≤ D → ∫ t, H D t ≤ K / (D * √D) := by
  obtain ⟨c1, hc1⟩ := pow_mul_bound (r := 24 / 25) (by norm_num) (by norm_num)
  obtain ⟨c2, hc2⟩ := pow_mul_bound (r := Real.exp (-(1 / 48))) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by norm_num))
  have hc1n : 0 ≤ c1 := by have := hc1 0; simpa using this
  have hc2n : 0 ≤ c2 := by have := hc2 0; simpa using this
  refine ⟨M4 * 48 ^ 2 * √48 / 288 + (25 / 24) ^ 2 * c1 * J8 + √(48 * π) * c2, fun D hD => ?_⟩
  have hD1 : 1 ≤ D := by omega
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hs : 0 < √(D : ℝ) := Real.sqrt_pos.mpr hDpos
  have hss : √(D : ℝ) ^ 2 = D := Real.sq_sqrt hDpos.le
  have hsD : √(D : ℝ) ≤ D := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hq : 0 < (D : ℝ) * √D := by positivity
  rw [integral_H hD1]
  -- first term
  have t1 : (D : ℝ) / 288 * (M4 / (((D : ℝ) / 48) ^ 2 * √((D : ℝ) / 48))) =
      (M4 * 48 ^ 2 * √48 / 288) / (D * √D) := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 48)]
    have h48 : 0 < √(48 : ℝ) := by positivity
    field_simp
  -- second term
  have t2 : (24 / 25 : ℝ) ^ (D - 2) * J8 ≤ (25 / 24) ^ 2 * c1 * J8 / (D * √D) := by
    have hpow : (24 / 25 : ℝ) ^ (D - 2) = (25 / 24) ^ 2 * (24 / 25 : ℝ) ^ D := by
      rw [show D = (D - 2) + 2 by omega, pow_add, show D - 2 + 2 - 2 = D - 2 by omega]
      ring
    have hb := hc1 D
    rw [hpow, le_div_iff₀ hq]
    have : (24 / 25 : ℝ) ^ D * (D * √D) ≤ c1 := by
      calc (24 / 25 : ℝ) ^ D * (D * √D) ≤ (24 / 25 : ℝ) ^ D * (D * D) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsD hDpos.le) (by positivity)
        _ = (D : ℝ) ^ 2 * (24 / 25) ^ D := by ring
        _ ≤ c1 := hb
    have hJ := J8_nonneg
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (25 / 24) ^ 2 * J8)]
  -- third term
  have t3 : Real.exp (-((D : ℝ) / 48)) * √(π / ((D : ℝ) / 48)) ≤ √(48 * π) * c2 / (D * √D) := by
    have he : Real.exp (-((D : ℝ) / 48)) = Real.exp (-(1 / 48)) ^ D := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hsq : √(π / ((D : ℝ) / 48)) = √(48 * π) / √D := by
      rw [show π / ((D : ℝ) / 48) = 48 * π / D by field_simp, Real.sqrt_div' _ hDpos.le]
    rw [he, hsq, le_div_iff₀ hq]
    have hb := hc2 D
    have h48 : 0 ≤ √(48 * π) := Real.sqrt_nonneg _
    have : Real.exp (-(1 / 48)) ^ D * D ≤ c2 := by
      calc Real.exp (-(1 / 48)) ^ D * D ≤ Real.exp (-(1 / 48)) ^ D * D ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
        _ = (D : ℝ) ^ 2 * Real.exp (-(1 / 48)) ^ D := by ring
        _ ≤ c2 := hb
    calc Real.exp (-(1 / 48)) ^ D * (√(48 * π) / √D) * (D * √D)
        = √(48 * π) * (Real.exp (-(1 / 48)) ^ D * D) := by field_simp
      _ ≤ √(48 * π) * c2 := mul_le_mul_of_nonneg_left this h48
  rw [t1]
  have := add_le_add (add_le_add (le_refl ((M4 * 48 ^ 2 * √48 / 288) / (D * √D))) t2) t3
  refine this.trans (le_of_eq ?_)
  field_simp

/-! ### The local limit theorem -/

lemma integrable_gauss_cos {b : ℝ} (hb : 0 < b) (u : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-b * t ^ 2) * Real.cos (t * u)) :=
  (integrable_exp_neg_mul_sq hb).mul_bdd (c := 1)
    ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _))

/-- The Gaussian profile `G_D(x_{n,k})` as a Gaussian Fourier integral. -/
lemma G_eq {n k : ℕ} :
    EulerianCert.Combinatorics.G ((n : ℝ) + 1) ((k : ℝ) / ((n : ℝ) + 1)) =
      1 / (2 * π) * ∫ t : ℝ, Real.exp (-(((n + 1 : ℕ) : ℝ) / 24) * t ^ 2) *
        Real.cos (t * ((k : ℝ) - ((n : ℝ) + 1) / 2)) := by
  have hD : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [gauss_cos (by push_cast; positivity)]
  unfold EulerianCert.Combinatorics.G
  push_cast
  have hexp : -6 * ((n : ℝ) + 1) * ((k : ℝ) / ((n : ℝ) + 1) - 1 / 2) ^ 2 =
      -((k : ℝ) - ((n : ℝ) + 1) / 2) ^ 2 / (4 * (((n : ℝ) + 1) / 24)) := by
    field_simp; ring
  rw [hexp]
  have hsq : √(π / (((n : ℝ) + 1) / 24)) = 2 * π * √(6 / (π * ((n : ℝ) + 1))) := by
    rw [show π / (((n : ℝ) + 1) / 24) = (2 * π) ^ 2 * (6 / (π * ((n : ℝ) + 1))) by
      field_simp; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsq]
  field_simp

/-- **Local limit theorem with rate**: `|p_{n,k} − G_D(x_{n,k})| ≤ K D^{−3/2}` for all
`n ≥ 1`, `k ≥ 1` (`D = n + 1`). -/
theorem local_limit_rate : ∃ K, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    |(EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial -
      EulerianCert.Combinatorics.G ((n : ℝ) + 1) ((k : ℝ) / ((n : ℝ) + 1))| ≤
      K / (((n : ℝ) + 1) * √((n : ℝ) + 1)) := by
  obtain ⟨K, hK⟩ := error_bound
  refine ⟨K / (2 * π), fun n k hn hk => ?_⟩
  set D := n + 1 with hDdef
  have hD : 2 ≤ D := by omega
  set u : ℝ := (k : ℝ) - ((n : ℝ) + 1) / 2
  have hb : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / 24 := by positivity
  rw [EulerianCert.EulerianFourier.eulerian_fourier_inversion hn hk, G_eq, ← mul_sub,
    ← integral_sub (EulerianCert.EulerianFourier.integrable_pow_rE_mul_cos hn u)
      (integrable_gauss_cos hb u)]
  have hbound : ‖∫ t : ℝ, (rE t ^ (n + 1) * Real.cos (t * u) -
      Real.exp (-(((n + 1 : ℕ) : ℝ) / 24) * t ^ 2) * Real.cos (t * u))‖ ≤ ∫ t, H D t := by
    apply norm_integral_le_of_norm_le (integrable_H (by omega))
    refine Eventually.of_forall (fun t => ?_)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    calc |rE t ^ (n + 1) - Real.exp (-(((n + 1 : ℕ) : ℝ) / 24) * t ^ 2)| * |Real.cos (t * u)|
        ≤ |rE t ^ (n + 1) - Real.exp (-(((n + 1 : ℕ) : ℝ) / 24) * t ^ 2)| * 1 :=
          mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
      _ ≤ H D t := by rw [mul_one]; exact pointwise hD t
  have hK' := hK D hD
  rw [Real.norm_eq_abs] at hbound
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  have hDcast : ((D : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast [hDdef]; ring
  rw [hDcast] at hK'
  calc 1 / (2 * π) * |∫ t : ℝ, (rE t ^ (n + 1) * Real.cos (t * u) -
        Real.exp (-(((n + 1 : ℕ) : ℝ) / 24) * t ^ 2) * Real.cos (t * u))|
      ≤ 1 / (2 * π) * (K / (((n : ℝ) + 1) * √((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (hbound.trans hK') (by positivity)
    _ = K / (2 * π) / (((n : ℝ) + 1) * √((n : ℝ) + 1)) := by ring

/-- **Eq. (82)**: `p_{n,k} ∼ G_D(x_{n,k})` uniformly for `(k − D/2)/√D` in compact sets:
for every `C` and `ε > 0` there is `N` such that `|p_{n,k}/G_D(x_{n,k}) − 1| ≤ ε` whenever
`n ≥ N` and `|k − D/2| ≤ C√D`. -/
theorem local_limit (C : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → 1 ≤ n → 1 ≤ k →
    |(k : ℝ) - ((n : ℝ) + 1) / 2| ≤ C * √((n : ℝ) + 1) →
    |(EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial /
      EulerianCert.Combinatorics.G ((n : ℝ) + 1) ((k : ℝ) / ((n : ℝ) + 1)) - 1| ≤ ε := by
  obtain ⟨K, hK⟩ := local_limit_rate
  set A : ℝ := |K| * Real.exp (6 * C ^ 2) / √(6 / π)
  obtain ⟨N, hN⟩ := exists_nat_gt (A / ε)
  refine ⟨N, fun n k hNn hn hk hu => ?_⟩
  set Dr : ℝ := (n : ℝ) + 1
  have hDr : 0 < Dr := by positivity
  have hsD : 0 < √Dr := Real.sqrt_pos.mpr hDr
  set Gv := EulerianCert.Combinatorics.G Dr ((k : ℝ) / Dr)
  -- lower bound for `G`
  have hG : √(6 / π) / √Dr * Real.exp (-(6 * C ^ 2)) ≤ Gv := by
    simp only [Gv, EulerianCert.Combinatorics.G]
    rw [show √(6 / (π * Dr)) = √(6 / π) / √Dr by
      rw [show 6 / (π * Dr) = (6 / π) / Dr by field_simp, Real.sqrt_div' _ hDr.le]]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hu2 : ((k : ℝ) - Dr / 2) ^ 2 ≤ C ^ 2 * Dr := by
      have := sq_le_sq' (abs_le.mp hu).1 (abs_le.mp hu).2
      rw [mul_pow, Real.sq_sqrt hDr.le] at this; exact this
    have : -6 * Dr * ((k : ℝ) / Dr - 1 / 2) ^ 2 = -6 * ((k : ℝ) - Dr / 2) ^ 2 / Dr := by
      field_simp
    rw [this, neg_mul, neg_div, neg_le_neg_iff, div_le_iff₀ hDr]
    linarith
  have hGpos : 0 < Gv := lt_of_lt_of_le (by positivity) hG
  have hrate := hK n k hn hk
  rw [show (EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial / Gv - 1 =
    ((EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial - Gv) / Gv by field_simp,
    abs_div, abs_of_pos hGpos, div_le_iff₀ hGpos]
  have hNr : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hAε : A < ε * Dr := by
    have := (div_lt_iff₀ hε).mp hN
    nlinarith
  calc |(EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial - Gv| ≤ K / (Dr * √Dr) := hrate
    _ ≤ |K| / (Dr * √Dr) := div_le_div_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ ε * (√(6 / π) / √Dr * Real.exp (-(6 * C ^ 2))) := by
        rw [div_le_iff₀ (by positivity)]
        have hexp : Real.exp (-(6 * C ^ 2)) * Real.exp (6 * C ^ 2) = 1 := by
          rw [← Real.exp_add]; simp
        have h6 : 0 < √(6 / π) := Real.sqrt_pos.mpr (by positivity)
        have hA : A * √(6 / π) = |K| * Real.exp (6 * C ^ 2) := by
          simp only [A]; field_simp
        have := mul_le_mul_of_nonneg_left hAε.le (by positivity :
          (0 : ℝ) ≤ √(6 / π) * Real.exp (-(6 * C ^ 2)))
        calc |K| = |K| * Real.exp (6 * C ^ 2) * Real.exp (-(6 * C ^ 2)) := by
              rw [mul_assoc, mul_comm (Real.exp _), hexp, mul_one]
          _ = A * √(6 / π) * Real.exp (-(6 * C ^ 2)) := by rw [hA]
          _ ≤ ε * Dr * √(6 / π) * Real.exp (-(6 * C ^ 2)) := by nlinarith
          _ = ε * (√(6 / π) / √Dr * Real.exp (-(6 * C ^ 2))) * (Dr * √Dr) := by
              field_simp
    _ ≤ ε * Gv := mul_le_mul_of_nonneg_left hG hε.le

end EulerianCert.LocalLimit
