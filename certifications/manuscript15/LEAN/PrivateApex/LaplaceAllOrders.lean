import PrivateApex.LogSincSeries
import PrivateApex.OddSecondOrder
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
PRIVATE.  The Laplace expansion of `∫₀^∞ u² |sin u / u|^(N+2) du` to every order.

With `M = N + 2` and `hm M 1 = ∫₀^∞ u² e^(-M u²/6) du`,

  `∫₀^∞ u² |sin u / u|^M du = hm M 1 * (∑ j < p, cC j / M ^ j + O(M ^ (-p)))`

for every `p` (`laplace_all_orders`).  The rational coefficients are

  `cC j = ∑ k ≤ j, (-1)^k / k! * [z^(j-k)] κ(z)^k * 3^(j+k) (2j+2k+1)!!`,

where `κ` is the series `kapC` of `(-log (sin u / u) - u²/6) / u⁴` in powers of `u²`.

The proof uses: the sharp remainder of the alternating exponential series
(`exp_neg_taylor`), a Watson-type lemma on `[0, 1]` (`watson_normalized`), ASTRA's Gaussian
majorant on `[1, π]` and the bound `|sin u / u| ≤ 1 / u` beyond `π`.
-/

namespace PrivateApex
open Real Finset MeasureTheory
open EulerianCert.LocalLimit (nonneg_of_deriv_nonneg)
open EulerianCert.CentralSlope (Mom_one)

/-! ### The exponential series with its alternating remainder -/

/-- Partial sums of the series of `exp (-t)`. -/
noncomputable def expNegSum (p : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range p, t ^ k * ((-1) ^ k / (k.factorial : ℝ))

theorem hasDerivAt_expNegSum (p : ℕ) (t : ℝ) :
    HasDerivAt (expNegSum (p + 1)) (-expNegSum p t) t := by
  have h : ∀ k ∈ range p,
      HasDerivAt (fun s : ℝ => s ^ (k + 1) * ((-1) ^ (k + 1) / ((k + 1).factorial : ℝ)))
        (-(t ^ k * ((-1) ^ k / (k.factorial : ℝ)))) t := by
    intro k _
    have h1 := (hasDerivAt_pow (k + 1) t).mul_const
      ((-1 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ))
    convert h1 using 1
    rw [Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  have e : expNegSum (p + 1) = fun s =>
      (∑ k ∈ range p, s ^ (k + 1) * ((-1) ^ (k + 1) / ((k + 1).factorial : ℝ))) + 1 := by
    funext s
    unfold expNegSum
    rw [sum_range_succ']
    simp
  rw [e]
  have h2 := (HasDerivAt.fun_sum h).add_const (1 : ℝ)
  convert h2 using 1
  unfold expNegSum
  rw [sum_neg_distrib]

/-- For `t ≥ 0` the remainder of the series of `exp (-t)` is at most its first omitted term. -/
theorem exp_neg_taylor (p : ℕ) : ∀ t : ℝ, 0 ≤ t →
    |exp (-t) - expNegSum p t| ≤ t ^ p / (p.factorial : ℝ) := by
  induction p with
  | zero =>
    intro t ht
    have h0 : expNegSum 0 t = 0 := by simp [expNegSum]
    rw [h0, sub_zero, abs_of_pos (exp_pos _), pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one]
    exact exp_le_one_iff.2 (by linarith)
  | succ p ih =>
    intro t ht
    have hR : ∀ s : ℝ, HasDerivAt (fun s => exp (-s) - expNegSum (p + 1) s)
        (-(exp (-s) - expNegSum p s)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => exp (-s)) (-exp (-s)) s := by
        have h := (hasDerivAt_neg' s).exp
        convert h using 1
        ring
      have h2 := h1.sub (hasDerivAt_expNegSum p s)
      convert h2 using 1
      ring
    have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ (p + 1) / ((p + 1).factorial : ℝ))
        (s ^ p / (p.factorial : ℝ)) s := by
      intro s
      have h := (hasDerivAt_pow (p + 1) s).div_const ((p + 1).factorial : ℝ)
      convert h using 1
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    have hE0 : expNegSum (p + 1) 0 = 1 := by
      unfold expNegSum
      rw [sum_range_succ']
      simp
    have up : 0 ≤ t ^ (p + 1) / ((p + 1).factorial : ℝ) -
        (exp (-t) - expNegSum (p + 1) t) :=
      nonneg_of_deriv_nonneg
        (f := fun s => s ^ (p + 1) / ((p + 1).factorial : ℝ) -
          (exp (-s) - expNegSum (p + 1) s))
        (f' := fun s => s ^ p / (p.factorial : ℝ) - -(exp (-s) - expNegSum p s))
        (fun s => (hB s).sub (hR s)) (by simp [hE0])
        (fun s hs => by
          have h := abs_le.1 (ih s hs)
          linarith [h.1]) ht
    have lo : 0 ≤ t ^ (p + 1) / ((p + 1).factorial : ℝ) +
        (exp (-t) - expNegSum (p + 1) t) :=
      nonneg_of_deriv_nonneg
        (f := fun s => s ^ (p + 1) / ((p + 1).factorial : ℝ) +
          (exp (-s) - expNegSum (p + 1) s))
        (f' := fun s => s ^ p / (p.factorial : ℝ) + -(exp (-s) - expNegSum p s))
        (fun s => (hB s).add (hR s)) (by simp [hE0])
        (fun s hs => by
          have h := abs_le.1 (ih s hs)
          linarith [h.2]) ht
    rw [abs_le]
    constructor <;> linarith

/-- Exponential decay is below every power. -/
theorem exp_small (p : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    exp (-(M / 12)) ≤ ((p.factorial : ℝ) * 12 ^ p) / M ^ p := by
  have hM0 : 0 < M := by linarith
  have h := pow_div_factorial_le_exp (x := M / 12) (by positivity) p
  have h' : (M / 12) ^ p ≤ exp (M / 12) * (p.factorial : ℝ) := by
    rwa [div_le_iff₀ (by positivity)] at h
  rw [exp_neg, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (exp_pos _)]
  calc M ^ p = (M / 12) ^ p * 12 ^ p := by
        rw [div_pow]
        field_simp
    _ ≤ exp (M / 12) * (p.factorial : ℝ) * 12 ^ p :=
        mul_le_mul_of_nonneg_right h' (by positivity)
    _ = exp (M / 12) * ((p.factorial : ℝ) * 12 ^ p) := by ring

/-! ### Normalised Gaussian moments -/

/-- `muQ r = 3^r (2r+1)!!`, the moment of `(M u²)^r` against `u² e^(-M u²/6)`. -/
def muQ : ℕ → ℚ
  | 0 => 1
  | r + 1 => muQ r * (6 * r + 9)

theorem muQ_pos (r : ℕ) : 0 < muQ r := by
  induction r with
  | zero => simp [muQ]
  | succ r ih =>
    simp only [muQ]
    positivity

theorem muQ_nonneg (r : ℕ) : (0 : ℝ) ≤ (muQ r : ℝ) := by exact_mod_cast (muQ_pos r).le

theorem hm_mu {M : ℝ} (hM : 0 < M) (r : ℕ) :
    hm M (r + 1) = (muQ r : ℝ) / M ^ r * hm M 1 := by
  induction r with
  | zero => simp [muQ]
  | succ r ih =>
    rw [hm_succ hM (r + 1), ih]
    simp only [muQ]
    push_cast
    field_simp
    ring

theorem gm_measurable (M : ℝ) (k : ℕ) : Measurable (gm M k) :=
  (by unfold gm; fun_prop : Continuous (gm M k)).measurable

theorem hm_one_lower {M : ℝ} (hM : 1 ≤ M) : 1 / M ^ 2 ≤ hm M 1 := by
  have hM0 : 0 < M := by linarith
  rw [hm_eq hM0 1, Mom_one, pow_one]
  have hs0 : 0 < √(M / 6) := sqrt_pos.2 (by positivity)
  have hs : √(M / 6) ≤ M := by
    calc √(M / 6) ≤ √(M ^ 2) := sqrt_le_sqrt (by nlinarith)
      _ = M := sqrt_sq hM0.le
  have hpi : 1 ≤ √π := by
    rw [show (1 : ℝ) = √1 by simp]
    exact sqrt_le_sqrt (by linarith [pi_gt_three])
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ M / 6),
    mul_le_mul_of_nonneg_right hpi (sq_nonneg M), sq_nonneg M]

/-! ### Gaussian tails beyond `1` -/

theorem gm_tail_pointwise {M : ℝ} (hM : 0 ≤ M) (k : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    gm M k u ≤ exp (-(M / 12)) * gm (M / 2) k u := by
  unfold gm
  have hu0 : 0 ≤ u := by linarith
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have h1 : exp (-(M / 6) * u ^ 2) = exp (-(M / 12) * u ^ 2) * exp (-(M / 2 / 6) * u ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  have h2 : exp (-(M / 12) * u ^ 2) ≤ exp (-(M / 12)) := by
    apply exp_le_exp.2
    nlinarith [mul_nonneg hM (sub_nonneg.2 hu2)]
  rw [h1]
  calc u ^ (2 * k) * (exp (-(M / 12) * u ^ 2) * exp (-(M / 2 / 6) * u ^ 2))
      = exp (-(M / 12) * u ^ 2) * (u ^ (2 * k) * exp (-(M / 2 / 6) * u ^ 2)) := by ring
    _ ≤ exp (-(M / 12)) * (u ^ (2 * k) * exp (-(M / 2 / 6) * u ^ 2)) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg (pow_nonneg hu0 _) (exp_pos _).le)

theorem gm_tail_le {M : ℝ} (hM : 0 < M) (k : ℕ) :
    ∫ u in Set.Ioi (1 : ℝ), gm M k u ≤ exp (-(M / 12)) * hm (M / 2) k := by
  have hM2 : 0 < M / 2 := by positivity
  have hI := (gm_integrable hM k).integrableOn (s := Set.Ioi (1 : ℝ))
  have hI2 := gm_integrable hM2 k
  calc ∫ u in Set.Ioi (1 : ℝ), gm M k u
      ≤ ∫ u in Set.Ioi (1 : ℝ), exp (-(M / 12)) * gm (M / 2) k u :=
        setIntegral_mono_on hI ((hI2.const_mul _).integrableOn) measurableSet_Ioi
          (fun u hu => gm_tail_pointwise hM.le k (le_of_lt hu))
    _ = exp (-(M / 12)) * ∫ u in Set.Ioi (1 : ℝ), gm (M / 2) k u := integral_const_mul _ _
    _ ≤ exp (-(M / 12)) * hm (M / 2) k := by
        apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
        unfold hm
        exact setIntegral_mono_set hI2.integrableOn
          (Filter.Eventually.of_forall fun u => gm_nonneg _ _ u)
          (Filter.Eventually.of_forall fun u (hu : u ∈ Set.Ioi (1 : ℝ)) =>
            Set.Ioi_subset_Ioi (zero_le_one' ℝ) hu)

theorem hm_half_eq {M : ℝ} (hM : 0 < M) (k : ℕ) : hm (M / 2) k = 2 ^ k * √2 * hm M k := by
  have ha : 0 < M / 6 := by positivity
  have e : M / 2 / 6 = (M / 6) / 2 := by ring
  have hs2 : (0 : ℝ) < √2 := sqrt_pos.2 (by norm_num)
  have hsa : 0 < √(M / 6) := sqrt_pos.2 ha
  have h22 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  rw [hm_eq (by positivity) k, hm_eq hM k, e, div_pow, sqrt_div ha.le]
  field_simp

theorem gm_tail_bound {M : ℝ} (hM : 1 ≤ M) (r : ℕ) :
    ∫ u in Set.Ioi (1 : ℝ), gm M (r + 1) u ≤
      exp (-(M / 12)) * (2 ^ (r + 2) * (muQ r : ℝ)) / M ^ r * hm M 1 := by
  have hM0 : 0 < M := by linarith
  have h1 := gm_tail_le hM0 (r + 1)
  have h2 := hm_half_eq hM0 (r + 1)
  have h3 := hm_mu hM0 r
  have hs2 : √2 ≤ 2 := sqrt_le_self_of_one_le (by norm_num)
  have hmu := muQ_nonneg r
  have hh : 0 ≤ hm M 1 := hm_nonneg M 1
  have hMr : 0 < M ^ r := pow_pos hM0 r
  have h4 : hm (M / 2) (r + 1) ≤ 2 ^ (r + 2) * (muQ r : ℝ) / M ^ r * hm M 1 := by
    rw [h2, h3]
    have hX : 0 ≤ (muQ r : ℝ) / M ^ r * hm M 1 := mul_nonneg (div_nonneg hmu hMr.le) hh
    calc 2 ^ (r + 1) * √2 * ((muQ r : ℝ) / M ^ r * hm M 1)
        ≤ 2 ^ (r + 1) * 2 * ((muQ r : ℝ) / M ^ r * hm M 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by positivity)) hX
      _ = 2 ^ (r + 2) * (muQ r : ℝ) / M ^ r * hm M 1 := by ring
  calc ∫ u in Set.Ioi (1 : ℝ), gm M (r + 1) u ≤ exp (-(M / 12)) * hm (M / 2) (r + 1) := h1
    _ ≤ exp (-(M / 12)) * (2 ^ (r + 2) * (muQ r : ℝ) / M ^ r * hm M 1) :=
        mul_le_mul_of_nonneg_left h4 (exp_pos _).le
    _ = exp (-(M / 12)) * (2 ^ (r + 2) * (muQ r : ℝ)) / M ^ r * hm M 1 := by ring

/-! ### A Watson-type lemma on `[0, 1]` -/

/-- Bookkeeping constant for the Gaussian tails of the polynomial part. -/
noncomputable def tailConst (a : ℕ → ℝ) (r q : ℕ) : ℝ :=
  ∑ i ∈ range q, |a i| * (2 ^ (r + i + 2) * (muQ (r + i) : ℝ))

theorem tailConst_nonneg (a : ℕ → ℝ) (r q : ℕ) : 0 ≤ tailConst a r q :=
  sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (muQ_nonneg _))

/-- If `φ` is approximated on `[0, 1]` by a polynomial in `u²` with error `C u^(2q)`, then its
integral against `u^(2r+2) e^(-M u²/6)` is given by the Gaussian moments of the polynomial, up to
the moment of the error and an exponentially small tail. -/
theorem watson_normalized {φ : ℝ → ℝ} (hφm : Measurable φ) {a : ℕ → ℝ} {q : ℕ} {C : ℝ}
    (hφ : ∀ u ∈ Set.Icc (0 : ℝ) 1, |φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i| ≤ C * |u ^ 2| ^ q)
    {M : ℝ} (hM : 1 ≤ M) (r : ℕ) :
    IntegrableOn (fun u => gm M (r + 1) u * φ u) (Set.Ioc 0 1) ∧
    |(∫ u in Set.Ioc (0 : ℝ) 1, gm M (r + 1) u * φ u) -
        hm M 1 * ∑ i ∈ range q, a i * ((muQ (r + i) : ℝ) / M ^ (r + i))| ≤
      hm M 1 * (C * ((muQ (r + q) : ℝ) / M ^ (r + q)) +
        exp (-(M / 12)) * (tailConst a r q / M ^ r)) := by
  have hM0 : 0 < M := by linarith
  have hh : 0 ≤ hm M 1 := hm_nonneg M 1
  have hC : 0 ≤ C := by
    have h := hφ 1 (by simp)
    simp only [one_pow, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hI : ∀ k, IntegrableOn (gm M k) (Set.Ioc (0 : ℝ) 1) :=
    fun k => (gm_integrable hM0 k).integrableOn
  have hpm : Measurable fun u : ℝ => ∑ i ∈ range q, a i * (u ^ 2) ^ i :=
    Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_id.pow_const 2).pow_const i)
  have hρm : Measurable fun u : ℝ => φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i := hφm.sub hpm
  have hdec : ∀ u, gm M (r + 1) u * φ u =
      (∑ i ∈ range q, a i * gm M (r + i + 1) u) +
        gm M (r + 1) u * (φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i) := by
    intro u
    have h1 : ∀ i ∈ range q, gm M (r + 1) u * (a i * (u ^ 2) ^ i) = a i * gm M (r + i + 1) u := by
      intro i _
      unfold gm
      ring
    rw [mul_sub, mul_sum, sum_congr rfl h1]
    ring
  have hρb : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      |gm M (r + 1) u * (φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i)| ≤ C * gm M (r + q + 1) u := by
    intro u hu
    have h := hφ u ⟨hu.1.le, hu.2⟩
    rw [abs_mul, abs_of_nonneg (gm_nonneg M (r + 1) u)]
    have e : C * gm M (r + q + 1) u = gm M (r + 1) u * (C * |u ^ 2| ^ q) := by
      rw [abs_of_nonneg (sq_nonneg u)]
      unfold gm
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (gm_nonneg M (r + 1) u)
  have hae : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖gm M (r + 1) u * (φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i)‖ ≤ C * gm M (r + q + 1) u :=
    (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun u hu => by rw [Real.norm_eq_abs]; exact hρb u hu)
  have hρI : IntegrableOn
      (fun u => gm M (r + 1) u * (φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i)) (Set.Ioc 0 1) :=
    Integrable.mono' ((hI (r + q + 1)).const_mul C)
      ((gm_measurable M (r + 1)).mul hρm).aestronglyMeasurable hae
  have hsumI : IntegrableOn (fun u => ∑ i ∈ range q, a i * gm M (r + i + 1) u) (Set.Ioc 0 1) :=
    integrable_finsetSum _ fun i _ => (hI (r + i + 1)).const_mul (a i)
  have hint : IntegrableOn (fun u => gm M (r + 1) u * φ u) (Set.Ioc 0 1) :=
    (hsumI.add hρI).congr (Filter.Eventually.of_forall fun u => (hdec u).symm)
  refine ⟨hint, ?_⟩
  have e1 : ∫ u in Set.Ioc (0 : ℝ) 1, gm M (r + 1) u * φ u =
      (∑ i ∈ range q, a i * ∫ u in Set.Ioc (0 : ℝ) 1, gm M (r + i + 1) u) +
        ∫ u in Set.Ioc (0 : ℝ) 1,
          gm M (r + 1) u * (φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hdec), integral_add hsumI hρI,
      integral_finsetSum _ fun i _ => (hI (r + i + 1)).const_mul (a i)]
    congr 1
    exact sum_congr rfl fun i _ => integral_const_mul _ _
  have e2 : ∀ k, ∫ u in Set.Ioc (0 : ℝ) 1, gm M k u =
      hm M k - ∫ u in Set.Ioi (1 : ℝ), gm M k u := by
    intro k
    have h := setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl (1 : ℝ))) measurableSet_Ioi
      (hI k) ((gm_integrable hM0 k).integrableOn (s := Set.Ioi (1 : ℝ)))
    rw [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] at h
    unfold hm
    linarith
  have hT0 : ∀ k, 0 ≤ ∫ u in Set.Ioi (1 : ℝ), gm M k u :=
    fun k => setIntegral_nonneg measurableSet_Ioi fun u _ => gm_nonneg M k u
  have e3 : |∫ u in Set.Ioc (0 : ℝ) 1,
      gm M (r + 1) u * (φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i)| ≤ C * hm M (r + q + 1) := by
    have h := norm_integral_le_of_norm_le ((hI (r + q + 1)).const_mul C) hae
    rw [Real.norm_eq_abs, integral_const_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [e2]
    linarith [hT0 (r + q + 1)]
  have e4 : ∑ i ∈ range q, a i * ∫ u in Set.Ioc (0 : ℝ) 1, gm M (r + i + 1) u =
      hm M 1 * ∑ i ∈ range q, a i * ((muQ (r + i) : ℝ) / M ^ (r + i)) -
        ∑ i ∈ range q, a i * ∫ u in Set.Ioi (1 : ℝ), gm M (r + i + 1) u := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [e2, hm_mu hM0 (r + i)]
    ring
  have e5 : |∑ i ∈ range q, a i * ∫ u in Set.Ioi (1 : ℝ), gm M (r + i + 1) u| ≤
      hm M 1 * (exp (-(M / 12)) * (tailConst a r q / M ^ r)) := by
    unfold tailConst
    rw [sum_div, mul_sum, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (hT0 _)]
    have ht := gm_tail_bound hM (r + i)
    have hMr : 0 < M ^ r := pow_pos hM0 r
    have hpow : M ^ r ≤ M ^ (r + i) := pow_le_pow_right₀ hM (Nat.le_add_right r i)
    have hnum : 0 ≤ |a i| * (2 ^ (r + i + 2) * (muQ (r + i) : ℝ)) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (muQ_nonneg _))
    calc |a i| * ∫ u in Set.Ioi (1 : ℝ), gm M (r + i + 1) u
        ≤ |a i| * (exp (-(M / 12)) * (2 ^ (r + i + 2) * (muQ (r + i) : ℝ)) / M ^ (r + i) *
            hm M 1) := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      _ = hm M 1 * (exp (-(M / 12)) *
            (|a i| * (2 ^ (r + i + 2) * (muQ (r + i) : ℝ)) / M ^ (r + i))) := by ring
      _ ≤ hm M 1 * (exp (-(M / 12)) *
            (|a i| * (2 ^ (r + i + 2) * (muQ (r + i) : ℝ)) / M ^ r)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hnum hMr hpow) (exp_pos _).le) hh
  have hfin : (∫ u in Set.Ioc (0 : ℝ) 1, gm M (r + 1) u * φ u) -
      hm M 1 * ∑ i ∈ range q, a i * ((muQ (r + i) : ℝ) / M ^ (r + i)) =
      (∫ u in Set.Ioc (0 : ℝ) 1,
          gm M (r + 1) u * (φ u - ∑ i ∈ range q, a i * (u ^ 2) ^ i)) +
        -∑ i ∈ range q, a i * ∫ u in Set.Ioi (1 : ℝ), gm M (r + i + 1) u := by
    rw [e1, e4]
    ring
  have e6 : C * hm M (r + q + 1) = hm M 1 * (C * ((muQ (r + q) : ℝ) / M ^ (r + q))) := by
    rw [hm_mu hM0 (r + q)]
    ring
  rw [hfin, mul_add, ← e6]
  refine (abs_add_le _ _).trans (add_le_add e3 ?_)
  rw [abs_neg]
  exact e5

/-! ### The main part of the integral -/

/-- The series `kapC` with real coefficients. -/
noncomputable abbrev kapR : ℕ → ℝ := fun i => (kapC i : ℝ)

/-- `∫₀¹ u^(4k+2) e^(-M u²/6) κ(u)^k du`. -/
noncomputable def Jint (M : ℝ) (k : ℕ) : ℝ :=
  ∫ u in Set.Ioc (0 : ℝ) 1, gm M (2 * k + 1) u * kap u ^ k

/-- The contribution of the remainder of the exponential series. -/
noncomputable def Rint (p : ℕ) (M : ℝ) : ℝ :=
  ∫ u in Set.Ioc (0 : ℝ) 1,
    gm M 1 u * (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u))

/-- `∫₀¹ u² (sin u / u)^M du`, written with the exponent in Gaussian form. -/
noncomputable def Wmain (M : ℝ) : ℝ :=
  ∫ u in Set.Ioc (0 : ℝ) 1, gm M 1 u * exp (-(M * u ^ 4 * kap u))

/-- The Laplace coefficients. -/
def cC (j : ℕ) : ℚ :=
  ∑ k ∈ range (j + 1), (-1) ^ k / (k.factorial : ℚ) * cpow kapC k (j - k) * muQ (j + k)

theorem cC_cast (j : ℕ) : ((cC j : ℚ) : ℝ) =
    ∑ k ∈ range (j + 1), (-1) ^ k / (k.factorial : ℝ) * cpow kapR k (j - k) *
      (muQ (j + k) : ℝ) := by
  unfold cC
  push_cast
  refine sum_congr rfl fun k _ => ?_
  rw [show ((cpow kapC k (j - k) : ℚ) : ℝ) = cpow kapR k (j - k) from
    map_cpow (Rat.castHom ℝ) kapC k (j - k)]

theorem c_sum_eq (p : ℕ) (M : ℝ) :
    ∑ j ∈ range p, (cC j : ℝ) / M ^ j =
      ∑ k ∈ range p, ∑ i ∈ range (p - k), (-1) ^ k / (k.factorial : ℝ) *
        (cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i))) := by
  rw [sum_triangle (fun k i => (-1) ^ k / (k.factorial : ℝ) *
    (cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)))) p]
  refine sum_congr rfl fun j _ => ?_
  rw [cC_cast, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have e1 : 2 * k + (j - k) = j + k := by omega
  have e2 : k + (j - k) = j := by omega
  show (-1) ^ k / (k.factorial : ℝ) * cpow kapR k (j - k) * (muQ (j + k) : ℝ) / M ^ j =
    (-1) ^ k / (k.factorial : ℝ) *
      (cpow kapR k (j - k) * ((muQ (2 * k + (j - k)) : ℝ) / M ^ (k + (j - k))))
  rw [e1, e2]
  ring

theorem term_bound (p k : ℕ) (hk : k < p) : ∃ B : ℝ, ∀ M : ℝ, 1 ≤ M →
    IntegrableOn (fun u => gm M (2 * k + 1) u * kap u ^ k) (Set.Ioc 0 1) ∧
    |M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i))| ≤ B * (hm M 1 / M ^ p) := by
  obtain ⟨C, hC⟩ := (kap_hasExp.pow k) (p - k)
  refine ⟨|C| * (muQ (k + p) : ℝ) +
    (p.factorial : ℝ) * 12 ^ p * tailConst (cpow kapR k) (2 * k) (p - k), fun M hM => ?_⟩
  have hM0 : 0 < M := by linarith
  have hφm : Measurable fun u => kap u ^ k := measurable_kap.pow_const k
  obtain ⟨hint, hW⟩ := watson_normalized hφm (a := cpow kapR k) (q := p - k) (C := C) hC hM
    (2 * k)
  refine ⟨hint, ?_⟩
  have hS0 := tailConst_nonneg (cpow kapR k) (2 * k) (p - k)
  have hh : 0 ≤ hm M 1 := hm_nonneg M 1
  have e2 : 2 * k + (p - k) = k + p := by omega
  have hMk : 0 < M ^ k := pow_pos hM0 k
  have hsum : hm M 1 * ∑ i ∈ range (p - k),
      cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)) =
      M ^ k * (hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (2 * k + i))) := by
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hp : M ^ (2 * k + i) = M ^ k * M ^ (k + i) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hp]
    field_simp
  have e : M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
      cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)) =
      M ^ k * (Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (2 * k + i))) := by
    rw [hsum]
    ring
  rw [e, abs_mul, abs_of_pos hMk]
  have hE := exp_small p hM
  rw [e2] at hW
  have h1 : M ^ k * (hm M 1 * (C * ((muQ (k + p) : ℝ) / M ^ (k + p)))) ≤
      |C| * (muQ (k + p) : ℝ) * (hm M 1 / M ^ p) := by
    have e' : M ^ k * (hm M 1 * (C * ((muQ (k + p) : ℝ) / M ^ (k + p)))) =
        C * ((muQ (k + p) : ℝ) * (hm M 1 / M ^ p)) := by
      rw [pow_add]
      field_simp
    rw [e', mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self C)
      (mul_nonneg (muQ_nonneg _) (div_nonneg hh (by positivity)))
  have h2 : M ^ k * (hm M 1 * (exp (-(M / 12)) *
      (tailConst (cpow kapR k) (2 * k) (p - k) / M ^ (2 * k)))) ≤
      (p.factorial : ℝ) * 12 ^ p * tailConst (cpow kapR k) (2 * k) (p - k) *
        (hm M 1 / M ^ p) := by
    have hk1 : (1 : ℝ) ≤ M ^ k := one_le_pow₀ hM
    have e' : M ^ k * (hm M 1 * (exp (-(M / 12)) *
        (tailConst (cpow kapR k) (2 * k) (p - k) / M ^ (2 * k)))) =
        exp (-(M / 12)) * (tailConst (cpow kapR k) (2 * k) (p - k) * hm M 1) / M ^ k := by
      rw [show 2 * k = k + k by ring, pow_add]
      field_simp
    rw [e']
    have hX : 0 ≤ tailConst (cpow kapR k) (2 * k) (p - k) * hm M 1 := mul_nonneg hS0 hh
    calc exp (-(M / 12)) * (tailConst (cpow kapR k) (2 * k) (p - k) * hm M 1) / M ^ k
        ≤ exp (-(M / 12)) * (tailConst (cpow kapR k) (2 * k) (p - k) * hm M 1) :=
          div_le_self (mul_nonneg (exp_pos _).le hX) hk1
      _ ≤ ((p.factorial : ℝ) * 12 ^ p / M ^ p) *
            (tailConst (cpow kapR k) (2 * k) (p - k) * hm M 1) :=
          mul_le_mul_of_nonneg_right hE hX
      _ = (p.factorial : ℝ) * 12 ^ p * tailConst (cpow kapR k) (2 * k) (p - k) *
            (hm M 1 / M ^ p) := by ring
  calc M ^ k * |Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (2 * k + i))|
      ≤ M ^ k * (hm M 1 * (C * ((muQ (k + p) : ℝ) / M ^ (k + p)) +
          exp (-(M / 12)) * (tailConst (cpow kapR k) (2 * k) (p - k) / M ^ (2 * k)))) :=
        mul_le_mul_of_nonneg_left hW hMk.le
    _ = M ^ k * (hm M 1 * (C * ((muQ (k + p) : ℝ) / M ^ (k + p)))) +
          M ^ k * (hm M 1 * (exp (-(M / 12)) *
            (tailConst (cpow kapR k) (2 * k) (p - k) / M ^ (2 * k)))) := by ring
    _ ≤ |C| * (muQ (k + p) : ℝ) * (hm M 1 / M ^ p) +
          (p.factorial : ℝ) * 12 ^ p * tailConst (cpow kapR k) (2 * k) (p - k) *
            (hm M 1 / M ^ p) := add_le_add h1 h2
    _ = (|C| * (muQ (k + p) : ℝ) +
          (p.factorial : ℝ) * 12 ^ p * tailConst (cpow kapR k) (2 * k) (p - k)) *
            (hm M 1 / M ^ p) := by ring

theorem rem_bound (p : ℕ) : ∃ B : ℝ, ∀ M : ℝ, 1 ≤ M →
    IntegrableOn (fun u => gm M 1 u *
      (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u))) (Set.Ioc 0 1) ∧
    |Rint p M| ≤ B * (hm M 1 / M ^ p) := by
  obtain ⟨K, hK⟩ := kap_bdd
  refine ⟨|K| ^ p * (muQ (2 * p) : ℝ), fun M hM => ?_⟩
  have hM0 : 0 < M := by linarith
  have hpt : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      |gm M 1 u * (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u))| ≤
        (M ^ p * |K| ^ p) * gm M (2 * p + 1) u := by
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have hk0 := kap_nonneg hu'.1 hu'.2
    have hkK : kap u ≤ |K| := (le_abs_self _).trans ((hK u hu').trans (le_abs_self K))
    have hMu : 0 ≤ M * u ^ 4 := by positivity
    have ht0 : 0 ≤ M * u ^ 4 * kap u := mul_nonneg hMu hk0
    have ht := exp_neg_taylor p _ ht0
    have hf : (1 : ℝ) ≤ (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have htp : (M * u ^ 4 * kap u) ^ p / (p.factorial : ℝ) ≤ M ^ p * |K| ^ p * (u ^ 4) ^ p := by
      calc (M * u ^ 4 * kap u) ^ p / (p.factorial : ℝ) ≤ (M * u ^ 4 * kap u) ^ p :=
            div_le_self (pow_nonneg ht0 p) hf
        _ ≤ (M * u ^ 4 * |K|) ^ p :=
            pow_le_pow_left₀ ht0 (mul_le_mul_of_nonneg_left hkK hMu) p
        _ = M ^ p * |K| ^ p * (u ^ 4) ^ p := by ring
    rw [abs_mul, abs_of_nonneg (gm_nonneg M 1 u)]
    calc gm M 1 u * |exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u)|
        ≤ gm M 1 u * (M ^ p * |K| ^ p * (u ^ 4) ^ p) :=
          mul_le_mul_of_nonneg_left (ht.trans htp) (gm_nonneg M 1 u)
      _ = (M ^ p * |K| ^ p) * gm M (2 * p + 1) u := by
          unfold gm
          ring
  have hmeas : Measurable fun u => gm M 1 u *
      (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u)) := by
    have ht : Measurable fun u : ℝ => M * u ^ 4 * kap u :=
      (measurable_const.mul (measurable_id.pow_const 4)).mul measurable_kap
    have he : Measurable fun u : ℝ => expNegSum p (M * u ^ 4 * kap u) := by
      unfold expNegSum
      exact Finset.measurable_sum _ fun k _ => (ht.pow_const k).mul_const _
    exact (gm_measurable M 1).mul ((ht.neg.exp).sub he)
  have hI : IntegrableOn (fun u => (M ^ p * |K| ^ p) * gm M (2 * p + 1) u) (Set.Ioc 0 1) :=
    ((gm_integrable hM0 _).integrableOn).const_mul _
  have hae : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖gm M 1 u * (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u))‖ ≤
        (M ^ p * |K| ^ p) * gm M (2 * p + 1) u :=
    (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun u hu => by rw [Real.norm_eq_abs]; exact hpt u hu)
  refine ⟨Integrable.mono' hI hmeas.aestronglyMeasurable hae, ?_⟩
  have h := norm_integral_le_of_norm_le hI hae
  rw [Real.norm_eq_abs, integral_const_mul] at h
  unfold Rint
  refine h.trans ?_
  have hle : ∫ u in Set.Ioc (0 : ℝ) 1, gm M (2 * p + 1) u ≤ hm M (2 * p + 1) := by
    unfold hm
    exact setIntegral_mono_set (gm_integrable hM0 _).integrableOn
      (Filter.Eventually.of_forall fun u => gm_nonneg _ _ u)
      (Filter.Eventually.of_forall fun u (hu : u ∈ Set.Ioc (0 : ℝ) 1) => hu.1)
  have e : M ^ p * |K| ^ p * hm M (2 * p + 1) =
      |K| ^ p * (muQ (2 * p) : ℝ) * (hm M 1 / M ^ p) := by
    rw [hm_mu hM0 (2 * p), show 2 * p = p + p by ring, pow_add]
    field_simp
  calc M ^ p * |K| ^ p * ∫ u in Set.Ioc (0 : ℝ) 1, gm M (2 * p + 1) u
      ≤ M ^ p * |K| ^ p * hm M (2 * p + 1) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = |K| ^ p * (muQ (2 * p) : ℝ) * (hm M 1 / M ^ p) := e

theorem main_decomp (p : ℕ) (M u : ℝ) :
    gm M 1 u * exp (-(M * u ^ 4 * kap u)) =
      (∑ k ∈ range p, ((-1) ^ k / (k.factorial : ℝ) * M ^ k) *
        (gm M (2 * k + 1) u * kap u ^ k)) +
        gm M 1 u * (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u)) := by
  have h : gm M 1 u * expNegSum p (M * u ^ 4 * kap u) =
      ∑ k ∈ range p, ((-1) ^ k / (k.factorial : ℝ) * M ^ k) *
        (gm M (2 * k + 1) u * kap u ^ k) := by
    unfold expNegSum
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    unfold gm
    rw [mul_pow, mul_pow]
    ring
  rw [← h]
  ring

/-- The main part of the integral to every order. -/
theorem Wmain_expand (p : ℕ) : ∃ B : ℝ, ∀ M : ℝ, 1 ≤ M →
    |Wmain M - hm M 1 * ∑ j ∈ range p, (cC j : ℝ) / M ^ j| ≤ B * (hm M 1 / M ^ p) := by
  choose! Bk hBk using fun k (hk : k < p) => term_bound p k hk
  obtain ⟨BR, hBR⟩ := rem_bound p
  refine ⟨(∑ k ∈ range p, |Bk k|) + |BR|, fun M hM => ?_⟩
  have hM0 : 0 < M := by linarith
  have hh : 0 ≤ hm M 1 / M ^ p := div_nonneg (hm_nonneg M 1) (by positivity)
  obtain ⟨hRI, hRb⟩ := hBR M hM
  have hkI : ∀ k ∈ range p, IntegrableOn (fun u => ((-1) ^ k / (k.factorial : ℝ) * M ^ k) *
      (gm M (2 * k + 1) u * kap u ^ k)) (Set.Ioc 0 1) :=
    fun k hk => ((hBk k (mem_range.1 hk) M hM).1).const_mul _
  have hsplit : Wmain M =
      (∑ k ∈ range p, ((-1) ^ k / (k.factorial : ℝ) * M ^ k) * Jint M k) + Rint p M := by
    unfold Wmain Jint Rint
    rw [integral_congr_ae (Filter.Eventually.of_forall (main_decomp p M)),
      integral_add (integrable_finsetSum _ hkI) hRI, integral_finsetSum _ hkI]
    congr 1
    exact sum_congr rfl fun k _ => integral_const_mul _ _
  have hterm : ∀ k ∈ range p, (-1) ^ k / (k.factorial : ℝ) *
      (M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i))) =
      ((-1) ^ k / (k.factorial : ℝ) * M ^ k) * Jint M k -
        hm M 1 * ∑ i ∈ range (p - k), (-1) ^ k / (k.factorial : ℝ) *
          (cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i))) := by
    intro k _
    rw [← mul_sum]
    ring
  have key : Wmain M - hm M 1 * ∑ j ∈ range p, (cC j : ℝ) / M ^ j =
      (∑ k ∈ range p, (-1) ^ k / (k.factorial : ℝ) *
        (M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
          cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)))) + Rint p M := by
    rw [hsplit, c_sum_eq p M, sum_congr rfl hterm, sum_sub_distrib, ← mul_sum]
    ring
  have hsum : |∑ k ∈ range p, (-1) ^ k / (k.factorial : ℝ) *
      (M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)))| ≤
      (∑ k ∈ range p, |Bk k|) * (hm M 1 / M ^ p) := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    have hb := (hBk k (mem_range.1 hk) M hM).2
    have hs : |(-1 : ℝ) ^ k / (k.factorial : ℝ)| ≤ 1 := by
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast,
        div_le_one (by positivity)]
      exact_mod_cast Nat.factorial_pos k
    rw [abs_mul]
    calc |(-1 : ℝ) ^ k / (k.factorial : ℝ)| * |M ^ k * Jint M k - hm M 1 *
          ∑ i ∈ range (p - k), cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i))|
        ≤ 1 * (|Bk k| * (hm M 1 / M ^ p)) :=
          mul_le_mul hs (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hh))
            (abs_nonneg _) zero_le_one
      _ = |Bk k| * (hm M 1 / M ^ p) := one_mul _
  rw [key, add_mul]
  exact (abs_add_le _ _).trans
    (add_le_add hsum (hRb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hh)))

/-! ### From the main part to the full integral -/

theorem weight_eq_main (N : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    weight N u = gm ((N : ℝ) + 2) 1 u * exp (-(((N : ℝ) + 2) * u ^ 4 * kap u)) := by
  have e : exp (-(u ^ 2 / 6 + u ^ 4 * kap u)) ^ (N + 2) =
      exp (-(((N : ℝ) + 2) / 6) * u ^ 2) * exp (-(((N : ℝ) + 2) * u ^ 4 * kap u)) := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring
  unfold weight gm
  rw [sinc_eq_exp h0 h1, abs_of_pos (exp_pos _), e]
  ring

theorem weight_tail_le (N : ℕ) (hN : 2 ≤ N) :
    ∫ x in Set.Ioi (1 : ℝ), weight N x ≤
      (∫ x in Set.Ioi (1 : ℝ), gm ((N : ℝ) + 2) 1 x) + ∫ x in Set.Ioi π, 1 / x ^ N := by
  have h1π : (1 : ℝ) ≤ π := by linarith [pi_gt_three]
  have hi := (weight_integrable_half N hN).mono_set (Set.Ioi_subset_Ioi (zero_le_one' ℝ))
  have hs := hi.mono_set (show Set.Ioc (1 : ℝ) π ⊆ Set.Ioi 1 from fun x hx => hx.1)
  have ht := hi.mono_set (Set.Ioi_subset_Ioi h1π)
  have he : ∫ x in Set.Ioi (1 : ℝ), weight N x =
      (∫ x in Set.Ioc (1 : ℝ) π, weight N x) + ∫ x in Set.Ioi π, weight N x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi h1π,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hs ht]
  have hgI : Integrable (gm ((N : ℝ) + 2) 1) := gm_integrable (by positivity) 1
  have hpt : ∀ x ∈ Set.Ioc (1 : ℝ) π, weight N x ≤ gm ((N : ℝ) + 2) 1 x := by
    intro x hx
    have h := weight_le_gauss N (x := x) ⟨by linarith [hx.1], hx.2⟩
    unfold gauss at h
    unfold gm
    rw [mul_one]
    exact h
  rw [he]
  apply add_le_add
  · exact (setIntegral_mono_on hs hgI.integrableOn measurableSet_Ioc hpt).trans
      (setIntegral_mono_set hgI.integrableOn
        (Filter.Eventually.of_forall fun x => gm_nonneg _ _ x)
        (Filter.Eventually.of_forall fun x (hx : x ∈ Set.Ioc (1 : ℝ) π) => hx.1))
  · exact setIntegral_mono_on ht (tail_integrable N hN) measurableSet_Ioi
      (fun x hx => weight_le_tail N (le_of_lt hx))

theorem pi_tail_small (p : ℕ) : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    1 / (((N : ℝ) - 1) * π ^ (N - 1)) ≤
      C * (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) := by
  refine ⟨((p + 2).factorial : ℝ) * exp 3, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Nat.add_sub_cancel]
  push_cast
  have hM1 : (1 : ℝ) ≤ (n : ℝ) + 1 + 2 := by linarith
  have hM0 : (0 : ℝ) < (n : ℝ) + 1 + 2 := by linarith
  have hlow := hm_one_lower hM1
  have hπn : 0 < π ^ n := pow_pos pi_pos n
  have hexp : exp (n : ℝ) ≤ π ^ n := by
    have h1 : exp (n : ℝ) = exp 1 ^ n := by rw [← exp_nat_mul, mul_one]
    rw [h1]
    exact pow_le_pow_left₀ (exp_pos 1).le (by linarith [exp_one_lt_d9, pi_gt_three]) n
  have hfac := pow_div_factorial_le_exp (x := (n : ℝ) + 1 + 2) hM0.le (p + 2)
  have hexpM : exp ((n : ℝ) + 1 + 2) = exp 3 * exp (n : ℝ) := by
    rw [← exp_add]
    congr 1
    ring
  have hA : 1 / (((n : ℝ) + 1 - 1) * π ^ n) ≤ 1 / exp (n : ℝ) := by
    apply one_div_le_one_div_of_le (exp_pos _)
    calc exp (n : ℝ) ≤ π ^ n := hexp
      _ = 1 * π ^ n := (one_mul _).symm
      _ ≤ ((n : ℝ) + 1 - 1) * π ^ n := mul_le_mul_of_nonneg_right (by linarith) hπn.le
  have hB' : 1 / exp (n : ℝ) ≤
      ((p + 2).factorial : ℝ) * exp 3 / ((n : ℝ) + 1 + 2) ^ (p + 2) := by
    rw [div_le_div_iff₀ (exp_pos _) (by positivity)]
    have h' : ((n : ℝ) + 1 + 2) ^ (p + 2) ≤
        exp ((n : ℝ) + 1 + 2) * ((p + 2).factorial : ℝ) := by
      rwa [div_le_iff₀ (by positivity)] at hfac
    rw [hexpM] at h'
    linarith
  have hC' : ((p + 2).factorial : ℝ) * exp 3 / ((n : ℝ) + 1 + 2) ^ (p + 2) ≤
      ((p + 2).factorial : ℝ) * exp 3 *
        (hm ((n : ℝ) + 1 + 2) 1 / ((n : ℝ) + 1 + 2) ^ p) := by
    have e : ((p + 2).factorial : ℝ) * exp 3 / ((n : ℝ) + 1 + 2) ^ (p + 2) =
        ((p + 2).factorial : ℝ) * exp 3 *
          ((1 / ((n : ℝ) + 1 + 2) ^ 2) / ((n : ℝ) + 1 + 2) ^ p) := by
      rw [pow_add]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hlow (by positivity)) (by positivity)
  exact hA.trans (hB'.trans hC')

theorem gm_tail_one {M : ℝ} (hM : 1 ≤ M) :
    ∫ u in Set.Ioi (1 : ℝ), gm M 1 u ≤ 4 * exp (-(M / 12)) * hm M 1 := by
  have h := gm_tail_bound hM 0
  have e : exp (-(M / 12)) * (2 ^ (0 + 2) * ((muQ 0 : ℚ) : ℝ)) / M ^ 0 * hm M 1 =
      4 * exp (-(M / 12)) * hm M 1 := by
    simp only [muQ, Rat.cast_one, pow_zero, div_one]
    ring
  rw [e] at h
  exact h

/-- **Laplace expansion to every order.**  With `M = N + 2`,
`∫₀^∞ u² |sin u / u|^M du = hm M 1 * (∑ j < p, cC j / M ^ j + O(M ^ (-p)))`. -/
theorem laplace_all_orders (p : ℕ) : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    |(∫ x in Set.Ioi (0 : ℝ), weight N x) -
        hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j| ≤
      C * (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) := by
  obtain ⟨B, hB⟩ := Wmain_expand p
  obtain ⟨Cπ, hCπ⟩ := pi_tail_small p
  refine ⟨|B| + 4 * ((p.factorial : ℝ) * 12 ^ p) + |Cπ|, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hM : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  have hM0 : (0 : ℝ) < (N : ℝ) + 2 := by linarith
  have hhm : 0 ≤ hm ((N : ℝ) + 2) 1 := hm_nonneg _ 1
  have hh : 0 ≤ hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p := div_nonneg hhm (by positivity)
  have hi := weight_integrable_half N hN
  have hi1 := hi.mono_set (show Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0 from fun x hx => hx.1)
  have hi2 := hi.mono_set (Set.Ioi_subset_Ioi (zero_le_one' ℝ))
  have hsplit : ∫ x in Set.Ioi (0 : ℝ), weight N x =
      (∫ x in Set.Ioc (0 : ℝ) 1, weight N x) + ∫ x in Set.Ioi (1 : ℝ), weight N x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2]
  have hmain : ∫ x in Set.Ioc (0 : ℝ) 1, weight N x = Wmain ((N : ℝ) + 2) := by
    unfold Wmain
    exact setIntegral_congr_fun measurableSet_Ioc fun u hu => weight_eq_main N hu.1.le hu.2
  have hW2a : 0 ≤ ∫ x in Set.Ioi (1 : ℝ), weight N x :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => weight_nonneg N x
  have hW2b : ∫ x in Set.Ioi (1 : ℝ), weight N x ≤
      (4 * ((p.factorial : ℝ) * 12 ^ p) + |Cπ|) *
        (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) := by
    have h1 := weight_tail_le N hN
    have h2 := gm_tail_one hM
    have h3 := exp_small p hM
    have h4 := hCπ N hN
    rw [tail_half_integral N hN] at h1
    have h5 : 4 * exp (-(((N : ℝ) + 2) / 12)) * hm ((N : ℝ) + 2) 1 ≤
        4 * ((p.factorial : ℝ) * 12 ^ p) * (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) := by
      calc 4 * exp (-(((N : ℝ) + 2) / 12)) * hm ((N : ℝ) + 2) 1
          ≤ 4 * ((p.factorial : ℝ) * 12 ^ p / ((N : ℝ) + 2) ^ p) * hm ((N : ℝ) + 2) 1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) hhm
        _ = _ := by ring
    have h6 : Cπ * (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) ≤
        |Cπ| * (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hh
    rw [add_mul]
    linarith
  have hb := hB ((N : ℝ) + 2) hM
  have e : (∫ x in Set.Ioc (0 : ℝ) 1, weight N x) + (∫ x in Set.Ioi (1 : ℝ), weight N x) -
      hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j =
      (Wmain ((N : ℝ) + 2) -
        hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j) +
        ∫ x in Set.Ioi (1 : ℝ), weight N x := by
    rw [hmain]
    ring
  rw [hsplit, e]
  calc |(Wmain ((N : ℝ) + 2) -
          hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j) +
          ∫ x in Set.Ioi (1 : ℝ), weight N x|
      ≤ |Wmain ((N : ℝ) + 2) -
          hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j| +
          |∫ x in Set.Ioi (1 : ℝ), weight N x| := abs_add_le _ _
    _ ≤ |B| * (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) +
          (4 * ((p.factorial : ℝ) * 12 ^ p) + |Cπ|) *
            (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) :=
        add_le_add (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self B) hh))
          (by rw [abs_of_nonneg hW2a]; exact hW2b)
    _ = (|B| + 4 * ((p.factorial : ℝ) * 12 ^ p) + |Cπ|) *
          (hm ((N : ℝ) + 2) 1 / ((N : ℝ) + 2) ^ p) := by ring

end PrivateApex
