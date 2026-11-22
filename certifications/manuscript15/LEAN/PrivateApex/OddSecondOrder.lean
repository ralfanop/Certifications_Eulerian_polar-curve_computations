import PrivateApex.SincExpBounds

/-!
PRIVATE: Manuscript 15, Theorem 7.4 to second order, and the even-order corollary.

Second-order Laplace expansion of `W(N) = ∫_0^∞ u² |sin u/u|^(N+2) du`, `M = N + 2`:

  `|W(N) - I_M (1 - 3/(4M) + 29/(160M²))| ≤ 4438 I_M / M³ + 1/((N-1) π^(N-1))`,
  `I_M = ∫_0^∞ u² e^(-Mu²/6) du`,

from the pointwise enclosures of `SincExpBounds` and exact Gaussian moments.  With
`s_n = (4D/π) W(D)`, `D = n + 1` (`OddSlopeTail.slopeQ_odd_eq_integral`) this gives, for the
actual Eulerian numbers and with no hypothesis,

* `odd_slope_second_order`:
    `|s_n - √(216/(πD)) (1 - 15/(4D) + 1829/(160D²))| ≤ K D^(-7/2)`  (odd `n ≥ 3`);
* `even_slope_second_order` (through the transfer `even_slope_second_order_coefficients`):
    `|t_n - 2 √(216/(πN)) (1 - 33/(4N) + 7589/(160N²))| ≤ K N^(-7/2)`  (even `n ≥ 4`, `N = n+1`).
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PrivateApex
open Real Set MeasureTheory Filter Topology
open EulerianCert.CentralSlope (Mom integrable_mom integral_mom Mom_eq_Gamma Mom_one
  pow_mul_bound_k)

/-! ### Gaussian monomials on the half-line -/

/-- `u^(2k) e^(-Mu²/6)`. -/
def gm (M : ℝ) (k : ℕ) (u : ℝ) : ℝ := u ^ (2 * k) * exp (-(M / 6) * u ^ 2)

theorem gm_nonneg (M : ℝ) (k : ℕ) (u : ℝ) : 0 ≤ gm M k u := by
  unfold gm
  have : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
  positivity

theorem gm_integrable {M : ℝ} (hM : 0 < M) (k : ℕ) : Integrable (gm M k) :=
  integrable_mom (b := M / 6) (by positivity) k

/-- `∫_0^∞ u^(2k) e^(-Mu²/6) du`. -/
def hm (M : ℝ) (k : ℕ) : ℝ := ∫ u in Ioi (0 : ℝ), gm M k u

theorem hm_nonneg (M : ℝ) (k : ℕ) : 0 ≤ hm M k :=
  setIntegral_nonneg measurableSet_Ioi (fun u _ => gm_nonneg M k u)

theorem hm_eq {M : ℝ} (hM : 0 < M) (k : ℕ) :
    hm M k = Mom k / (2 * ((M / 6) ^ k * √(M / 6))) := by
  have h := integral_comp_abs (f := gm M k)
  have e : (fun x : ℝ => gm M k |x|) = gm M k := by
    funext x; unfold gm; rw [pow_mul, sq_abs, ← pow_mul]
  rw [e] at h
  have h2 : ∫ x : ℝ, gm M k x = Mom k / ((M / 6) ^ k * √(M / 6)) :=
    integral_mom (b := M / 6) (by positivity) k
  have h3 : ∫ x in Ioi (0 : ℝ), gm M k x = (∫ x : ℝ, gm M k x) / 2 := by rw [h]; ring
  unfold hm
  rw [h3, h2, div_div]
  ring

theorem Mom_succ (k : ℕ) : Mom (k + 1) = ((k : ℝ) + 1 / 2) * Mom k := by
  rw [Mom_eq_Gamma, Mom_eq_Gamma]
  have h : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
  rw [← Real.Gamma_add_one h]
  congr 1; push_cast; ring

theorem hm_succ {M : ℝ} (hM : 0 < M) (k : ℕ) :
    hm M (k + 1) = (6 * (k : ℝ) + 3) / M * hm M k := by
  have hs : 0 < √(M / 6) := sqrt_pos.mpr (by positivity)
  rw [hm_eq hM, hm_eq hM, Mom_succ, pow_succ]
  field_simp
  ring

theorem hm_values {M : ℝ} (hM : 0 < M) :
    hm M 3 = 135 / M ^ 2 * hm M 1 ∧ hm M 4 = 2835 / M ^ 3 * hm M 1 ∧
    hm M 5 = 76545 / M ^ 4 * hm M 1 ∧ hm M 6 = 2525985 / M ^ 5 * hm M 1 ∧
    hm M 7 = 98513415 / M ^ 6 * hm M 1 := by
  have h2 : hm M 2 = 9 / M * hm M 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, hm_succ hM 1]; norm_num
  have h3 : hm M 3 = 15 / M * hm M 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, hm_succ hM 2]; norm_num
  have h4 : hm M 4 = 21 / M * hm M 3 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, hm_succ hM 3]; norm_num
  have h5 : hm M 5 = 27 / M * hm M 4 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, hm_succ hM 4]; norm_num
  have h6 : hm M 6 = 33 / M * hm M 5 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, hm_succ hM 5]; norm_num
  have h7 : hm M 7 = 39 / M * hm M 6 := by
    rw [show (7 : ℕ) = 6 + 1 from rfl, hm_succ hM 6]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h3, h2]; ring
  · rw [h4, h3, h2]; ring
  · rw [h5, h4, h3, h2]; ring
  · rw [h6, h5, h4, h3, h2]; ring
  · rw [h7, h6, h5, h4, h3, h2]; ring

/-- Integral of a linear combination of the Gaussian monomials of orders `1, 3, 4, 5, 6, 7`. -/
theorem lin6 {M : ℝ} (hM : 0 < M) (c1 c3 c4 c5 c6 c7 : ℝ) :
    IntegrableOn (fun u => c1 * gm M 1 u + c3 * gm M 3 u + c4 * gm M 4 u + c5 * gm M 5 u +
      c6 * gm M 6 u + c7 * gm M 7 u) (Ioi (0 : ℝ)) ∧
    ∫ u in Ioi (0 : ℝ), (c1 * gm M 1 u + c3 * gm M 3 u + c4 * gm M 4 u + c5 * gm M 5 u +
      c6 * gm M 6 u + c7 * gm M 7 u) =
      c1 * hm M 1 + c3 * hm M 3 + c4 * hm M 4 + c5 * hm M 5 + c6 * hm M 6 + c7 * hm M 7 := by
  have i (c : ℝ) (k : ℕ) : IntegrableOn (fun u => c * gm M k u) (Ioi (0 : ℝ)) :=
    ((gm_integrable hM k).const_mul c).integrableOn
  have e (c : ℝ) (k : ℕ) : ∫ u in Ioi (0 : ℝ), c * gm M k u = c * hm M k := by
    unfold hm; exact integral_const_mul c _
  have i13 : IntegrableOn (fun u => c1 * gm M 1 u + c3 * gm M 3 u) (Ioi (0 : ℝ)) :=
    (i c1 1).add (i c3 3)
  have i134 : IntegrableOn (fun u => c1 * gm M 1 u + c3 * gm M 3 u + c4 * gm M 4 u)
      (Ioi (0 : ℝ)) := i13.add (i c4 4)
  have i1345 : IntegrableOn (fun u => c1 * gm M 1 u + c3 * gm M 3 u + c4 * gm M 4 u +
      c5 * gm M 5 u) (Ioi (0 : ℝ)) := i134.add (i c5 5)
  have i13456 : IntegrableOn (fun u => c1 * gm M 1 u + c3 * gm M 3 u + c4 * gm M 4 u +
      c5 * gm M 5 u + c6 * gm M 6 u) (Ioi (0 : ℝ)) := i1345.add (i c6 6)
  refine ⟨i13456.add (i c7 7), ?_⟩
  rw [integral_add i13456 (i c7 7), integral_add i1345 (i c6 6), integral_add i134 (i c5 5),
    integral_add i13 (i c4 4), integral_add (i c1 1) (i c3 3), e, e, e, e, e, e]

/-! ### Dominating and minorising functions -/

/-- Upper comparison function on `[0, π]`. -/
def Hdom (M u : ℝ) : ℝ :=
  u ^ 2 * exp (-(M / 6) * u ^ 2) * Pup M u + u ^ 8 * exp (-(M / 6) * u ^ 2)

/-- Lower comparison function on `(0, ∞)`. -/
def Ldom (M u : ℝ) : ℝ :=
  u ^ 2 * exp (-(M / 6) * u ^ 2) * (Plow M u - u ^ 6 - M ^ 2 / 2 * (1 / 180) ^ 2 * u ^ 12)

theorem Hdom_eq (M u : ℝ) : Hdom M u =
    1 * gm M 1 u + -(M / 180) * gm M 3 u + (-(M / 2835) + 1) * gm M 4 u +
    (M / 1000 + M ^ 2 / 2 * (1 / 180) ^ 2) * gm M 5 u +
    (M ^ 2 / 2 * (2 * (1 / 180) * (1 / 2835))) * gm M 6 u +
    (M ^ 2 / 2 * (1 / 2835) ^ 2) * gm M 7 u := by
  unfold Hdom Pup gm; ring

theorem Ldom_eq (M u : ℝ) : Ldom M u =
    1 * gm M 1 u + -(M / 180) * gm M 3 u + (-(M / 2835) - 1) * gm M 4 u +
    (-(M / 1000) + M ^ 2 / 2 * (1 / 180) ^ 2) * gm M 5 u + 0 * gm M 6 u +
    (-(M ^ 3 / 6 * (7 / 1000) ^ 3) - M ^ 2 / 2 * (1 / 180) ^ 2) * gm M 7 u := by
  unfold Ldom Plow gm; ring

theorem Hdom_nonneg {M : ℝ} (hM : 0 ≤ M) (u : ℝ) : 0 ≤ Hdom M u := by
  unfold Hdom
  exact add_nonneg (mul_nonneg (by positivity) (Pup_nonneg hM u)) (by positivity)

theorem Hdom_integral {M : ℝ} (hM : 1 ≤ M) :
    IntegrableOn (fun u => Hdom M u) (Ioi (0 : ℝ)) ∧
    ∫ u in Ioi (0 : ℝ), Hdom M u ≤
      hm M 1 * (1 - 3 / (4 * M) + 29 / (160 * M ^ 2) + 2924 / M ^ 3) := by
  have hM0 : 0 < M := by linarith
  obtain ⟨hi, he⟩ := lin6 hM0 1 (-(M / 180)) (-(M / 2835) + 1)
    (M / 1000 + M ^ 2 / 2 * (1 / 180) ^ 2) (M ^ 2 / 2 * (2 * (1 / 180) * (1 / 2835)))
    (M ^ 2 / 2 * (1 / 2835) ^ 2)
  simp only [Hdom_eq]
  refine ⟨hi, ?_⟩
  rw [he]
  obtain ⟨h3, h4, h5, h6, h7⟩ := hm_values hM0
  rw [h3, h4, h5, h6, h7]
  have h1 := hm_nonneg M 1
  have key : 1 * hm M 1 + -(M / 180) * (135 / M ^ 2 * hm M 1) +
      (-(M / 2835) + 1) * (2835 / M ^ 3 * hm M 1) +
      (M / 1000 + M ^ 2 / 2 * (1 / 180) ^ 2) * (76545 / M ^ 4 * hm M 1) +
      M ^ 2 / 2 * (2 * (1 / 180) * (1 / 2835)) * (2525985 / M ^ 5 * hm M 1) +
      M ^ 2 / 2 * (1 / 2835) ^ 2 * (98513415 / M ^ 6 * hm M 1) =
      hm M 1 * (1 - 3 / (4 * M) + 29 / (160 * M ^ 2) + 583299 / (200 * M ^ 3) +
        429 / (70 * M ^ 4)) := by
    field_simp
    ring
  rw [key]
  apply mul_le_mul_of_nonneg_left _ h1
  have hp3 : 0 < M ^ 3 := pow_pos hM0 3
  have h43 : 429 / (70 * M ^ 4) ≤ 429 / (70 * M ^ 3) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have e3 : 583299 / (200 * M ^ 3) + 429 / (70 * M ^ 3) =
      (583299 / 200 + 429 / 70) / M ^ 3 := by ring
  have e4 : (583299 / 200 + 429 / 70 : ℝ) / M ^ 3 ≤ 2924 / M ^ 3 :=
    div_le_div_of_nonneg_right (by norm_num) hp3.le
  linarith

theorem Ldom_integral {M : ℝ} (hM : 1 ≤ M) :
    IntegrableOn (fun u => Ldom M u) (Ioi (0 : ℝ)) ∧
    hm M 1 * (1 - 3 / (4 * M) + 29 / (160 * M ^ 2) - 4438 / M ^ 3) ≤
      ∫ u in Ioi (0 : ℝ), Ldom M u := by
  have hM0 : 0 < M := by linarith
  obtain ⟨hi, he⟩ := lin6 hM0 1 (-(M / 180)) (-(M / 2835) - 1)
    (-(M / 1000) + M ^ 2 / 2 * (1 / 180) ^ 2) 0
    (-(M ^ 3 / 6 * (7 / 1000) ^ 3) - M ^ 2 / 2 * (1 / 180) ^ 2)
  simp only [Ldom_eq]
  refine ⟨hi, ?_⟩
  rw [he]
  obtain ⟨h3, h4, h5, h6, h7⟩ := hm_values hM0
  rw [h3, h4, h5, h6, h7]
  have h1 := hm_nonneg M 1
  have key : 1 * hm M 1 + -(M / 180) * (135 / M ^ 2 * hm M 1) +
      (-(M / 2835) - 1) * (2835 / M ^ 3 * hm M 1) +
      (-(M / 1000) + M ^ 2 / 2 * (1 / 180) ^ 2) * (76545 / M ^ 4 * hm M 1) +
      0 * (2525985 / M ^ 5 * hm M 1) +
      (-(M ^ 3 / 6 * (7 / 1000) ^ 3) - M ^ 2 / 2 * (1 / 180) ^ 2) *
        (98513415 / M ^ 6 * hm M 1) =
      hm M 1 * (1 - 3 / (4 * M) + 29 / (160 * M ^ 2) - 1166870673423 / (400000000 * M ^ 3) -
        243243 / (160 * M ^ 4)) := by
    field_simp
    ring
  rw [key]
  apply mul_le_mul_of_nonneg_left _ h1
  have hp3 : 0 < M ^ 3 := pow_pos hM0 3
  have h43 : 243243 / (160 * M ^ 4) ≤ 243243 / (160 * M ^ 3) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have e3 : 1166870673423 / (400000000 * M ^ 3) + 243243 / (160 * M ^ 3) =
      (1166870673423 / 400000000 + 243243 / 160) / M ^ 3 := by ring
  have e4 : (1166870673423 / 400000000 + 243243 / 160 : ℝ) / M ^ 3 ≤ 4438 / M ^ 3 :=
    div_le_div_of_nonneg_right (by norm_num) hp3.le
  linarith

/-! ### Two-sided bound for the half-line integral of the weight -/

theorem weight_integral_le_dom (N : ℕ) (hN : 2 ≤ N) {H : ℝ → ℝ}
    (hHi : IntegrableOn H (Ioi (0 : ℝ))) (hH0 : ∀ x, 0 ≤ H x)
    (hdom : ∀ x ∈ Icc (0 : ℝ) π, weight N x ≤ H x) :
    (∫ x in Ioi (0 : ℝ), weight N x) ≤
      (∫ x in Ioi (0 : ℝ), H x) + (∫ x in Ioi π, 1 / x ^ N) := by
  have hi := weight_integrable_half N hN
  have hs := hi.mono_set (show Ioc (0 : ℝ) π ⊆ Ioi 0 from fun x hx => hx.1)
  have ht := hi.mono_set (Ioi_subset_Ioi pi_pos.le)
  have hu : Ioc (0 : ℝ) π ∪ Ioi π = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact pi_pos.trans h
    · intro h
      by_cases hp : x ≤ π
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr (lt_of_not_ge hp)
  have hd : Disjoint (Ioc (0 : ℝ) π) (Ioi π) := by
    rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hx.2) hy
  have he : (∫ x in Ioi (0 : ℝ), weight N x) =
      (∫ x in Ioc (0 : ℝ) π, weight N x) + (∫ x in Ioi π, weight N x) := by
    rw [← hu, setIntegral_union hd measurableSet_Ioi hs ht]
  rw [he]
  apply add_le_add
  · apply (setIntegral_mono_on hs (hHi.mono_set (fun x hx => hx.1)) measurableSet_Ioc
      (fun x hx => hdom x ⟨hx.1.le, hx.2⟩)).trans
    exact setIntegral_mono_set hHi (Eventually.of_forall (fun x => hH0 x))
      (Eventually.of_forall (fun x hx => hx.1))
  · exact setIntegral_mono_on ht (tail_integrable N hN) measurableSet_Ioi
      (fun x hx => weight_le_tail N hx.le)

theorem W_upper (N : ℕ) (hN : 2 ≤ N) :
    (∫ x in Ioi (0 : ℝ), weight N x) ≤
      hm ((N : ℝ) + 2) 1 * (1 - 3 / (4 * ((N : ℝ) + 2)) + 29 / (160 * ((N : ℝ) + 2) ^ 2) +
        2924 / ((N : ℝ) + 2) ^ 3) + 1 / (((N : ℝ) - 1) * π ^ (N - 1)) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hM : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  have hM0 : (0 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  obtain ⟨hi, hI⟩ := Hdom_integral hM
  have hdom : ∀ x ∈ Icc (0 : ℝ) π, weight N x ≤ Hdom ((N : ℝ) + 2) x := by
    intro x hx
    have hE : 0 ≤ exp (-(((N : ℝ) + 2) / 6) * x ^ 2) := (exp_pos _).le
    unfold Hdom
    by_cases h1 : x ≤ 1
    · have h := weight_le_Pup N hx.1 h1
      have h8 : 0 ≤ x ^ 8 * exp (-(((N : ℝ) + 2) / 6) * x ^ 2) := by positivity
      linarith
    · have h1' : 1 ≤ x := (not_le.mp h1).le
      have hg := weight_le_gauss N hx
      unfold gauss at hg
      have hp : 0 ≤ x ^ 2 * exp (-(((N : ℝ) + 2) / 6) * x ^ 2) * Pup ((N : ℝ) + 2) x :=
        mul_nonneg (by positivity) (Pup_nonneg hM0 x)
      have h28 : x ^ 2 ≤ x ^ 8 := pow_le_pow_right₀ h1' (by norm_num)
      have := mul_le_mul_of_nonneg_right h28 hE
      linarith
  have h := weight_integral_le_dom N hN hi (Hdom_nonneg hM0) hdom
  rw [tail_half_integral N hN] at h
  linarith

theorem W_lower (N : ℕ) (hN : 2 ≤ N) :
    hm ((N : ℝ) + 2) 1 * (1 - 3 / (4 * ((N : ℝ) + 2)) + 29 / (160 * ((N : ℝ) + 2) ^ 2) -
        4438 / ((N : ℝ) + 2) ^ 3) ≤ ∫ x in Ioi (0 : ℝ), weight N x := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hM : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  have hM0 : (0 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  obtain ⟨hi, hI⟩ := Ldom_integral hM
  refine hI.trans (setIntegral_mono_on hi (weight_integrable_half N hN) measurableSet_Ioi ?_)
  intro x hx
  have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
  have hE : 0 ≤ exp (-(((N : ℝ) + 2) / 6) * x ^ 2) := (exp_pos _).le
  unfold Ldom
  by_cases h1 : x ≤ 1
  · have h := Plow_le_weight N hx0 h1
    have hc : 0 ≤ x ^ 2 * exp (-(((N : ℝ) + 2) / 6) * x ^ 2) *
        (x ^ 6 + ((N : ℝ) + 2) ^ 2 / 2 * (1 / 180) ^ 2 * x ^ 12) := by positivity
    linarith
  · have h1' : 1 ≤ x := (not_le.mp h1).le
    have hw := weight_nonneg N x
    have hneg : Plow ((N : ℝ) + 2) x - x ^ 6 -
        ((N : ℝ) + 2) ^ 2 / 2 * (1 / 180) ^ 2 * x ^ 12 ≤ 0 := by
      unfold Plow
      have h6 : 1 ≤ x ^ 6 := one_le_pow₀ h1'
      have h812 : x ^ 8 ≤ x ^ 12 := pow_le_pow_right₀ h1' (by norm_num)
      have t1 : 0 ≤ ((N : ℝ) + 2) / 180 * x ^ 4 := by positivity
      have t2 : 0 ≤ ((N : ℝ) + 2) / 2835 * x ^ 6 := by positivity
      have t3 : 0 ≤ ((N : ℝ) + 2) / 1000 * x ^ 8 := by positivity
      have t4 : 0 ≤ ((N : ℝ) + 2) ^ 3 / 6 * (7 / 1000) ^ 3 * x ^ 12 := by positivity
      have t5 := mul_nonneg (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 2) ^ 2 / 2 * (1 / 180) ^ 2)
        (sub_nonneg.mpr h812)
      nlinarith
    have := mul_nonpos_of_nonneg_of_nonpos
      (by positivity : (0 : ℝ) ≤ x ^ 2 * exp (-(((N : ℝ) + 2) / 6) * x ^ 2)) hneg
    linarith

/-! ### From the exponent `M = D + 2` to the order parameter `D` -/

theorem sqrt_mul_cube {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) : √(x * r ^ 3) = √x * r * √r := by
  have h : √(r ^ 2) = r := sqrt_sq hr
  calc √(x * r ^ 3) = √(x * r ^ 2 * r) := by congr 1; ring
    _ = √x * √(r ^ 2) * √r := by
        rw [sqrt_mul (mul_nonneg hx (sq_nonneg r)), sqrt_mul hx]
    _ = √x * r * √r := by rw [h]

theorem G_eq {D : ℝ} (hD : 0 < D) :
    √(216 * D ^ 2 / (π * (D + 2) ^ 3)) = sig D * (D / (D + 2)) * √(D / (D + 2)) := by
  unfold sig
  rw [← sqrt_mul_cube (by positivity) (by positivity)]
  congr 1
  field_simp

theorem four_D_hm {D : ℝ} (hD : 0 < D) :
    4 * D / π * hm (D + 2) 1 = sig D * (D / (D + 2)) * √(D / (D + 2)) := by
  have hM : (0 : ℝ) < D + 2 := by linarith
  have hs : 0 < √((D + 2) / 6) := sqrt_pos.mpr (by positivity)
  have e : hm (D + 2) 1 = √π / (4 * ((D + 2) / 6) * √((D + 2) / 6)) := by
    rw [hm_eq hM, Mom_one, pow_one]
    field_simp
    ring
  rw [← G_eq hD, ← gauss_term_eq hD, e]

theorem sqrt_le_self_of_one_le {D : ℝ} (hD : 1 ≤ D) : √D ≤ D := by
  have h0 : 0 ≤ D := by linarith
  calc √D ≤ √(D ^ 2) := sqrt_le_sqrt (by nlinarith)
    _ = D := sqrt_sq h0

/-- The contribution of `u ≥ π` is below every power of `1/n`. -/
theorem tail_bound {c : ℝ} (n : ℕ) (hn : 2 ≤ n) (hc : (n : ℝ) ^ 4 * (1 / 3) ^ n ≤ c) :
    4 * (n : ℝ) / (((n : ℝ) - 1) * π ^ n) ≤ 8 * |c| / ((n : ℝ) ^ 3 * √(n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hpow : (1 : ℝ) ≤ ((1 : ℝ) / 3) ^ n * π ^ n := by
    rw [← mul_pow]; exact one_le_pow₀ (by linarith [pi_gt_three])
  have ht1 : 4 * (n : ℝ) / (((n : ℝ) - 1) * π ^ n) ≤ 8 * ((1 : ℝ) / 3) ^ n := by
    rw [div_le_iff₀ (mul_pos hn1 (pow_pos pi_pos n))]
    calc 4 * (n : ℝ) ≤ 8 * ((n : ℝ) - 1) * 1 := by linarith
      _ ≤ 8 * ((n : ℝ) - 1) * (((1 : ℝ) / 3) ^ n * π ^ n) :=
          mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = 8 * ((1 : ℝ) / 3) ^ n * (((n : ℝ) - 1) * π ^ n) := by ring
  have ht2 : ((1 : ℝ) / 3) ^ n ≤ |c| / (n : ℝ) ^ 4 := by
    rw [le_div_iff₀ (pow_pos hn0 4)]
    linarith [le_abs_self c]
  have hsD : √(n : ℝ) ≤ (n : ℝ) := sqrt_le_self_of_one_le (by linarith)
  have hsD0 : 0 < √(n : ℝ) := sqrt_pos.mpr hn0
  have ht3 : |c| / (n : ℝ) ^ 4 ≤ |c| / ((n : ℝ) ^ 3 * √(n : ℝ)) := by
    apply div_le_div_of_nonneg_left (abs_nonneg c) (by positivity)
    calc (n : ℝ) ^ 3 * √(n : ℝ) ≤ (n : ℝ) ^ 3 * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hsD (by positivity)
      _ = (n : ℝ) ^ 4 := by ring
  calc 4 * (n : ℝ) / (((n : ℝ) - 1) * π ^ n) ≤ 8 * ((1 : ℝ) / 3) ^ n := ht1
    _ ≤ 8 * (|c| / ((n : ℝ) ^ 3 * √(n : ℝ))) := by linarith
    _ = 8 * |c| / ((n : ℝ) ^ 3 * √(n : ℝ)) := by ring

/-- `(1+2/D)^(-3/2) (1 - 3/(4(D+2)) + 29/(160(D+2)²)) = 1 - 15/(4D) + 1829/(160D²) + O(D⁻³)`. -/
theorem ratio_bound_MD {D : ℝ} (hD : 2 ≤ D) :
    |D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) * √(D / (D + 2)) -
        (1 - 15 / (4 * D) + 1829 / (160 * D ^ 2))| ≤ 229 / D ^ 3 := by
  have hD0 : 0 < D := by linarith
  obtain ⟨-, hU, hL⟩ := rho_bounds (N := D / 2) (by linarith)
  have e0 : D / 2 / (D / 2 + 1) = D / (D + 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e1 : 1 / (2 * (D / 2)) = 1 / D := by congr 1; ring
  have e2 : 3 / (8 * (D / 2) ^ 2) = 3 / (2 * D ^ 2) := by congr 1; ring
  have e3 : 5 / (16 * (D / 2) ^ 3) = 5 / (2 * D ^ 3) := by congr 1; ring
  rw [e0, e1, e2] at hU
  rw [e0, e1, e2, e3] at hL
  have hρ : |√(D / (D + 2)) - (1 - 1 / D + 3 / (2 * D ^ 2))| ≤ 5 / (2 * D ^ 3) := by
    have h5 : (0 : ℝ) ≤ 5 / (2 * D ^ 3) := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hr0 : 0 ≤ D / (D + 2) := by positivity
  have hr1 : D / (D + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have ha : 3 / (4 * (D + 2)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have ha0 : 0 ≤ 3 / (4 * (D + 2)) := by positivity
  have hb : 29 / (160 * (D + 2) ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hb0 : 0 ≤ 29 / (160 * (D + 2) ^ 2) := by positivity
  have hR : |D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2))| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg hr0, abs_of_nonneg (by linarith)]
    calc D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) ≤ 1 * 2 :=
          mul_le_mul hr1 (by linarith) (by linarith) (by norm_num)
      _ = 2 := one_mul 2
  have hkey : D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
        (1 - 1 / D + 3 / (2 * D ^ 2)) - (1 - 15 / (4 * D) + 1829 / (160 * D ^ 2)) =
      -((9406 * D ^ 2 + 33009 * D + 29264) / (320 * D ^ 2 * (D + 2) ^ 3)) := by
    field_simp
    ring
  have hRU : |D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
        (1 - 1 / D + 3 / (2 * D ^ 2)) - (1 - 15 / (4 * D) + 1829 / (160 * D ^ 2))| ≤
      224 / D ^ 3 := by
    have hden : 0 < 320 * D ^ 2 * (D + 2) ^ 3 := by positivity
    rw [hkey, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ hden (by positivity)]
    have p3 : 0 < D ^ 3 := pow_pos hD0 3
    have p4 : 0 < D ^ 4 := pow_pos hD0 4
    have p5 : 0 < D ^ 5 := pow_pos hD0 5
    have p2 : 0 < D ^ 2 := pow_pos hD0 2
    nlinarith
  have hsplit : D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
        √(D / (D + 2)) - (1 - 15 / (4 * D) + 1829 / (160 * D ^ 2)) =
      D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
        (√(D / (D + 2)) - (1 - 1 / D + 3 / (2 * D ^ 2))) +
      (D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
        (1 - 1 / D + 3 / (2 * D ^ 2)) - (1 - 15 / (4 * D) + 1829 / (160 * D ^ 2))) := by ring
  rw [hsplit]
  calc |D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
          (√(D / (D + 2)) - (1 - 1 / D + 3 / (2 * D ^ 2))) +
        (D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
          (1 - 1 / D + 3 / (2 * D ^ 2)) - (1 - 15 / (4 * D) + 1829 / (160 * D ^ 2)))|
      ≤ |D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
          (√(D / (D + 2)) - (1 - 1 / D + 3 / (2 * D ^ 2)))| +
        |D / (D + 2) * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2)) *
          (1 - 1 / D + 3 / (2 * D ^ 2)) - (1 - 15 / (4 * D) + 1829 / (160 * D ^ 2))| :=
        abs_add_le _ _
    _ ≤ 2 * (5 / (2 * D ^ 3)) + 224 / D ^ 3 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hR hρ (abs_nonneg _) (by norm_num)) hRU
    _ = 229 / D ^ 3 := by ring

/-! ### Second-order expansions of the actual central slopes -/

/-- **Odd central slopes to second order** (Manuscript 15, Theorem 7.4 with `J = 3`), for the
actual Eulerian numbers: for odd `n = 2j+1 ≥ 3` and `D = n + 1`,
`|s_n - √(216/(πD)) (1 - 15/(4D) + 1829/(160D²))| ≤ K D^(-7/2)`. -/
theorem odd_slope_second_order : ∃ K, ∀ j : ℕ, 1 ≤ j →
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        (1 + (-15 / 4) / ((2 * j + 2 : ℕ) : ℝ) +
          (1829 / 160) / ((2 * j + 2 : ℕ) : ℝ) ^ 2)| ≤
      K / (((2 * j + 2 : ℕ) : ℝ) ^ 3 * √((2 * j + 2 : ℕ) : ℝ)) := by
  obtain ⟨c, hc⟩ := pow_mul_bound_k 4 (r := 1 / 3) (by norm_num) (by norm_num)
  refine ⟨√(216 / π) * 4667 + 8 * |c|, fun j hj => ?_⟩
  have hDnat : 2 ≤ 2 * j + 2 := by omega
  have hs := slopeQ_odd_eq_integral hj
  have hU := W_upper (2 * j + 2) hDnat
  have hL := W_lower (2 * j + 2) hDnat
  have htb := tail_bound (2 * j + 2) hDnat (hc (2 * j + 2))
  have htail := tail_term_eq (2 * j + 2) hDnat
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ((2 * j + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hDdef] at hs hU hL htb htail ⊢
  have hD4 : (4 : ℝ) ≤ D := by
    rw [hDdef]; exact_mod_cast (show 4 ≤ 2 * j + 2 by omega)
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D - 1 := by linarith
  -- abbreviations
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∫ x in Ioi (0 : ℝ), weight (2 * j + 2) x := ⟨_, rfl⟩
  obtain ⟨mn, hmn⟩ : ∃ mn : ℝ, mn = 1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2 : ℝ, q2 = 1 / (D + 2) ^ 3 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 / D ^ 3 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = sig D * (D / (D + 2)) * √(D / (D + 2)) := ⟨_, rfl⟩
  obtain ⟨t4, ht4⟩ : ∃ t4 : ℝ, t4 = 4 * D / ((D - 1) * π ^ (2 * j + 2)) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ 4 * D / π := by positivity
  have hκI : 4 * D / π * hm (D + 2) 1 = B := by rw [hB]; exact four_D_hm hD0
  rw [← hW] at hs hU hL
  have hq20 : 0 ≤ q2 := by rw [hq2]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq2q : q2 ≤ q := by
    rw [hq2, hq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ hD0.le (by linarith) 3
  have hS0 : 0 ≤ sig D := sig_nonneg D
  have hr0 : 0 ≤ D / (D + 2) := by positivity
  have hr1 : D / (D + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hsr0 : 0 ≤ √(D / (D + 2)) := sqrt_nonneg _
  have hsr1 : √(D / (D + 2)) ≤ 1 := by
    rw [show (1 : ℝ) = √1 from sqrt_one.symm]; exact sqrt_le_sqrt hr1
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBS : B ≤ sig D := by
    rw [hB]
    calc sig D * (D / (D + 2)) * √(D / (D + 2)) ≤ sig D * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr1 hS0) hsr1 hsr0 (by linarith)
      _ = sig D := by ring
  have hBq : B * q2 ≤ sig D * q := mul_le_mul hBS hq2q hq20 hS0
  -- upper and lower bounds for the slope
  have h1 : ((slopeQ (2 * j + 1) : ℚ) : ℝ) ≤ B * (mn + 2924 * q2) + t4 := by
    rw [hs]
    calc 4 * D / π * W
        ≤ 4 * D / π * (hm (D + 2) 1 * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2) +
            2924 / (D + 2) ^ 3) + 1 / ((D - 1) * π ^ (2 * j + 2 - 1))) :=
          mul_le_mul_of_nonneg_left hU hκ0
      _ = 4 * D / π * hm (D + 2) 1 * (mn + 2924 * q2) +
          4 * D / π * (1 / ((D - 1) * π ^ (2 * j + 2 - 1))) := by rw [hmn, hq2]; ring
      _ = B * (mn + 2924 * q2) + t4 := by rw [hκI, htail, ht4]
  have h2 : B * (mn - 4438 * q2) ≤ ((slopeQ (2 * j + 1) : ℚ) : ℝ) := by
    rw [hs]
    calc B * (mn - 4438 * q2)
        = 4 * D / π * (hm (D + 2) 1 * (1 - 3 / (4 * (D + 2)) + 29 / (160 * (D + 2) ^ 2) -
            4438 / (D + 2) ^ 3)) := by rw [← hκI, hmn, hq2]; ring
      _ ≤ 4 * D / π * W := mul_le_mul_of_nonneg_left hL hκ0
  -- conversion from `D + 2` to `D`
  have hratio := ratio_bound_MD (D := D) (by linarith)
  rw [← hmn] at hratio
  have hT : (1 : ℝ) + (-15 / 4) / D + (1829 / 160) / D ^ 2 =
      1 - 15 / (4 * D) + 1829 / (160 * D ^ 2) := by
    field_simp
    ring
  rw [hT]
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 - 15 / (4 * D) + 1829 / (160 * D ^ 2) := ⟨_, rfl⟩
  rw [← hTdef] at hratio ⊢
  have hr : |B * mn - sig D * T| ≤ sig D * (229 * q) := by
    have e : B * mn - sig D * T =
        sig D * (D / (D + 2) * mn * √(D / (D + 2)) - T) := by rw [hB]; ring
    rw [e, abs_mul, abs_of_nonneg hS0, hq]
    apply mul_le_mul_of_nonneg_left _ hS0
    calc |D / (D + 2) * mn * √(D / (D + 2)) - T| ≤ 229 / D ^ 3 := hratio
      _ = 229 * (1 / D ^ 3) := by ring
  -- the exponentially small tail
  have ht40 : 0 ≤ t4 := by rw [ht4]; positivity
  have ht : t4 ≤ 8 * |c| / (D ^ 3 * √D) := by rw [ht4]; exact htb
  -- assembly
  have hSq : sig D * (4667 * q) = √(216 / π) * 4667 / (D ^ 3 * √D) := by
    have hsD0 : 0 < √D := sqrt_pos.mpr hD0
    rw [sig_eq hD0, hq]
    field_simp
  have hmain : |((slopeQ (2 * j + 1) : ℚ) : ℝ) - sig D * T| ≤ sig D * (4667 * q) + t4 := by
    obtain ⟨hr1', hr2'⟩ := abs_le.mp hr
    have hB2 : 0 ≤ B * q2 := mul_nonneg hB0 hq20
    have hSq0 : 0 ≤ sig D * q := mul_nonneg hS0 hq0
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hfin : sig D * (4667 * q) + t4 ≤
      (√(216 / π) * 4667 + 8 * |c|) / (D ^ 3 * √D) := by
    rw [hSq, add_div]
    linarith
  have hsig : √(216 / (π * D)) = sig D := rfl
  rw [hsig]
  exact hmain.trans hfin

/-- The same statement with the coefficients in the form `1 - 15/(4D) + 1829/(160D²)`. -/
theorem odd_slope_second_order' : ∃ K, ∀ j : ℕ, 1 ≤ j →
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        (1 - 15 / (4 * ((2 * j + 2 : ℕ) : ℝ)) + 1829 / (160 * ((2 * j + 2 : ℕ) : ℝ) ^ 2))| ≤
      K / (((2 * j + 2 : ℕ) : ℝ) ^ 3 * √((2 * j + 2 : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := odd_slope_second_order
  refine ⟨K, fun j hj => ?_⟩
  have h := hK j hj
  have hD0 : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
  have e : (1 : ℝ) + (-15 / 4) / ((2 * j + 2 : ℕ) : ℝ) +
      (1829 / 160) / ((2 * j + 2 : ℕ) : ℝ) ^ 2 =
      1 - 15 / (4 * ((2 * j + 2 : ℕ) : ℝ)) + 1829 / (160 * ((2 * j + 2 : ℕ) : ℝ) ^ 2) := by
    field_simp
    ring
  rw [e] at h
  exact h

/-- **Even central slopes to second order** (unconditional): for even `n = 2m ≥ 4`, `N = n+1`,
`|t_n - 2 √(216/(πN)) (1 - 33/(4N) + 7589/(160N²))| ≤ K N^(-7/2)`. -/
theorem even_slope_second_order : ∃ K, ∀ m : ℕ, 2 ≤ m →
    |((slopeQ (2 * m) : ℚ) : ℝ) - 2 * √(216 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        (1 - 33 / (4 * ((2 * m + 1 : ℕ) : ℝ)) +
          7589 / (160 * ((2 * m + 1 : ℕ) : ℝ) ^ 2))| ≤
      K / (((2 * m + 1 : ℕ) : ℝ) ^ 3 * √((2 * m + 1 : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := odd_slope_second_order
  exact ⟨_, fun m hm => even_slope_second_order_coefficients K 1 hK m hm (by omega)⟩

#print axioms hm_values
#print axioms W_upper
#print axioms W_lower
#print axioms ratio_bound_MD
#print axioms odd_slope_second_order
#print axioms odd_slope_second_order'
#print axioms even_slope_second_order
end PrivateApex
