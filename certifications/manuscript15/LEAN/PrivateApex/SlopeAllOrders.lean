import PrivateApex.LaplaceAllOrders
import Mathlib.Analysis.Analytic.Binomial

/-!
PRIVATE.  Manuscript 15, Section 7: the central slopes to every asymptotic order.

For odd `n = 2j + 1 ≥ 3` and `x = n + 1`,

  `s_n = √(216 / (π x)) * (∑ i < p, dC i / x ^ i + O(x ^ (-p)))`      (`odd_slope_all_orders`),

and for even `n = 2m ≥ 4` and `x = n + 1`,

  `t_n = √(864 / (π x)) * (∑ i < p, eC i / x ^ i + O(x ^ (-p)))`      (`even_slope_all_orders`),

for every `p`.  Here `slopeQ` is the exact rational slope built from the Eulerian numbers.

* `dC` is obtained from the Laplace coefficients `cC` by the substitution `1/(x+2) = z/(1+2z)`,
  `z = 1/x`, and multiplication by `(1 + 2z)^(-3/2)`.
* `eC = evenTransfer dC`, where `evenTransfer` is the formal operation
  `Q(z) = D(z / (1 + z)) / ((1 + z)^(3/2) (1 + 3z))`.  The theorem `even_of_odd_hasExp`
  transfers *any* all-order expansion of the odd slopes to the even slopes through the exact
  identity between consecutive slopes.
* `dC_unique`, `eC_unique`: the coefficient sequences are uniquely determined by the slopes.
* `cC_values`, `dC_values`, `eC_values` give the coefficients up to the sixth order by kernel
  evaluation; `odd_slope_sixth_order` and `even_slope_sixth_order` are the resulting explicit
  statements with remainder `O(x ^ (-7))`.
-/

namespace PrivateApex
open Real Finset MeasureTheory

/-! ### Rational coefficient sequences -/

/-- Coefficients of `(1 + y) ^ (-1/2)`. -/
def binQ : ℕ → ℚ
  | 0 => 1
  | i + 1 => binQ i * (-1 / 2 - i) / (i + 1)

/-- Coefficients of `1 / (1 + c z)`. -/
def geoQ (c : ℚ) (i : ℕ) : ℚ := (-c) ^ i

/-- Coefficients of `(1 + c z) ^ (-1/2)`. -/
def binQc (c : ℚ) (i : ℕ) : ℚ := binQ i * c ^ i

/-- Odd-order coefficients: `D(z) = (1 + 2z)^(-3/2) C(z / (1 + 2z))`. -/
def dC : ℕ → ℚ := cmul (cmul (geoQ 2) (binQc 2)) (ccomp cC (geoQ 2))

/-- The formal transfer from odd to even orders:
`Q(z) = D(z / (1 + z)) / ((1 + z)^(3/2) (1 + 3z))`. -/
def evenTransfer (d : ℕ → ℚ) : ℕ → ℚ :=
  cmul (cmul (cmul (geoQ 1) (geoQ 3)) (binQc 1)) (ccomp d (geoQ 1))

/-- Even-order coefficients. -/
def eC : ℕ → ℚ := evenTransfer dC

/-- The even-order coefficients written directly from the Laplace coefficients:
`Q(z) = (1 + 3z)^(-5/2) C(z / (1 + 3z))`. -/
def eDirect : ℕ → ℚ := cmul (cmul (cmul (geoQ 3) (geoQ 3)) (binQc 3)) (ccomp cC (geoQ 3))

theorem cC_values : cC 0 = 1 ∧ cC 1 = -3 / 4 ∧ cC 2 = 29 / 160 ∧ cC 3 = 351 / 3200 ∧
    cC 4 = 17877 / 358400 ∧ cC 5 = -465741 / 5120000 ∧
    cC 6 = -110563031 / 401408000 := by decide +kernel

theorem dC_values : dC 0 = 1 ∧ dC 1 = -15 / 4 ∧ dC 2 = 1829 / 160 ∧ dC 3 = -101709 / 3200 ∧
    dC 4 = 29934309 / 358400 ∧ dC 5 = -7564058487 / 35840000 ∧
    dC 6 = 1040050193381 / 2007040000 := by decide +kernel

theorem eC_values : eC 0 = 1 ∧ eC 1 = -33 / 4 ∧ eC 2 = 7589 / 160 ∧ eC 3 = -744579 / 3200 ∧
    eC 4 = 373339749 / 358400 ∧ eC 5 = -157351476537 / 35840000 ∧
    eC 6 = 7113539517793 / 401408000 := by decide +kernel

/-- The two formulas for the even-order coefficients agree up to the sixth order. -/
theorem eDirect_check : ∀ j ∈ range 7, eC j = eDirect j := by decide +kernel

theorem geoQ_cast (c : ℚ) :
    (fun i => ((geoQ c i : ℚ) : ℝ)) = fun i => (-(c : ℝ)) ^ i := by
  funext i
  simp [geoQ]

theorem binQc_cast (c : ℚ) :
    (fun i => ((binQc c i : ℚ) : ℝ)) = fun i => (binQ i : ℝ) * (c : ℝ) ^ i := by
  funext i
  simp [binQc]

theorem dC_cast (i : ℕ) : ((dC i : ℚ) : ℝ) =
    cmul (cmul (fun i => (-2 : ℝ) ^ i) (fun i => (binQ i : ℝ) * 2 ^ i))
      (ccomp (fun i => (cC i : ℝ)) (fun i => (-2 : ℝ) ^ i)) i := by
  have h1 : (fun i => ((cmul (geoQ 2) (binQc 2) i : ℚ) : ℝ)) =
      cmul (fun i => ((geoQ 2 i : ℚ) : ℝ)) (fun i => ((binQc 2 i : ℚ) : ℝ)) :=
    funext fun i => map_cmul (Rat.castHom ℝ) _ _ i
  have h2 : (fun i => ((ccomp cC (geoQ 2) i : ℚ) : ℝ)) =
      ccomp (fun i => (cC i : ℝ)) (fun i => ((geoQ 2 i : ℚ) : ℝ)) :=
    funext fun i => map_ccomp (Rat.castHom ℝ) _ _ i
  have h3 : ((dC i : ℚ) : ℝ) = cmul (fun i => ((cmul (geoQ 2) (binQc 2) i : ℚ) : ℝ))
      (fun i => ((ccomp cC (geoQ 2) i : ℚ) : ℝ)) i := map_cmul (Rat.castHom ℝ) _ _ i
  rw [h3, h1, h2, geoQ_cast, binQc_cast]
  simp only [Rat.cast_ofNat]

theorem evenTransfer_cast (d : ℕ → ℚ) (i : ℕ) : ((evenTransfer d i : ℚ) : ℝ) =
    cmul (cmul (cmul (fun i => (-1 : ℝ) ^ i) (fun i => (-3 : ℝ) ^ i))
      (fun i => (binQ i : ℝ) * 1 ^ i)) (ccomp (fun i => (d i : ℝ)) (fun i => (-1 : ℝ) ^ i)) i := by
  have h0 : (fun i => ((cmul (geoQ 1) (geoQ 3) i : ℚ) : ℝ)) =
      cmul (fun i => ((geoQ 1 i : ℚ) : ℝ)) (fun i => ((geoQ 3 i : ℚ) : ℝ)) :=
    funext fun i => map_cmul (Rat.castHom ℝ) _ _ i
  have h1 : (fun i => ((cmul (cmul (geoQ 1) (geoQ 3)) (binQc 1) i : ℚ) : ℝ)) =
      cmul (fun i => ((cmul (geoQ 1) (geoQ 3) i : ℚ) : ℝ)) (fun i => ((binQc 1 i : ℚ) : ℝ)) :=
    funext fun i => map_cmul (Rat.castHom ℝ) _ _ i
  have h2 : (fun i => ((ccomp d (geoQ 1) i : ℚ) : ℝ)) =
      ccomp (fun i => (d i : ℝ)) (fun i => ((geoQ 1 i : ℚ) : ℝ)) :=
    funext fun i => map_ccomp (Rat.castHom ℝ) _ _ i
  have h3 : ((evenTransfer d i : ℚ) : ℝ) =
      cmul (fun i => ((cmul (cmul (geoQ 1) (geoQ 3)) (binQc 1) i : ℚ) : ℝ))
        (fun i => ((ccomp d (geoQ 1) i : ℚ) : ℝ)) i := map_cmul (Rat.castHom ℝ) _ _ i
  rw [h3, h1, h0, h2, geoQ_cast, geoQ_cast, binQc_cast]
  simp only [Rat.cast_ofNat, Rat.cast_one]

/-! ### The binomial series of exponent `-1/2` -/

theorem binQ_cast (i : ℕ) : ((binQ i : ℚ) : ℝ) = Ring.choose (-1 / 2 : ℝ) i := by
  induction i with
  | zero => simp [binQ]
  | succ i ih =>
    have h := Ring.choose_smul_choose (-1 / 2 : ℝ) (Nat.le_succ i)
    simp only [Nat.succ_eq_add_one, Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul] at h
    have hne : ((i : ℝ) + 1) ≠ 0 := by positivity
    simp only [binQ]
    push_cast
    rw [ih, div_eq_iff hne]
    push_cast at h
    linarith

theorem binomial_partialSum (y : ℝ) (n : ℕ) :
    (binomialSeries ℝ (-1 / 2 : ℝ)).partialSum n y = ∑ i ∈ range n, (binQ i : ℝ) * y ^ i := by
  unfold FormalMultilinearSeries.partialSum
  refine sum_congr rfl fun i _ => ?_
  rw [binQ_cast]
  simp [binomialSeries]
  ring

theorem binom_bound (n : ℕ) : ∃ D : ℝ, ∀ y : ℝ, |y| ≤ 3 / 5 →
    |(1 + y) ^ (-1 / 2 : ℝ) - ∑ i ∈ range n, (binQ i : ℝ) * y ^ i| ≤ D * |y| ^ n := by
  let r' : NNReal := ⟨3 / 4, by norm_num⟩
  have hr' : (r' : ℝ) = 3 / 4 := rfl
  have hr : (r' : ENNReal) < 1 := by
    rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, hr', NNReal.coe_one]
    norm_num
  obtain ⟨a, _, C, _, h⟩ :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℝ))).uniform_geometric_approx' hr
  refine ⟨C * (a / (3 / 4)) ^ n, fun y hy => ?_⟩
  have hy' : y ∈ Metric.ball (0 : ℝ) (r' : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, hr']
    linarith
  have h1 := h y hy' n
  simp only [zero_add, binomial_partialSum, Real.norm_eq_abs, hr'] at h1
  calc |(1 + y) ^ (-1 / 2 : ℝ) - ∑ i ∈ range n, (binQ i : ℝ) * y ^ i|
      ≤ C * (a * (|y| / (3 / 4))) ^ n := h1
    _ = C * (a / (3 / 4)) ^ n * |y| ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        ring

theorem rpow_neg_half {x : ℝ} (hx : 0 < x) : x ^ (-1 / 2 : ℝ) = √(1 / x) := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, rpow_neg hx.le, ← sqrt_eq_rpow, one_div,
    sqrt_inv]

/-! ### Two elementary expansions -/

section
variable {α : Type*} {S : Set α} {w : α → ℝ}

theorem HasExp.comap {β : Type*} {f : α → ℝ} {a : ℕ → ℝ} (hf : HasExp S w f a) {T : Set β}
    (φ : β → α) (hφ : ∀ x ∈ T, φ x ∈ S) :
    HasExp T (fun x => w (φ x)) (fun x => f (φ x)) a :=
  fun P => (hf P).imp fun _ hC x hx => hC (φ x) (hφ x hx)

theorem geo_hasExp (c : ℝ) (hc : 0 ≤ c) (hw : ∀ x ∈ S, 0 ≤ w x) :
    HasExp S w (fun x => 1 / (1 + c * w x)) (fun i => (-c) ^ i) := by
  intro P
  refine ⟨c ^ P, fun x hx => ?_⟩
  have hcw : 0 ≤ c * w x := mul_nonneg hc (hw x hx)
  have hpos : 0 < 1 + c * w x := by linarith
  have e : 1 / (1 + c * w x) - ∑ i ∈ range P, (-c) ^ i * w x ^ i =
      (-c * w x) ^ P / (1 + c * w x) := by
    have hgeo : ∑ i ∈ range P, (-c) ^ i * w x ^ i = ∑ i ∈ range P, (-c * w x) ^ i :=
      sum_congr rfl fun i _ => (mul_pow _ _ _).symm
    have hq := geom_sum_mul (-c * w x) P
    rw [hgeo, eq_div_iff hpos.ne', sub_mul, one_div_mul_cancel hpos.ne']
    linear_combination hq
  rw [e, abs_div, abs_of_pos hpos, abs_pow, abs_mul, abs_neg, abs_of_nonneg hc, mul_pow]
  exact div_le_self (by positivity) (by linarith)

theorem bin_hasExp (c : ℝ) (hc : 0 ≤ c) (hw : ∀ x ∈ S, 0 ≤ w x ∧ c * w x ≤ 3 / 5) :
    HasExp S w (fun x => (1 + c * w x) ^ (-1 / 2 : ℝ)) (fun i => (binQ i : ℝ) * c ^ i) := by
  intro P
  obtain ⟨D, hD⟩ := binom_bound P
  refine ⟨D * c ^ P, fun x hx => ?_⟩
  obtain ⟨h0, h1⟩ := hw x hx
  have hy : |c * w x| ≤ 3 / 5 := by
    rw [abs_of_nonneg (mul_nonneg hc h0)]
    exact h1
  have h := hD (c * w x) hy
  have e : ∑ i ∈ range P, (binQ i : ℝ) * c ^ i * w x ^ i =
      ∑ i ∈ range P, (binQ i : ℝ) * (c * w x) ^ i :=
    sum_congr rfl fun i _ => by rw [mul_pow]; ring
  rw [e]
  calc |(1 + c * w x) ^ (-1 / 2 : ℝ) - ∑ i ∈ range P, (binQ i : ℝ) * (c * w x) ^ i|
      ≤ D * |c * w x| ^ P := h
    _ = D * c ^ P * |w x| ^ P := by
        rw [abs_mul, abs_of_nonneg hc, mul_pow]
        ring

end

theorem sig_pos' {x : ℝ} (hx : 0 < x) : 0 < sig x := by
  unfold sig
  positivity

/-- Passage from the normalised form to the statement with explicit prefactor. -/
theorem of_ratio {s x C σ : ℝ} {a : ℕ → ℝ} {p : ℕ} (hσ : 0 < σ) (hx : 0 < x)
    (h : |s / σ - ∑ i ∈ range p, a i * (1 / x) ^ i| ≤ C * |1 / x| ^ p) :
    |s - σ * ∑ i ∈ range p, a i / x ^ i| ≤ C * σ / x ^ p := by
  have e1 : ∑ i ∈ range p, a i * (1 / x) ^ i = ∑ i ∈ range p, a i / x ^ i :=
    sum_congr rfl fun i _ => by rw [one_div, inv_pow, div_eq_mul_inv]
  have e2 : s - σ * ∑ i ∈ range p, a i / x ^ i = σ * (s / σ - ∑ i ∈ range p, a i / x ^ i) := by
    field_simp
  rw [e1, abs_of_pos (by positivity : (0 : ℝ) < 1 / x), one_div, inv_pow] at h
  rw [e2, abs_mul, abs_of_pos hσ]
  calc σ * |s / σ - ∑ i ∈ range p, a i / x ^ i| ≤ σ * (C * (x ^ p)⁻¹) :=
        mul_le_mul_of_nonneg_left h hσ.le
    _ = C * σ / x ^ p := by
        rw [div_eq_mul_inv]
        ring

/-! ### The Laplace expansion as an expansion in `1 / (N + 2)` -/

theorem laplace_hasExp :
    HasExp {N : ℕ | 2 ≤ N} (fun N => 1 / ((N : ℝ) + 2))
      (fun N => (∫ x in Set.Ioi (0 : ℝ), weight N x) / hm ((N : ℝ) + 2) 1)
      (fun i => (cC i : ℝ)) := by
  intro P
  obtain ⟨C, hC⟩ := laplace_all_orders P
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hM : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  have hpos : 0 < hm ((N : ℝ) + 2) 1 := lt_of_lt_of_le (by positivity) (hm_one_lower hM)
  show |(∫ x in Set.Ioi (0 : ℝ), weight N x) / hm ((N : ℝ) + 2) 1 -
      ∑ i ∈ range P, (cC i : ℝ) * (1 / ((N : ℝ) + 2)) ^ i| ≤ C * |1 / ((N : ℝ) + 2)| ^ P
  generalize (∫ x in Set.Ioi (0 : ℝ), weight N x) = W at h ⊢
  generalize hm ((N : ℝ) + 2) 1 = H at h hpos ⊢
  generalize (N : ℝ) + 2 = M at h hM ⊢
  have hM0 : 0 < M := by linarith
  have e1 : ∑ i ∈ range P, (cC i : ℝ) * (1 / M) ^ i = ∑ i ∈ range P, (cC i : ℝ) / M ^ i :=
    sum_congr rfl fun i _ => by rw [one_div, inv_pow, div_eq_mul_inv]
  have e2 : W / H - ∑ i ∈ range P, (cC i : ℝ) / M ^ i =
      (W - H * ∑ i ∈ range P, (cC i : ℝ) / M ^ i) / H := by
    field_simp
  rw [e1, e2, abs_div, abs_of_pos hpos, div_le_iff₀ hpos,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / M), one_div, inv_pow]
  calc |W - H * ∑ i ∈ range P, (cC i : ℝ) / M ^ i| ≤ C * (H / M ^ P) := h
    _ = C * (M ^ P)⁻¹ * H := by
        rw [div_eq_mul_inv]
        ring

/-! ### Odd orders -/

/-- The slope integral `4 N / π ∫₀^∞ u² |sin u / u|^(N+2) du`, divided by `√(216 / (π N))`,
expands in powers of `1 / N` with the coefficients `dC`, for all integers `N ≥ 4`. -/
theorem slope_integral_hasExp :
    HasExp {N : ℕ | 4 ≤ N} (fun N => 1 / (N : ℝ))
      (fun N => 4 * (N : ℝ) / π * (∫ x in Set.Ioi (0 : ℝ), weight N x) / sig (N : ℝ))
      (fun i => (dC i : ℝ)) := by
  have hw0 : ∀ N ∈ {N : ℕ | 4 ≤ N}, (0 : ℝ) ≤ 1 / (N : ℝ) := fun N _ => by positivity
  have hF : HasExp {N : ℕ | 4 ≤ N} (fun N => 1 / ((N : ℝ) + 2))
      (fun N => (∫ x in Set.Ioi (0 : ℝ), weight N x) / hm ((N : ℝ) + 2) 1)
      (fun i => (cC i : ℝ)) :=
    laplace_hasExp.mono fun N (hN : 4 ≤ N) => (show 2 ≤ N by omega)
  have hy : HasExp {N : ℕ | 4 ≤ N} (fun N => 1 / (N : ℝ))
      (fun N => 1 / (1 + 2 * (1 / (N : ℝ)))) (fun i => (-2 : ℝ) ^ i) :=
    geo_hasExp 2 (by norm_num) hw0
  have hFw := hF.comp (w := fun N : ℕ => 1 / (N : ℝ))
    (y := fun N : ℕ => 1 / (1 + 2 * (1 / (N : ℝ))))
    (fun N hN => by
      have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 4 ≤ N from hN)
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      show 1 / ((N : ℝ) + 2) = 1 / (N : ℝ) * (1 / (1 + 2 * (1 / (N : ℝ))))
      field_simp) hy
  have hρ : HasExp {N : ℕ | 4 ≤ N} (fun N => 1 / (N : ℝ))
      (fun N => (1 + 2 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ)) (fun i => (binQ i : ℝ) * 2 ^ i) :=
    bin_hasExp 2 (by norm_num) fun N hN => by
      have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 4 ≤ N from hN)
      constructor
      · positivity
      · rw [mul_one_div, div_le_iff₀ (by linarith)]
        linarith
  have hprod := (hy.mul hρ).mul hFw
  refine (hprod.congr fun N hN => ?_).congr_coeff fun i => dC_cast i
  have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 4 ≤ N from hN)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hsig : 0 < sig (N : ℝ) := sig_pos' hN0
  have hhm : 0 < hm ((N : ℝ) + 2) 1 :=
    lt_of_lt_of_le (by positivity) (hm_one_lower (by linarith))
  have hfour := four_D_hm hN0
  have hy1 : 1 / (1 + 2 * (1 / (N : ℝ))) = (N : ℝ) / ((N : ℝ) + 2) := by field_simp
  have hρ1 : (1 + 2 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ) = √((N : ℝ) / ((N : ℝ) + 2)) := by
    rw [rpow_neg_half (by positivity), hy1]
  show 4 * (N : ℝ) / π * (∫ x in Set.Ioi (0 : ℝ), weight N x) / sig (N : ℝ) =
    1 / (1 + 2 * (1 / (N : ℝ))) * (1 + 2 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ) *
      ((∫ x in Set.Ioi (0 : ℝ), weight N x) / hm ((N : ℝ) + 2) 1)
  rw [hy1, hρ1, div_eq_iff hsig.ne']
  have e : 4 * (N : ℝ) / π * (∫ x in Set.Ioi (0 : ℝ), weight N x) =
      (4 * (N : ℝ) / π * hm ((N : ℝ) + 2) 1) *
        ((∫ x in Set.Ioi (0 : ℝ), weight N x) / hm ((N : ℝ) + 2) 1) := by
    field_simp
  rw [e, hfour]
  ring

/-- Odd orders, normalised form. -/
theorem odd_slope_hasExp :
    HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => ((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ))
      (fun i => (dC i : ℝ)) := by
  have h := slope_integral_hasExp.comap (T := {j : ℕ | 1 ≤ j}) (fun j => 2 * j + 2)
    (fun j (hj : 1 ≤ j) => (show 4 ≤ 2 * j + 2 by omega))
  refine h.congr fun j hj => ?_
  show ((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ) =
    4 * ((2 * j + 2 : ℕ) : ℝ) / π * (∫ x in Set.Ioi (0 : ℝ), weight (2 * j + 2) x) /
      sig ((2 * j + 2 : ℕ) : ℝ)
  rw [slopeQ_odd_eq_integral hj]

/-- **Odd central slopes to every order.**  For `n = 2j + 1 ≥ 3` and `x = n + 1`,
`s_n = √(216 / (π x)) (∑ i < p, dC i / x ^ i + O(x ^ (-p)))`. -/
theorem odd_slope_all_orders (p : ℕ) : ∃ K : ℝ, ∀ j : ℕ, 1 ≤ j →
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (dC i : ℝ) / ((2 * j + 2 : ℕ) : ℝ) ^ i| ≤
      K * √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) / ((2 * j + 2 : ℕ) : ℝ) ^ p := by
  obtain ⟨C, hC⟩ := odd_slope_hasExp p
  refine ⟨C, fun j hj => ?_⟩
  have hx : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
  exact of_ratio (σ := sig ((2 * j + 2 : ℕ) : ℝ)) (sig_pos' hx) hx (hC j hj)

/-! ### Even orders: the transfer through consecutive slopes -/

theorem even_ratio_identity {N s σ r : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hr : 0 < r) :
    (2 * N ^ 2 / ((N + 1) * (N + 3)) * s) / (2 * σ) =
      N / (N + 1) * (N / (N + 3)) * r * (s / (σ * r)) := by
  field_simp

/-- **Transfer theorem.**  Any all-order expansion of the odd slopes, with coefficients `d`,
yields the all-order expansion of the even slopes with coefficients `evenTransfer d`. -/
theorem even_of_odd_hasExp (d : ℕ → ℚ)
    (hodd : HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => ((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ))
      (fun i => (d i : ℝ))) :
    HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => ((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ)))
      (fun i => (evenTransfer d i : ℝ)) := by
  have hw0 : ∀ m ∈ {m : ℕ | 2 ≤ m}, (0 : ℝ) ≤ 1 / ((2 * m + 1 : ℕ) : ℝ) :=
    fun m _ => by positivity
  have hG := hodd.mono fun m (hm : 2 ≤ m) => (show 1 ≤ m by omega)
  have hy1 : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => 1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ)))) (fun i => (-1 : ℝ) ^ i) :=
    geo_hasExp 1 zero_le_one hw0
  have hy3 : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => 1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ)))) (fun i => (-3 : ℝ) ^ i) :=
    geo_hasExp 3 (by norm_num) hw0
  have hGw := hG.comp (w := fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
    (y := fun m => 1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))))
    (fun m _ => by
      show 1 / ((2 * m + 2 : ℕ) : ℝ) =
        1 / ((2 * m + 1 : ℕ) : ℝ) * (1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))))
      push_cast
      field_simp
      ring) hy1
  have hρ : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ))
      (fun i => (binQ i : ℝ) * 1 ^ i) :=
    bin_hasExp 1 zero_le_one fun m hm => by
      have h5 : (5 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 5 ≤ 2 * m + 1 by have : 2 ≤ m := hm; omega)
      constructor
      · positivity
      · rw [one_mul, div_le_iff₀ (by linarith)]
        linarith
  have hprod := ((hy1.mul hy3).mul hρ).mul hGw
  refine (hprod.congr fun m hm => ?_).congr_coeff fun i => evenTransfer_cast d i
  have hm' : 2 ≤ m := hm
  have hN0 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hD : ((2 * m + 2 : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hy1e : 1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))) =
      ((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 1) := by field_simp
  have hy3e : 1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))) =
      ((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 3) := by field_simp
  have hρe : (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ) =
      √(((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
    rw [rpow_neg_half (by positivity), hy1e]
  show ((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ)) =
    1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))) * (1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ)))) *
      (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ) *
      (((slopeQ (2 * m + 1) : ℚ) : ℝ) / sig ((2 * m + 2 : ℕ) : ℝ))
  rw [slopeQ_even_cast hm', hD, sig_succ hN0, hy1e, hy3e, hρe]
  exact even_ratio_identity hN0 (sig_pos' hN0) (sqrt_pos.2 (by positivity))

/-- Even orders, normalised form. -/
theorem even_slope_hasExp :
    HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => ((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ)))
      (fun i => (eC i : ℝ)) :=
  even_of_odd_hasExp dC odd_slope_hasExp

theorem sqrt_864 (x : ℝ) : √(864 / (π * x)) = 2 * sig x := by
  unfold sig
  rw [show (864 : ℝ) / (π * x) = 2 ^ 2 * (216 / (π * x)) by ring, sqrt_mul (by positivity),
    sqrt_sq (by norm_num)]

/-- **Even central slopes to every order.**  For `n = 2m ≥ 4` and `x = n + 1`,
`t_n = √(864 / (π x)) (∑ i < p, eC i / x ^ i + O(x ^ (-p)))`. -/
theorem even_slope_all_orders (p : ℕ) : ∃ K : ℝ, ∀ m : ℕ, 2 ≤ m →
    |((slopeQ (2 * m) : ℚ) : ℝ) - √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (eC i : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ i| ≤
      K * √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) / ((2 * m + 1 : ℕ) : ℝ) ^ p := by
  obtain ⟨C, hC⟩ := even_slope_hasExp p
  refine ⟨C, fun m hm => ?_⟩
  have hx : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hσ : 0 < 2 * sig ((2 * m + 1 : ℕ) : ℝ) := by
    have := sig_pos' hx
    positivity
  rw [sqrt_864]
  exact of_ratio hσ hx (hC m hm)

/-! ### Uniqueness of the coefficients -/

theorem odd_gauge_small : ∀ ε > 0, ∃ j ∈ {j : ℕ | 1 ≤ j},
    (1 / ((2 * j + 2 : ℕ) : ℝ)) ≠ 0 ∧ |1 / ((2 * j + 2 : ℕ) : ℝ)| < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hpos : (0 : ℝ) < ((2 * (k + 1) + 2 : ℕ) : ℝ) := by positivity
  refine ⟨k + 1, (show 1 ≤ k + 1 by omega), by positivity, ?_⟩
  rw [abs_of_pos (by positivity), div_lt_iff₀ hpos]
  have h1 : 1 / ε < ((2 * (k + 1) + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [div_lt_iff₀ hε] at h1
  linarith

theorem even_gauge_small : ∀ ε > 0, ∃ m ∈ {m : ℕ | 2 ≤ m},
    (1 / ((2 * m + 1 : ℕ) : ℝ)) ≠ 0 ∧ |1 / ((2 * m + 1 : ℕ) : ℝ)| < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hpos : (0 : ℝ) < ((2 * (k + 2) + 1 : ℕ) : ℝ) := by positivity
  refine ⟨k + 2, (show 2 ≤ k + 2 by omega), by positivity, ?_⟩
  rw [abs_of_pos (by positivity), div_lt_iff₀ hpos]
  have h1 : 1 / ε < ((2 * (k + 2) + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [div_lt_iff₀ hε] at h1
  linarith

/-- The odd-order coefficients are determined by the slopes: any sequence with the all-order
expansion property coincides with `dC`. -/
theorem dC_unique (d : ℕ → ℝ)
    (h : HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => ((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ)) d) :
    d = fun i => (dC i : ℝ) :=
  h.unique odd_slope_hasExp odd_gauge_small

/-- The even-order coefficients are determined by the slopes. -/
theorem eC_unique (e : ℕ → ℝ)
    (h : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => ((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ))) e) :
    e = fun i => (eC i : ℝ) :=
  h.unique even_slope_hasExp even_gauge_small

/-! ### Explicit sixth order -/

/-- Odd orders with the first seven coefficients and remainder `O(x ^ (-7))`. -/
theorem odd_slope_sixth_order : ∃ K : ℝ, ∀ j : ℕ, 1 ≤ j → ∀ x : ℝ, x = ((2 * j + 2 : ℕ) : ℝ) →
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * x)) *
        (1 - 15 / (4 * x) + 1829 / (160 * x ^ 2) - 101709 / (3200 * x ^ 3) +
          29934309 / (358400 * x ^ 4) - 7564058487 / (35840000 * x ^ 5) +
          1040050193381 / (2007040000 * x ^ 6))| ≤ K * √(216 / (π * x)) / x ^ 7 := by
  obtain ⟨K, hK⟩ := odd_slope_all_orders 7
  refine ⟨K, fun j hj x hx => ?_⟩
  have h := hK j hj
  rw [← hx] at h
  have hx0 : (0 : ℝ) < x := by rw [hx]; positivity
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := dC_values
  have hsum : ∑ i ∈ range 7, (dC i : ℝ) / x ^ i =
      1 - 15 / (4 * x) + 1829 / (160 * x ^ 2) - 101709 / (3200 * x ^ 3) +
        29934309 / (358400 * x ^ 4) - 7564058487 / (35840000 * x ^ 5) +
        1040050193381 / (2007040000 * x ^ 6) := by
    simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6]
    push_cast
    field_simp
    ring
  rw [hsum] at h
  exact h

/-- Even orders with the first seven coefficients and remainder `O(x ^ (-7))`. -/
theorem even_slope_sixth_order : ∃ K : ℝ, ∀ m : ℕ, 2 ≤ m → ∀ x : ℝ, x = ((2 * m + 1 : ℕ) : ℝ) →
    |((slopeQ (2 * m) : ℚ) : ℝ) - √(864 / (π * x)) *
        (1 - 33 / (4 * x) + 7589 / (160 * x ^ 2) - 744579 / (3200 * x ^ 3) +
          373339749 / (358400 * x ^ 4) - 157351476537 / (35840000 * x ^ 5) +
          7113539517793 / (401408000 * x ^ 6))| ≤ K * √(864 / (π * x)) / x ^ 7 := by
  obtain ⟨K, hK⟩ := even_slope_all_orders 7
  refine ⟨K, fun m hm x hx => ?_⟩
  have h := hK m hm
  rw [← hx] at h
  have hx0 : (0 : ℝ) < x := by rw [hx]; positivity
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := eC_values
  have hsum : ∑ i ∈ range 7, (eC i : ℝ) / x ^ i =
      1 - 33 / (4 * x) + 7589 / (160 * x ^ 2) - 744579 / (3200 * x ^ 3) +
        373339749 / (358400 * x ^ 4) - 157351476537 / (35840000 * x ^ 5) +
        7113539517793 / (401408000 * x ^ 6) := by
    simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6]
    push_cast
    field_simp
    ring
  rw [hsum] at h
  exact h

end PrivateApex
