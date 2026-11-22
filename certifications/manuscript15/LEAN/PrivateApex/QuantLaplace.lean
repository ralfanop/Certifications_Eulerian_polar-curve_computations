import PrivateApex.QuantSinc

/-!
PRIVATE.  Manuscript 15: the Laplace expansion with explicit remainder.

`LaplaceAllOrders` proves, for every order `p`, the existence of a constant in

  `∫₀^∞ u² |sin u / u|^(N+2) du = hm M 1 * (∑ j < p, cC j / M ^ j + O(M ^ (-p)))`,  `M = N + 2`.

Here the remainder is bounded explicitly, for `p ≤ 7` and every integer `N ≥ 2`, in the two-term
form (`laplace_explicit`)

  `|∫₀^∞ weight N - hm M 1 * ∑ j < p, cC j / M ^ j| ≤
      hm M 1 * (lapA p / M ^ p + exp (-M / 12) * lapT p)`,

with the rational constants `lapA p` (algebraic part) and `lapT p` (exponentially small part).
The proofs follow those of `LaplaceAllOrders`, with the constants of `QuantSinc` in place of the
existential ones; the exponentially small terms are kept separate instead of being converted into
powers of `1 / M`.
-/

namespace PrivateApex
open Real Finset MeasureTheory

/-- One term of the exponential series, with explicit constants. -/
theorem term_boundQ {p k : ℕ} (hk : k < p) (hp : p < 8) {M : ℝ} (hM : 1 ≤ M) :
    IntegrableOn (fun u => gm M (2 * k + 1) u * kap u ^ k) (Set.Ioc 0 1) ∧
    |M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i))| ≤
      hm M 1 * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ) / M ^ p +
        exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k)) := by
  have hM0 : 0 < M := by linarith
  have hφm : Measurable fun u => kap u ^ k := measurable_kap.pow_const k
  have hC : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |kap u ^ k - ∑ i ∈ range (p - k), cpow kapR k i * (u ^ 2) ^ i| ≤
        (kpK k (p - k) : ℝ) * |u ^ 2| ^ (p - k) :=
    fun u hu => kap_pow_bound (by omega) (by omega) hu
  obtain ⟨hint, hW⟩ := watson_normalized hφm (a := cpow kapR k) (q := p - k)
    (C := (kpK k (p - k) : ℝ)) hC hM (2 * k)
  refine ⟨hint, ?_⟩
  have hS0 := tailConst_nonneg (cpow kapR k) (2 * k) (p - k)
  have hh : 0 ≤ hm M 1 := hm_nonneg M 1
  have e2 : 2 * k + (p - k) = k + p := by omega
  have hMk : 0 < M ^ k := pow_pos hM0 k
  have hMp : 0 < M ^ p := pow_pos hM0 p
  have hsum : hm M 1 * ∑ i ∈ range (p - k),
      cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)) =
      M ^ k * (hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (2 * k + i))) := by
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hpw : M ^ (2 * k + i) = M ^ k * M ^ (k + i) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpw]
    field_simp
  have e : M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
      cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)) =
      M ^ k * (Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (2 * k + i))) := by
    rw [hsum]
    ring
  rw [e, abs_mul, abs_of_pos hMk]
  rw [e2] at hW
  have hk1 : (1 : ℝ) ≤ M ^ k := one_le_pow₀ hM
  have hMkp : M ^ (k + p) = M ^ k * M ^ p := pow_add M k p
  have hMkk : M ^ (2 * k) = M ^ k * M ^ k := by rw [two_mul, pow_add]
  have eq1 : M ^ k * (hm M 1 * ((kpK k (p - k) : ℝ) * ((muQ (k + p) : ℝ) / M ^ (k + p)) +
        exp (-(M / 12)) * (tailConst (cpow kapR k) (2 * k) (p - k) / M ^ (2 * k)))) =
      hm M 1 * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ) / M ^ p +
        exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k) / M ^ k) := by
    rw [hMkp, hMkk]
    field_simp
  have hX : 0 ≤ exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k) :=
    mul_nonneg (exp_pos _).le hS0
  calc M ^ k * |Jint M k - hm M 1 * ∑ i ∈ range (p - k),
        cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (2 * k + i))|
      ≤ M ^ k * (hm M 1 * ((kpK k (p - k) : ℝ) * ((muQ (k + p) : ℝ) / M ^ (k + p)) +
          exp (-(M / 12)) * (tailConst (cpow kapR k) (2 * k) (p - k) / M ^ (2 * k)))) :=
        mul_le_mul_of_nonneg_left hW hMk.le
    _ = hm M 1 * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ) / M ^ p +
          exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k) / M ^ k) := eq1
    _ ≤ hm M 1 * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ) / M ^ p +
          exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right (div_le_self hX hk1) _) hh

/-- The remainder of the exponential series, with explicit constant. -/
theorem rem_boundQ (p : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    IntegrableOn (fun u => gm M 1 u *
      (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u))) (Set.Ioc 0 1) ∧
    |Rint p M| ≤ hm M 1 *
      ((kapK 0 : ℝ) ^ p * (muQ (2 * p) : ℝ) / (p.factorial : ℝ) / M ^ p) := by
  set K : ℝ := (kapK 0 : ℝ) with hKdef
  have hM0 : 0 < M := by linarith
  have hfac : (0 : ℝ) < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (kap_abs_le (u := 0) ⟨le_rfl, zero_le_one⟩)
  have hpt : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      |gm M 1 u * (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u))| ≤
        (M ^ p * K ^ p / (p.factorial : ℝ)) * gm M (2 * p + 1) u := by
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have hk0 := kap_nonneg hu'.1 hu'.2
    have hkK : kap u ≤ K := (le_abs_self _).trans (kap_abs_le hu')
    have hMu : 0 ≤ M * u ^ 4 := by positivity
    have ht0 : 0 ≤ M * u ^ 4 * kap u := mul_nonneg hMu hk0
    have ht := exp_neg_taylor p _ ht0
    have htp : (M * u ^ 4 * kap u) ^ p / (p.factorial : ℝ) ≤
        M ^ p * K ^ p * (u ^ 4) ^ p / (p.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hfac.le
      calc (M * u ^ 4 * kap u) ^ p ≤ (M * u ^ 4 * K) ^ p :=
            pow_le_pow_left₀ ht0 (mul_le_mul_of_nonneg_left hkK hMu) p
        _ = M ^ p * K ^ p * (u ^ 4) ^ p := by ring
    rw [abs_mul, abs_of_nonneg (gm_nonneg M 1 u)]
    calc gm M 1 u * |exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u)|
        ≤ gm M 1 u * (M ^ p * K ^ p * (u ^ 4) ^ p / (p.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (ht.trans htp) (gm_nonneg M 1 u)
      _ = (M ^ p * K ^ p / (p.factorial : ℝ)) * gm M (2 * p + 1) u := by
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
  have hI : IntegrableOn (fun u => (M ^ p * K ^ p / (p.factorial : ℝ)) * gm M (2 * p + 1) u)
      (Set.Ioc 0 1) :=
    ((gm_integrable hM0 _).integrableOn).const_mul _
  have hae : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖gm M 1 u * (exp (-(M * u ^ 4 * kap u)) - expNegSum p (M * u ^ 4 * kap u))‖ ≤
        (M ^ p * K ^ p / (p.factorial : ℝ)) * gm M (2 * p + 1) u :=
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
  have e : M ^ p * K ^ p / (p.factorial : ℝ) * hm M (2 * p + 1) =
      hm M 1 * (K ^ p * (muQ (2 * p) : ℝ) / (p.factorial : ℝ) / M ^ p) := by
    rw [hm_mu hM0 (2 * p), show 2 * p = p + p by ring, pow_add]
    field_simp
  calc M ^ p * K ^ p / (p.factorial : ℝ) * ∫ u in Set.Ioc (0 : ℝ) 1, gm M (2 * p + 1) u
      ≤ M ^ p * K ^ p / (p.factorial : ℝ) * hm M (2 * p + 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = hm M 1 * (K ^ p * (muQ (2 * p) : ℝ) / (p.factorial : ℝ) / M ^ p) := e

/-- Algebraic part of the constant of the main integral. -/
def lapA1 (p : ℕ) : ℚ :=
  ∑ k ∈ range p, 1 / (k.factorial : ℚ) * (kpK k (p - k) * muQ (k + p)) +
    kapK 0 ^ p * muQ (2 * p) / (p.factorial : ℚ)

/-- Exponentially small part of the constant of the main integral (real form). -/
noncomputable def lapT1r (p : ℕ) : ℝ :=
  ∑ k ∈ range p, 1 / (k.factorial : ℝ) * tailConst (cpow kapR k) (2 * k) (p - k)

/-- Exponentially small part of the constant of the main integral (rational form). -/
def lapT1 (p : ℕ) : ℚ :=
  ∑ k ∈ range p, 1 / (k.factorial : ℚ) *
    ∑ i ∈ range (p - k), |cpow kapTab k i| * (2 ^ (2 * k + i + 2) * muQ (2 * k + i))

theorem lapT1r_eq {p : ℕ} (hp : p ≤ 8) : lapT1r p = (lapT1 p : ℝ) := by
  unfold lapT1r lapT1 tailConst
  push_cast
  refine sum_congr rfl fun k hk => ?_
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have hk' := mem_range.1 hk
  have hc : cpow kapR k i = ((cpow kapTab k i : ℚ) : ℝ) := by
    rw [show ((cpow kapTab k i : ℚ) : ℝ) = cpow (fun j => (kapTab j : ℝ)) k i from
      map_cpow (Rat.castHom ℝ) kapTab k i]
    exact cpow_congr (a := kapR) (b := fun j => (kapTab j : ℝ)) k i fun j hj => by
      show ((kapC j : ℚ) : ℝ) = ((kapTab j : ℚ) : ℝ)
      rw [kapC_eq_kapTab j (mem_range.2 (by omega))]
  rw [hc]

/-- The main integral `∫₀¹`, with explicit two-term remainder. -/
theorem Wmain_expandQ {p : ℕ} (hp : p < 8) {M : ℝ} (hM : 1 ≤ M) :
    |Wmain M - hm M 1 * ∑ j ∈ range p, (cC j : ℝ) / M ^ j| ≤
      hm M 1 * ((lapA1 p : ℝ) / M ^ p + exp (-(M / 12)) * lapT1r p) := by
  have hM0 : 0 < M := by linarith
  have hh : 0 ≤ hm M 1 := hm_nonneg M 1
  have hMp : 0 < M ^ p := pow_pos hM0 p
  obtain ⟨hRI, hRb⟩ := rem_boundQ p hM
  have hkI : ∀ k ∈ range p, IntegrableOn (fun u => ((-1) ^ k / (k.factorial : ℝ) * M ^ k) *
      (gm M (2 * k + 1) u * kap u ^ k)) (Set.Ioc 0 1) :=
    fun k hk => ((term_boundQ (mem_range.1 hk) hp hM).1).const_mul _
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
      ∑ k ∈ range p, 1 / (k.factorial : ℝ) *
        (hm M 1 * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ) / M ^ p +
          exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k))) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    have hb := (term_boundQ (mem_range.1 hk) hp hM).2
    have hs : |(-1 : ℝ) ^ k / (k.factorial : ℝ)| = 1 / (k.factorial : ℝ) := by
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
    rw [abs_mul, hs]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hA : ((lapA1 p : ℚ) : ℝ) =
      ∑ k ∈ range p, 1 / (k.factorial : ℝ) * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ)) +
        (kapK 0 : ℝ) ^ p * (muQ (2 * p) : ℝ) / (p.factorial : ℝ) := by
    simp [lapA1]
  have hfin : ∑ k ∈ range p, 1 / (k.factorial : ℝ) *
        (hm M 1 * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ) / M ^ p +
          exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k))) +
      hm M 1 * ((kapK 0 : ℝ) ^ p * (muQ (2 * p) : ℝ) / (p.factorial : ℝ) / M ^ p) =
      hm M 1 * ((lapA1 p : ℝ) / M ^ p + exp (-(M / 12)) * lapT1r p) := by
    rw [hA, lapT1r]
    have h1 : ∀ k ∈ range p, 1 / (k.factorial : ℝ) *
        (hm M 1 * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ) / M ^ p +
          exp (-(M / 12)) * tailConst (cpow kapR k) (2 * k) (p - k))) =
        hm M 1 * (1 / (k.factorial : ℝ) * ((kpK k (p - k) : ℝ) * (muQ (k + p) : ℝ))) / M ^ p +
          hm M 1 * exp (-(M / 12)) *
            (1 / (k.factorial : ℝ) * tailConst (cpow kapR k) (2 * k) (p - k)) :=
      fun k _ => by ring
    rw [sum_congr rfl h1, sum_add_distrib, ← sum_div, ← mul_sum, ← mul_sum]
    ring
  rw [key]
  calc _ ≤ |∑ k ∈ range p, (-1) ^ k / (k.factorial : ℝ) *
          (M ^ k * Jint M k - hm M 1 * ∑ i ∈ range (p - k),
            cpow kapR k i * ((muQ (2 * k + i) : ℝ) / M ^ (k + i)))| + |Rint p M| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add hsum hRb
    _ = _ := hfin

/-! ### The tails -/

theorem exp_three_le : exp 3 ≤ 21 := by
  have h1 : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
  have h2 : exp 1 ≤ 2.7182818286 := exp_one_lt_d9.le
  rw [h1]
  calc exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ (exp_pos 1).le h2 3
    _ ≤ 21 := by norm_num

/-- The tail beyond `π` is exponentially small relative to the Gaussian moment. -/
theorem pi_tail_exp {N : ℕ} (hN : 2 ≤ N) :
    1 / (((N : ℝ) - 1) * π ^ (N - 1)) ≤
      50 * exp (-(((N : ℝ) + 2) / 12)) * hm ((N : ℝ) + 2) 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Nat.add_sub_cancel]
  push_cast
  set M : ℝ := (n : ℝ) + 1 + 2 with hMdef
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hlow := hm_one_lower hM1
  have hπn : 0 < π ^ n := pow_pos pi_pos n
  have hexp : exp (n : ℝ) ≤ π ^ n := by
    have h1 : exp (n : ℝ) = exp 1 ^ n := by rw [← exp_nat_mul, mul_one]
    rw [h1]
    exact pow_le_pow_left₀ (exp_pos 1).le (by linarith [exp_one_lt_d9, pi_gt_three]) n
  have hA : 1 / (((n : ℝ) + 1 - 1) * π ^ n) ≤ 1 / exp (n : ℝ) := by
    apply one_div_le_one_div_of_le (exp_pos _)
    calc exp (n : ℝ) ≤ π ^ n := hexp
      _ = 1 * π ^ n := (one_mul _).symm
      _ ≤ ((n : ℝ) + 1 - 1) * π ^ n := mul_le_mul_of_nonneg_right (by linarith) hπn.le
  -- `exp (-n) = exp 3 * exp (-M/12) * exp (-11 M/12)`
  have hsplit : 1 / exp (n : ℝ) = exp 3 * exp (-(M / 12)) * exp (-(11 * M / 12)) := by
    rw [one_div, ← exp_neg, ← exp_add, ← exp_add]
    congr 1
    rw [hMdef]
    ring
  have hq : exp (-(11 * M / 12)) ≤ 288 / 121 / M ^ 2 := by
    have hx : (0 : ℝ) ≤ 11 * M / 12 := by positivity
    have h := quadratic_le_exp_of_nonneg hx
    have hpos : 0 < exp (11 * M / 12) := exp_pos _
    rw [exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos (by positivity)]
    nlinarith [sq_nonneg M]
  have h3 := exp_three_le
  have hE : 0 ≤ exp (-(M / 12)) := (exp_pos _).le
  calc 1 / (((n : ℝ) + 1 - 1) * π ^ n) ≤ 1 / exp (n : ℝ) := hA
    _ = exp 3 * exp (-(M / 12)) * exp (-(11 * M / 12)) := hsplit
    _ ≤ 21 * exp (-(M / 12)) * (288 / 121 / M ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h3 hE) hq (exp_pos _).le (by positivity)
    _ = 21 * (288 / 121) * exp (-(M / 12)) * (1 / M ^ 2) := by ring
    _ ≤ 50 * exp (-(M / 12)) * hm M 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by norm_num) hE) hlow (by positivity)
          (by positivity)

/-- Algebraic part of the explicit Laplace constant. -/
def lapA (p : ℕ) : ℚ := lapA1 p

/-- Exponentially small part of the explicit Laplace constant. -/
def lapT (p : ℕ) : ℚ := lapT1 p + 54

/-- **Laplace expansion with explicit remainder**, orders `p ≤ 7`, every integer `N ≥ 2`. -/
theorem laplace_explicit {p : ℕ} (hp : p < 8) {N : ℕ} (hN : 2 ≤ N) :
    |(∫ x in Set.Ioi (0 : ℝ), weight N x) -
        hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j| ≤
      hm ((N : ℝ) + 2) 1 * ((lapA p : ℝ) / ((N : ℝ) + 2) ^ p +
        exp (-(((N : ℝ) + 2) / 12)) * (lapT p : ℝ)) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hM : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  have hhm : 0 ≤ hm ((N : ℝ) + 2) 1 := hm_nonneg _ 1
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
      hm ((N : ℝ) + 2) 1 * (exp (-(((N : ℝ) + 2) / 12)) * 54) := by
    have h1 := weight_tail_le N hN
    have h2 := gm_tail_one hM
    have h4 := pi_tail_exp hN
    rw [tail_half_integral N hN] at h1
    linarith
  have hb := Wmain_expandQ hp hM
  rw [lapT1r_eq (by omega)] at hb
  have e : (∫ x in Set.Ioc (0 : ℝ) 1, weight N x) + (∫ x in Set.Ioi (1 : ℝ), weight N x) -
      hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j =
      (Wmain ((N : ℝ) + 2) -
        hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j) +
        ∫ x in Set.Ioi (1 : ℝ), weight N x := by
    rw [hmain]
    ring
  have hT : ((lapT p : ℚ) : ℝ) = (lapT1 p : ℝ) + 54 := by simp [lapT]
  rw [hsplit, e, hT]
  calc _ ≤ |Wmain ((N : ℝ) + 2) -
          hm ((N : ℝ) + 2) 1 * ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j| +
          |∫ x in Set.Ioi (1 : ℝ), weight N x| := abs_add_le _ _
    _ ≤ hm ((N : ℝ) + 2) 1 * ((lapA1 p : ℝ) / ((N : ℝ) + 2) ^ p +
          exp (-(((N : ℝ) + 2) / 12)) * (lapT1 p : ℝ)) +
          hm ((N : ℝ) + 2) 1 * (exp (-(((N : ℝ) + 2) / 12)) * 54) :=
        add_le_add hb (by rw [abs_of_nonneg hW2a]; exact hW2b)
    _ = _ := by
        unfold lapA
        ring

end PrivateApex
