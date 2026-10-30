import EulerianGrothendieck.UniformParameterNorm
import EulerianGrothendieck.UniformVacuumAsymptotics

/-! # Task I: parameter-uniform reciprocal (vacuum) remainders

For every `c0 > 1/12` and every order `R` there is `K(c0,R)` with
`|1/N_M(c) - ∑_{r≤R} p_r(c)/M^r| ≤ K/M^{R+1}` for all `c ≥ c0` and `M ≥ 1`,
where `N_M(c) = E exp(S_M T_M/(cM))` is the actual probability integral and
`p_r(c) = uniformVacuumCoefficient (1/(12c)) r` are the reciprocal coefficients.

The proof controls the reciprocal coefficients uniformly, not pointwise: with `A_0(t) ≥ 1`
and a uniform bound `A` for the first `R+1` norm coefficients, the inverse coefficients
satisfy `|d_r| ≤ (A+1)^r`; the truncation defect `1 - B D` is bounded through the
`ℓ¹` coefficient norm `polyAbsEval`, which is submultiplicative; and `N_M(t) ≥ 1`. -/

noncomputable section
open scoped BigOperators
open Polynomial Finset MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

theorem polyAbsEval_trunc (f : PowerSeries ℝ) (n : ℕ) :
    polyAbsEval (PowerSeries.trunc n f) 1 = ∑ r ∈ range n, |PowerSeries.coeff r f| := by
  unfold polyAbsEval
  rw [tsum_eq_sum (s := range n)]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [PowerSeries.coeff_trunc, if_pos (Finset.mem_range.mp hr), one_pow, mul_one]
  · intro r hr
    rw [PowerSeries.coeff_trunc, if_neg (by simpa using hr)]
    simp

theorem polyAbsEval_add_le (p q : ℝ[X]) :
    polyAbsEval (p + q) 1 ≤ polyAbsEval p 1 + polyAbsEval q 1 := by
  unfold polyAbsEval
  rw [← (polyAbsEval_summable p 1).tsum_add (polyAbsEval_summable q 1)]
  apply Summable.tsum_le_tsum _ (polyAbsEval_summable (p + q) 1)
    ((polyAbsEval_summable p 1).add (polyAbsEval_summable q 1))
  intro r
  simp only [Polynomial.coeff_add, one_pow, mul_one]
  exact abs_add_le _ _

theorem polyAbsEval_neg (p : ℝ[X]) (h : ℝ) : polyAbsEval (-p) h = polyAbsEval p h := by
  unfold polyAbsEval
  simp [Polynomial.coeff_neg, abs_neg]

theorem polyAbsEval_eq_sum_support (p : ℝ[X]) :
    polyAbsEval p 1 = ∑ j ∈ p.support, |p.coeff j| := by
  unfold polyAbsEval
  rw [tsum_eq_sum (s := p.support)]
  · simp
  · intro r hr
    rw [Polynomial.notMem_support_iff.mp hr]
    simp

theorem polyAbsEval_mul_le (p q : ℝ[X]) :
    polyAbsEval (p * q) 1 ≤ polyAbsEval p 1 * polyAbsEval q 1 := by
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  rw [Finset.sum_mul]
  calc polyAbsEval (∑ j ∈ p.support, C (p.coeff j) * X ^ j * q) 1
      ≤ ∑ j ∈ p.support, polyAbsEval (C (p.coeff j) * X ^ j * q) 1 :=
        polyAbsEval_sum_le _ _ 1 (by norm_num)
    _ = ∑ j ∈ p.support, |p.coeff j| * polyAbsEval q 1 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_assoc, polyAbsEval_C_mul, polyAbsEval_X_pow_mul, one_pow, one_mul]
    _ = polyAbsEval p 1 * polyAbsEval q 1 := by
        rw [← Finset.sum_mul, polyAbsEval_eq_sum_support p]

/-- Uniform growth bound for the coefficients of the inverse power series. -/
theorem inverseSeriesCoefficient_bound (b : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) (R : ℕ)
    (hb0 : 1 ≤ |b 0|) (hb : ∀ j, j ≤ R → |b j| ≤ A) :
    ∀ r, r ≤ R → |inverseSeriesCoefficient b r| ≤ (A + 1) ^ r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    have hb0' : b 0 ≠ 0 := by
      intro h; rw [h, abs_zero] at hb0; linarith
    have hinv : |(b 0)⁻¹| ≤ 1 := by
      rw [abs_inv]; exact inv_le_one_of_one_le₀ hb0
    unfold inverseSeriesCoefficient
    rw [PowerSeries.coeff_inv]
    rw [PowerSeries.constantCoeff_mk]
    split_ifs with h0
    · subst h0; rw [pow_zero]; exact hinv
    · -- the recursive step
      have hterm : ∀ x ∈ Finset.antidiagonal r,
          |(if x.2 < r then PowerSeries.coeff x.1 (PowerSeries.mk b) *
              PowerSeries.coeff x.2 (PowerSeries.mk b)⁻¹ else 0)| ≤
            (if x.2 < r then A * (A + 1) ^ x.2 else 0) := by
        intro x hx
        split_ifs with hlt
        · rw [abs_mul, PowerSeries.coeff_mk]
          have hx1 : x.1 ≤ R := by
            have := Finset.mem_antidiagonal.mp hx; omega
          have := ih x.2 hlt (by omega)
          unfold inverseSeriesCoefficient at this
          exact mul_le_mul (hb x.1 hx1) this (abs_nonneg _) hA
        · simp
      have hsum : ∑ x ∈ Finset.antidiagonal r, (if x.2 < r then A * (A + 1) ^ x.2 else 0) =
          A * ∑ l ∈ range r, (A + 1) ^ l := by
        rw [← Finset.Nat.sum_antidiagonal_swap]
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i _ => if i < r then A * (A+1)^i else 0) r]
        rw [Nat.succ_eq_add_one, Finset.sum_range_succ, if_neg (lt_irrefl r), add_zero,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [if_pos (Finset.mem_range.mp hl)]
      have hgeom := geom_sum_mul_add A r
      calc |-(b 0)⁻¹ * ∑ x ∈ Finset.antidiagonal r,
              (if x.2 < r then PowerSeries.coeff x.1 (PowerSeries.mk b) *
                PowerSeries.coeff x.2 (PowerSeries.mk b)⁻¹ else 0)|
          = |(b 0)⁻¹| * |∑ x ∈ Finset.antidiagonal r,
              (if x.2 < r then PowerSeries.coeff x.1 (PowerSeries.mk b) *
                PowerSeries.coeff x.2 (PowerSeries.mk b)⁻¹ else 0)| := by
            rw [abs_mul, abs_neg]
        _ ≤ 1 * ∑ x ∈ Finset.antidiagonal r, (if x.2 < r then A * (A + 1) ^ x.2 else 0) := by
            apply mul_le_mul hinv ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum hterm)) (abs_nonneg _) zero_le_one
        _ = A * ∑ l ∈ range r, (A + 1) ^ l := by rw [one_mul, hsum]
        _ ≤ (A + 1) ^ r := by nlinarith [hgeom]

/-- General parameter-uniform all-order inversion.  The hypotheses are a uniform lower bound
`N ≥ 1`, `|b_0| ≥ 1`, a uniform bound for the first `R+1` coefficients and a uniform remainder
for `N` itself; nothing about `1/N` is assumed. -/
theorem reciprocal_uniform_remainder {ι : Type*} (N : ι → ℕ → ℝ) (b : ι → ℕ → ℝ) (R : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (hN : ∀ i M, M ≠ 0 → 1 ≤ N i M) (hb0 : ∀ i, 1 ≤ |b i 0|)
    (hb : ∀ i j, j ≤ R → |b i j| ≤ A)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ i M, M ≠ 0 →
      |N i M - ∑ r ∈ range (R+1), b i r/(M:ℝ)^r| ≤ C/(M:ℝ)^(R+1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i M, M ≠ 0 →
      |1/(N i M) - ∑ r ∈ range (R+1), inverseSeriesCoefficient (b i) r/(M:ℝ)^r| ≤
        K/(M:ℝ)^(R+1) := by
  obtain ⟨C, hC, hCrem⟩ := hrem
  obtain ⟨Sstar, hSstar⟩ : ∃ S : ℝ, S = ∑ r ∈ range (R+1), (A + 1) ^ r := ⟨_, rfl⟩
  obtain ⟨Pstar, hPstar⟩ : ∃ P : ℝ, P = (R + 1 : ℝ) * A := ⟨_, rfl⟩
  have hSs : 0 ≤ Sstar := by rw [hSstar]; exact Finset.sum_nonneg (fun r _ => by positivity)
  have hPs : 0 ≤ Pstar := by rw [hPstar]; positivity
  refine ⟨(1 + Pstar * Sstar + C * Sstar) / 1, by positivity, ?_⟩
  intro i M hM
  have hbi0 : b i 0 ≠ 0 := by
    intro h; have := hb0 i; rw [h, abs_zero] at this; linarith
  let B := PowerSeries.trunc (R+1) (PowerSeries.mk (b i))
  let D := PowerSeries.trunc (R+1) ((PowerSeries.mk (b i))⁻¹)
  let S := polyAbsEval D 1
  let T := polyAbsEval (1 - B * D) 1
  have hS : 0 ≤ S := polyAbsEval_nonneg D 1 (by norm_num)
  have hT : 0 ≤ T := polyAbsEval_nonneg (1 - B * D) 1 (by norm_num)
  have hSle : S ≤ Sstar := by
    change polyAbsEval (PowerSeries.trunc (R+1) ((PowerSeries.mk (b i))⁻¹)) 1 ≤ Sstar
    rw [polyAbsEval_trunc, hSstar]
    apply Finset.sum_le_sum
    intro r hr
    exact inverseSeriesCoefficient_bound (b i) A hA R (hb0 i) (hb i) r
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
  have hPle : polyAbsEval B 1 ≤ Pstar := by
    change polyAbsEval (PowerSeries.trunc (R+1) (PowerSeries.mk (b i))) 1 ≤ Pstar
    rw [polyAbsEval_trunc]
    calc ∑ r ∈ range (R+1), |PowerSeries.coeff r (PowerSeries.mk (b i))|
        ≤ ∑ r ∈ range (R+1), A := by
          apply Finset.sum_le_sum
          intro r hr
          rw [PowerSeries.coeff_mk]
          exact hb i r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      _ = Pstar := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hPstar]
          push_cast
          ring
  have hTle : T ≤ 1 + Pstar * Sstar := by
    change polyAbsEval (1 - B * D) 1 ≤ _
    rw [sub_eq_add_neg]
    calc polyAbsEval (1 + -(B * D)) 1 ≤ polyAbsEval 1 1 + polyAbsEval (-(B * D)) 1 :=
          polyAbsEval_add_le _ _
      _ = 1 + polyAbsEval (B * D) 1 := by rw [polyAbsEval_one, polyAbsEval_neg]
      _ ≤ 1 + polyAbsEval B 1 * polyAbsEval D 1 := by linarith [polyAbsEval_mul_le B D]
      _ ≤ 1 + Pstar * Sstar := by
          have h0 : 0 ≤ polyAbsEval B 1 := polyAbsEval_nonneg B 1 (by norm_num)
          nlinarith [mul_le_mul hPle hSle hS hPs]
  let h := 1/(M:ℝ)
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := (div_le_one (by positivity)).2 hM1
  have hBval : B.eval h = ∑ r ∈ range (R+1), b i r/(M:ℝ)^r := by
    rw [trunc_eval_eq]
    simp only [PowerSeries.coeff_mk, h, one_div_pow, mul_one_div]
  have hDval : D.eval h = ∑ r ∈ range (R+1), inverseSeriesCoefficient (b i) r/(M:ℝ)^r := by
    rw [trunc_eval_eq]
    simp only [inverseSeriesCoefficient, h, one_div_pow, mul_one_div]
  have hz : ∀ r ≤ R, (1 - B * D).coeff r = 0 := by
    intro r hr
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, truncated_inverse_low_coeff (b i) hbi0 R r hr]
    ring
  have hBD : |1 - B.eval h * D.eval h| ≤ T * h^(R+1) := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul] using
      polynomial_zero_low_coeff_remainder (1 - B * D) R h hh hh1 hz
  have hNB : |N i M - B.eval h| ≤ C * h^(R+1) := by
    rw [hBval]
    simpa only [h, one_div_pow, mul_one_div] using hCrem i M hM
  have H := reciprocal_remainder_transfer (N i M) (B.eval h) (D.eval h) C T S 1 h (R+1)
    one_pos (hN i M hM) hh hC hT hS hNB hBD (polynomial_abs_eval_le D h hh hh1)
  have hmono : (T + C * S) / 1 * h^(R+1) ≤ (1 + Pstar * Sstar + C * Sstar) / 1 * h^(R+1) := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh _)
    rw [div_one, div_one]
    nlinarith [mul_le_mul_of_nonneg_left hSle hC]
  have H2 := H.trans hmono
  simpa only [hDval, h, one_div_pow, mul_one_div] using H2

/-- Uniform bound for the norm coefficients `A_r(t)`, `0 < t ≤ T < 1`. -/
theorem uniformNormCoefficient_uniform_bound (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 < t → t ≤ T → |uniformNormCoefficient t r| ≤ A := by
  have hs : Summable (fun k => (T^2)^k * |(uniformSquaredPolynomial k).coeff r|) := by
    have h := weighted_coefficients_summable uniformSquaredPolynomial (fun k => (T^2)^k)
      4 128 (T^2) 2 r (by norm_num) (by norm_num) (sq_pos_of_pos hT0) (by nlinarith)
      (fun k => pow_nonneg (sq_nonneg T) k) (fun k => le_rfl)
      (fun k => uniformSquaredPolynomial_coefficient_bound k r)
    refine (h.abs).congr (fun k => ?_)
    rw [abs_mul, abs_of_nonneg (pow_nonneg (sq_nonneg T) k)]
  refine ⟨∑' k, (T^2)^k * |(uniformSquaredPolynomial k).coeff r|,
    tsum_nonneg (fun k => by positivity), ?_⟩
  intro t ht0 htT
  have ht1 : t < 1 := lt_of_le_of_lt htT hT1
  have habs := uniformNormCoefficient_absolute_summability t ht0 ht1 r
  unfold uniformNormCoefficient
  have hn : Summable (fun k => ‖binomialWeight t k * (uniformSquaredPolynomial k).coeff r‖) := by
    simpa only [Real.norm_eq_abs] using habs
  have hnorm := norm_tsum_le_tsum_norm hn
  simp only [Real.norm_eq_abs] at hnorm
  calc |∑' k, binomialWeight t k * (uniformSquaredPolynomial k).coeff r|
      ≤ ∑' k, |binomialWeight t k * (uniformSquaredPolynomial k).coeff r| := hnorm
    _ ≤ ∑' k, (T^2)^k * |(uniformSquaredPolynomial k).coeff r| := by
        apply Summable.tsum_le_tsum _ habs hs
        intro k
        rw [abs_mul, abs_of_nonneg (binomialWeight_nonneg t k)]
        exact mul_le_mul_of_nonneg_right (binomialWeight_parameter_bound t T ht0.le htT k)
          (abs_nonneg _)

/-- **Uniform vacuum remainder in the normalised variable** `t = 1/(12c)`, `0 < t ≤ T < 1`. -/
theorem uniformVacuumSeries_uniform_parameters (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ T → ∀ M : ℕ, M ≠ 0 →
      |1/(uniformNormSeries M t) -
        ∑ r ∈ range (R+1), uniformVacuumCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  -- a uniform bound for the first `R+1` coefficients
  choose A hA0 hAb using fun r => uniformNormCoefficient_uniform_bound T hT0 hT1 r
  set Astar := ∑ r ∈ range (R+1), A r with hAstar
  have hAs : 0 ≤ Astar := Finset.sum_nonneg (fun r _ => hA0 r)
  let ι := {t : ℝ // 0 < t ∧ t ≤ T}
  obtain ⟨C, hC, hCrem⟩ := uniformNormSeries_uniform_parameters T hT0 hT1 R
  have H := reciprocal_uniform_remainder (ι := ι) (fun i M => uniformNormSeries M i.1)
    (fun i => uniformNormCoefficient i.1) R Astar hAs
    (fun i M hM => uniformNormSeries_ge_one M hM i.1 i.2.1 (lt_of_le_of_lt i.2.2 hT1))
    (fun i => (uniformNormCoefficient_zero_ge_one i.1 i.2.1 (lt_of_le_of_lt i.2.2 hT1)).trans
      (le_abs_self _))
    (fun i j hj => (hAb j i.1 i.2.1 i.2.2).trans
      (Finset.single_le_sum (fun r _ => hA0 r) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))))
    ⟨C, hC, fun i M hM => hCrem i.1 i.2.1 i.2.2 M hM⟩
  obtain ⟨K, hK, hKrem⟩ := H
  exact ⟨K, hK, fun t ht0 htT M hM => hKrem ⟨t, ht0, htT⟩ M hM⟩

/-- **Task I.**  For every `c0 > 1/12` and `R`, a single constant `K(c0,R)` bounds the
reciprocal remainder of the actual probability integral for all `c ≥ c0` and `M ≥ 1`. -/
theorem raw_uniform_vacuum_uniform_parameters
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c0 : ℝ) (hc0 : 1/12 < c0) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, c0 ≤ c → ∀ M : ℕ, M ≠ 0 →
      |1/(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/
        (c*(M:ℝ))) ∂μ.prod μ) -
        ∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  have hc00 : 0 < c0 := by linarith
  have hT0 : 0 < 1/(12*c0) := by positivity
  have hT1 : 1/(12*c0) < 1 := by
    apply (div_lt_one (by positivity : 0 < 12*c0)).2
    linarith
  obtain ⟨K, hK, hrem⟩ := uniformVacuumSeries_uniform_parameters (1/(12*c0)) hT0 hT1 R
  refine ⟨K, hK, ?_⟩
  intro c hc M hM
  have hcpos : 0 < c := lt_of_lt_of_le hc00 hc
  have ht : 0 < 1/(12*c) := by positivity
  have htT : 1/(12*c) ≤ 1/(12*c0) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < 12*c0)
    linarith
  rw [raw_uniform_kernel_identity U hU hind hlaw c (ne_of_gt hcpos) M hM]
  exact hrem (1/(12*c)) ht htT M hM

end EulerianGrothendieck
