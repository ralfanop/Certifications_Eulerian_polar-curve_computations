import EulerianGrothendieck.ComplexArcsineDisk
import EulerianGrothendieck.DirichletChiFive
import EulerianGrothendieck.CentralBinomialMoments
import EulerianGrothendieck.FockVacuumProjection

/-! # Task E, part 2: Proposition 10.1 (Catalan--Lipschitz--Dirichlet specialisation)

`catalanB` is the binomial power series `B = ∑ binom(2n,n) Xⁿ`, `theta f = X · f'`, and
`evalSeries f x = ∑' coeff_n(f) xⁿ`.  With `x* = 1/20`:

* `catalanB_value`: `B(1/20) = √5/2`;
* `catalanTheta_value`: `[(Θ² - Θ)B](1/20) = 3√5/128`;
* `catalan_lipschitz_dirichlet_bridge`:
  `B(1/20) = (sup_{D_B} |H0'|)⁻¹ = log φ / L(1,χ₅) = √5/2`;
* `cL_eq`: `c_L = B(1/20)/6 = √5/12`;
* `vacuum_limit_cL`, `fock_vacuum_limit_cL`: the actual (probability-integral, resp. intrinsic
  Fock) vacuum probability at `c_L` converges to `p_∞(c_L) = 2/√5 = 1/B(1/20)`;
  `p_∞` is the limit itself, not a formula. -/

noncomputable section
open scoped BigOperators
open Filter Topology Finset MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck.Catalan

/-- The binomial generating function `B(x) = ∑ binom(2n,n) xⁿ`, as a formal power series. -/
def catalanB : PowerSeries ℝ := PowerSeries.mk (fun n => (n.centralBinom : ℝ))

/-- The Euler operator `Θ = x d/dx` on formal power series. -/
def theta (f : PowerSeries ℝ) : PowerSeries ℝ := PowerSeries.X * PowerSeries.derivative ℝ f

/-- Evaluation of a power series by its coefficient series. -/
def evalSeries (f : PowerSeries ℝ) (x : ℝ) : ℝ := ∑' n, PowerSeries.coeff n f * x ^ n

theorem coeff_theta (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (theta f) = n * PowerSeries.coeff n f := by
  unfold theta
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast; ring

theorem coeff_catalanB (n : ℕ) : PowerSeries.coeff n catalanB = (n.centralBinom : ℝ) := by
  simp [catalanB]

theorem central_term (n : ℕ) (x : ℝ) :
    (n.centralBinom : ℝ) * x ^ n = centralCoefficient n * (4 * x) ^ n := by
  unfold centralCoefficient
  rw [mul_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero n four_ne_zero)]

theorem sqrt_four_fifths : Real.sqrt (1 - 1/5) = 2 / Real.sqrt 5 := by
  rw [show (1:ℝ) - 1/5 = 4/5 by norm_num, Real.sqrt_div' _ (by norm_num),
    show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem catalanB_hasSum : HasSum (fun n => PowerSeries.coeff n catalanB * (1/20 : ℝ) ^ n)
    (Real.sqrt 5 / 2) := by
  have hs := centralCoefficient_geometric_summable (1/5) (by norm_num) (by norm_num)
  have hv := centralBinomial_sum (1/5) (by norm_num) (by norm_num)
  have h : HasSum (fun n => centralCoefficient n * (1/5 : ℝ) ^ n) (Real.sqrt 5 / 2) := by
    rw [show Real.sqrt 5 / 2 = 1 / Real.sqrt (1 - 1/5) by rw [sqrt_four_fifths, one_div_div], ← hv]
    exact hs.hasSum
  have hfun : (fun n => PowerSeries.coeff n catalanB * (1/20 : ℝ) ^ n) =
      fun n => centralCoefficient n * (1/5 : ℝ) ^ n := by
    funext n
    rw [coeff_catalanB, central_term]
    norm_num
  rw [hfun]
  exact h

/-- **`B(1/20) = √5/2`**. -/
theorem catalanB_value : evalSeries catalanB (1/20) = Real.sqrt 5 / 2 :=
  catalanB_hasSum.tsum_eq

/-- **`[(Θ² - Θ)B](1/20) = 3√5/128`**. -/
theorem catalanTheta_value :
    evalSeries (theta (theta catalanB) - theta catalanB) (1/20) = 3 * Real.sqrt 5 / 128 := by
  have h := centralBinomial_second_factorial_moment_hasSum (1/5) (by norm_num) (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hval : (3/4:ℝ) * (1/5) ^ 2 * (1 / Real.sqrt (1 - 1/5)) ^ 5 = 3 * Real.sqrt 5 / 128 := by
    rw [sqrt_four_fifths, one_div_div]
    linear_combination (3/3200 * Real.sqrt 5 * (Real.sqrt 5 ^ 2 + 5)) * h5
  rw [hval] at h
  have hfun : (fun n => PowerSeries.coeff n (theta (theta catalanB) - theta catalanB) * (1/20 : ℝ) ^ n) =
      fun n : ℕ => (n:ℝ) * ((n:ℝ) - 1) * centralCoefficient n * (1/5 : ℝ) ^ n := by
    funext n
    simp only [map_sub, coeff_theta, coeff_catalanB]
    have hc := central_term n (1/20)
    rw [show (4:ℝ) * (1/20) = 1/5 by norm_num] at hc
    calc ((n:ℝ) * ((n:ℝ) * (n.centralBinom : ℝ)) - (n:ℝ) * (n.centralBinom : ℝ)) * (1/20:ℝ) ^ n
        = (n:ℝ) * ((n:ℝ) - 1) * ((n.centralBinom : ℝ) * (1/20:ℝ) ^ n) := by ring
      _ = (n:ℝ) * ((n:ℝ) - 1) * centralCoefficient n * (1/5:ℝ) ^ n := by rw [hc]; ring
  unfold evalSeries
  rw [hfun]
  exact h.tsum_eq

/-- The arithmetic scale `c_L = √5/12`. -/
def cL : ℝ := Real.sqrt 5 / 12

theorem cL_eq : cL = evalSeries catalanB (1/20) / 6 := by
  rw [catalanB_value, cL]; ring

open EulerianGrothendieck.ArcsinDisk EulerianGrothendieck.Dirichlet in
/-- **Proposition 10.1, boxed identity**:
`B(1/20) = (sup_{z∈D_B}|H0'(z)|)⁻¹ = log φ / L(1,χ₅) = √5/2`. -/
theorem catalan_lipschitz_dirichlet_bridge :
    evalSeries catalanB (1/20) = (sSup ((fun z => ‖deriv H0 z‖) '' diskB))⁻¹ ∧
    (sSup ((fun z => ‖deriv H0 z‖) '' diskB))⁻¹ = Real.log phi / LOneChiFive ∧
    Real.log phi / LOneChiFive = Real.sqrt 5 / 2 := by
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hphi : 1 < phi := by
    unfold phi
    have : 1 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  have hlog : 0 < Real.log phi := Real.log_pos hphi
  have h3 : Real.log phi / LOneChiFive = Real.sqrt 5 / 2 := by
    rw [LOneChiFive_eq, div_mul_eq_mul_div, div_div_eq_mul_div,
      mul_comm (Real.log phi) (Real.sqrt 5), mul_div_mul_right _ _ hlog.ne']
  refine ⟨?_, ?_, h3⟩
  · rw [catalanB_value, sSup_norm_deriv_H0, inv_div]
  · rw [sSup_norm_deriv_H0, h3, inv_div]

theorem uniformVacuumCoefficient_zero (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    uniformVacuumCoefficient t 0 = Real.sqrt (1 - t ^ 2) := by
  unfold uniformVacuumCoefficient inverseSeriesCoefficient
  rw [PowerSeries.coeff_inv, if_pos rfl]
  have : PowerSeries.constantCoeff (PowerSeries.mk (uniformNormCoefficient t)) =
      uniformNormCoefficient t 0 := by simp
  rw [this, uniformNormCoefficient_zero_closed t ht0 ht1, one_div, inv_inv]

/-- **`p_∞(c_L) = 2/√5 = 1/B(1/20)`**: the actual vacuum probability `1/N_M(c_L)` converges. -/
theorem vacuum_limit_cL
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) :
    Tendsto (fun M : ℕ => 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
      (∑ i ∈ range M, U i xy.2) / (cL * (M:ℝ))) ∂μ.prod μ) atTop
      (𝓝 (1 / evalSeries catalanB (1/20))) := by
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h15 : 1 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hcL : 1/12 < cL := by unfold cL; linarith
  obtain ⟨K, hK, hrem⟩ := EulerianGrothendieck.raw_uniform_vacuum_all_orders U hU hind hlaw cL hcL 0
  have ht : 1/(12*cL) = 1 / Real.sqrt 5 := by
    unfold cL
    rw [show (12:ℝ) * (Real.sqrt 5 / 12) = Real.sqrt 5 by ring]
  have ht0 : 0 < 1/(12*cL) := by rw [ht]; positivity
  have ht1 : 1/(12*cL) < 1 := by rw [ht, div_lt_one hs5]; exact h15
  have hcoef : uniformVacuumCoefficient (1/(12*cL)) 0 = 1 / evalSeries catalanB (1/20) := by
    rw [uniformVacuumCoefficient_zero _ ht0 ht1, ht, catalanB_value, div_pow, one_pow, h5,
      sqrt_four_fifths, one_div_div]
  rw [← hcoef]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M0, hM0⟩ := exists_nat_gt ((K + 1) / ε)
  refine ⟨M0 + 1, fun M hM => ?_⟩
  have hM' : M ≠ 0 := by omega
  have hMpos : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM'
  have hb := hrem M hM'
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, div_one, pow_one] at hb
  rw [Real.dist_eq]
  have hMgt : (K + 1) / ε < M := by
    have : (M0:ℝ) + 1 ≤ M := by exact_mod_cast hM
    linarith
  rw [div_lt_iff₀ hε] at hMgt
  calc _ ≤ K / M := hb
    _ < ε := by
      rw [div_lt_iff₀ hMpos]
      linarith

open EulerianGrothendieck.Fock in
/-- The same limit for the intrinsic Fock vacuum probability `p_{E,M}(c_L M)`. -/
theorem fock_vacuum_limit_cL
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) :
    Tendsto (fun M : ℕ => fockVacuumProbability (cL * M) M) atTop
      (𝓝 (1 / evalSeries catalanB (1/20))) := by
  refine (vacuum_limit_cL U hU hind hlaw).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with M hM
  have hMpos : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hcL : 0 < cL := by unfold cL; positivity
  rw [fockVacuumProbability, (fock_vacuum_probability U hU hind hlaw M (mul_pos hcL hMpos)).2.2]

end EulerianGrothendieck.Catalan
