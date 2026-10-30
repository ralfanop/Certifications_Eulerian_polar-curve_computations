import EulerianGrothendieck.CentralBinomialSeries

noncomputable section
open scoped BigOperators
open PowerSeries Finset
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

theorem centralSeries_square_inverse : (1-PowerSeries.X)*centralSeries^2 = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, centralSeries_square_coeff, PowerSeries.coeff_one]
  cases n with
  | zero => simp
  | succ n => rw [PowerSeries.coeff_succ_X_mul, centralSeries_square_coeff]; simp

theorem centralSeries_first_derivative :
    PowerSeries.derivative ℝ centralSeries = PowerSeries.C (1/2:ℝ)*centralSeries^3 := by
  calc
    _ = ((1-PowerSeries.X)*centralSeries^2)*PowerSeries.derivative ℝ centralSeries := by
      rw [centralSeries_square_inverse, one_mul]
    _ = centralSeries^2*((1-PowerSeries.X)*PowerSeries.derivative ℝ centralSeries) := by ring
    _ = centralSeries^2*(PowerSeries.C (1/2:ℝ)*centralSeries) := by rw [centralSeries_ode]
    _ = _ := by ring

theorem centralSeries_second_derivative :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ centralSeries) =
      PowerSeries.C (3/4:ℝ)*centralSeries^5 := by
  rw [centralSeries_first_derivative, Derivation.leibniz, PowerSeries.derivative_C]
  simp only [zero_mul, zero_add, smul_eq_mul]
  rw [Derivation.leibniz_pow, centralSeries_first_derivative]
  simp only [nsmul_eq_mul, smul_eq_mul]
  have hc3 : PowerSeries.C (3:ℝ) = (3:PowerSeries ℝ) := by
    calc
      _ = PowerSeries.C ((1:ℝ)+1+1) := by norm_num
      _ = 1+1+1 := by rw [map_add, map_add, map_one]
      _ = 3 := by ring
  have hc : PowerSeries.C (1/2:ℝ)*(3:PowerSeries ℝ)*PowerSeries.C (1/2:ℝ) =
      PowerSeries.C (3/4:ℝ) := by
    calc
      _ = PowerSeries.C (1/2:ℝ)*PowerSeries.C (3:ℝ)*PowerSeries.C (1/2:ℝ) := by rw [hc3]
      _ = PowerSeries.C ((1/2:ℝ)*3*(1/2)) := by rw [← map_mul, ← map_mul]
      _ = _ := by norm_num
  calc
    _ = (PowerSeries.C (1/2:ℝ)*(3:PowerSeries ℝ)*PowerSeries.C (1/2:ℝ))*centralSeries^5 := by norm_num; ring
    _ = _ := by rw [hc]

theorem powerSeries_product_hasSum (f g : PowerSeries ℝ) (s a b : ℝ)
    (hf : HasSum (fun n => PowerSeries.coeff n f*s^n) a)
    (hg : HasSum (fun n => PowerSeries.coeff n g*s^n) b) :
    HasSum (fun n => PowerSeries.coeff n (f*g)*s^n) (a*b) := by
  have h := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_iff.2 hf.summable) (summable_norm_iff.2 hg.summable)
  rw [hf.tsum_eq, hg.tsum_eq] at h
  apply h.congr_fun
  intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j l => PowerSeries.coeff j f*PowerSeries.coeff l g) n, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have he : j+(n-j)=n := Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  calc
    _ = (PowerSeries.coeff j f*PowerSeries.coeff (n-j) g)*(s^j*s^(n-j)) := by rw [← pow_add, he]
    _ = _ := by ring

theorem centralSeries_power_hasSum (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) (m : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (centralSeries^m)*s^n)
      ((∑' k, centralCoefficient k*s^k)^m) := by
  induction m with
  | zero =>
    simp only [pow_zero, PowerSeries.coeff_one]
    convert (hasSum_ite_eq 0 (1:ℝ)) using 1
    ext n
    split_ifs with hn
    · subst n; simp
    · simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    apply powerSeries_product_hasSum _ _ _ _ _ ih
    simpa only [centralSeries_coeff] using (centralCoefficient_geometric_summable s hs0 hs1).hasSum

theorem centralBinomial_second_factorial_moment_hasSum (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum (fun k : ℕ => (k:ℝ)*(k-1)*centralCoefficient k*s^k)
      ((3/4:ℝ)*s^2*(1/Real.sqrt (1-s))^5) := by
  have h5 := (centralSeries_power_hasSum s hs0 hs1 5).mul_left ((3/4:ℝ)*s^2)
  rw [centralBinomial_sum s hs0 hs1] at h5
  have hc : ∀ n : ℕ, (n+2:ℝ)*(n+1)*centralCoefficient (n+2) =
      (3/4:ℝ)*PowerSeries.coeff n (centralSeries^5) := by
    intro n
    have h := congrArg (PowerSeries.coeff (R := ℝ) n) centralSeries_second_derivative
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
      PowerSeries.coeff_C_mul, centralSeries_coeff] at h
    push_cast at h
    nlinarith
  have hs : HasSum (fun n : ℕ => (n+2:ℝ)*(n+1)*centralCoefficient (n+2)*s^(n+2))
      ((3/4:ℝ)*s^2*(1/Real.sqrt (1-s))^5) := by
    apply h5.congr_fun
    intro n
    rw [hc, pow_add]
    ring
  let f := fun k : ℕ => (k:ℝ)*(k-1)*centralCoefficient k*s^k
  have hs' : HasSum (fun n => f (n+2)) ((3/4:ℝ)*s^2*(1/Real.sqrt (1-s))^5) := by
    apply hs.congr_fun
    intro n
    dsimp [f]
    push_cast
    ring
  have hsum := hs'.sum_range_add
  simpa [f, Finset.sum_range_succ] using hsum

end EulerianGrothendieck
