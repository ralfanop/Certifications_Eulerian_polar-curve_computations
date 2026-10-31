import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Appendix A: the moment sequence of the Eulerian profile

Manuscript V173, Appendix A, eqs. (284)–(298) (source labels `eq:A058962-*`, `eq:moments-*`,
`eq:gudermannian`, `eq:lambertian*`, `eq:central-binomial-semifactorial`, `eq:catalan-semifactorial`).

`m k = ∫_{-1/2}^{1/2} t^{2k} dt`, `a k = 4^k (2k+1)` its reciprocal.
`arctanh x := (1/2) log((1+x)/(1-x))` and `arccoth x := arctanh (1/x)`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace EulerianBridge.AppendixA

/-- Even moments of the uniform law on `[-1/2,1/2]` (eq. (27)). -/
noncomputable def m (k : ℕ) : ℝ := ∫ t in (-1/2:ℝ)..(1/2), t ^ (2 * k)

/-- OEIS A058962: `a(k) = 4^k (2k+1)`. -/
def a (k : ℕ) : ℕ := 4 ^ k * (2 * k + 1)

theorem m_eq (k : ℕ) : m k = 1 / (4 ^ k * (2 * k + 1)) := by
  unfold m
  rw [integral_pow]
  have h4 : ((1:ℝ) / 2) ^ (2 * k + 1) = 1 / (2 * 4 ^ k) := by
    rw [div_pow, one_pow, pow_succ, pow_mul]; norm_num; ring
  have h4' : (-(1:ℝ) / 2) ^ (2 * k + 1) = -(1 / (2 * 4 ^ k)) := by
    rw [show (-(1:ℝ) / 2) = -(1 / 2) by ring, Odd.neg_pow ⟨k, rfl⟩, h4]
  rw [show (2 * k + 1 : ℕ) = 2 * k + 1 from rfl, h4, h4']
  push_cast
  field_simp
  ring

/-- The reciprocals of the moments are `a(k)`. -/
theorem m_inv (k : ℕ) : (m k)⁻¹ = (a k : ℝ) := by
  rw [m_eq, one_div, inv_inv]; unfold a; push_cast; ring

/-- `a(k) = b(2k+1)` with `b(n) = n 2^{n-1}` (OEIS A001787, edges of the `n`-cube). -/
theorem a_eq_hypercube_edges (k : ℕ) : a k = (2 * k + 1) * 2 ^ (2 * k) := by
  unfold a; rw [pow_mul]; norm_num; ring

/-- Eq. (286): `a(k) = 8 a(k-1) - 16 a(k-2)`, written without subtraction. -/
theorem a_rec (k : ℕ) : a (k + 2) + 16 * a k = 8 * a (k + 1) := by
  unfold a; ring

/-- Eq. (284): ordinary generating function, `|x| < 1/4`. -/
theorem a_ogf {x : ℝ} (hx : |x| < 1 / 4) :
    HasSum (fun k => (a k : ℝ) * x ^ k) ((1 + 4 * x) / (1 - 4 * x) ^ 2) := by
  have hy : ‖4 * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul]; norm_num; linarith
  have h1 : HasSum (fun k : ℕ => ((k : ℝ) * (4 * x) ^ k)) ((4 * x) / (1 - 4 * x) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hy
  have h0 : HasSum (fun k : ℕ => (4 * x) ^ k) (1 - 4 * x)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hy
  have hne : (1 - 4 * x) ≠ 0 := by
    have : |4 * x| < 1 := by simpa using hy
    intro h; rw [abs_lt] at this; linarith
  have := (h1.mul_left 2).add h0
  convert this using 1
  · funext k; unfold a; push_cast; rw [mul_pow]; ring
  · field_simp; ring

/-- Eq. (285): exponential generating function. -/
theorem a_egf (x : ℝ) :
    HasSum (fun k => (a k : ℝ) * x ^ k / k.factorial) (Real.exp (4 * x) * (1 + 8 * x)) := by
  have he : HasSum (fun k : ℕ => (4 * x) ^ k / k.factorial) (Real.exp (4 * x)) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ℝ (4 * x)
  -- k (4x)^k / k! = 4x (4x)^{k-1}/(k-1)!
  have hk : HasSum (fun k : ℕ => (k : ℝ) * (4 * x) ^ k / k.factorial) (4 * x * Real.exp (4 * x)) := by
    have hs := (he.mul_left (4 * x))
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, zero_div, sub_zero]
    convert hs using 1
    funext k
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  have := (hk.mul_left 2).add he
  convert this using 1
  · funext k; unfold a; push_cast; rw [mul_pow]; ring
  · ring

/-- `arctanh x = (1/2) log((1+x)/(1-x))`. -/
noncomputable def arctanh (x : ℝ) : ℝ := (1 / 2) * Real.log ((1 + x) / (1 - x))

/-- `arccoth x = arctanh (1/x)`. -/
noncomputable def arccoth (x : ℝ) : ℝ := arctanh (1 / x)

/-- Eq. (287): `∑ 1/(4^k (2k+1)) = 2 arctanh(1/2) = 2 arccoth 2 = log 3`. -/
theorem moments_sum :
    HasSum (fun k : ℕ => 1 / ((4:ℝ) ^ k * (2 * k + 1))) (2 * arctanh (1 / 2)) ∧
      2 * arctanh (1 / 2) = 2 * arccoth 2 ∧ 2 * arctanh (1 / 2) = Real.log 3 := by
  have hlog : 2 * arctanh (1 / 2) = Real.log 3 := by
    unfold arctanh; norm_num; ring
  refine ⟨?_, by unfold arccoth; norm_num, hlog⟩
  rw [hlog]
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := 1 / 2) (by norm_num [abs_of_pos])
  have h3 : Real.log (1 + 1 / 2) - Real.log (1 - 1 / 2) = Real.log 3 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [h3] at h
  convert h using 1
  funext k
  rw [pow_succ, pow_mul]
  norm_num
  field_simp
  rw [← mul_pow]; norm_num

/-- The same value by summing (27) under the integral: `∫_{-1/2}^{1/2} (1-t^2)^{-1} dt = log 3`. -/
theorem integral_inv_one_sub_sq : ∫ t in (-1/2:ℝ)..(1/2), (1 - t ^ 2)⁻¹ = Real.log 3 := by
  have hderiv : ∀ t ∈ Set.uIcc (-1/2:ℝ) (1/2),
      HasDerivAt (fun t => (1 / 2) * (Real.log (1 + t) - Real.log (1 - t))) ((1 - t ^ 2)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have h1 : 0 < 1 + t := by linarith [ht.1]
    have h2 : 0 < 1 - t := by linarith [ht.2]
    have d1 : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + t)) t := by
      simpa using ((hasDerivAt_id t).const_add 1).log h1.ne'
    have d2 : HasDerivAt (fun t => Real.log (1 - t)) (-1 / (1 - t)) t := by
      simpa using ((hasDerivAt_id t).const_sub 1).log h2.ne'
    have h3 : (1 - t ^ 2) ≠ 0 := by have := mul_pos h1 h2; nlinarith
    convert (d1.sub d2).const_mul (1 / 2) using 1
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv]
  · norm_num
    have e : Real.log (3/2) = Real.log 3 - Real.log 2 := by rw [Real.log_div] <;> norm_num
    have e' : Real.log (1/2) = - Real.log 2 := by rw [one_div, Real.log_inv]
    rw [e, e']; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    nlinarith [ht.1, ht.2]

/-- Eq. (288): the Gudermannian function `gd ψ = ∫_0^ψ sech u du`. -/
noncomputable def gd (ψ : ℝ) : ℝ := ∫ u in (0:ℝ)..ψ, 1 / Real.cosh u

/-- Eq. (289): `gd⁻¹ φ := ∫_0^φ sec t dt`. -/
noncomputable def gdInv (φ : ℝ) : ℝ := ∫ t in (0:ℝ)..φ, 1 / Real.cos t

/-- Eq. (289): `gd⁻¹ φ = arctanh(sin φ)` for `|φ| < π/2`. -/
theorem gdInv_eq_arctanh_sin {φ : ℝ} (hφ : |φ| < π / 2) : gdInv φ = arctanh (Real.sin φ) := by
  have hφ' := abs_lt.mp hφ
  have hcos : ∀ t ∈ Set.uIcc 0 φ, 0 < Real.cos t := by
    intro t ht
    apply Real.cos_pos_of_mem_Ioo
    rcases Set.mem_uIcc.mp ht with h | h <;> constructor <;> linarith [h.1, h.2]
  have hderiv : ∀ t ∈ Set.uIcc 0 φ, HasDerivAt (fun t => arctanh (Real.sin t)) (1 / Real.cos t) t := by
    intro t ht
    have hc := hcos t ht
    have hs1 : 0 < 1 + Real.sin t := by nlinarith [Real.sin_sq_add_cos_sq t, Real.neg_one_le_sin t]
    have hs2 : 0 < 1 - Real.sin t := by nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_le_one t]
    have d1 : HasDerivAt (fun t => Real.log (1 + Real.sin t)) (Real.cos t / (1 + Real.sin t)) t := by
      simpa using ((Real.hasDerivAt_sin t).const_add 1).log hs1.ne'
    have d2 : HasDerivAt (fun t => Real.log (1 - Real.sin t)) (-Real.cos t / (1 - Real.sin t)) t := by
      simpa using ((Real.hasDerivAt_sin t).const_sub 1).log hs2.ne'
    have hfun : (fun t => arctanh (Real.sin t)) =ᶠ[nhds t]
        fun t => (1 / 2) * (Real.log (1 + Real.sin t) - Real.log (1 - Real.sin t)) := by
      have hU : ∀ᶠ s in nhds t, 0 < 1 + Real.sin s ∧ 0 < 1 - Real.sin s := by
        have c1 : ContinuousAt (fun s => 1 + Real.sin s) t := by fun_prop
        have c2 : ContinuousAt (fun s => 1 - Real.sin s) t := by fun_prop
        exact (c1.eventually (lt_mem_nhds hs1)).and (c2.eventually (lt_mem_nhds hs2))
      filter_upwards [hU] with s hs
      unfold arctanh
      rw [Real.log_div hs.1.ne' hs.2.ne']
    refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
    convert (d1.sub d2).const_mul (1 / 2) using 1
    have hcos2 : Real.cos t ^ 2 = (1 + Real.sin t) * (1 - Real.sin t) := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    field_simp
    nlinarith [hcos2]
  unfold gdInv
  rw [integral_eq_sub_of_hasDerivAt hderiv]
  · unfold arctanh; simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const Real.continuous_cos.continuousOn
    intro t ht; exact (hcos t ht).ne'

/-- Eq. (290): `gd⁻¹(π/4) = arctanh(1/√2) = log(1+√2)`. -/
theorem gdInv_pi_div_four :
    gdInv (π / 4) = arctanh (1 / Real.sqrt 2) ∧ arctanh (1 / Real.sqrt 2) = Real.log (1 + Real.sqrt 2) := by
  have hpi : |π / 4| < π / 2 := by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos]
  refine ⟨?_, ?_⟩
  · rw [gdInv_eq_arctanh_sin hpi, Real.sin_pi_div_four]
    congr 1
    rw [eq_div_iff (by positivity)]
    have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    field_simp
    nlinarith
  · unfold arctanh
    have hs : 0 < Real.sqrt 2 := by positivity
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hlt : 1 < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have key : (1 + 1 / Real.sqrt 2) / (1 - 1 / Real.sqrt 2) = (1 + Real.sqrt 2) ^ 2 := by
      have hne : Real.sqrt 2 - 1 ≠ 0 := by linarith
      have hlt' : 1 / Real.sqrt 2 < 1 := by rw [div_lt_one hs]; exact hlt
      rw [div_eq_iff (sub_ne_zero.mpr (ne_of_gt hlt'))]
      field_simp
      nlinarith
    rw [key, Real.log_pow]
    push_cast; ring

/-- Eq. (291): `sin(arctan(4/3)) = 4/5` and `gd⁻¹(arctan(4/3)) = arctanh(4/5) = 2 arctanh(1/2) = log 3`. -/
theorem gdInv_arctan_four_thirds :
    Real.sin (Real.arctan (4 / 3)) = 4 / 5 ∧
      gdInv (Real.arctan (4 / 3)) = arctanh (4 / 5) ∧
      arctanh (4 / 5) = 2 * arctanh (1 / 2) ∧ 2 * arctanh (1 / 2) = Real.log 3 := by
  have hsin : Real.sin (Real.arctan (4 / 3)) = 4 / 5 := by
    rw [Real.sin_arctan]
    rw [show (1:ℝ) + (4 / 3) ^ 2 = (5 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have habs : |Real.arctan (4 / 3)| < π / 2 := by
    rw [abs_lt]; exact ⟨by linarith [Real.neg_pi_div_two_lt_arctan (4/3)], Real.arctan_lt_pi_div_two _⟩
  refine ⟨hsin, by rw [gdInv_eq_arctanh_sin habs, hsin], ?_, ?_⟩
  · unfold arctanh; norm_num
    rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  · unfold arctanh; norm_num; ring

/-- Double factorial of an odd number, `(2k-1)!! = 1·3···(2k-1)` (OEIS A001147). -/
def oddDF (k : ℕ) : ℕ := (2 * k - 1).doubleFactorial

theorem oddDF_succ (k : ℕ) : oddDF (k + 1) = (2 * k + 1) * oddDF k := by
  unfold oddDF
  rcases k with _ | k
  · simp
  · rw [show 2 * (k + 1 + 1) - 1 = (2 * k + 1) + 2 by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      Nat.doubleFactorial_add_two]
    ring

/-- `(2k)! = 2^k k! (2k-1)!!`. -/
theorem factorial_two_mul (k : ℕ) : (2 * k).factorial = 2 ^ k * k.factorial * oddDF k := by
  induction k with
  | zero => simp [oddDF]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, ih,
      oddDF_succ, Nat.factorial_succ]
    ring

/-- Eq. (293): `C(2k,k) = 2^k (2k-1)!!/k!`, in the multiplicative form `k! C(2k,k) = 2^k (2k-1)!!`. -/
theorem central_binom_semifactorial (k : ℕ) : k.factorial * Nat.centralBinom k = 2 ^ k * oddDF k := by
  have h := Nat.succ_mul_centralBinom_succ k
  have hfac : (2 * k).factorial = Nat.centralBinom k * k.factorial * k.factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose, ← Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ 2 * k),
      show 2 * k - k = k by omega]
  rw [factorial_two_mul] at hfac
  have hk : 0 < k.factorial := Nat.factorial_pos k
  have : 2 ^ k * oddDF k * k.factorial = Nat.centralBinom k * k.factorial * k.factorial := by
    rw [← hfac]; ring
  have := Nat.eq_of_mul_eq_mul_right hk this
  linarith [this]

/-- Eq. (294): `C_k = C(2k,k)/(k+1)`, in the form `(k+1)! C_k = 2^k (2k-1)!!`. -/
theorem catalan_semifactorial (k : ℕ) : (k + 1).factorial * catalan k = 2 ^ k * oddDF k := by
  rw [← central_binom_semifactorial, Nat.factorial_succ, catalan_eq_centralBinom_div,
    Nat.mul_comm (k + 1), Nat.mul_assoc]
  congr 1
  exact Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom k)

/-- Eq. (292): `m_k = (2k-1)!!/(4^k (2k+1)!!)`, since `(2k+1)!! = (2k+1)(2k-1)!!`. -/
theorem m_semifactorial (k : ℕ) : m k = (oddDF k : ℝ) / (4 ^ k * oddDF (k + 1)) := by
  rw [m_eq, oddDF_succ]
  have hpos : (0:ℝ) < oddDF k := by
    unfold oddDF; exact_mod_cast Nat.doubleFactorial_pos _
  push_cast
  field_simp

/-- Eq. (295): uniform law on `[-2,2]`: `(1/4)∫_{-2}^{2} x^{2k} dx = 4^k/(2k+1) = 16^k m_k`. -/
theorem uniform_moments (k : ℕ) :
    (1 / 4) * ∫ x in (-2:ℝ)..2, x ^ (2 * k) = 4 ^ k / (2 * k + 1) ∧ (4:ℝ) ^ k / (2 * k + 1) = 16 ^ k * m k := by
  refine ⟨?_, ?_⟩
  · rw [integral_pow]
    rw [show ((-2:ℝ)) ^ (2 * k + 1) = -(2 * 4 ^ k) by
          rw [Odd.neg_pow ⟨k, rfl⟩, pow_succ, pow_mul]; norm_num; ring,
        show ((2:ℝ)) ^ (2 * k + 1) = 2 * 4 ^ k by rw [pow_succ, pow_mul]; norm_num; ring]
    push_cast; field_simp; ring
  · rw [m_eq, show (16:ℝ) ^ k = 4 ^ k * 4 ^ k by rw [← mul_pow]; norm_num]
    field_simp

end EulerianBridge.AppendixA
