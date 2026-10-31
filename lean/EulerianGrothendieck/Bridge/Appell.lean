import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Section 4: formal operators `f(D)` on polynomials

For a formal power series `f = ∑ f_k z^k` over a field `K` of characteristic zero,
`op f p = ∑_k f_k D^k p` (a finite sum, because `D` is locally nilpotent on `K[X]`).

We prove that `op` is a `K`-linear map, that `op 1 = id`, `op X = D`, `op (f - g) = op f - op g`,
and that `op (f * g) = op f ∘ op g`. The proof of multiplicativity goes through the exponential
generating function: `op f (X^n) = n! · [z^n] (f(z) e^{xz})` (Appell property).

We also prove the analytic identification of the averaging operator over `ℝ`:
`(op M p)(x) = ∫_0^1 p(x+t) dt` with `M(z) = ∑ z^k/(k+1)!` (manuscript (58)).
-/

open Finset
open scoped Nat

namespace EulerianBridge.Appell

variable {K : Type*} [Field K] [CharZero K]

local notation "D" => (Polynomial.derivative : Polynomial K →ₗ[K] Polynomial K)

/-- The finite sum `∑_{k < N} f_k D^k p`. -/
noncomputable def opSum (f : PowerSeries K) (N : ℕ) (p : Polynomial K) : Polynomial K :=
  ∑ k ∈ range N, PowerSeries.coeff k f • (D ^ k) p

theorem pow_D_apply (k : ℕ) (p : Polynomial K) : (D ^ k) p = Polynomial.derivative^[k] p := by
  rw [Module.End.pow_apply]

theorem pow_D_eq_zero {p : Polynomial K} {k : ℕ} (h : p.natDegree < k) : (D ^ k) p = 0 := by
  rw [pow_D_apply]; exact Polynomial.iterate_derivative_eq_zero h

theorem opSum_eq (f : PowerSeries K) {p : Polynomial K} {N N' : ℕ} (hN : p.natDegree < N)
    (hN' : p.natDegree < N') : opSum f N p = opSum f N' p := by
  unfold opSum
  wlog h : N ≤ N' generalizing N N'
  · exact (this hN' hN (by omega)).symm
  refine Finset.sum_subset (Finset.range_mono h) (fun k hk hk' => ?_)
  simp only [mem_range, not_lt] at hk'
  rw [pow_D_eq_zero (by omega), smul_zero]

/-- `op f p = ∑_k f_k D^k p`. -/
noncomputable def op (f : PowerSeries K) : Polynomial K →ₗ[K] Polynomial K where
  toFun p := opSum f (p.natDegree + 1) p
  map_add' p q := by
    set N := max (max p.natDegree q.natDegree) (p + q).natDegree + 1
    rw [opSum_eq f (Nat.lt_succ_self _) (show (p + q).natDegree < N by omega),
      opSum_eq f (Nat.lt_succ_self _) (show p.natDegree < N by omega),
      opSum_eq f (Nat.lt_succ_self _) (show q.natDegree < N by omega)]
    unfold opSum
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    rw [map_add, smul_add]
  map_smul' c p := by
    have h : (c • p).natDegree ≤ p.natDegree := Polynomial.natDegree_smul_le c p
    simp only [RingHom.id_apply]
    rw [opSum_eq f (Nat.lt_succ_self _) (show (c • p).natDegree < p.natDegree + 1 by omega)]
    unfold opSum
    rw [smul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_comm]

theorem op_apply (f : PowerSeries K) (p : Polynomial K) :
    op f p = ∑ k ∈ range (p.natDegree + 1), PowerSeries.coeff k f • (D ^ k) p := rfl

theorem op_apply_of_lt (f : PowerSeries K) {p : Polynomial K} {N : ℕ} (hN : p.natDegree < N) :
    op f p = ∑ k ∈ range N, PowerSeries.coeff k f • (D ^ k) p :=
  opSum_eq f (Nat.lt_succ_self _) hN

theorem op_sub (f g : PowerSeries K) : op (f - g) = op f - op g := by
  refine LinearMap.ext (fun p => ?_)
  simp only [LinearMap.sub_apply, op_apply, map_sub, sub_smul, sum_sub_distrib]

theorem op_one : op (1 : PowerSeries K) = LinearMap.id := by
  refine LinearMap.ext (fun p => ?_)
  rw [op_apply, sum_eq_single 0]
  · simp
  · intro k _ hk; simp [PowerSeries.coeff_one, hk]
  · intro h; simp at h

theorem op_X : op (PowerSeries.X : PowerSeries K) = D := by
  refine LinearMap.ext (fun p => ?_)
  rw [op_apply_of_lt _ (show p.natDegree < p.natDegree + 2 by omega), sum_eq_single 1]
  · simp [PowerSeries.coeff_X]
  · intro k _ hk; simp [PowerSeries.coeff_X, hk]
  · intro h; simp at h

/-! ## The Appell property -/

/-- `e^{xz} = ∑ x^n z^n/n!` in `K[x]⟦z⟧`. -/
noncomputable def expXZ : PowerSeries (Polynomial K) :=
  PowerSeries.mk fun n => Polynomial.C ((n ! : K)⁻¹) * Polynomial.X ^ n

/-- `f` viewed in `K[x]⟦z⟧` with constant polynomial coefficients. -/
noncomputable def lift (f : PowerSeries K) : PowerSeries (Polynomial K) := PowerSeries.map Polynomial.C f

theorem op_X_pow (f : PowerSeries K) (n : ℕ) :
    op f (Polynomial.X ^ n) = (n ! : K) • PowerSeries.coeff n (lift f * expXZ) := by
  rw [op_apply, Polynomial.natDegree_X_pow, PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, smul_sum]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [pow_D_apply, Polynomial.iterate_derivative_X_pow_eq_smul]
  simp only [lift, expXZ, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  have hfac : ((n - k)! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hd : (n.descFactorial k : K) = (n ! : K) * ((n - k)! : K)⁻¹ := by
    rw [← Nat.factorial_mul_descFactorial hk']; push_cast; field_simp
  rw [hd, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  simp only [map_mul]
  ring

/-- The coefficientwise application of `op f` to a generating function. -/
theorem op_coeff_lift_mul (f g : PowerSeries K) (n : ℕ) :
    op f (PowerSeries.coeff n (lift g * expXZ)) = PowerSeries.coeff n (lift g * (lift f * expXZ)) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine sum_congr rfl (fun ij _ => ?_)
  simp only [lift, expXZ, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  have h1 : Polynomial.C (PowerSeries.coeff ij.1 g) * (Polynomial.C ((ij.2 ! : K)⁻¹) * Polynomial.X ^ ij.2)
      = (PowerSeries.coeff ij.1 g * (ij.2 ! : K)⁻¹) • Polynomial.X ^ ij.2 := by
    rw [Polynomial.smul_eq_C_mul, map_mul, mul_assoc]
  rw [h1, map_smul, op_X_pow, smul_smul, Polynomial.smul_eq_C_mul]
  have hfac : (ij.2 ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [show PowerSeries.coeff ij.1 g * (ij.2 ! : K)⁻¹ * (ij.2 ! : K) = PowerSeries.coeff ij.1 g by
    field_simp]
  rfl

theorem op_mul_X_pow (f g : PowerSeries K) (n : ℕ) :
    op (f * g) (Polynomial.X ^ n) = op f (op g (Polynomial.X ^ n)) := by
  rw [op_X_pow g, map_smul, op_coeff_lift_mul, op_X_pow]
  congr 2
  simp only [lift, map_mul]
  ring

/-- Multiplicativity: `op (f * g) = op f ∘ op g`. -/
theorem op_mul (f g : PowerSeries K) : op (f * g) = (op f).comp (op g) := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← Polynomial.X_pow_eq_monomial,
    op_mul_X_pow]

theorem op_comp_eq_id {f g : PowerSeries K} (h : f * g = 1) : (op f).comp (op g) = LinearMap.id := by
  rw [← op_mul, h, op_one]

/-! ## The averaging operator and its integral form over `ℝ` -/

/-- `M(z) = ∑ z^k/(k+1)!`, the symbol of the averaging operator `𝒜 = M(D)` (eqs. (57)–(58)). -/
noncomputable def Mser (K : Type*) [Field K] : PowerSeries K :=
  PowerSeries.mk fun k => ((k + 1)! : K)⁻¹

theorem X_mul_Mser : (PowerSeries.X : PowerSeries K) * Mser K = PowerSeries.exp K - 1 := by
  ext n
  rcases n with _ | n
  · simp [Mser]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [Mser, PowerSeries.coeff_exp]

/-- An antiderivative of a polynomial. -/
noncomputable def antideriv (p : Polynomial K) : Polynomial K :=
  ∑ i ∈ range (p.natDegree + 1), Polynomial.C (p.coeff i / (i + 1)) * Polynomial.X ^ (i + 1)

theorem derivative_antideriv (p : Polynomial K) : Polynomial.derivative (antideriv p) = p := by
  unfold antideriv
  rw [Polynomial.derivative_sum]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.derivative_C_mul_X_pow]
  simp only [Nat.add_sub_cancel]
  congr 2
  have : ((i:K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero i
  push_cast
  field_simp

/-- Taylor's formula at the evaluation level: `Q(x+1) = ∑_k (D^k Q)(x)/k!`. -/
theorem eval_add_one (Q : Polynomial K) (x : K) {N : ℕ} (hN : Q.natDegree < N) :
    Q.eval (x + 1) = ∑ k ∈ range N, ((k ! : K)⁻¹) * ((D ^ k) Q).eval x := by
  rw [show x + 1 = 1 + x by ring, ← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range' (n := N) (by rw [Polynomial.natDegree_taylor]; omega)]
  refine sum_congr rfl (fun k _ => ?_)
  rw [one_pow, mul_one, Polynomial.taylor_coeff, pow_D_apply]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := k)) Q
  simp only [LinearMap.smul_apply] at h
  rw [← h, Polynomial.eval_smul, nsmul_eq_mul]
  have : (k ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- `𝒜 p = Q(x+1) - Q(x)` for any antiderivative `Q` of `p`. -/
theorem op_Mser_eval (p : Polynomial K) (x : K) :
    (op (Mser K) p).eval x = (antideriv p).eval (x + 1) - (antideriv p).eval x := by
  set Q := antideriv p
  have hQ : Polynomial.derivative Q = p := derivative_antideriv p
  have hdeg : p.natDegree < Q.natDegree + 1 := by
    have := Polynomial.natDegree_derivative_le Q; rw [hQ] at this; omega
  set N := Q.natDegree + p.natDegree + 1
  rw [eval_add_one Q x (show Q.natDegree < N + 1 by omega), sum_range_succ',
    op_apply_of_lt _ (show p.natDegree < N by omega), Polynomial.eval_finset_sum]
  simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
    add_sub_cancel_right]
  refine sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_smul, smul_eq_mul, pow_succ, Module.End.mul_apply, hQ]
  simp [Mser]

/-- Eq. (58): over `ℝ`, `(𝒜 p)(x) = ∫_0^1 p(x+t) dt` with `𝒜 = M(D)`. -/
theorem op_Mser_integral (p : Polynomial ℝ) (x : ℝ) :
    (op (Mser ℝ) p).eval x = ∫ t in (0:ℝ)..1, p.eval (x + t) := by
  rw [op_Mser_eval]
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t => (antideriv p).eval (x + t)) (p.eval (x + t)) t := by
    intro t _
    have h := ((antideriv p).hasDerivAt (x + t)).comp t ((hasDerivAt_id t).const_add x)
    rw [derivative_antideriv, mul_one] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((Polynomial.continuous (p := p)).comp (continuous_const.add continuous_id)).intervalIntegrable 0 1)]
  simp

/-! ## Change of scalars -/

theorem op_map (σ : ℚ →+* ℝ) (f : PowerSeries ℚ) (p : Polynomial ℚ) :
    (op f p).map σ = op (PowerSeries.map σ f) (p.map σ) := by
  rw [op_apply, op_apply_of_lt _ (show (p.map σ).natDegree < p.natDegree + 1 by
    rw [Polynomial.natDegree_map]; omega), Polynomial.map_sum]
  refine sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.map_smul, pow_D_apply, pow_D_apply, Polynomial.iterate_derivative_map,
    PowerSeries.coeff_map]

theorem map_Mser (σ : ℚ →+* ℝ) : PowerSeries.map σ (Mser ℚ) = Mser ℝ := by
  ext k; simp [Mser]

end EulerianBridge.Appell
