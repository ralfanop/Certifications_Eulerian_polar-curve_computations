import Bridge.BernoulliAppell
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Theorem 4.2: hyperbolic duplication and the Euler–Appell operator

Manuscript V173, eqs. (65)–(70).

* (65) `M(4z) = ((e^{2z}+1)/2) M(2z)` and (66) `e^z M(2z)/M(4z) = sech z`, both in `ℚ⟦z⟧` and as
  identities of complex functions (`M(z) = (e^z - 1)/z`, `M(0) = 1`);
* (67) `𝒮 := e^D M(2D) M(4D)^{-1} = sech D`;
* (69) the Euler polynomials `E_n` defined by `2e^{xz}/(e^z+1) = ∑ E_n(x) z^n/n!`;
* (68) `𝒮(x^n) = 2^n E_n((x+1)/2)`; (70) `e^{xz} sech z = 2e^{(x+1)z}/(e^{2z}+1)`.
-/

open Finset
open scoped Nat

namespace EulerianBridge.Duplication

open EulerianBridge.Appell EulerianBridge.BernoulliAppell PowerSeries

/-- `M(az)`. -/
noncomputable def Mres (a : ℚ) : PowerSeries ℚ := rescale a (Mser ℚ)
/-- `e^{az}`. -/
noncomputable def expRes (a : ℚ) : PowerSeries ℚ := rescale a (exp ℚ)

theorem X_mul_Mres (a : ℚ) : PowerSeries.C a * PowerSeries.X * Mres a = expRes a - 1 := by
  have := congrArg (rescale a) (X_mul_Mser (K := ℚ))
  rw [map_mul, rescale_X, map_sub, map_one] at this
  simpa [Mres, expRes, mul_comm, mul_assoc] using this

theorem expRes_mul (a b : ℚ) : expRes a * expRes b = expRes (a + b) := by
  unfold expRes; rw [exp_mul_exp_eq_exp_add]

theorem exp_eq_expRes_one : exp ℚ = expRes 1 := by simp [expRes]

/-- Eq. (65), formal: `2 M(4z) = (e^{2z} + 1) M(2z)`. -/
theorem duplication : PowerSeries.C (2:ℚ) * Mres 4 = (expRes 2 + 1) * Mres 2 := by
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ))
  have h4 := X_mul_Mres 4
  have h2 := X_mul_Mres 2
  have e4 : expRes 4 = expRes 2 * expRes 2 := by rw [expRes_mul]; norm_num
  have : PowerSeries.C (4:ℚ) * (PowerSeries.X * Mres 4)
      = PowerSeries.C (2:ℚ) * (PowerSeries.X * Mres 2) * (expRes 2 + 1) := by
    rw [← mul_assoc, h4, ← mul_assoc, h2, e4]; ring
  have hC : (PowerSeries.C (4:ℚ)) = PowerSeries.C (2:ℚ) * PowerSeries.C (2:ℚ) := by
    rw [← map_mul]; norm_num
  rw [hC] at this
  have h2ne : (PowerSeries.C (2:ℚ)) ≠ 0 := by
    intro h; have := congrArg (coeff 0) h; simp at this
  apply mul_left_cancel₀ h2ne
  calc PowerSeries.C (2:ℚ) * (PowerSeries.X * (PowerSeries.C (2:ℚ) * Mres 4))
      = PowerSeries.C 2 * PowerSeries.C 2 * (PowerSeries.X * Mres 4) := by ring
    _ = PowerSeries.C (2:ℚ) * (PowerSeries.X * Mres 2) * (expRes 2 + 1) := this
    _ = PowerSeries.C (2:ℚ) * (PowerSeries.X * ((expRes 2 + 1) * Mres 2)) := by ring

/-- `cosh z = (e^z + e^{-z})/2`. -/
noncomputable def coshSer : PowerSeries ℚ := PowerSeries.C (1/2 : ℚ) * (exp ℚ + expRes (-1))

theorem constantCoeff_rescale' (a : ℚ) (f : PowerSeries ℚ) : constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, ← coeff_zero_eq_constantCoeff_apply]; simp

theorem constantCoeff_coshSer : constantCoeff coshSer = 1 := by
  simp [coshSer, expRes, constantCoeff_rescale']; norm_num

/-- `sech z`, the inverse of `cosh z`. -/
noncomputable def sechSer : PowerSeries ℚ := invOfUnit coshSer 1

theorem coshSer_mul_sechSer : coshSer * sechSer = 1 :=
  mul_invOfUnit _ _ (by rw [constantCoeff_coshSer]; simp)

theorem eq_sechSer {f : PowerSeries ℚ} (h : coshSer * f = 1) : f = sechSer := by
  calc f = (sechSer * coshSer) * f := by rw [mul_comm sechSer, coshSer_mul_sechSer, one_mul]
    _ = sechSer := by rw [mul_assoc, h, mul_one]

/-- `cosh(z) e^z = (e^{2z} + 1)/2`. -/
theorem coshSer_mul_exp : coshSer * exp ℚ = PowerSeries.C (1/2 : ℚ) * (expRes 2 + 1) := by
  unfold coshSer
  rw [exp_eq_expRes_one]
  have h1 : expRes 1 * expRes 1 = expRes 2 := by rw [expRes_mul]; norm_num
  have h0 : expRes (-1) * expRes 1 = 1 := by rw [expRes_mul]; simp [expRes]
  linear_combination (PowerSeries.C (1/2 : ℚ)) * h1 + (PowerSeries.C (1/2 : ℚ)) * h0

/-- Eq. (66), formal: `e^z M(2z) = sech(z) M(4z)`. -/
theorem sech_operator : exp ℚ * Mres 2 = sechSer * Mres 4 := by
  have key : coshSer * (exp ℚ * Mres 2) = Mres 4 := by
    have hd := duplication
    have hC : PowerSeries.C (1/2 : ℚ) * PowerSeries.C 2 = 1 := by rw [← map_mul]; norm_num
    calc coshSer * (exp ℚ * Mres 2) = PowerSeries.C (1/2 : ℚ) * ((expRes 2 + 1) * Mres 2) := by
          rw [← mul_assoc, coshSer_mul_exp]; ring
      _ = PowerSeries.C (1/2 : ℚ) * (PowerSeries.C 2 * Mres 4) := by rw [hd]
      _ = Mres 4 := by rw [← mul_assoc, hC, one_mul]
  calc exp ℚ * Mres 2 = (sechSer * coshSer) * (exp ℚ * Mres 2) := by
        rw [mul_comm sechSer, coshSer_mul_sechSer, one_mul]
    _ = sechSer * Mres 4 := by rw [mul_assoc, key]

theorem constantCoeff_Mres (a : ℚ) : constantCoeff (Mres a) = 1 := by
  rw [Mres, constantCoeff_rescale']; simp [Mser]

/-- `M(4z)^{-1}`. -/
noncomputable def Mres4Inv : PowerSeries ℚ := invOfUnit (Mres 4) 1

theorem Mres4_mul_inv : Mres 4 * Mres4Inv = 1 :=
  mul_invOfUnit _ _ (by rw [constantCoeff_Mres]; simp)

/-- The symbol of `𝒮 = e^D M(2D) M(4D)^{-1}`. -/
noncomputable def SSym : PowerSeries ℚ := exp ℚ * Mres 2 * Mres4Inv

/-- Eq. (67): `𝒮 = sech D`. -/
theorem S_eq_sech : op SSym = op sechSer := by
  unfold SSym; rw [sech_operator, mul_assoc, Mres4_mul_inv, mul_one]

/-! ## Euler polynomials -/

/-- `e^z + 1`, with constant coefficient `2`. -/
noncomputable def expAddOne : PowerSeries ℚ := exp ℚ + 1

theorem constantCoeff_expAddOne : constantCoeff expAddOne = ((Units.mk0 (2:ℚ) two_ne_zero : ℚˣ) : ℚ) := by
  simp [expAddOne]; norm_num

/-- `2/(e^z + 1)`. -/
noncomputable def eulerGF : PowerSeries ℚ :=
  PowerSeries.C (2:ℚ) * invOfUnit expAddOne (Units.mk0 (2:ℚ) two_ne_zero)

/-- Eq. (69): the Euler polynomials, `E_n(x) = n! [z^n] (2 e^{xz}/(e^z+1))`. -/
noncomputable def eulerPoly (n : ℕ) : Polynomial ℚ := (n ! : ℚ) • PowerSeries.coeff n (lift eulerGF * expXZ)

theorem eulerPoly_eq_op (n : ℕ) : eulerPoly n = op eulerGF (Polynomial.X ^ n) := by
  rw [op_X_pow]; rfl

/-- The explicit expansion `op f (x^n) = ∑ f_k n^{\underline k} x^{n-k}`. -/
theorem op_X_pow_sum (f : PowerSeries ℚ) (n : ℕ) :
    op f (Polynomial.X ^ n) = ∑ k ∈ range (n + 1),
      Polynomial.C (PowerSeries.coeff k f * n.descFactorial k) * Polynomial.X ^ (n - k) := by
  rw [op_apply, Polynomial.natDegree_X_pow]
  refine sum_congr rfl (fun k _ => ?_)
  rw [pow_D_apply, Polynomial.iterate_derivative_X_pow_eq_smul, smul_smul, Polynomial.smul_eq_C_mul]

/-- The shift: `e^D p = p(x+1)`. -/
theorem op_exp (p : Polynomial ℚ) : op (exp ℚ) p = p.comp (Polynomial.X + 1) := by
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    eval_add_one p x (Nat.lt_succ_self _), op_apply, Polynomial.eval_finset_sum]
  refine sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_smul, smul_eq_mul, coeff_exp]
  simp

theorem op_X_add_one_pow (f : PowerSeries ℚ) (n : ℕ) :
    op f ((Polynomial.X + 1) ^ n) = ∑ k ∈ range (n + 1),
      Polynomial.C (PowerSeries.coeff k f * n.descFactorial k) * (Polynomial.X + 1) ^ (n - k) := by
  have hdeg : ((Polynomial.X + 1 : Polynomial ℚ) ^ n).natDegree = n := by
    have h1 : (Polynomial.X + 1 : Polynomial ℚ).natDegree = 1 := by
      rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]
    rw [Polynomial.natDegree_pow, h1, mul_one]
  rw [op_apply, hdeg]
  refine sum_congr rfl (fun k _ => ?_)
  have := Polynomial.iterate_derivative_X_add_pow (R := ℚ) n k 1
  rw [map_one] at this
  rw [pow_D_apply, this, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Polynomial.smul_eq_C_mul]

/-- `2/(e^{2z}+1) · e^z · cosh z = 1`, i.e. `sech z = e^z · 2/(e^{2z}+1)`. -/
theorem sech_eq_euler : rescale (2:ℚ) eulerGF * exp ℚ = sechSer := by
  apply (eq_sechSer _).symm.symm
  have hinv : expAddOne * invOfUnit expAddOne (Units.mk0 (2:ℚ) two_ne_zero) = 1 :=
    mul_invOfUnit _ _ constantCoeff_expAddOne
  have hr := congrArg (rescale (2:ℚ)) hinv
  rw [map_mul, map_one] at hr
  have he : rescale (2:ℚ) expAddOne = expRes 2 + 1 := by simp [expAddOne, expRes]
  rw [he] at hr
  have hC2 : rescale (2:ℚ) (PowerSeries.C (2:ℚ)) = PowerSeries.C 2 := by
    ext m; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
  unfold eulerGF
  rw [map_mul, hC2]
  calc coshSer * (PowerSeries.C (2:ℚ) * rescale 2 (invOfUnit expAddOne (Units.mk0 2 two_ne_zero)) * exp ℚ)
      = PowerSeries.C (2:ℚ) * (coshSer * exp ℚ) * rescale 2 (invOfUnit expAddOne (Units.mk0 2 two_ne_zero)) := by
        ring
    _ = PowerSeries.C (2:ℚ) * PowerSeries.C (1/2 : ℚ) *
          ((expRes 2 + 1) * rescale 2 (invOfUnit expAddOne (Units.mk0 2 two_ne_zero))) := by
        rw [coshSer_mul_exp]; ring
    _ = 1 := by rw [hr, ← map_mul]; norm_num

/-- Eq. (68): `𝒮(x^n) = 2^n E_n((x+1)/2)`. -/
theorem S_X_pow (n : ℕ) :
    op SSym (Polynomial.X ^ n) =
      Polynomial.C ((2:ℚ) ^ n) * (eulerPoly n).comp (Polynomial.C (1/2 : ℚ) * (Polynomial.X + 1)) := by
  rw [S_eq_sech, ← sech_eq_euler, op_mul, LinearMap.comp_apply, op_exp, Polynomial.X_pow_comp,
    op_X_add_one_pow, eulerPoly_eq_op, op_X_pow_sum, Polynomial.sum_comp, mul_sum]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, mul_pow, coeff_rescale,
    ← Polynomial.C_pow]
  have h2 : (2:ℚ) ^ n * (1 / 2) ^ (n - k) = 2 ^ k := by
    rw [← Nat.sub_add_cancel hk', pow_add, Nat.add_sub_cancel, one_div, inv_pow]
    field_simp
  calc Polynomial.C (2 ^ k * PowerSeries.coeff k eulerGF * ↑(n.descFactorial k)) * (Polynomial.X + 1) ^ (n - k)
      = Polynomial.C ((2:ℚ) ^ n * (1 / 2) ^ (n - k) * (PowerSeries.coeff k eulerGF * ↑(n.descFactorial k))) *
          (Polynomial.X + 1) ^ (n - k) := by rw [h2]; ring_nf
    _ = _ := by simp only [map_mul]; ring

/-! ## The function identities over `ℂ` -/

/-- `M(z) = (e^z - 1)/z`, `M(0) = 1`. -/
noncomputable def Mc (z : ℂ) : ℂ := if z = 0 then 1 else (Complex.exp z - 1) / z

/-- Eq. (65) as an identity of entire functions: `M(4z) = ((e^{2z}+1)/2) M(2z)`. -/
theorem Mc_duplication (z : ℂ) : Mc (4 * z) = (Complex.exp (2 * z) + 1) / 2 * Mc (2 * z) := by
  unfold Mc
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [if_neg (by simpa using hz), if_neg (by simpa using hz)]
  have e4 : Complex.exp (4 * z) = Complex.exp (2 * z) ^ 2 := by
    rw [← Complex.exp_nat_mul]; ring_nf
  rw [e4]
  field_simp
  ring

/-- Eq. (66): `e^z M(2z)/M(4z) = sech z` wherever `M(2z) ≠ 0` and `cosh z ≠ 0`. -/
theorem Mc_sech (z : ℂ) (h2 : Mc (2 * z) ≠ 0) (hc : Complex.cosh z ≠ 0) :
    Complex.exp z * Mc (2 * z) / Mc (4 * z) = 1 / Complex.cosh z := by
  rw [Mc_duplication]
  have hcosh : Complex.exp (2 * z) + 1 = 2 * Complex.exp z * Complex.cosh z := by
    rw [Complex.cosh, show 2 * z = z + z by ring, Complex.exp_add, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero z]
  rw [hcosh]
  field_simp [Complex.exp_ne_zero z]

/-- Eq. (70): `e^{xz} sech z = 2 e^{(x+1)z}/(e^{2z}+1)`. -/
theorem euler_comparison (x z : ℂ) (hc : Complex.cosh z ≠ 0) :
    Complex.exp (x * z) / Complex.cosh z = 2 * Complex.exp ((x + 1) * z) / (Complex.exp (2 * z) + 1) := by
  have hcosh : Complex.exp (2 * z) + 1 = 2 * Complex.exp z * Complex.cosh z := by
    rw [Complex.cosh, show 2 * z = z + z by ring, Complex.exp_add, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero z]
  rw [hcosh, show (x + 1) * z = x * z + z by ring, Complex.exp_add]
  field_simp [Complex.exp_ne_zero z]

end EulerianBridge.Duplication
