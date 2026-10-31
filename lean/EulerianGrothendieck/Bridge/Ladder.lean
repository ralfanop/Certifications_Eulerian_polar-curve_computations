import Bridge.Fock3b
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Proposition 3.8: the Eulerian polyanalytic ladder (algebraic part)

Manuscript V173, eqs. (30)–(33).

Wirtinger derivatives are defined through the real Fréchet derivative,
`∂_z F = (D F·1 - i D F·i)/2`, `∂_z̄ F = (D F·1 + i D F·i)/2`, and
`a_α = α^{-1/2} ∂_z̄`, `a_α† = α^{-1/2}(-∂_z + α z̄)`.
With `phi_n(t,z) = (α z̄ - i t)^n e^{itz}` and
`E_n(z) = (n! αⁿ)^{-1/2} ∫_{-1/2}^{1/2} phi_n(t,z) dt` (eq. (30)) we prove:
* `E_0 = r_E`;
* (32) `a E_0 = 0`, `a E_n = √n E_{n-1}`, `a† E_n = √(n+1) E_{n+1}`, hence `(a†)ⁿ r_E = √(n!) E_n`;
* (31) `∂_z̄ⁿ E_n = √(n! αⁿ) r_E ≢ 0` and `∂_z̄^{n+1} E_n = 0`.
-/

open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped ComplexConjugate Nat

namespace EulerianBridge.Ladder

open EulerianGrothendieck.Fock

/-! ## Wirtinger derivatives -/

/-- `∂_z` of a real-linear map. -/
noncomputable def wz (L : ℂ →L[ℝ] ℂ) : ℂ := (1 / 2) * (L 1 - I * L I)
/-- `∂_z̄` of a real-linear map. -/
noncomputable def wzb (L : ℂ →L[ℝ] ℂ) : ℂ := (1 / 2) * (L 1 + I * L I)

noncomputable def dz (F : ℂ → ℂ) (z : ℂ) : ℂ := wz (fderiv ℝ F z)
noncomputable def dzb (F : ℂ → ℂ) (z : ℂ) : ℂ := wzb (fderiv ℝ F z)

theorem wz_add (L K : ℂ →L[ℝ] ℂ) : wz (L + K) = wz L + wz K := by
  simp [wz]; ring
theorem wzb_add (L K : ℂ →L[ℝ] ℂ) : wzb (L + K) = wzb L + wzb K := by
  simp [wzb]; ring
theorem wz_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) : wz (c • L) = c * wz L := by
  simp [wz]; ring
theorem wzb_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) : wzb (c • L) = c * wzb L := by
  simp [wzb]; ring

/-- Holomorphic derivative `c`: the real-linear map `v ↦ c v`. -/
noncomputable def hol (c : ℂ) : ℂ →L[ℝ] ℂ := c • (ContinuousLinearMap.id ℝ ℂ).restrictScalars ℝ

theorem wz_hol (c : ℂ) : wz (hol c) = c := by
  simp [wz, hol] <;> ring_nf <;> simp [I_sq] <;> ring
theorem wzb_hol (c : ℂ) : wzb (hol c) = 0 := by
  simp [wzb, hol] <;> ring_nf <;> simp [I_sq] <;> ring

theorem wz_conj : wz (Complex.conjCLE.toContinuousLinearMap) = 0 := by
  simp [wz] <;> ring_nf <;> simp [I_sq] <;> ring
theorem wzb_conj : wzb (Complex.conjCLE.toContinuousLinearMap) = 1 := by
  simp [wzb] <;> ring_nf <;> simp [I_sq] <;> ring

theorem hasFDerivAt_of_hasDerivAt {f : ℂ → ℂ} {c z : ℂ} (h : HasDerivAt f c z) :
    HasFDerivAt f (hol c) z := by
  have := h.hasFDerivAt.restrictScalars ℝ
  convert this using 1
  ext v; simp [hol, mul_comm]

/-! ## The integrands `phi_n` -/

/-- `phi_n(t,z) = (α z̄ - i t)^n e^{itz}`. -/
noncomputable def phi (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : ℂ := ((α:ℂ) * conj z - I * t) ^ n * cexp (I * t * z)

/-- The real derivative of `phi_n(t,·)`. -/
noncomputable def Dphi (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ((α:ℂ) * conj z - I * t) ^ n • hol (I * t * cexp (I * t * z)) +
    cexp (I * t * z) • ((n * ((α:ℂ) * conj z - I * t) ^ (n - 1) * α) •
      Complex.conjCLE.toContinuousLinearMap)

theorem hasFDerivAt_phi (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : HasFDerivAt (phi α n t) (Dphi α n t z) z := by
  have hP : HasFDerivAt (fun z : ℂ => (α:ℂ) * conj z - I * t)
      ((α:ℂ) • Complex.conjCLE.toContinuousLinearMap) z := by
    have := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).const_smul (α:ℂ)
    exact this.sub_const _
  have hPn := hP.pow n
  have he : HasFDerivAt (fun z : ℂ => cexp (I * t * z)) (hol (I * t * cexp (I * t * z))) z := by
    apply hasFDerivAt_of_hasDerivAt
    have := ((hasDerivAt_id z).const_mul (I * t)).cexp
    convert this using 1; simp; ring
  have h := hPn.mul he
  unfold phi Dphi
  convert h using 1
  ext v
  simp [smul_eq_mul]
  ring

theorem wzb_Dphi (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) :
    wzb (Dphi α n t z) = n * α * (if n = 0 then 0 else phi α (n - 1) t z) := by
  unfold Dphi
  rw [wzb_add, wzb_smul, wzb_hol, wzb_smul, wzb_smul, wzb_conj]
  split_ifs with h
  · subst h; simp
  · unfold phi; ring

theorem wz_Dphi (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : wz (Dphi α n t z) = I * t * phi α n t z := by
  unfold Dphi
  rw [wz_add, wz_smul, wz_hol, wz_smul, wz_smul, wz_conj]
  unfold phi; ring

theorem continuous_Dphi_apply (α : ℝ) (n : ℕ) (v : ℂ) :
    Continuous (fun p : ℂ × ℝ => Dphi α n p.2 p.1 v) := by
  unfold Dphi hol
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul]
  fun_prop

theorem Dphi_eq (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) :
    Dphi α n t z = (((α:ℂ) * conj z - I * t) ^ n * (I * t * cexp (I * t * z))) •
        ((ContinuousLinearMap.id ℝ ℂ).restrictScalars ℝ) +
      (cexp (I * t * z) * (n * ((α:ℂ) * conj z - I * t) ^ (n - 1) * α)) •
        Complex.conjCLE.toContinuousLinearMap := by
  unfold Dphi hol; rw [smul_smul, smul_smul]

theorem continuous_Dphi (α : ℝ) (n : ℕ) : Continuous (fun p : ℂ × ℝ => Dphi α n p.2 p.1) := by
  have h1 : Continuous (fun p : ℂ × ℝ => ((α:ℂ) * conj p.1 - I * p.2) ^ n * (I * p.2 * cexp (I * p.2 * p.1))) := by
    fun_prop
  have h2 : Continuous (fun p : ℂ × ℝ =>
      cexp (I * p.2 * p.1) * (n * ((α:ℂ) * conj p.1 - I * p.2) ^ (n - 1) * α)) := by fun_prop
  have h := (h1.smul (continuous_const (y := (ContinuousLinearMap.id ℝ ℂ).restrictScalars ℝ))).add
    (h2.smul (continuous_const (y := (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ))))
  exact h.congr (fun p => (Dphi_eq α n p.2 p.1).symm)

theorem continuous_phi_t (α : ℝ) (n : ℕ) (z : ℂ) : Continuous (fun t : ℝ => phi α n t z) := by
  unfold phi; fun_prop

/-! ## Differentiation under the integral sign -/

/-- `I_n(z) = ∫_{-1/2}^{1/2} φ_n(t,z) dt`. -/
noncomputable def Ij (α : ℝ) (n : ℕ) (z : ℂ) : ℂ := ∫ t in (-1/2:ℝ)..(1/2), phi α n t z

noncomputable def DIj (α : ℝ) (n : ℕ) (z : ℂ) : ℂ →L[ℝ] ℂ := ∫ t in (-1/2:ℝ)..(1/2), Dphi α n t z

theorem hasFDerivAt_Ij (α : ℝ) (n : ℕ) (z : ℂ) : HasFDerivAt (Ij α n) (DIj α n z) z := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod (isCompact_Icc (a := (-1/2:ℝ)) (b := 1/2))).exists_bound_of_continuousOn
    (continuous_Dphi α n).continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x t => phi α n t x) (F' := fun x t => Dphi α n t x) (bound := fun _ => C) zero_lt_one
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun x => (continuous_phi_t α n x).aestronglyMeasurable)
  · exact (continuous_phi_t α n z).intervalIntegrable _ _
  · exact ((continuous_Dphi α n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall (fun t ht x hx => hC (x, t) ⟨Metric.ball_subset_closedBall hx, ?_⟩)
    rw [uIoc_of_le (by norm_num)] at ht; exact ⟨ht.1.le, ht.2⟩
  · exact _root_.intervalIntegrable_const (by simp)
  · exact Eventually.of_forall (fun t _ x _ => hasFDerivAt_phi α n t x)

theorem intervalIntegrable_Dphi_apply (α : ℝ) (n : ℕ) (z v : ℂ) :
    IntervalIntegrable (fun t : ℝ => Dphi α n t z v) volume (-1/2) (1/2) :=
  (((continuous_Dphi_apply α n v).comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _

theorem DIj_apply (α : ℝ) (n : ℕ) (z v : ℂ) : DIj α n z v = ∫ t in (-1/2:ℝ)..(1/2), Dphi α n t z v := by
  unfold DIj
  rw [ContinuousLinearMap.intervalIntegral_apply]
  exact ((continuous_Dphi α n).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

theorem wzb_DIj (α : ℝ) (n : ℕ) (z : ℂ) :
    wzb (DIj α n z) = n * α * (if n = 0 then 0 else Ij α (n - 1) z) := by
  have h : wzb (DIj α n z) = ∫ t in (-1/2:ℝ)..(1/2), wzb (Dphi α n t z) := by
    unfold wzb
    rw [DIj_apply, DIj_apply, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (intervalIntegrable_Dphi_apply α n z 1)
        ((intervalIntegrable_Dphi_apply α n z I).const_mul I),
      ← intervalIntegral.integral_const_mul]
  rw [h]
  simp_rw [wzb_Dphi]
  rw [intervalIntegral.integral_const_mul]
  split_ifs with hn
  · simp
  · rfl

theorem wz_DIj (α : ℝ) (n : ℕ) (z : ℂ) :
    wz (DIj α n z) = ∫ t in (-1/2:ℝ)..(1/2), I * t * phi α n t z := by
  have h : wz (DIj α n z) = ∫ t in (-1/2:ℝ)..(1/2), wz (Dphi α n t z) := by
    unfold wz
    rw [DIj_apply, DIj_apply, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_Dphi_apply α n z 1)
        ((intervalIntegrable_Dphi_apply α n z I).const_mul I),
      ← intervalIntegral.integral_const_mul]
  rw [h]
  simp_rw [wz_Dphi]

/-! ## The ladder -/

/-- `c_n = (n! αⁿ)^{-1/2}`. -/
noncomputable def cn (α : ℝ) (n : ℕ) : ℝ := 1 / Real.sqrt (n ! * α ^ n)

/-- `E_n^α` (eq. (30)). -/
noncomputable def E (α : ℝ) (n : ℕ) (z : ℂ) : ℂ := (cn α n : ℂ) * Ij α n z

/-- `a_α F = α^{-1/2} ∂_z̄ F`. -/
noncomputable def a (α : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ := (1 / Real.sqrt α : ℝ) * dzb F z

/-- `a_α† F = α^{-1/2}(-∂_z F + α z̄ F)`. -/
noncomputable def adag (α : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / Real.sqrt α : ℝ) * (-dz F z + (α:ℂ) * conj z * F z)

theorem dzb_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z : ℂ} (h : HasFDerivAt F L z) : dzb F z = wzb L := by
  unfold dzb; rw [h.fderiv]

theorem dz_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z : ℂ} (h : HasFDerivAt F L z) : dz F z = wz L := by
  unfold dz; rw [h.fderiv]

theorem hasFDerivAt_const_mul_Ij (α : ℝ) (k : ℂ) (n : ℕ) (z : ℂ) :
    HasFDerivAt (fun z => k * Ij α n z) (k • DIj α n z) z := by
  have := (hasFDerivAt_Ij α n z).const_smul k
  simpa [smul_eq_mul] using this

theorem E_zero (α : ℝ) : E α 0 = rE := by
  funext z
  unfold E cn Ij phi rE
  simp

theorem cn_pos {α : ℝ} (hα : 0 < α) (n : ℕ) : 0 < cn α n := by
  unfold cn; have : 0 < (n ! : ℝ) * α ^ n := by positivity
  positivity

theorem cn_succ {α : ℝ} (hα : 0 < α) (n : ℕ) :
    cn α n = cn α (n + 1) * Real.sqrt ((n + 1) * α) := by
  unfold cn
  have h1 : (0:ℝ) < n ! * α ^ n := by positivity
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  rw [show ((n:ℝ) + 1) * n ! * (α ^ n * α) = (n ! * α ^ n) * ((n + 1) * α) by ring,
    Real.sqrt_mul h1.le]
  have h2 : 0 < Real.sqrt ((n + 1) * α) := Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < Real.sqrt (n ! * α ^ n) := Real.sqrt_pos.mpr h1
  field_simp

/-- (32), first two relations: `a E_0 = 0` and `a E_{n+1} = √(n+1) E_n`. -/
theorem a_E (α : ℝ) (hα : 0 < α) (n : ℕ) :
    a α (E α 0) = 0 ∧ a α (E α (n + 1)) = fun z => (Real.sqrt (n + 1) : ℂ) * E α n z := by
  constructor
  · funext z
    unfold a
    rw [show E α 0 = fun z => (cn α 0 : ℂ) * Ij α 0 z from rfl,
      dzb_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ 0 z), wzb_smul, wzb_DIj]
    simp
  · funext z
    unfold a
    rw [show E α (n + 1) = fun z => (cn α (n + 1) : ℂ) * Ij α (n + 1) z from rfl,
      dzb_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ (n + 1) z), wzb_smul, wzb_DIj, if_neg (Nat.succ_ne_zero n),
      Nat.add_sub_cancel]
    unfold E
    rw [cn_succ hα n]
    have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
    have hsq : Real.sqrt ((n + 1) * α) = Real.sqrt (n + 1) * Real.sqrt α := Real.sqrt_mul (by positivity) α
    have hαs : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
    rw [hsq]
    push_cast
    have hs' : (Real.sqrt α : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hαs' : (Real.sqrt α : ℂ) * Real.sqrt α = α := by exact_mod_cast hαs
    have hn1 : (Real.sqrt (n + 1) : ℂ) * Real.sqrt (n + 1) = n + 1 := by
      exact_mod_cast Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ n + 1)
    field_simp
    linear_combination (-(cn α (n + 1) : ℂ) * Ij α n z * ((Real.sqrt α : ℂ) * (Real.sqrt α : ℂ))) * hn1
      + (-(cn α (n + 1) : ℂ) * Ij α n z * ((n:ℂ) + 1)) * hαs'

/-- (32), third relation: `a† E_n = √(n+1) E_{n+1}`. -/
theorem adag_E (α : ℝ) (hα : 0 < α) (n : ℕ) :
    adag α (E α n) = fun z => (Real.sqrt (n + 1) : ℂ) * E α (n + 1) z := by
  funext z
  unfold adag
  rw [show E α n = fun z => (cn α n : ℂ) * Ij α n z from rfl,
    dz_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ n z), wz_smul, wz_DIj]
  have hsum : -((cn α n : ℂ) * ∫ t in (-1/2:ℝ)..(1/2), I * t * phi α n t z) + (α:ℂ) * conj z * ((cn α n : ℂ) * Ij α n z)
      = (cn α n : ℂ) * Ij α (n + 1) z := by
    have h1 : IntervalIntegrable (fun t : ℝ => I * t * phi α n t z) volume (-1/2) (1/2) :=
      Continuous.intervalIntegrable (by unfold phi; fun_prop) _ _
    have h2 : IntervalIntegrable (fun t : ℝ => phi α n t z) volume (-1/2) (1/2) :=
      Continuous.intervalIntegrable (by unfold phi; fun_prop) _ _
    have : Ij α (n + 1) z = (α:ℂ) * conj z * Ij α n z - ∫ t in (-1/2:ℝ)..(1/2), I * t * phi α n t z := by
      unfold Ij
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (h2.const_mul _) h1]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      beta_reduce; unfold phi; ring
    rw [this]; ring
  rw [hsum]
  unfold E
  rw [cn_succ hα n]
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hsq : Real.sqrt ((n + 1) * α) = Real.sqrt (n + 1) * Real.sqrt α := Real.sqrt_mul (by positivity) α
  rw [hsq]
  push_cast
  have hs' : (Real.sqrt α : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

/-- The first equality of (30): `(a†)ⁿ r_E = √(n!) E_n`. -/
theorem adag_iter (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (adag α)^[n] rE = fun z => (Real.sqrt (n !) : ℂ) * E α n z := by
  induction n with
  | zero => funext z; simp [E_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext z
    have h : adag α (fun z => (Real.sqrt (n !) : ℂ) * E α n z) z =
        (Real.sqrt (n !) : ℂ) * adag α (E α n) z := by
      unfold adag E
      have hE : (fun z => (Real.sqrt (n !) : ℂ) * ((cn α n : ℂ) * Ij α n z)) =
          fun z => ((Real.sqrt (n !) : ℂ) * (cn α n : ℂ)) * Ij α n z := by funext z; ring
      rw [hE, dz_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ n z), dz_of_hasFDerivAt
        (hasFDerivAt_const_mul_Ij α _ n z), wz_smul, wz_smul]
      ring
    rw [h, adag_E α hα n]
    simp only
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.sqrt_mul (by positivity), mul_comm (Real.sqrt _) (Real.sqrt _)]
    push_cast; ring

/-- `∂_z̄^k (k' I_n) = k' n!/(n-k)! α^k I_{n-k}` for `k ≤ n`, and `0` beyond. -/
theorem dzb_iter (α : ℝ) (n : ℕ) (k' : ℂ) :
    ∀ k ≤ n, dzb^[k] (fun z => k' * Ij α n z) =
      fun z => k' * ((n.descFactorial k : ℂ) * (α:ℂ) ^ k) * Ij α (n - k) z := by
  intro k hk
  induction k with
  | zero => funext z; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    funext z
    rw [dzb_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ (n - k) z), wzb_smul, wzb_DIj,
      if_neg (by omega), show n - k - 1 = n - (k + 1) by omega, Nat.descFactorial_succ]
    push_cast
    rw [Nat.cast_sub (by omega)]
    ring

/-- (31): `∂_z̄ⁿ E_n = √(n! αⁿ) r_E` and `∂_z̄^{n+1} E_n = 0`; `r_E ≢ 0`. -/
theorem exact_order (α : ℝ) (hα : 0 < α) (n : ℕ) :
    dzb^[n] (E α n) = (fun z => (Real.sqrt (n ! * α ^ n) : ℂ) * rE z) ∧
      dzb^[n + 1] (E α n) = 0 ∧ rE 0 ≠ 0 := by
  have h1 : dzb^[n] (E α n) = fun z => (cn α n : ℂ) * ((n.descFactorial n : ℂ) * (α:ℂ) ^ n) * Ij α 0 z := by
    rw [show E α n = fun z => (cn α n : ℂ) * Ij α n z from rfl, dzb_iter α n _ n le_rfl, Nat.sub_self]
  refine ⟨?_, ?_, by rw [rE_zero]; exact one_ne_zero⟩
  · rw [h1]
    funext z
    have hI0 : Ij α 0 z = rE z := by
      have := congrFun (E_zero α) z
      unfold E cn at this; simpa using this
    rw [hI0, Nat.descFactorial_self]
    unfold cn
    have hp : (0:ℝ) < n ! * α ^ n := by positivity
    have hs : 0 < Real.sqrt (n ! * α ^ n) := Real.sqrt_pos.mpr hp
    have hss : Real.sqrt (n ! * α ^ n) * Real.sqrt (n ! * α ^ n) = n ! * α ^ n := Real.mul_self_sqrt hp.le
    push_cast
    have hs' : (Real.sqrt (n ! * α ^ n) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hss' : (Real.sqrt (n ! * α ^ n) : ℂ) * Real.sqrt (n ! * α ^ n) = n ! * α ^ n := by exact_mod_cast hss
    field_simp
    linear_combination (rE z) * hss'.symm
  · rw [Function.iterate_succ_apply', h1]
    funext z
    rw [dzb_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ 0 z), wzb_smul, wzb_DIj]
    simp

end EulerianBridge.Ladder
