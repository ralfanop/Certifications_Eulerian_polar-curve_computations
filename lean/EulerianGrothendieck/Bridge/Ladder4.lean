import Bridge.Ladder3
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Proposition 3.8 (continued): Gaussian integration by parts and `J_{nm}`

`J_{nm}(t,s) = ∫ \overline{φ_n(t,z)} φ_m(s,z) dμ_α(z) = δ_{nm} n! αⁿ e^{st/α}`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate Nat

namespace EulerianBridge.Ladder

open EulerianGrothendieck.Fock

variable {α : ℝ}

/-- The complex Gaussian density. -/
noncomputable def ρc (α : ℝ) (z : ℂ) : ℂ := ((α / Real.pi : ℝ) : ℂ) * cexp (-(α:ℂ) * (z * conj z))

theorem ρc_eq (α : ℝ) (z : ℂ) : ρc α z = (fockDensity α z : ℂ) := by
  unfold ρc fockDensity
  rw [Complex.mul_conj, ← Complex.normSq_eq_norm_sq, Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast; ring_nf

noncomputable def idR : ℂ →L[ℝ] ℂ := ContinuousLinearMap.id ℝ ℂ
noncomputable def conjL : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap

theorem wzb_idR : wzb idR = 0 := by
  simp [wzb, idR] <;> ring_nf <;> simp [I_sq] <;> ring

theorem wzb_conjL_comp (L : ℂ →L[ℝ] ℂ) : wzb (conjL.comp L) = conj (wz L) := by
  simp only [wzb, wz, conjL, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_mul, map_sub, map_add, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

noncomputable def Dρ (α : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (((α / Real.pi : ℝ) : ℂ) * (cexp (-(α:ℂ) * (z * conj z)) * (-(α:ℂ)))) • (z • conjL + conj z • idR)

theorem hasFDerivAt_ρc (α : ℝ) (z : ℂ) : HasFDerivAt (ρc α) (Dρ α z) z := by
  have hq : HasFDerivAt (fun z : ℂ => z * conj z) (z • conjL + conj z • idR) z := by
    have := (hasFDerivAt_id (𝕜 := ℝ) z).mul (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z))
    convert this using 1
  have h := ((hq.const_mul (-(α:ℂ))).cexp).const_mul (((α / Real.pi : ℝ) : ℂ))
  unfold ρc Dρ
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wzb_Dρ (α : ℝ) (z : ℂ) : wzb (Dρ α z) = -(α:ℂ) * z * ρc α z := by
  unfold Dρ
  rw [wzb_smul, wzb_add, wzb_smul, wzb_smul, wzb_idR]
  have : wzb conjL = 1 := wzb_conj
  rw [this]; unfold ρc; ring

theorem Dρ_apply (α : ℝ) (z v : ℂ) : Dρ α z v = -(α:ℂ) * ρc α z * (z * conj v + conj z * v) := by
  unfold Dρ ρc conjL idR
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul]
  ring

/-! ## `U = \overline{φ_n} ρ` -/

noncomputable def U (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : ℂ := conj (phi α n t z) * ρc α z

noncomputable def DU (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  conj (phi α n t z) • Dρ α z + ρc α z • conjL.comp (Dphi α n t z)

theorem hasFDerivAt_U (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : HasFDerivAt (U α n t) (DU α n t z) z := by
  have hc : HasFDerivAt (fun z => conj (phi α n t z)) (conjL.comp (Dphi α n t z)) z :=
    (conjL.hasFDerivAt).comp z (hasFDerivAt_phi α n t z)
  have h := hc.mul (hasFDerivAt_ρc α z)
  unfold U DU
  convert h using 1

theorem wzb_DU (α : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) :
    wzb (DU α n t z) = -(conj (phi α (n + 1) t z) * ρc α z) := by
  unfold DU
  rw [wzb_add, wzb_smul, wzb_smul, wzb_Dρ, wzb_conjL_comp, wz_Dphi]
  unfold phi
  simp only [map_mul, map_pow, map_sub, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  ring

theorem DU_apply (α : ℝ) (n : ℕ) (t : ℝ) (z v : ℂ) :
    DU α n t z v = (conj (phi α n t z) * (-(α:ℂ) * (z * conj v + conj z * v)) + conj (Dphi α n t z v)) *
      ρc α z := by
  unfold DU
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, Dρ_apply, conjL, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  ring

/-! ## Integration by parts -/

theorem integrable_mul_ρ {α : ℝ} (hα : 0 < α) {f : ℂ → ℂ} (hf : ExpBdd f) :
    Integrable (fun z => f z * ρc α z) := by
  simp_rw [ρc_eq]; exact hf.integrable hα

/-- `∫ U ∂_z̄V dμ = -∫ ∂_z̄U V dμ` for `U = \overline{φ_n(t)} ρ`, `V = φ_m(s)`. -/
theorem ibp (hα : 0 < α) (n m : ℕ) (t s : ℝ) :
    ∫ z, U α n t z * wzb (Dphi α m s z) = -∫ z, wzb (DU α n t z) * phi α m s z := by
  have hint : ∀ v : ℂ, (Integrable (fun z => U α n t z * Dphi α m s z v)) ∧
      Integrable (fun z => DU α n t z v * phi α m s z) := by
    intro v
    constructor
    · have := integrable_mul_ρ hα ((expBdd_phi α n t).conj.mul (expBdd_Dphi α m s v))
      refine this.congr (Eventually.of_forall (fun z => ?_)); simp only [U]; ring
    · have h1 : ExpBdd (fun z => (conj (phi α n t z) * (-(α:ℂ) * (z * conj v + conj z * v)) +
          conj (Dphi α n t z v)) * phi α m s z) :=
        (((expBdd_phi α n t).conj.mul ((ExpBdd.const (-(α:ℂ))).mul ((ExpBdd.id.mul (ExpBdd.const v).conj).add
          (ExpBdd.id.conj.mul (ExpBdd.const v))))).add (expBdd_Dphi α n t v).conj).mul (expBdd_phi α m s)
      have := integrable_mul_ρ hα h1
      refine this.congr (Eventually.of_forall (fun z => ?_)); simp only [DU_apply]; ring
  have hUV : Integrable (fun z => U α n t z * phi α m s z) := by
    have := integrable_mul_ρ hα ((expBdd_phi α n t).conj.mul (expBdd_phi α m s))
    refine this.congr (Eventually.of_forall (fun z => ?_)); simp only [U]; ring
  have key : ∀ v : ℂ, ∫ z, U α n t z * Dphi α m s z v = -∫ z, DU α n t z v * phi α m s z := by
    intro v
    have := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
      (B := ContinuousLinearMap.mul ℝ ℂ) (v := v) (f := U α n t) (f' := DU α n t)
      (g := phi α m s) (g' := Dphi α m s)
      (by simpa using (hint v).2) (by simpa using (hint v).1) (by simpa using hUV)
      (hasFDerivAt_U α n t) (hasFDerivAt_phi α m s)
    simpa using this
  have e1 : ∀ z, U α n t z * wzb (Dphi α m s z) =
      (1/2 : ℂ) * (U α n t z * Dphi α m s z 1) + (1/2 * I) * (U α n t z * Dphi α m s z I) := by
    intro z; simp only [wzb]; ring
  have e2 : ∀ z, wzb (DU α n t z) * phi α m s z =
      (1/2 : ℂ) * (DU α n t z 1 * phi α m s z) + (1/2 * I) * (DU α n t z I * phi α m s z) := by
    intro z; simp only [wzb]; ring
  simp_rw [e1, e2]
  rw [integral_add ((hint 1).1.const_mul _) ((hint I).1.const_mul _),
    integral_add ((hint 1).2.const_mul _) ((hint I).2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, key 1, key I]
  ring

/-! ## The recursion for `J_{nm}` -/

/-- `J_{nm}(t,s) = ∫ \overline{φ_n(t,z)} φ_m(s,z) dμ_α`. -/
noncomputable def J (α : ℝ) (n m : ℕ) (t s : ℝ) : ℂ :=
  ∫ z, conj (phi α n t z) * phi α m s z * (fockDensity α z : ℂ)

theorem J_eq (α : ℝ) (n m : ℕ) (t s : ℝ) : J α n m t s = ∫ z, U α n t z * phi α m s z := by
  unfold J U
  congr 1; funext z; rw [← ρc_eq]; ring

theorem J_rec (hα : 0 < α) (n m : ℕ) (t s : ℝ) :
    J α (n + 1) m t s = m * α * (if m = 0 then 0 else J α n (m - 1) t s) := by
  have h := ibp hα n m t s
  simp_rw [wzb_Dphi, wzb_DU] at h
  rw [J_eq]
  have e : ∀ z, U α (n + 1) t z * phi α m s z = -(-(conj (phi α (n + 1) t z) * ρc α z) * phi α m s z) := by
    intro z; unfold U; ring
  simp_rw [e]
  rw [integral_neg, ← h]
  split_ifs with hm
  · subst hm; simp
  · rw [J_eq, ← integral_const_mul]
    congr 1; funext z; ring

theorem J_zero_zero (hα : 0 < α) (t s : ℝ) : J α 0 0 t s = cexp ((s:ℂ) * t / α) := by
  rw [← gaussian_pairing hα s t]
  unfold J phi
  congr 1; funext z
  rw [pow_zero, pow_zero, one_mul, one_mul, ← Complex.exp_conj, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem J_conj (α : ℝ) (n m : ℕ) (t s : ℝ) : conj (J α n m t s) = J α m n s t := by
  unfold J
  rw [← integral_conj]
  congr 1; funext z
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- `J_{nm}(t,s) = δ_{nm} n! αⁿ e^{st/α}`. -/
theorem J_closed (hα : 0 < α) : ∀ (n m : ℕ) (t s : ℝ),
    J α n m t s = if n = m then (n ! : ℂ) * (α:ℂ) ^ n * cexp ((s:ℂ) * t / α) else 0 := by
  intro n
  induction n with
  | zero =>
    intro m t s
    rcases m with _ | m
    · simp [J_zero_zero hα]
    · have h := J_conj α (m + 1) 0 s t
      rw [J_rec hα m 0 s t] at h
      simp only [if_pos rfl, mul_zero, map_zero, CharP.cast_eq_zero, zero_mul] at h
      rw [← h]; simp
  | succ n ih =>
    intro m t s
    rw [J_rec hα n m t s]
    rcases m with _ | m
    · simp
    · rw [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, ih m t s]
      by_cases h : n = m
      · subst h; simp [Nat.factorial_succ]; push_cast; ring
      · rw [if_neg h, if_neg (by omega)]; simp

end EulerianBridge.Ladder
