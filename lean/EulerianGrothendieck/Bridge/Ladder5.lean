import Bridge.Ladder4

/-!
# Proposition 3.8 (conclusion): `E_n ∈ L²(μ_α)` and `⟨E_n, E_m⟩ = 4α δ_{nm} Shi(1/(4α))`
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate Nat

namespace EulerianBridge.Ladder

open EulerianGrothendieck.Fock

variable {α : ℝ}

/-- `μ_I`: Lebesgue measure on `(-1/2,1/2]`. -/
noncomputable abbrev μI : Measure ℝ := volume.restrict (Ioc (-1/2:ℝ) (1/2))

theorem Ij_eq_set (α : ℝ) (n : ℕ) (z : ℂ) : Ij α n z = ∫ t, phi α n t z ∂μI := by
  unfold Ij; rw [intervalIntegral.integral_of_le (by norm_num)]

theorem norm_phi_le_half (hα : 0 < α) (n : ℕ) {t : ℝ} (ht : t ∈ Ioc (-1/2:ℝ) (1/2)) (z : ℂ) :
    ‖phi α n t z‖ ≤ (n ! * Real.exp (1/2)) * Real.exp ((α + 1/2) * ‖z‖) := by
  have h := norm_phi_le α hα n t z
  have ht' : |t| ≤ 1/2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  refine h.trans ?_
  gcongr

theorem continuous_E (α : ℝ) (n : ℕ) : Continuous (E α n) := by
  have : Differentiable ℝ (E α n) := fun z => (hasFDerivAt_const_mul_Ij α _ n z).differentiableAt
  exact this.continuous

theorem norm_E_le (hα : 0 < α) (n : ℕ) (z : ℂ) :
    ‖E α n z‖ ≤ cn α n * ((n ! * Real.exp (1/2)) * Real.exp ((α + 1/2) * ‖z‖)) := by
  unfold E
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cn_pos hα n), Ij]
  apply mul_le_mul_of_nonneg_left _ (cn_pos hα n).le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1/2:ℝ)) (b := 1/2)
    (C := (n ! * Real.exp (1/2)) * Real.exp ((α + 1/2) * ‖z‖)) (f := fun t => phi α n t z)
    (fun t ht => by rw [uIoc_of_le (by norm_num)] at ht; exact norm_phi_le_half hα n ht z)
  refine h.trans (le_of_eq ?_)
  norm_num

/-- `E_n ∈ L²(μ_α)` (Proposition 3.8). -/
theorem memLp_E (hα : 0 < α) (n : ℕ) : MemLp (E α n) 2 (fockMeasure α) := by
  have hc := continuous_E α n
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  rw [fockMeasure, integrable_withDensity_iff_integrable_smul (measurable_fockDensity_nnreal α)]
  set K := cn α n * ((n ! * Real.exp (1/2)))
  refine ((integrable_exp_norm hα (2 * (α + 1/2))).const_mul (K ^ 2)).mono' ?_
    (Eventually.of_forall (fun z => ?_))
  · exact ((continuous_real_toNNReal.comp (continuous_fockDensity α)).smul
      (hc.norm.pow 2)).aestronglyMeasurable
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (fockDensity_nonneg hα.le z), smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fockDensity_nonneg hα.le z) (sq_nonneg _)), mul_comm]
    have hb := norm_E_le hα n z
    have hK : cn α n * ((n ! * Real.exp (1/2)) * Real.exp ((α + 1/2) * ‖z‖)) = K * Real.exp ((α + 1/2) * ‖z‖) := by
      simp only [K]; ring
    rw [hK] at hb
    have hsq : ‖E α n z‖ ^ 2 ≤ K ^ 2 * Real.exp (2 * (α + 1/2) * ‖z‖) := by
      calc ‖E α n z‖ ^ 2 ≤ (K * Real.exp ((α + 1/2) * ‖z‖)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = K ^ 2 * Real.exp (2 * (α + 1/2) * ‖z‖) := by
            rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    calc ‖E α n z‖ ^ 2 * fockDensity α z ≤ K ^ 2 * Real.exp (2 * (α + 1/2) * ‖z‖) * fockDensity α z :=
          mul_le_mul_of_nonneg_right hsq (fockDensity_nonneg hα.le z)
      _ = K ^ 2 * (Real.exp (2 * (α + 1/2) * ‖z‖) * fockDensity α z) := by ring

/-! ## Fubini -/

theorem integrable_triple (hα : 0 < α) (n m : ℕ) :
    Integrable (fun q : ℂ × (ℝ × ℝ) => conj (phi α n q.2.1 q.1) * phi α m q.2.2 q.1 * (fockDensity α q.1 : ℂ))
      ((volume : Measure ℂ).prod (μI.prod μI)) := by
  set K := (n ! * Real.exp (1/2)) * (m ! * Real.exp (1/2))
  have hdom : Integrable (fun q : ℂ × (ℝ × ℝ) =>
      (K * (Real.exp (2 * (α + 1/2) * ‖q.1‖) * fockDensity α q.1)) * (1 : ℝ)) ((volume : Measure ℂ).prod (μI.prod μI)) := by
    have h1 := (integrable_exp_norm hα (2 * (α + 1/2))).const_mul K
    have h2 : Integrable (fun _ : ℝ × ℝ => (1:ℝ)) (μI.prod μI) := integrable_const _
    exact h1.mul_prod h2
  refine hdom.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (fun q : ℂ × (ℝ × ℝ) => phi α n q.2.1 q.1) := by unfold phi; fun_prop
    have h2 : Continuous (fun q : ℂ × (ℝ × ℝ) => phi α m q.2.2 q.1) := by unfold phi; fun_prop
    exact ((Complex.continuous_conj.comp h1).mul h2).mul
      (Complex.continuous_ofReal.comp ((continuous_fockDensity α).comp continuous_fst))
  · have hae : ∀ᵐ q ∂((volume : Measure ℂ).prod (μI.prod μI)), q.2.1 ∈ Ioc (-1/2:ℝ) (1/2) ∧ q.2.2 ∈ Ioc (-1/2:ℝ) (1/2) := by
      have hp : ∀ᵐ p ∂(μI.prod μI), p.1 ∈ Ioc (-1/2:ℝ) (1/2) ∧ p.2 ∈ Ioc (-1/2:ℝ) (1/2) := by
        have a1 : ∀ᵐ t ∂μI, t ∈ Ioc (-1/2:ℝ) (1/2) := ae_restrict_mem measurableSet_Ioc
        exact (Measure.quasiMeasurePreserving_fst.ae a1).and (Measure.quasiMeasurePreserving_snd.ae a1)
      exact Measure.quasiMeasurePreserving_snd.ae hp
    filter_upwards [hae] with q hq
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fockDensity_nonneg hα.le _), mul_one]
    have b1 := norm_phi_le_half hα n hq.1 q.1
    have b2 := norm_phi_le_half hα m hq.2 q.1
    have he : Real.exp (2 * (α + 1/2) * ‖q.1‖) = Real.exp ((α + 1/2) * ‖q.1‖) * Real.exp ((α + 1/2) * ‖q.1‖) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]
    have hf := fockDensity_nonneg hα.le q.1
    calc ‖phi α n q.2.1 q.1‖ * ‖phi α m q.2.2 q.1‖ * fockDensity α q.1
        ≤ ((n ! * Real.exp (1/2)) * Real.exp ((α + 1/2) * ‖q.1‖)) *
            ((m ! * Real.exp (1/2)) * Real.exp ((α + 1/2) * ‖q.1‖)) * fockDensity α q.1 := by
          gcongr
      _ = K * (Real.exp ((α + 1/2) * ‖q.1‖) * Real.exp ((α + 1/2) * ‖q.1‖) * fockDensity α q.1) := by
          simp only [K]; ring

/-- `⟨E_n, E_m⟩ = c_n c_m ∫∫ J_{nm}`. -/
theorem inner_E_eq (hα : 0 < α) (n m : ℕ) :
    ∫ z, conj (E α n z) * E α m z * (fockDensity α z : ℂ) =
      (cn α n : ℂ) * cn α m * ∫ p, J α n m p.1 p.2 ∂(μI.prod μI) := by
  have hpoint : ∀ z, conj (E α n z) * E α m z * (fockDensity α z : ℂ) =
      (cn α n : ℂ) * cn α m * ∫ p, conj (phi α n p.1 z) * phi α m p.2 z * (fockDensity α z : ℂ) ∂(μI.prod μI) := by
    intro z
    unfold E
    rw [Ij_eq_set, Ij_eq_set, map_mul, Complex.conj_ofReal, ← integral_conj]
    have hprod := integral_prod_mul (μ := μI) (ν := μI) (fun t => conj (phi α n t z)) (fun s => phi α m s z)
    rw [show (cn α n : ℂ) * (∫ t, conj (phi α n t z) ∂μI) * ((cn α m : ℂ) * ∫ s, phi α m s z ∂μI) *
        (fockDensity α z : ℂ) = (cn α n : ℂ) * cn α m * (((∫ t, conj (phi α n t z) ∂μI) *
          ∫ s, phi α m s z ∂μI) * (fockDensity α z : ℂ)) by ring, ← hprod, ← integral_mul_const]
  simp_rw [hpoint]
  rw [integral_const_mul]
  congr 1
  have hswap := integral_integral_swap (f := fun (z : ℂ) (p : ℝ × ℝ) =>
    conj (phi α n p.1 z) * phi α m p.2 z * (fockDensity α z : ℂ)) (μ := volume) (ν := μI.prod μI)
    (by simpa [Function.uncurry] using integrable_triple hα n m)
  rw [hswap]
  rfl

/-- Proposition 3.8, eq. (31): `⟨E_n, E_m⟩_{L²(μ_α)} = δ_{nm} ‖r_E‖² = 4α δ_{nm} Shi(1/(4α))`. -/
theorem inner_E (hα : 0 < α) (n m : ℕ) :
    ∫ z, conj (E α n z) * E α m z * (fockDensity α z : ℂ) =
      if n = m then ((4 * α * EulerianBridge.Fock3.Shi (1 / (4 * α)) : ℝ) : ℂ) else 0 := by
  rw [inner_E_eq hα]
  simp_rw [J_closed hα]
  split_ifs with h
  · subst h
    rw [integral_const_mul]
    -- `∫∫ e^{st/α} = ‖r_E‖² = 4α Shi(1/(4α))`
    have hreal : ∫ p, cexp ((p.2:ℂ) * p.1 / α) ∂(μI.prod μI) =
        ((∫ t in (-1/2:ℝ)..(1/2), ∫ s in (-1/2:ℝ)..(1/2), Real.exp (t * s / α) : ℝ) : ℂ) := by
      rw [← EulerianBridge.Fock3.integral_ν (fun t s => Real.exp (t * s / α)) (by fun_prop),
        ← integral_complex_ofReal]
      congr 1; funext p
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [hreal, ← EulerianBridge.Fock3.fock_norm_rE hα, (EulerianBridge.Fock3.fock_norm_Shi hα).1,
      (EulerianBridge.Fock3.fock_norm_Shi hα).2]
    unfold cn
    have hp : (0:ℝ) < n ! * α ^ n := by positivity
    have hs : 0 < Real.sqrt (n ! * α ^ n) := Real.sqrt_pos.mpr hp
    have hss : (Real.sqrt (n ! * α ^ n) : ℂ) * Real.sqrt (n ! * α ^ n) = n ! * α ^ n := by
      exact_mod_cast Real.mul_self_sqrt hp.le
    have hs' : (Real.sqrt (n ! * α ^ n) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
    linear_combination ((α:ℂ) * (EulerianBridge.Fock3.Shi (1 / (4 * α)) : ℂ)) * hss.symm
  · simp

/-- The normalised sequence `E_n/[4α Shi(1/(4α))]^{1/2}` is orthonormal in `L²(μ_α)`. -/
theorem orthonormal_E (hα : 0 < α) (n m : ℕ) :
    let N := Real.sqrt (4 * α * EulerianBridge.Fock3.Shi (1 / (4 * α)))
    ∫ z, conj (E α n z / N) * (E α m z / N) * (fockDensity α z : ℂ) = if n = m then 1 else 0 := by
  intro N
  have hpos : 0 < 4 * α * EulerianBridge.Fock3.Shi (1 / (4 * α)) := by
    rw [← (EulerianBridge.Fock3.fock_norm_Shi hα).2, ← (EulerianBridge.Fock3.fock_norm_Shi hα).1]
    rw [EulerianBridge.Fock3.fock_norm_rE hα]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _).intervalIntegrable _ _
    · intro t _
      exact intervalIntegral.intervalIntegral_pos_of_pos_on
        ((Continuous.intervalIntegrable (by fun_prop) _ _)) (fun s _ => Real.exp_pos _) (by norm_num)
    · norm_num
  have hN : (N : ℂ) * N = ((4 * α * EulerianBridge.Fock3.Shi (1 / (4 * α)) : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hpos.le
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have e : ∀ z, conj (E α n z / N) * (E α m z / N) * (fockDensity α z : ℂ) =
      (1 / ((N : ℂ) * N)) * (conj (E α n z) * E α m z * (fockDensity α z : ℂ)) := by
    intro z; rw [map_div₀, Complex.conj_ofReal]; field_simp
  simp_rw [e]
  rw [integral_const_mul, inner_E hα, hN]
  have hS : ((4 * α * EulerianBridge.Fock3.Shi (1 / (4 * α)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  split_ifs <;> field_simp <;> simp

end EulerianBridge.Ladder

namespace EulerianBridge.Ladder

theorem a_const_mul (α : ℝ) (k : ℂ) (n : ℕ) :
    a α (fun z => k * E α n z) = fun z => k * a α (E α n) z := by
  funext z
  unfold a E
  have hE : (fun z => k * ((cn α n : ℂ) * Ij α n z)) = fun z => (k * (cn α n : ℂ)) * Ij α n z := by
    funext z; ring
  rw [hE, dzb_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ n z),
    dzb_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ n z), wzb_smul, wzb_smul]
  ring

theorem adag_const_mul (α : ℝ) (k : ℂ) (n : ℕ) :
    adag α (fun z => k * E α n z) = fun z => k * adag α (E α n) z := by
  funext z
  unfold adag E
  have hE : (fun z => k * ((cn α n : ℂ) * Ij α n z)) = fun z => (k * (cn α n : ℂ)) * Ij α n z := by
    funext z; ring
  rw [hE, dz_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ n z),
    dz_of_hasFDerivAt (hasFDerivAt_const_mul_Ij α _ n z), wz_smul, wz_smul]
  ring

/-- The canonical commutation relation `[a, a†] = I` on the ladder (eq. (16)). -/
theorem commutator_E (α : ℝ) (hα : 0 < α) (n : ℕ) :
    a α (adag α (E α n)) = (fun z => (n + 1 : ℂ) * E α n z) ∧
      adag α (a α (E α (n + 1))) = (fun z => (n + 1 : ℂ) * E α (n + 1) z) := by
  have hs : (Real.sqrt (n + 1) : ℂ) * Real.sqrt (n + 1) = n + 1 := by
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ n + 1)
  constructor
  · rw [adag_E α hα n, a_const_mul, (a_E α hα n).2]
    funext z; push_cast; rw [← mul_assoc, hs]
  · rw [(a_E α hα n).2, adag_const_mul, adag_E α hα n]
    funext z; push_cast; rw [← mul_assoc, hs]

end EulerianBridge.Ladder
