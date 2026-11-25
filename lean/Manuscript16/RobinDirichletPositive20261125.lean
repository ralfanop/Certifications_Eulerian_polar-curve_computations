import Mathlib
import Manuscript16.RobinDirichletL2Bounded20261125

/-!
# M16 v16.5 §14.2, Proposition 14.2: the Dirichlet and Robin Green operators are positive

`Manuscript16.RobinDirichletL2Bounded20261125` (PR #605) realises the Dirichlet and Robin Green
kernels of Proposition 14.2 as bounded operators `KDop`, `KRop = KDop + P_a` on
`L² = L²((0,∞); ℂ)`, and leaves open their self-adjointness and positivity.  This file closes
that gap by an explicit Volterra factorisation of the Dirichlet kernel.

* Part A (Volterra kernel): `ψ(z,s) = 1_{s ≤ z} e^{−a(z−s)}` and, for `z, w ≥ 0`,
  `∫₀^∞ ψ(z,s) ψ(w,s) ds = G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)` (`integral_psi_mul_psi`).
* Part B (Volterra operators): `(V h)(z) = ∫₀^∞ ψ(z,s) h(s) ds` and
  `(W f)(s) = ∫₀^∞ ψ(w,s) f(w) dw` are bounded on `L²(0,∞)` (`Vop`, `Wop`).
* Part C: `⟪V h, f⟫ = ⟪h, W f⟫` (Fubini), hence `V = W†` (`Vop_eq_adjoint`).
* Part D: `K_D f = V (W f)` almost everywhere for every `f ∈ L²(0,∞)` (Fubini and Part A), hence
  **`K_D = W† W`** as operators on `L²(0,∞)` (`KDop_eq_adjoint_comp`).
* Part E (consequences): `K_D` is a positive, self-adjoint operator, `⟪f, K_D f⟫ = ‖W f‖²`,
  `‖K_D‖ = ‖W‖²` and `‖W‖ ≤ a⁻¹`; `K_R = K_D + P_a` is positive and self-adjoint for `β < a`;
  manuscript form `prop14_2_positive`.

Not claimed: the self-adjoint realisations `H_D`, `H_R` on `H²(0,∞)` and the identification
`KDop = (H_D − t)⁻¹`, `KRop = (H_R − t)⁻¹`; strict positivity or injectivity; Schatten-ideal
membership; the essential spectrum; any Maxwell or geometric identification.
-/

namespace Manuscript16.RobinDirichletPositive

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne Manuscript16.RobinDirichletL2Bounded

noncomputable section

variable {a β : ℝ}

/-! ### Part A: the Volterra kernel and the factorisation of `G_D` -/

/-- The Volterra kernel `ψ(z,s) = 1_{s ≤ z} e^{−a(z−s)}`. -/
def psi (a z s : ℝ) : ℝ := if s ≤ z then Real.exp (-a * (z - s)) else 0

theorem psi_nonneg (a z s : ℝ) : 0 ≤ psi a z s := by
  unfold psi
  split_ifs <;> positivity

theorem psi_le_exp (a z s : ℝ) : psi a z s ≤ Real.exp (-a * |z - s|) := by
  unfold psi
  split_ifs with h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
  · positivity

theorem abs_psi_le (a z s : ℝ) : |psi a z s| ≤ Real.exp (-a * |z - s|) := by
  rw [abs_of_nonneg (psi_nonneg a z s)]
  exact psi_le_exp a z s

theorem measurable_psi (a : ℝ) : Measurable (Function.uncurry (psi a)) := by
  change Measurable fun p : ℝ × ℝ => if p.2 ≤ p.1 then Real.exp (-a * (p.1 - p.2)) else 0
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (by fun_prop)
    measurable_const

theorem psi_mul_psi (a z w s : ℝ) : psi a z s * psi a w s =
    (Iic (min z w)).indicator (fun s => Real.exp (-a * (z + w) + 2 * a * s)) s := by
  unfold psi
  by_cases hz : s ≤ z <;> by_cases hw : s ≤ w
  · simp only [hz, hw, ↓reduceIte]
    rw [indicator_of_mem (mem_Iic.mpr (le_min hz hw)), ← Real.exp_add]
    ring_nf
  · simp only [hz, hw, ↓reduceIte, mul_zero]
    rw [indicator_of_notMem]
    exact fun h => hw ((mem_Iic.mp h).trans (min_le_right z w))
  · simp only [hz, hw, ↓reduceIte, zero_mul]
    rw [indicator_of_notMem]
    exact fun h => hz ((mem_Iic.mp h).trans (min_le_left z w))
  · simp only [hz, hw, ↓reduceIte, zero_mul]
    rw [indicator_of_notMem]
    exact fun h => hz ((mem_Iic.mp h).trans (min_le_left z w))

/-- **Volterra factorisation of the Dirichlet kernel.** For `z, w ≥ 0`,
`∫₀^∞ ψ(z,s) ψ(w,s) ds = ∫₀^{min(z,w)} e^{−a(z−s)} e^{−a(w−s)} ds = G_D(z,w)`. -/
theorem integral_psi_mul_psi (ha : 0 < a) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) :
    ∫ s in Ioi 0, psi a z s * psi a w s = greenD a z w := by
  have hm : 0 ≤ min z w := le_min hz hw
  simp_rw [psi_mul_psi]
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, ← intervalIntegral.integral_of_le hm]
  have hderiv : ∀ x ∈ uIcc 0 (min z w), HasDerivAt
      (fun s => Real.exp (-a * (z + w) + 2 * a * s) / (2 * a))
      (Real.exp (-a * (z + w) + 2 * a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun s => -a * (z + w) + 2 * a * s) (2 * a) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 * a)).const_add (-a * (z + w))
    have h2 := (h1.exp).div_const (2 * a)
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold greenD
  have habs : -a * (z + w) + 2 * a * min z w = -a * |z - w| := by
    rcases le_total z w with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [habs, mul_zero, add_zero, sub_div]

/-! ### Part B: the Volterra operators `V`, `W` on `L²(0,∞)` -/

/-- `L²(0,∞)` membership of a measurable function dominated by `C e^{−az}`. -/
theorem memLp_of_bound_meas (ha : 0 < a) {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (hb : ∀ w, 0 < w → |g w| ≤ C * Real.exp (-a * w)) :
    MemLp (fun w => (g w : ℂ)) 2 μ := by
  refine (((memLp_exp_real ha).const_mul C).of_le hg.aestronglyMeasurable ?_).ofReal
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hb w hw).trans (le_abs_self _)

theorem memLp_psi_row (ha : 0 < a) (z : ℝ) : MemLp (fun s => (psi a z s : ℂ)) 2 μ :=
  memLp_of_bound_meas ha (measurable_psi a).of_uncurry_left (Real.exp (a * |z|))
    (fun s hs => (abs_psi_le a z s).trans (exp_abs_sub_le ha.le z hs))

theorem memLp_psi_col (ha : 0 < a) (s : ℝ) : MemLp (fun w => (psi a w s : ℂ)) 2 μ :=
  memLp_of_bound_meas ha (measurable_psi a).of_uncurry_right (Real.exp (a * |s|))
    (fun w hw => by
      refine (abs_psi_le a w s).trans ?_
      rw [abs_sub_comm]
      exact exp_abs_sub_le ha.le s hw)

/-- The row section `ψ(z,·) ∈ L²(0,∞)`. -/
def rowVec (ha : 0 < a) (z : ℝ) : L2 := (memLp_psi_row ha z).toLp _

/-- The column section `ψ(·,s) ∈ L²(0,∞)`. -/
def colVec (ha : 0 < a) (s : ℝ) : L2 := (memLp_psi_col ha s).toLp _

/-- `(V h)(z) = ∫₀^∞ ψ(z,s) h(s) ds`. -/
def Vfun (ha : 0 < a) (h : L2) (z : ℝ) : ℂ := ⟪rowVec ha z, h⟫

/-- `(W f)(s) = ∫₀^∞ ψ(w,s) f(w) dw`. -/
def Wfun (ha : 0 < a) (f : L2) (s : ℝ) : ℂ := ⟪colVec ha s, f⟫

theorem Vfun_eq_integral (ha : 0 < a) (h : L2) (z : ℝ) :
    Vfun ha h z = ∫ s, (psi a z s : ℂ) * h s ∂μ := by
  rw [Vfun, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_psi_row ha z).coeFn_toLp] with s hs
  rw [rowVec, hs, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

theorem Wfun_eq_integral (ha : 0 < a) (f : L2) (s : ℝ) :
    Wfun ha f s = ∫ w, (psi a w s : ℂ) * f w ∂μ := by
  rw [Wfun, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_psi_col ha s).coeFn_toLp] with w hw
  rw [colVec, hw, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- The kernel `e^{−a|z−w|}` with values in `ℝ≥0∞`. -/
def expK (a z w : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a * |z - w|))

theorem measurable_expK (a : ℝ) : Measurable (Function.uncurry (expK a)) := by
  have hc : Continuous fun p : ℝ × ℝ => Real.exp (-a * |p.1 - p.2|) := by fun_prop
  exact hc.measurable.ennreal_ofReal

theorem expK_symm (a z w : ℝ) : expK a z w = expK a w z := by
  rw [expK, expK, abs_sub_comm]

/-- `∫_ℝ e^{−a|z−w|} dw = 2/a`. -/
theorem lintegral_expK_real (ha : 0 < a) (z : ℝ) :
    ∫⁻ w, expK a z w = ENNReal.ofReal (2 / a) := by
  have hshift : (∫⁻ w, expK a z w) = ∫⁻ x, ENNReal.ofReal (Real.exp (-a * |x|)) := by
    have h := lintegral_sub_right_eq_self
      (μ := (volume : Measure ℝ)) (fun x => ENNReal.ofReal (Real.exp (-a * |x|))) z
    rw [← h]
    apply lintegral_congr
    intro w
    rw [expK, abs_sub_comm]
  rw [hshift, ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_abs ha)
    (Eventually.of_forall fun x => by positivity), integral_exp_neg_abs ha]

theorem row_expK (ha : 0 < a) (z : ℝ) : ∫⁻ w, expK a z w ∂μ ≤ ENNReal.ofReal (2 / a) :=
  (setLIntegral_le_lintegral _ _).trans (lintegral_expK_real ha z).le

theorem col_expK (ha : 0 < a) (w : ℝ) : ∫⁻ z, expK a z w ∂μ ≤ ENNReal.ofReal (2 / a) := by
  simp_rw [expK_symm a _ w]
  exact row_expK ha w

theorem enorm_le_expK {k : ℝ → ℝ → ℝ} (hkb : ∀ z w, |k z w| ≤ Real.exp (-a * |z - w|))
    (z w : ℝ) : ‖(k z w : ℂ)‖ₑ ≤ expK a z w := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, expK]
  exact ENNReal.ofReal_le_ofReal (hkb z w)

/-- Schur bound for a kernel dominated by `e^{−a|z−w|}`. -/
theorem lintegral_kernel_sq_le (ha : 0 < a) {k : ℝ → ℝ → ℝ}
    (hkb : ∀ z w, |k z w| ≤ Real.exp (-a * |z - w|)) (f : L2) :
    ∫⁻ z, ‖∫ w, (k z w : ℂ) * f w ∂μ‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal (2 / a) ^ 2 * ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ := by
  refine le_trans ?_ (schur_lintegral (measurable_expK a)
    (Lp.aestronglyMeasurable f).enorm ENNReal.ofReal_ne_top (row_expK ha) (col_expK ha))
  apply lintegral_mono
  intro z
  apply pow_le_pow_left₀ zero_le
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  apply lintegral_mono
  intro w
  dsimp only
  rw [enorm_mul]
  gcongr
  exact enorm_le_expK hkb z w

theorem aestronglyMeasurable_kernel {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k))
    (f : L2) : AEStronglyMeasurable (fun z => ∫ w, (k z w : ℂ) * f w ∂μ) μ := by
  have hm : Measurable fun p : ℝ × ℝ => (k p.1 p.2 : ℂ) := Complex.measurable_ofReal.comp hk
  exact (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'

theorem eLpNorm_kernel_le (ha : 0 < a) {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k))
    (hkb : ∀ z w, |k z w| ≤ Real.exp (-a * |z - w|)) (f : L2) :
    eLpNorm (fun z => ∫ w, (k z w : ℂ) * f w ∂μ) 2 μ ≤ ENNReal.ofReal (2 / a) * eLpNorm f 2 μ := by
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (aestronglyMeasurable_kernel hk f),
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable f),
    eLpNorm', eLpNorm']
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ z, ‖∫ w, (k z w : ℂ) * f w ∂μ‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (2 / a) ^ 2 * ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_kernel_sq_le ha hkb f) (by norm_num)
    _ = ENNReal.ofReal (2 / a) * (∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.rpow_two (ENNReal.ofReal (2 / a)), ← ENNReal.rpow_mul]
        norm_num

theorem memLp_kernel (ha : 0 < a) {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k))
    (hkb : ∀ z w, |k z w| ≤ Real.exp (-a * |z - w|)) (f : L2) :
    MemLp (fun z => ∫ w, (k z w : ℂ) * f w ∂μ) 2 μ :=
  memLp_iff.mpr ((eLpNorm_kernel_le ha hk hkb f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)))

theorem norm_toLp_kernel_le (ha : 0 < a) {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k))
    (hkb : ∀ z w, |k z w| ≤ Real.exp (-a * |z - w|)) (f : L2) :
    ‖(memLp_kernel ha hk hkb f).toLp _‖ ≤ (2 / a) * ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) (eLpNorm_kernel_le ha hk hkb f)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h

theorem abs_psi_swap_le (a : ℝ) (s w : ℝ) : |psi a w s| ≤ Real.exp (-a * |s - w|) := by
  rw [abs_sub_comm]
  exact abs_psi_le a w s

theorem measurable_psi_swap (a : ℝ) : Measurable (Function.uncurry fun s w => psi a w s) :=
  (measurable_psi a).comp measurable_swap

theorem memLp_Vfun (ha : 0 < a) (h : L2) : MemLp (Vfun ha h) 2 μ := by
  have e : Vfun ha h = fun z => ∫ s, (psi a z s : ℂ) * h s ∂μ := funext (Vfun_eq_integral ha h)
  rw [e]
  exact memLp_kernel ha (measurable_psi a) (abs_psi_le a) h

theorem memLp_Wfun (ha : 0 < a) (f : L2) : MemLp (Wfun ha f) 2 μ := by
  have e : Wfun ha f = fun s => ∫ w, (psi a w s : ℂ) * f w ∂μ := funext (Wfun_eq_integral ha f)
  rw [e]
  exact memLp_kernel ha (measurable_psi_swap a) (abs_psi_swap_le a) f

theorem norm_toLp_Vfun_le (ha : 0 < a) (h : L2) :
    ‖(memLp_Vfun ha h).toLp (Vfun ha h)‖ ≤ (2 / a) * ‖h‖ := by
  have e : Vfun ha h = fun z => ∫ s, (psi a z s : ℂ) * h s ∂μ := funext (Vfun_eq_integral ha h)
  have h1 := norm_toLp_kernel_le ha (measurable_psi a) (abs_psi_le a) h
  rw [Lp.norm_toLp] at h1 ⊢
  rwa [e]

theorem norm_toLp_Wfun_le (ha : 0 < a) (f : L2) :
    ‖(memLp_Wfun ha f).toLp (Wfun ha f)‖ ≤ (2 / a) * ‖f‖ := by
  have e : Wfun ha f = fun s => ∫ w, (psi a w s : ℂ) * f w ∂μ := funext (Wfun_eq_integral ha f)
  have h1 := norm_toLp_kernel_le ha (measurable_psi_swap a) (abs_psi_swap_le a) f
  rw [Lp.norm_toLp] at h1 ⊢
  rwa [e]

theorem Vfun_add (ha : 0 < a) (f g : L2) : Vfun ha (f + g) = Vfun ha f + Vfun ha g := by
  funext z
  simp [Vfun, inner_add_right]

theorem Vfun_smul (ha : 0 < a) (c : ℂ) (f : L2) : Vfun ha (c • f) = c • Vfun ha f := by
  funext z
  simp [Vfun, inner_smul_right]

theorem Wfun_add (ha : 0 < a) (f g : L2) : Wfun ha (f + g) = Wfun ha f + Wfun ha g := by
  funext z
  simp [Wfun, inner_add_right]

theorem Wfun_smul (ha : 0 < a) (c : ℂ) (f : L2) : Wfun ha (c • f) = c • Wfun ha f := by
  funext z
  simp [Wfun, inner_smul_right]

/-- The Volterra operator `V` as a bounded operator on `L²(0,∞)`. -/
def Vop (ha : 0 < a) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun h => (memLp_Vfun ha h).toLp (Vfun ha h)
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by rw [Vfun_add])
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by rw [Vfun_smul]) }
    (2 / a) (norm_toLp_Vfun_le ha)

/-- The operator `W` as a bounded operator on `L²(0,∞)`. -/
def Wop (ha : 0 < a) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_Wfun ha f).toLp (Wfun ha f)
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by rw [Wfun_add])
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by rw [Wfun_smul]) }
    (2 / a) (norm_toLp_Wfun_le ha)

theorem Vop_ae_eq (ha : 0 < a) (h : L2) : (Vop ha h : ℝ → ℂ) =ᵐ[μ] Vfun ha h :=
  (memLp_Vfun ha h).coeFn_toLp

theorem Wop_ae_eq (ha : 0 < a) (f : L2) : (Wop ha f : ℝ → ℂ) =ᵐ[μ] Wfun ha f :=
  (memLp_Wfun ha f).coeFn_toLp

/-! ### Part C: `V = W†` -/

theorem mul_le_sq_add_sq (x y : ℝ≥0∞) : x * y ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · calc x * y ≤ y * y := by gcongr
      _ = y ^ 2 := (sq y).symm
      _ ≤ x ^ 2 + y ^ 2 := le_add_self
  · calc x * y ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ x ^ 2 + y ^ 2 := le_self_add

theorem lintegral_enorm_sq_lt_top {g : ℝ → ℂ} (hg : MemLp g 2 μ) :
    ∫⁻ s, ‖g s‖ₑ ^ 2 ∂μ < ⊤ := by
  have h := hg.eLpNorm_lt_top
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hg.aestronglyMeasurable, eLpNorm'] at h
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h

/-- Integrability on `(0,∞)²` of `k(z,s) g(s) f(z)` for a kernel dominated by `e^{−a|z−s|}` and
`f, g ∈ L²(0,∞)`. -/
theorem integrable_kernel_prod (ha : 0 < a) {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k))
    (hkb : ∀ z w, |k z w| ≤ Real.exp (-a * |z - w|)) {g f : ℝ → ℂ}
    (hg : MemLp g 2 μ) (hf : MemLp f 2 μ) :
    Integrable (fun p : ℝ × ℝ => (k p.1 p.2 : ℂ) * g p.2 * f p.1) (μ.prod μ) := by
  have hm : Measurable fun p : ℝ × ℝ => (k p.1 p.2 : ℂ) := Complex.measurable_ofReal.comp hk
  have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => (k p.1 p.2 : ℂ) * g p.2 * f p.1) (μ.prod μ) :=
    (hm.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd).mul hf.aestronglyMeasurable.comp_fst
  refine ⟨hF, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hB : AEMeasurable (fun p : ℝ × ℝ => expK a p.1 p.2 * ‖g p.2‖ₑ * ‖f p.1‖ₑ) (μ.prod μ) :=
    ((measurable_expK a).aemeasurable.mul hg.aestronglyMeasurable.enorm.comp_snd).mul hf.aestronglyMeasurable.enorm.comp_fst
  calc ∫⁻ p, ‖(k p.1 p.2 : ℂ) * g p.2 * f p.1‖ₑ ∂(μ.prod μ)
      ≤ ∫⁻ p, expK a p.1 p.2 * ‖g p.2‖ₑ * ‖f p.1‖ₑ ∂(μ.prod μ) := by
        apply lintegral_mono
        intro p
        dsimp only
        rw [enorm_mul, enorm_mul]
        gcongr
        exact enorm_le_expK hkb p.1 p.2
    _ = ∫⁻ z, (∫⁻ s, expK a z s * ‖g s‖ₑ ∂μ) * ‖f z‖ₑ ∂μ := by
        rw [lintegral_prod _ hB]
        apply lintegral_congr
        intro z
        dsimp only
        have hz' : AEMeasurable (fun s => expK a z s * ‖g s‖ₑ) μ :=
          (measurable_expK a).of_uncurry_left.aemeasurable.mul hg.aestronglyMeasurable.enorm
        exact lintegral_mul_const'' _ hz'
    _ ≤ ∫⁻ z, (∫⁻ s, expK a z s * ‖g s‖ₑ ∂μ) ^ 2 + ‖f z‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun z => mul_le_sq_add_sq _ _
    _ = ∫⁻ z, (∫⁻ s, expK a z s * ‖g s‖ₑ ∂μ) ^ 2 ∂μ + ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ :=
        lintegral_add_right' _ (hf.aestronglyMeasurable.enorm.pow_const 2)
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨?_, lintegral_enorm_sq_lt_top hf⟩
        refine (schur_lintegral (measurable_expK a) hg.aestronglyMeasurable.enorm ENNReal.ofReal_ne_top
          (row_expK ha) (col_expK ha)).trans_lt ?_
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          (lintegral_enorm_sq_lt_top hg)

/-- `⟪V h, f⟫ = ⟪h, W f⟫` for all `h, f ∈ L²(0,∞)` (Fubini). -/
theorem inner_Vop (ha : 0 < a) (h f : L2) : ⟪Vop ha h, f⟫ = ⟪h, Wop ha f⟫ := by
  have hconj : MemLp (fun s => (starRingEnd ℂ) (h s)) 2 μ := (Lp.memLp h).star
  have hint := integrable_kernel_prod ha (measurable_psi a) (abs_psi_le a) hconj (Lp.memLp f)
  rw [L2.inner_def, L2.inner_def]
  calc ∫ z, ⟪(Vop ha h : ℝ → ℂ) z, (f : ℝ → ℂ) z⟫ ∂μ
      = ∫ z, ∫ s, (psi a z s : ℂ) * (starRingEnd ℂ) (h s) * f z ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [Vop_ae_eq ha h] with z hz
        rw [hz, Vfun_eq_integral, RCLike.inner_apply, ← integral_conj, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with s
        simp only [map_mul, Complex.conj_ofReal]
        ring
    _ = ∫ s, ∫ z, (psi a z s : ℂ) * (starRingEnd ℂ) (h s) * f z ∂μ ∂μ :=
        integral_integral_swap hint
    _ = ∫ s, ⟪(h : ℝ → ℂ) s, (Wop ha f : ℝ → ℂ) s⟫ ∂μ := by
        apply integral_congr_ae
        filter_upwards [Wop_ae_eq ha f] with s hs
        rw [hs, Wfun_eq_integral, RCLike.inner_apply, ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with z
        ring

/-- `V = W†`. -/
theorem Vop_eq_adjoint (ha : 0 < a) : Vop ha = ContinuousLinearMap.adjoint (Wop ha) :=
  (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (inner_Vop ha)

/-! ### Part D: `K_D = V W = W† W` -/

/-- `V (W f) = K_D f` pointwise on `[0,∞)`. -/
theorem Vfun_Wop (ha : 0 < a) (f : L2) {z : ℝ} (hz : 0 ≤ z) :
    Vfun ha (Wop ha f) z = KD ha f z := by
  have hrow := memLp_psi_row ha z
  have hint := integrable_kernel_prod ha (measurable_psi_swap a) (abs_psi_swap_le a)
    (Lp.memLp f) hrow
  rw [Vfun_eq_integral, KD_eq_integral]
  calc ∫ s, (psi a z s : ℂ) * (Wop ha f : ℝ → ℂ) s ∂μ
      = ∫ s, ∫ w, (psi a w s : ℂ) * f w * (psi a z s : ℂ) ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [Wop_ae_eq ha f] with s hs
        rw [hs, Wfun_eq_integral, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with w
        ring
    _ = ∫ w, ∫ s, (psi a w s : ℂ) * f w * (psi a z s : ℂ) ∂μ ∂μ :=
        integral_integral_swap hint
    _ = ∫ w in Ioi 0, (greenD a z w : ℂ) * f w := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        have e : (fun s => (psi a w s : ℂ) * f w * (psi a z s : ℂ)) =
            fun s => (((psi a z s * psi a w s : ℝ)) : ℂ) * f w := by
          funext s
          push_cast
          ring
        rw [e, integral_mul_const, integral_complex_ofReal, integral_psi_mul_psi ha hz (le_of_lt hw)]

/-- `K_D f = V (W f)` almost everywhere on `(0,∞)`. -/
theorem KDop_eq_Vop_comp (ha : 0 < a) : KDop ha = Vop ha ∘L Wop ha := by
  ext1 f
  apply Lp.ext
  filter_upwards [KDop_ae_eq ha f, Vop_ae_eq ha (Wop ha f),
    ae_restrict_mem measurableSet_Ioi] with z h1 h2 hz
  rw [h1, ContinuousLinearMap.comp_apply, h2, Vfun_Wop ha f (le_of_lt hz)]

/-- **Factorisation `K_D = W† W`** on `L²(0,∞)`. -/
theorem KDop_eq_adjoint_comp (ha : 0 < a) :
    KDop ha = ContinuousLinearMap.adjoint (Wop ha) ∘L Wop ha := by
  rw [KDop_eq_Vop_comp, Vop_eq_adjoint]

/-! ### Part E: positivity and self-adjointness -/

/-- `K_D` is a positive operator on `L²(0,∞)`. -/
theorem KDop_isPositive (ha : 0 < a) : (KDop ha).IsPositive := by
  rw [KDop_eq_adjoint_comp]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- `K_D` is self-adjoint on `L²(0,∞)`. -/
theorem KDop_isSelfAdjoint (ha : 0 < a) : IsSelfAdjoint (KDop ha) :=
  (KDop_isPositive ha).isSelfAdjoint

/-- Energy identity `⟪f, K_D f⟫ = ‖W f‖²`. -/
theorem inner_KDop_self (ha : 0 < a) (f : L2) :
    ⟪f, KDop ha f⟫ = ((‖Wop ha f‖ ^ 2 : ℝ) : ℂ) := by
  rw [KDop_eq_adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ _).symm

/-- `‖K_D‖ = ‖W‖²` (C*-identity). -/
theorem norm_KDop_eq (ha : 0 < a) : ‖KDop ha‖ = ‖Wop ha‖ ^ 2 := by
  rw [KDop_eq_adjoint_comp, ContinuousLinearMap.norm_adjoint_comp_self, sq]

/-- `‖W‖ ≤ a⁻¹`. -/
theorem norm_Wop_le (ha : 0 < a) : ‖Wop ha‖ ≤ a⁻¹ := by
  have h : ‖Wop ha‖ ^ 2 ≤ a⁻¹ ^ 2 := by
    rw [← norm_KDop_eq, inv_pow]
    exact norm_KDop_le ha
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- `K_R = K_D + P_a` is a positive operator for `β < a`. -/
theorem KRop_isPositive (ha : 0 < a) (hab : β < a) : (KRop ha β).IsPositive :=
  (KDop_isPositive ha).add (robinDiff_isPositive ha hab)

/-- `K_R` is self-adjoint for `β < a`. -/
theorem KRop_isSelfAdjoint (ha : 0 < a) (hab : β < a) : IsSelfAdjoint (KRop ha β) :=
  (KRop_isPositive ha hab).isSelfAdjoint

/-! ### Manuscript form -/

/-- Proposition 14.2 (§14.2), positivity: with `c = ‖κ‖²`, `β > 0`, `t < c − β²` and
`a = √(c − t)`, the Dirichlet and Robin Green operators on `L²(0,∞)` factor as `K_D = W† W` and
`K_R = W† W + P_a`; both are positive and self-adjoint, and `⟪f, K_D f⟫ = ‖W f‖²`. -/
theorem prop14_2_positive {κ : EuclideanSpace ℝ (Fin 2)} {t : ℝ} (hβ : 0 < β)
    (ht : t < ‖κ‖ ^ 2 - β ^ 2) :
    KDop (aOf_pos hβ ht) =
        ContinuousLinearMap.adjoint (Wop (aOf_pos hβ ht)) ∘L Wop (aOf_pos hβ ht) ∧
    KRop (aOf_pos hβ ht) β =
        ContinuousLinearMap.adjoint (Wop (aOf_pos hβ ht)) ∘L Wop (aOf_pos hβ ht) +
          robinDiff (aOf_pos hβ ht) β ∧
    (KDop (aOf_pos hβ ht)).IsPositive ∧ (KRop (aOf_pos hβ ht) β).IsPositive ∧
    IsSelfAdjoint (KDop (aOf_pos hβ ht)) ∧ IsSelfAdjoint (KRop (aOf_pos hβ ht) β) ∧
    (∀ f : L2, ⟪f, KDop (aOf_pos hβ ht) f⟫ = ((‖Wop (aOf_pos hβ ht) f‖ ^ 2 : ℝ) : ℂ)) := by
  have hab := lt_aOf hβ ht
  refine ⟨KDop_eq_adjoint_comp _, ?_, KDop_isPositive _, KRop_isPositive _ hab,
    KDop_isSelfAdjoint _, KRop_isSelfAdjoint _ hab, inner_KDop_self _⟩
  rw [KRop, KDop_eq_adjoint_comp]

end

end Manuscript16.RobinDirichletPositive

#print axioms Manuscript16.RobinDirichletPositive.psi_nonneg
#print axioms Manuscript16.RobinDirichletPositive.psi_le_exp
#print axioms Manuscript16.RobinDirichletPositive.abs_psi_le
#print axioms Manuscript16.RobinDirichletPositive.measurable_psi
#print axioms Manuscript16.RobinDirichletPositive.psi_mul_psi
#print axioms Manuscript16.RobinDirichletPositive.integral_psi_mul_psi
#print axioms Manuscript16.RobinDirichletPositive.memLp_of_bound_meas
#print axioms Manuscript16.RobinDirichletPositive.memLp_psi_row
#print axioms Manuscript16.RobinDirichletPositive.memLp_psi_col
#print axioms Manuscript16.RobinDirichletPositive.Vfun_eq_integral
#print axioms Manuscript16.RobinDirichletPositive.Wfun_eq_integral
#print axioms Manuscript16.RobinDirichletPositive.measurable_expK
#print axioms Manuscript16.RobinDirichletPositive.expK_symm
#print axioms Manuscript16.RobinDirichletPositive.lintegral_expK_real
#print axioms Manuscript16.RobinDirichletPositive.row_expK
#print axioms Manuscript16.RobinDirichletPositive.col_expK
#print axioms Manuscript16.RobinDirichletPositive.enorm_le_expK
#print axioms Manuscript16.RobinDirichletPositive.lintegral_kernel_sq_le
#print axioms Manuscript16.RobinDirichletPositive.aestronglyMeasurable_kernel
#print axioms Manuscript16.RobinDirichletPositive.eLpNorm_kernel_le
#print axioms Manuscript16.RobinDirichletPositive.memLp_kernel
#print axioms Manuscript16.RobinDirichletPositive.norm_toLp_kernel_le
#print axioms Manuscript16.RobinDirichletPositive.abs_psi_swap_le
#print axioms Manuscript16.RobinDirichletPositive.measurable_psi_swap
#print axioms Manuscript16.RobinDirichletPositive.memLp_Vfun
#print axioms Manuscript16.RobinDirichletPositive.memLp_Wfun
#print axioms Manuscript16.RobinDirichletPositive.norm_toLp_Vfun_le
#print axioms Manuscript16.RobinDirichletPositive.norm_toLp_Wfun_le
#print axioms Manuscript16.RobinDirichletPositive.Vfun_add
#print axioms Manuscript16.RobinDirichletPositive.Vfun_smul
#print axioms Manuscript16.RobinDirichletPositive.Wfun_add
#print axioms Manuscript16.RobinDirichletPositive.Wfun_smul
#print axioms Manuscript16.RobinDirichletPositive.Vop_ae_eq
#print axioms Manuscript16.RobinDirichletPositive.Wop_ae_eq
#print axioms Manuscript16.RobinDirichletPositive.mul_le_sq_add_sq
#print axioms Manuscript16.RobinDirichletPositive.lintegral_enorm_sq_lt_top
#print axioms Manuscript16.RobinDirichletPositive.integrable_kernel_prod
#print axioms Manuscript16.RobinDirichletPositive.inner_Vop
#print axioms Manuscript16.RobinDirichletPositive.Vop_eq_adjoint
#print axioms Manuscript16.RobinDirichletPositive.Vfun_Wop
#print axioms Manuscript16.RobinDirichletPositive.KDop_eq_Vop_comp
#print axioms Manuscript16.RobinDirichletPositive.KDop_eq_adjoint_comp
#print axioms Manuscript16.RobinDirichletPositive.KDop_isPositive
#print axioms Manuscript16.RobinDirichletPositive.KDop_isSelfAdjoint
#print axioms Manuscript16.RobinDirichletPositive.inner_KDop_self
#print axioms Manuscript16.RobinDirichletPositive.norm_KDop_eq
#print axioms Manuscript16.RobinDirichletPositive.norm_Wop_le
#print axioms Manuscript16.RobinDirichletPositive.KRop_isPositive
#print axioms Manuscript16.RobinDirichletPositive.KRop_isSelfAdjoint
#print axioms Manuscript16.RobinDirichletPositive.prop14_2_positive
