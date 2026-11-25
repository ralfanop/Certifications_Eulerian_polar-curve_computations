import Mathlib

/-!
# M16 v16.5 §14.2, Proposition 14.2: the Robin–Dirichlet resolvent difference is rank one

Setting of the audit note `audits/Manuscript16_v16_5_RobinResolventRankOne_20261116.md`:
`c = |κ|²`, `β > 0`, `H = −d²/dz² + c` on `L²(0, ∞)` with the Robin condition
`u'(0) = −β u(0)` or the Dirichlet condition `u(0) = 0`; for real `t < c − β²` put
`a = √(c − t) > β`.  The Green kernels are

* `G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)`,
* `G_R(z,w) = (e^{−a|z−w|} + ((a+β)/(a−β)) e^{−a(z+w)})/(2a)`,

and the claim is `(H_R − t)⁻¹ − (H_D − t)⁻¹ = (a−β)⁻¹ |v_a⟩⟨v_a|`, `v_a(z) = e^{−az}`, a positive
rank-one operator with trace `1/(2a(a−β))`.

This file proves, with `μ` = Lebesgue measure on `(0, ∞)` and `L2 = L²((0,∞); ℂ)`:

* Part A (kernels): `greenR_sub_greenD` (`G_R − G_D = e^{−az}e^{−aw}/(a−β)`, from the scalar
  identity `((a+β)/(a−β) + 1)/(2a) = 1/(a−β)`), symmetry, `G_D(0,w) = 0`, and the Robin condition
  `∂_z G_R(0,w) = −β G_R(0,w)` (`greenR_robin_condition`).
* Part B (operator): `v_a ∈ L²(0,∞)` with `‖v_a‖² = 1/(2a)`; `robinDiff = (a−β)⁻¹ |v_a⟩⟨v_a|`
  is positive (`robinDiff_isPositive`), has range `ℂ v_a` and rank one (`range_robinDiff`,
  `finrank_range_robinDiff`), norm `1/(2a(a−β))` (`norm_robinDiff`), and on **every** Hilbert
  basis its diagonal is summable with sum `1/(2a(a−β))` (`robinDiff_diagonal_hasSum`).
* Part C (integral operators): `G_D(z,·), G_R(z,·) ∈ L²(0,∞)` for every `z`;
  `(K_D f)(z) = ∫₀^∞ G_D(z,w) f(w) dw` and `(K_R f)(z) = ∫₀^∞ G_R(z,w) f(w) dw` for every
  `f ∈ L²(0,∞)`; `(K_D f)(0) = 0`; `(K_R f)(z) − (K_D f)(z) = (a−β)⁻¹ e^{−az} ⟪v_a, f⟫` for every
  `z` (`KR_sub_KD`), hence `robinDiff f = K_R f − K_D f` in `L²` (`robinDiff_ae_eq`).
* Part D (classical solutions): for continuous `f` with `e^{−aw} f ∈ L¹(0,∞)`,
  `u_D(z) = ∫₀^∞ G_D(z,w) f(w) dw` and `u_R(z) = ∫₀^∞ G_R(z,w) f(w) dw` (`z ≥ 0`) are given by
  variation of parameters, are twice differentiable on `ℝ` with `−u'' + a² u = f`, and satisfy
  `u_D(0) = 0`, `u_R'(0) = −β u_R(0)`; for continuous `f ∈ L²(0,∞)` these are `K_D f`, `K_R f`
  (`KD_toLp`, `KR_toLp`).
* Part E (uniqueness): every bounded classical solution of `u'' = a² u` on `[0,∞)` (one-sided
  derivatives at `0`) is `u(0) e^{−az}`; with the Dirichlet condition, or with the Robin condition
  and `β < a`, it vanishes.  Hence `u_D`, `u_R` are the unique bounded classical solutions of the
  two boundary problems (`dirichlet_solution_unique`, `robin_solution_unique`, under the
  hypothesis that `u_D`, resp. `u_R`, is bounded).
* Manuscript form `prop14_2` with `c = ‖κ‖²`, `κ ∈ EuclideanSpace ℝ (Fin 2)`, `β > 0`,
  `t < c − β²`, `a = √(c − t)`.

Not claimed: the self-adjoint Robin and Dirichlet realisations on the half-line Sobolev space
`H²(0,∞)` (trace theorem, domains) and the identification of `K_D`, `K_R` with their resolvents on
all of `L²` (only classical solutions for continuous data are treated); boundedness of `K_D`,
`K_R` as operators on `L²`; trace-class membership in a Schatten-ideal sense (the diagonal sum is
proved on every Hilbert basis, for this rank-one operator); the pole at `a = β`, its residue and
eigenprojection; preservation of the essential spectrum; any Maxwell identification.
-/

namespace Manuscript16.RobinDirichletRankOne

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace

noncomputable section

/-! ### Part A: the Dirichlet and Robin Green kernels -/

/-- Robin reflection coefficient `(a + β)/(a − β)`. -/
def rho (a β : ℝ) : ℝ := (a + β) / (a - β)

/-- Dirichlet Green kernel `G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)`. -/
def greenD (a z w : ℝ) : ℝ :=
  (Real.exp (-a * |z - w|) - Real.exp (-a * (z + w))) / (2 * a)

/-- Robin Green kernel `G_R(z,w) = (e^{−a|z−w|} + ((a+β)/(a−β)) e^{−a(z+w)})/(2a)`. -/
def greenR (a β z w : ℝ) : ℝ :=
  (Real.exp (-a * |z - w|) + rho a β * Real.exp (-a * (z + w))) / (2 * a)

variable {a β : ℝ}

theorem rho_pos (hβ : 0 < β) (hab : β < a) : 0 < rho a β := by
  unfold rho
  apply div_pos <;> linarith

/-- The elementary scalar identity of the audit note: `((a+β)/(a−β) + 1)/(2a) = 1/(a−β)`. -/
theorem scalar_identity (ha : 0 < a) (hab : β < a) :
    (rho a β + 1) / (2 * a) = 1 / (a - β) := by
  unfold rho
  have h1 : a - β ≠ 0 := by linarith
  have h2 : a ≠ 0 := ha.ne'
  field_simp
  ring

/-- The free term cancels: `G_R − G_D = e^{−az} e^{−aw}/(a − β)`. -/
theorem greenR_sub_greenD (ha : 0 < a) (hab : β < a) (z w : ℝ) :
    greenR a β z w - greenD a z w = Real.exp (-a * z) * Real.exp (-a * w) / (a - β) := by
  have hs := scalar_identity ha hab
  have he : Real.exp (-a * (z + w)) = Real.exp (-a * z) * Real.exp (-a * w) := by
    rw [← Real.exp_add]; ring_nf
  unfold greenR greenD
  rw [he]
  have h2 : (2 * a) ≠ 0 := by positivity
  calc _ = (rho a β + 1) / (2 * a) * (Real.exp (-a * z) * Real.exp (-a * w)) := by
          field_simp; ring
    _ = _ := by rw [hs]; ring

theorem greenD_symm (a z w : ℝ) : greenD a z w = greenD a w z := by
  unfold greenD; rw [abs_sub_comm, add_comm z w]

theorem greenR_symm (a β z w : ℝ) : greenR a β z w = greenR a β w z := by
  unfold greenR; rw [abs_sub_comm, add_comm z w]

/-- Dirichlet condition of the kernel: `G_D(0, w) = 0` for `w ≥ 0`. -/
theorem greenD_zero_left (a : ℝ) {w : ℝ} (hw : 0 ≤ w) : greenD a 0 w = 0 := by
  unfold greenD
  rw [zero_sub, abs_neg, abs_of_nonneg hw, zero_add, sub_self, zero_div]

/-- Near the boundary (`z < w`) the Robin kernel is the smooth branch. -/
def greenRLeft (a β w z : ℝ) : ℝ :=
  (Real.exp (-a * (w - z)) + rho a β * Real.exp (-a * (z + w))) / (2 * a)

theorem greenR_eq_left {w z : ℝ} (hz : z < w) : greenR a β z w = greenRLeft a β w z := by
  unfold greenR greenRLeft
  rw [abs_of_neg (by linarith : z - w < 0), neg_sub]

theorem hasDerivAt_greenRLeft (a β w z : ℝ) :
    HasDerivAt (greenRLeft a β w)
      ((a * Real.exp (-a * (w - z)) - a * rho a β * Real.exp (-a * (z + w))) / (2 * a)) z := by
  have h1 : HasDerivAt (fun z => -a * (w - z)) a z := by
    simpa using ((hasDerivAt_id z).const_sub w).const_mul (-a)
  have h2 : HasDerivAt (fun z => -a * (z + w)) (-a) z := by
    simpa using ((hasDerivAt_id z).add_const w).const_mul (-a)
  have h := ((h1.exp).add ((h2.exp).const_mul (rho a β))).div_const (2 * a)
  unfold greenRLeft
  convert h using 1
  ring

/-- Robin condition of the kernel: `∂_z G_R(0, w) = −β G_R(0, w)` for every `w > 0`. -/
theorem greenR_robin_condition (ha : 0 < a) (hab : β < a) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun z => greenR a β z w) (-β * greenR a β 0 w) 0 := by
  have hev : greenRLeft a β w =ᶠ[𝓝 0] fun z => greenR a β z w := by
    filter_upwards [Iio_mem_nhds hw] with z hz
    exact (greenR_eq_left hz).symm
  refine ((hasDerivAt_greenRLeft a β w 0).congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [greenR_eq_left hw]
  unfold greenRLeft rho
  have h1 : a - β ≠ 0 := by linarith
  have h2 : a ≠ 0 := ha.ne'
  simp only [sub_zero, zero_add]
  field_simp
  ring

/-! ### Part B: the rank-one operator on `L²((0,∞); ℂ)` -/

/-- Lebesgue measure on the half-line `(0, ∞)`. -/
abbrev μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-- `L²((0, ∞); ℂ)`. -/
abbrev L2 := Lp (α := ℝ) ℂ 2 μ

theorem memLp_exp_real (ha : 0 < a) : MemLp (fun w : ℝ => Real.exp (-a * w)) 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  have h : (fun w : ℝ => ‖Real.exp (-a * w)‖ ^ 2) = fun w => Real.exp (-(2 * a) * w) := by
    funext w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]
    ring_nf
  rw [h]
  exact exp_neg_integrableOn_Ioi 0 (by linarith)

theorem memLp_exp (ha : 0 < a) : MemLp (fun w : ℝ => ((Real.exp (-a * w) : ℝ) : ℂ)) 2 μ :=
  (memLp_exp_real ha).ofReal

/-- The vector `v_a(z) = e^{−az}` in `L²(0, ∞)`. -/
def expVec (ha : 0 < a) : L2 := (memLp_exp ha).toLp _

theorem expVec_ae (ha : 0 < a) :
    (expVec ha : ℝ → ℂ) =ᵐ[μ] fun w => ((Real.exp (-a * w) : ℝ) : ℂ) :=
  (memLp_exp ha).coeFn_toLp

/-- `⟪v_a, v_a⟫ = ∫₀^∞ e^{−2az} dz = 1/(2a)`. -/
theorem inner_expVec_self (ha : 0 < a) :
    ⟪expVec ha, expVec ha⟫ = (((2 * a)⁻¹ : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have h1 : (∫ w, ⟪(expVec ha : ℝ → ℂ) w, (expVec ha : ℝ → ℂ) w⟫ ∂μ) =
      ∫ w, ((Real.exp (-(2 * a) * w) : ℝ) : ℂ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [expVec_ae ha] with w hw
    rw [hw, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
  rw [h1, integral_complex_ofReal, integral_exp_mul_Ioi (by linarith) 0]
  congr 1
  simp only [mul_zero, Real.exp_zero]
  field_simp

theorem norm_expVec_sq (ha : 0 < a) : ‖expVec ha‖ ^ 2 = (2 * a)⁻¹ := by
  have h := inner_expVec_self ha
  rw [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact h

theorem expVec_ne_zero (ha : 0 < a) : expVec ha ≠ 0 := by
  intro h
  have := norm_expVec_sq ha
  rw [h, norm_zero] at this
  have : (0 : ℝ) < (2 * a)⁻¹ := by positivity
  linarith

/-- The Robin–Dirichlet resolvent difference of Proposition 14.2:
`P_a = (a − β)⁻¹ |v_a⟩⟨v_a|`. -/
def robinDiff (ha : 0 < a) (β : ℝ) : L2 →L[ℂ] L2 :=
  (((a - β)⁻¹ : ℝ) : ℂ) • rankOne ℂ (expVec ha) (expVec ha)

theorem robinDiff_apply (ha : 0 < a) (β : ℝ) (f : L2) :
    robinDiff ha β f = ((((a - β)⁻¹ : ℝ) : ℂ) * ⟪expVec ha, f⟫) • expVec ha := by
  simp [robinDiff, rankOne_apply, smul_smul]

/-- `P_a` is a positive operator. -/
theorem robinDiff_isPositive (ha : 0 < a) (hab : β < a) : (robinDiff ha β).IsPositive := by
  apply (isPositive_rankOne_self (expVec ha)).smul_of_nonneg
  exact Complex.zero_le_real.mpr (inv_nonneg.mpr (by linarith))

/-- `‖P_a‖ = 1/(2a(a − β))`. -/
theorem norm_robinDiff (ha : 0 < a) (hab : β < a) :
    ‖robinDiff ha β‖ = (2 * a * (a - β))⁻¹ := by
  rw [robinDiff, norm_smul, norm_rankOne, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by linarith : (0:ℝ) < a - β)), ← sq, norm_expVec_sq ha]
  have h1 : a - β ≠ 0 := by linarith
  have h2 : a ≠ 0 := ha.ne'
  field_simp

/-- `P_a` has rank one: its range is the line spanned by `v_a`. -/
theorem range_robinDiff (ha : 0 < a) (hab : β < a) :
    LinearMap.range (robinDiff ha β).toLinearMap = ℂ ∙ expVec ha := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨_, (robinDiff_apply ha β f).symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    have hc : (((a - β)⁻¹ : ℝ) : ℂ) * (((2 * a)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have h1 : (a - β)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
      have h2 : (2 * a)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
      exact_mod_cast mul_ne_zero h1 h2
    refine ⟨((((a - β)⁻¹ : ℝ) : ℂ) * (((2 * a)⁻¹ : ℝ) : ℂ))⁻¹ • expVec ha, ?_⟩
    change robinDiff ha β _ = _
    rw [robinDiff_apply, inner_smul_right, inner_expVec_self,
      show (((a - β)⁻¹ : ℝ) : ℂ) * (((((a - β)⁻¹ : ℝ) : ℂ) * (((2 * a)⁻¹ : ℝ) : ℂ))⁻¹ *
          (((2 * a)⁻¹ : ℝ) : ℂ)) = ((((a - β)⁻¹ : ℝ) : ℂ) * (((2 * a)⁻¹ : ℝ) : ℂ))⁻¹ *
          ((((a - β)⁻¹ : ℝ) : ℂ) * (((2 * a)⁻¹ : ℝ) : ℂ)) by ring,
      inv_mul_cancel₀ hc, one_smul]

theorem finrank_range_robinDiff (ha : 0 < a) (hab : β < a) :
    Module.finrank ℂ (LinearMap.range (robinDiff ha β).toLinearMap) = 1 := by
  rw [range_robinDiff ha hab]
  exact finrank_span_singleton (expVec_ne_zero ha)

/-- Trace formula: on every Hilbert basis of `L²(0,∞)` the diagonal of `P_a` is summable with
sum `1/(2a(a − β))`. -/
theorem robinDiff_diagonal_hasSum (ha : 0 < a) {ι : Type*}
    (b : HilbertBasis ι ℂ L2) :
    HasSum (fun i => ⟪b i, robinDiff ha β (b i)⟫) (((2 * a * (a - β))⁻¹ : ℝ) : ℂ) := by
  have h := (b.hasSum_inner_mul_inner (expVec ha) (expVec ha)).mul_left
    (((a - β)⁻¹ : ℝ) : ℂ)
  rw [inner_expVec_self] at h
  have he : (((a - β)⁻¹ : ℝ) : ℂ) * (((2 * a)⁻¹ : ℝ) : ℂ) = (((2 * a * (a - β))⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [mul_inv, mul_inv]
    ring
  rw [he] at h
  convert h using 1
  funext i
  rw [robinDiff_apply, inner_smul_right]
  ring

/-! ### Part C: the Green kernels as integral operators on `L²(0,∞)` -/

theorem exp_abs_sub_le (ha : 0 ≤ a) (z : ℝ) {w : ℝ} (hw : 0 < w) :
    Real.exp (-a * |z - w|) ≤ Real.exp (a * |z|) * Real.exp (-a * w) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := abs_sub_abs_le_abs_sub w z
  rw [abs_of_pos hw, abs_sub_comm] at h
  nlinarith

theorem exp_add_le (ha : 0 ≤ a) (z w : ℝ) :
    Real.exp (-a * (z + w)) ≤ Real.exp (a * |z|) * Real.exp (-a * w) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [neg_abs_le z]

theorem memLp_of_bound (ha : 0 < a) {g : ℝ → ℝ} (hg : Continuous g) (C : ℝ)
    (hb : ∀ w, 0 < w → |g w| ≤ C * Real.exp (-a * w)) :
    MemLp (fun w => (g w : ℂ)) 2 μ := by
  refine (((memLp_exp_real ha).const_mul C).of_le hg.aestronglyMeasurable ?_).ofReal
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hb w hw).trans (le_abs_self _)

theorem abs_greenD_le (ha : 0 < a) (z : ℝ) {w : ℝ} (hw : 0 < w) :
    |greenD a z w| ≤ Real.exp (a * |z|) / a * Real.exp (-a * w) := by
  have h1 := exp_abs_sub_le ha.le z hw
  have h2 := exp_add_le ha.le z w
  have h3 : |Real.exp (-a * |z - w|) - Real.exp (-a * (z + w))| ≤
      Real.exp (-a * |z - w|) + Real.exp (-a * (z + w)) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  unfold greenD
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * a), div_le_iff₀ (by positivity)]
  have he : Real.exp (a * |z|) / a * Real.exp (-a * w) * (2 * a) =
      2 * (Real.exp (a * |z|) * Real.exp (-a * w)) := by
    field_simp
  rw [he]
  linarith

theorem abs_greenR_le (ha : 0 < a) (β z : ℝ) {w : ℝ} (hw : 0 < w) :
    |greenR a β z w| ≤ (1 + |rho a β|) * Real.exp (a * |z|) / (2 * a) * Real.exp (-a * w) := by
  have h1 := exp_abs_sub_le ha.le z hw
  have h2 := exp_add_le ha.le z w
  have h3 : |Real.exp (-a * |z - w|) + rho a β * Real.exp (-a * (z + w))| ≤
      Real.exp (-a * |z - w|) + |rho a β| * Real.exp (-a * (z + w)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (Real.exp_pos _)]
  unfold greenR
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * a), div_le_iff₀ (by positivity)]
  have he : (1 + |rho a β|) * Real.exp (a * |z|) / (2 * a) * Real.exp (-a * w) * (2 * a) =
      (1 + |rho a β|) * (Real.exp (a * |z|) * Real.exp (-a * w)) := by
    field_simp
  rw [he]
  have h4 : |rho a β| * Real.exp (-a * (z + w)) ≤
      |rho a β| * (Real.exp (a * |z|) * Real.exp (-a * w)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  nlinarith

theorem continuous_greenD (a z : ℝ) : Continuous (greenD a z) := by
  unfold greenD; fun_prop

theorem continuous_greenR (a β z : ℝ) : Continuous (greenR a β z) := by
  unfold greenR; fun_prop

theorem memLp_greenD (ha : 0 < a) (z : ℝ) : MemLp (fun w => (greenD a z w : ℂ)) 2 μ :=
  memLp_of_bound ha (continuous_greenD a z) _ (fun _ hw => abs_greenD_le ha z hw)

theorem memLp_greenR (ha : 0 < a) (β z : ℝ) : MemLp (fun w => (greenR a β z w : ℂ)) 2 μ :=
  memLp_of_bound ha (continuous_greenR a β z) _ (fun _ hw => abs_greenR_le ha β z hw)

/-- The Dirichlet kernel section `G_D(z, ·) ∈ L²(0,∞)`. -/
def kD (ha : 0 < a) (z : ℝ) : L2 := (memLp_greenD ha z).toLp _

/-- The Robin kernel section `G_R(z, ·) ∈ L²(0,∞)`. -/
def kR (ha : 0 < a) (β z : ℝ) : L2 := (memLp_greenR ha β z).toLp _

/-- The free part cancels in `L²`: `G_R(z,·) − G_D(z,·) = (a−β)⁻¹ e^{−az} v_a`. -/
theorem kR_sub_kD (ha : 0 < a) (hab : β < a) (z : ℝ) :
    kR ha β z - kD ha z = ((((a - β)⁻¹ * Real.exp (-a * z)) : ℝ) : ℂ) • expVec ha := by
  rw [kR, kD, expVec, ← MemLp.toLp_sub, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  refine Filter.Eventually.of_forall (fun w => ?_)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Complex.ofReal_sub, greenR_sub_greenD ha hab, ← Complex.ofReal_mul]
  congr 1
  field_simp

/-- `G_D(0, ·) = 0` in `L²(0,∞)`. -/
theorem kD_zero (ha : 0 < a) : kD ha 0 = 0 := by
  rw [kD, ← MemLp.toLp_zero (MemLp.zero : MemLp (0 : ℝ → ℂ) 2 μ)]
  apply MemLp.toLp_congr
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
  simp [greenD_zero_left a (le_of_lt hw)]

/-- The Dirichlet integral operator `(K_D f)(z) = ∫₀^∞ G_D(z,w) f(w) dw`. -/
def KD (ha : 0 < a) (f : L2) (z : ℝ) : ℂ := ⟪kD ha z, f⟫

/-- The Robin integral operator `(K_R f)(z) = ∫₀^∞ G_R(z,w) f(w) dw`. -/
def KR (ha : 0 < a) (β : ℝ) (f : L2) (z : ℝ) : ℂ := ⟪kR ha β z, f⟫

theorem KD_eq_integral (ha : 0 < a) (f : L2) (z : ℝ) :
    KD ha f z = ∫ w in Ioi 0, (greenD a z w : ℂ) * f w := by
  rw [KD, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_greenD ha z).coeFn_toLp] with w hw
  rw [kD, hw, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

theorem KR_eq_integral (ha : 0 < a) (β : ℝ) (f : L2) (z : ℝ) :
    KR ha β f z = ∫ w in Ioi 0, (greenR a β z w : ℂ) * f w := by
  rw [KR, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_greenR ha β z).coeFn_toLp] with w hw
  rw [kR, hw, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- Dirichlet condition of the integral operator: `(K_D f)(0) = 0` for every `f ∈ L²`. -/
theorem KD_zero_left (ha : 0 < a) (f : L2) : KD ha f 0 = 0 := by
  rw [KD, kD_zero, inner_zero_left]

/-- Pointwise rank-one formula: `(K_R f)(z) − (K_D f)(z) = (a−β)⁻¹ e^{−az} ⟪v_a, f⟫`
for every `f ∈ L²(0,∞)` and every `z`. -/
theorem KR_sub_KD (ha : 0 < a) (hab : β < a) (f : L2) (z : ℝ) :
    KR ha β f z - KD ha f z =
      ((((a - β)⁻¹ * Real.exp (-a * z)) : ℝ) : ℂ) * ⟪expVec ha, f⟫ := by
  rw [KR, KD, ← inner_sub_left, kR_sub_kD ha hab, inner_smul_left, Complex.conj_ofReal]

/-- Operator form of Proposition 14.2: `P_a f = K_R f − K_D f` almost everywhere on `(0,∞)`. -/
theorem robinDiff_ae_eq (ha : 0 < a) (hab : β < a) (f : L2) :
    (robinDiff ha β f : ℝ → ℂ) =ᵐ[μ] fun z => KR ha β f z - KD ha f z := by
  rw [robinDiff_apply]
  filter_upwards [Lp.coeFn_smul ((((a - β)⁻¹ : ℝ) : ℂ) * ⟪expVec ha, f⟫) (expVec ha),
    expVec_ae ha] with z h1 h2
  rw [h1, Pi.smul_apply, h2, KR_sub_KD ha hab, smul_eq_mul]
  push_cast
  ring

/-! ### Part E: uniqueness of bounded classical solutions on the half-line -/

/-- If `g' = c g` on `[0, ∞)` (one-sided derivatives), then `g z = g 0 · e^{cz}` for `z ≥ 0`. -/
theorem eq_exp_of_hasDerivWithinAt {g : ℝ → ℝ} (c : ℝ)
    (hg : ∀ z, 0 ≤ z → HasDerivWithinAt g (c * g z) (Ici 0) z) {z : ℝ} (hz : 0 ≤ z) :
    g z = g 0 * Real.exp (c * z) := by
  set F : ℝ → ℝ := fun t => g t * Real.exp (-c * t) with hFdef
  have hF : ∀ t, 0 ≤ t → HasDerivWithinAt F 0 (Ici 0) t := by
    intro t ht
    have he : HasDerivAt (fun t => Real.exp (-c * t)) (Real.exp (-c * t) * (-c)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-c)).exp
    convert (hg t ht).mul he.hasDerivWithinAt using 1
    ring
  have hcont : ContinuousOn F (Icc 0 z) := fun t ht =>
    (hF t ht.1).continuousWithinAt.mono Icc_subset_Ici_self
  have h0 : F z = F 0 := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hF t ht.1).mono (Ici_subset_Ici.mpr ht.1)) z ⟨hz, le_rfl⟩
  simp only [hFdef, mul_zero, Real.exp_zero, mul_one] at h0
  calc g z = g z * Real.exp (-c * z) * Real.exp (c * z) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
    _ = g 0 * Real.exp (c * z) := by rw [h0]

/-- Every bounded classical solution of `u'' = a² u` on `[0, ∞)` is `u(0) e^{−az}`. -/
theorem bounded_solution_eq (ha : 0 < a) {u u' : ℝ → ℝ}
    (hu : ∀ z, 0 ≤ z → HasDerivWithinAt u (u' z) (Ici 0) z)
    (hu' : ∀ z, 0 ≤ z → HasDerivWithinAt u' (a ^ 2 * u z) (Ici 0) z)
    (hbdd : ∃ M, ∀ z, 0 ≤ z → |u z| ≤ M) :
    ∀ z, 0 ≤ z → u z = u 0 * Real.exp (-a * z) := by
  obtain ⟨M, hM⟩ := hbdd
  set g : ℝ → ℝ := fun t => u' t + a * u t with hgdef
  set h : ℝ → ℝ := fun t => u' t - a * u t with hhdef
  have hg : ∀ z, 0 ≤ z → HasDerivWithinAt g (a * g z) (Ici 0) z := fun z hz => by
    convert (hu' z hz).add ((hu z hz).const_mul a) using 1
    simp only [hgdef]; ring
  have hh : ∀ z, 0 ≤ z → HasDerivWithinAt h (-a * h z) (Ici 0) z := fun z hz => by
    convert (hu' z hz).sub ((hu z hz).const_mul a) using 1
    simp only [hhdef]; ring
  have hu2 : ∀ z, 0 ≤ z → 2 * a * u z = g 0 * Real.exp (a * z) - h 0 * Real.exp (-a * z) := by
    intro z hz
    rw [← eq_exp_of_hasDerivWithinAt a hg hz, ← eq_exp_of_hasDerivWithinAt (-a) hh hz]
    simp only [hgdef, hhdef]; ring
  have hg0 : g 0 = 0 := by
    by_contra hne
    have hpos : 0 < |g 0| := abs_pos.mpr hne
    obtain ⟨z, hz0, hz⟩ : ∃ z, 0 ≤ z ∧ (2 * a * M + |h 0| + 1) / |g 0| < Real.exp (a * z) := by
      have ht : Tendsto (fun z => Real.exp (a * z)) atTop atTop :=
        Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
      obtain ⟨z, hz⟩ := ((ht.eventually_gt_atTop _).and (eventually_ge_atTop 0)).exists
      exact ⟨z, hz.2, hz.1⟩
    have h1 := hu2 z hz0
    have h2 := hM z hz0
    have hexp : Real.exp (-a * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hexp0 : 0 < Real.exp (-a * z) := Real.exp_pos _
    rw [div_lt_iff₀ hpos] at hz
    have key : |g 0| * Real.exp (a * z) ≤ 2 * a * |u z| + |h 0| * Real.exp (-a * z) := by
      have h3 : |g 0 * Real.exp (a * z)| ≤ |2 * a * u z| + |h 0 * Real.exp (-a * z)| := by
        rw [show g 0 * Real.exp (a * z) = 2 * a * u z + h 0 * Real.exp (-a * z) by linarith]
        exact abs_add_le _ _
      rwa [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * a),
        abs_mul, abs_of_pos hexp0] at h3
    have h4 : 2 * a * |u z| ≤ 2 * a * M := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : |h 0| * Real.exp (-a * z) ≤ |h 0| := by
      calc |h 0| * Real.exp (-a * z) ≤ |h 0| * 1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = |h 0| := mul_one _
    nlinarith
  intro z hz
  have h1 := hu2 z hz
  have h0 := hu2 0 le_rfl
  rw [hg0, zero_mul, zero_sub] at h1 h0
  simp only [mul_zero, Real.exp_zero, mul_one] at h0
  have h2a : (2 * a) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2a
  rw [h1, ← mul_assoc, h0]
  ring

/-- Uniqueness for the Dirichlet problem: a bounded classical solution of `−u'' + a² u = 0` on
`[0, ∞)` with `u(0) = 0` vanishes. -/
theorem dirichlet_uniqueness (ha : 0 < a) {u u' : ℝ → ℝ}
    (hu : ∀ z, 0 ≤ z → HasDerivWithinAt u (u' z) (Ici 0) z)
    (hu' : ∀ z, 0 ≤ z → HasDerivWithinAt u' (a ^ 2 * u z) (Ici 0) z)
    (hbdd : ∃ M, ∀ z, 0 ≤ z → |u z| ≤ M) (hD : u 0 = 0) :
    ∀ z, 0 ≤ z → u z = 0 := by
  intro z hz
  rw [bounded_solution_eq ha hu hu' hbdd z hz, hD, zero_mul]

/-- Uniqueness for the Robin problem: if `0 < a` and `β < a`, a bounded classical solution of
`−u'' + a² u = 0` on `[0, ∞)` with `u'(0) = −β u(0)` vanishes. -/
theorem robin_uniqueness (ha : 0 < a) (hab : β < a) {u u' : ℝ → ℝ}
    (hu : ∀ z, 0 ≤ z → HasDerivWithinAt u (u' z) (Ici 0) z)
    (hu' : ∀ z, 0 ≤ z → HasDerivWithinAt u' (a ^ 2 * u z) (Ici 0) z)
    (hbdd : ∃ M, ∀ z, 0 ≤ z → |u z| ≤ M) (hR : u' 0 = -β * u 0) :
    ∀ z, 0 ≤ z → u z = 0 := by
  have hform := bounded_solution_eq ha hu hu' hbdd
  have hE : HasDerivWithinAt (fun z => u 0 * Real.exp (-a * z)) (u 0 * (Real.exp (-a * 0) * (-a)))
      (Ici 0) 0 := by
    have : HasDerivAt (fun z => Real.exp (-a * z)) (Real.exp (-a * 0) * (-a)) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_mul (-a)).exp
    exact (this.const_mul (u 0)).hasDerivWithinAt
  have hU : HasDerivWithinAt (fun z => u 0 * Real.exp (-a * z)) (u' 0) (Ici 0) 0 :=
    (hu 0 le_rfl).congr (fun z hz => (hform z hz).symm) (hform 0 le_rfl).symm
  have hd := (uniqueDiffWithinAt_Ici (0:ℝ)).eq_deriv _ hU hE
  simp only [mul_zero, Real.exp_zero, one_mul] at hd
  have hu0 : u 0 = 0 := by
    have : (a - β) * u 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by linarith)
    · exact h
  intro z hz
  rw [hform z hz, hu0, zero_mul]

/-! ### Part D: the Green kernels produce the classical solutions -/

/-- `C_f = ∫₀^∞ e^{−aw} f(w) dw`. -/
def tailC (a : ℝ) (f : ℝ → ℝ) : ℝ := ∫ w in Ioi 0, Real.exp (-a * w) * f w

/-- `I₁(z) = ∫₀^z sinh(aw) f(w) dw`. -/
def I1 (a : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ := ∫ w in (0:ℝ)..z, Real.sinh (a * w) * f w

/-- `I₂(z) = C_f − ∫₀^z e^{−aw} f(w) dw` (`= ∫_z^∞ e^{−aw} f(w) dw` for `z ≥ 0`). -/
def I2 (a : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  tailC a f - ∫ w in (0:ℝ)..z, Real.exp (-a * w) * f w

/-- Variation-of-parameters form of `∫₀^∞ G_D(z,w) f(w) dw`. -/
def solD (a : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  (Real.exp (-a * z) * I1 a f z + Real.sinh (a * z) * I2 a f z) / a

/-- Its derivative. -/
def solD' (a : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  -Real.exp (-a * z) * I1 a f z + Real.cosh (a * z) * I2 a f z

/-- Robin solution `u_R = u_D + (a−β)⁻¹ C_f e^{−az}`. -/
def solR (a β : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  solD a f z + tailC a f / (a - β) * Real.exp (-a * z)

/-- Its derivative. -/
def solR' (a β : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  solD' a f z - a * (tailC a f / (a - β)) * Real.exp (-a * z)

theorem hasDerivAt_I1 {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    HasDerivAt (I1 a f) (Real.sinh (a * z) * f z) z :=
  ((by fun_prop : Continuous fun w => Real.sinh (a * w) * f w).integral_hasStrictDerivAt 0 z).hasDerivAt

theorem hasDerivAt_I2 {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    HasDerivAt (I2 a f) (-(Real.exp (-a * z) * f z)) z :=
  (((by fun_prop : Continuous fun w => Real.exp (-a * w) * f w).integral_hasStrictDerivAt
    0 z).hasDerivAt).const_sub _

theorem hasDerivAt_expneg (a z : ℝ) :
    HasDerivAt (fun z => Real.exp (-a * z)) (-a * Real.exp (-a * z)) z := by
  have h : HasDerivAt (fun z => -a * z) (-a) z := by
    simpa using (hasDerivAt_id z).const_mul (-a)
  convert h.exp using 1
  ring

theorem hasDerivAt_sinh_mul (a z : ℝ) :
    HasDerivAt (fun z => Real.sinh (a * z)) (a * Real.cosh (a * z)) z := by
  have h : HasDerivAt (fun z => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  convert h.sinh using 1
  ring

theorem hasDerivAt_cosh_mul (a z : ℝ) :
    HasDerivAt (fun z => Real.cosh (a * z)) (a * Real.sinh (a * z)) z := by
  have h : HasDerivAt (fun z => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  convert h.cosh using 1
  ring

/-- `u_D' = solD'`. -/
theorem hasDerivAt_solD (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    HasDerivAt (solD a f) (solD' a f z) z := by
  have h := (((hasDerivAt_expneg a z).mul (hasDerivAt_I1 (a := a) hf z)).add
    ((hasDerivAt_sinh_mul a z).mul (hasDerivAt_I2 (a := a) hf z))).div_const a
  unfold solD
  convert h using 1
  unfold solD'
  field_simp
  ring

/-- `u_D'' = a² u_D − f`, i.e. `−u_D'' + a² u_D = f` on `ℝ`. -/
theorem hasDerivAt_solD' (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    HasDerivAt (solD' a f) (a ^ 2 * solD a f z - f z) z := by
  have h := ((hasDerivAt_expneg a z).neg.mul (hasDerivAt_I1 (a := a) hf z)).add
    ((hasDerivAt_cosh_mul a z).mul (hasDerivAt_I2 (a := a) hf z))
  have hsc : Real.sinh (a * z) + Real.cosh (a * z) = Real.exp (a * z) := Real.sinh_add_cosh _
  have hee : Real.exp (-a * z) * Real.exp (a * z) = 1 := by
    rw [← Real.exp_add]; simp
  have hs : a ^ 2 * solD a f z =
      a * (Real.exp (-a * z) * I1 a f z + Real.sinh (a * z) * I2 a f z) := by
    unfold solD; field_simp
  unfold solD'
  convert h using 1
  simp only [Pi.neg_apply]
  rw [hs]
  linear_combination (Real.exp (-a * z) * f z) * hsc + f z * hee

theorem solD_zero (a : ℝ) (f : ℝ → ℝ) : solD a f 0 = 0 := by
  simp [solD, I1]

theorem solD'_zero (a : ℝ) (f : ℝ → ℝ) : solD' a f 0 = tailC a f := by
  simp [solD', I1, I2]

theorem hasDerivAt_solR (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    HasDerivAt (solR a β f) (solR' a β f z) z := by
  have h := (hasDerivAt_solD ha hf z).add ((hasDerivAt_expneg a z).const_mul (tailC a f / (a - β)))
  unfold solR solR'
  convert h using 1
  ring

theorem hasDerivAt_solR' (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    HasDerivAt (solR' a β f) (a ^ 2 * solR a β f z - f z) z := by
  have h := (hasDerivAt_solD' ha hf z).sub
    ((hasDerivAt_expneg a z).const_mul (a * (tailC a f / (a - β))))
  unfold solR' solR
  convert h using 1
  ring

/-- Robin condition of the classical solution: `u_R'(0) = −β u_R(0)`. -/
theorem solR_robin (hab : β < a) (f : ℝ → ℝ) : solR' a β f 0 = -β * solR a β f 0 := by
  have h : a - β ≠ 0 := by linarith
  simp only [solR', solR, solD_zero, solD'_zero, mul_zero, Real.exp_zero, mul_one, zero_add]
  field_simp
  ring

/-- `∫₀^∞ G_D(z,w) f(w) dw = u_D(z)` for every `z ≥ 0`. -/
theorem integral_greenD_mul (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f)
    (hint : IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0)) {z : ℝ} (hz : 0 ≤ z) :
    ∫ w in Ioi 0, greenD a z w * f w = solD a f z := by
  have hGint : IntegrableOn (fun w => greenD a z w * f w) (Ioi 0) := by
    refine Integrable.mono' (hint.norm.const_mul (Real.exp (a * |z|) / a)) ?_ ?_
    · exact ((continuous_greenD a z).mul hf).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |greenD a z w| * |f w|
          ≤ (Real.exp (a * |z|) / a * Real.exp (-a * w)) * |f w| :=
            mul_le_mul_of_nonneg_right (abs_greenD_le ha z hw) (abs_nonneg _)
        _ = _ := by ring
  have hEint := hint
  rw [← Ioc_union_Ioi_eq_Ioi hz, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hGint.mono_set Ioc_subset_Ioi_self) (hGint.mono_set (Ioi_subset_Ioi hz))]
  have hp1 : ∫ w in Ioc 0 z, greenD a z w * f w = Real.exp (-a * z) / a * I1 a f z := by
    rw [I1, intervalIntegral.integral_of_le hz, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro w hw
    have e1 : Real.exp (-a * |z - w|) = Real.exp (-a * z) * Real.exp (a * w) := by
      rw [abs_of_nonneg (by linarith [hw.2] : 0 ≤ z - w), ← Real.exp_add]; ring_nf
    have e2 : Real.exp (-a * (z + w)) = Real.exp (-a * z) * Real.exp (-(a * w)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [greenD]
    rw [e1, e2, Real.sinh_eq]
    field_simp
  have hp2 : ∫ w in Ioi z, greenD a z w * f w =
      Real.sinh (a * z) / a * ∫ w in Ioi z, Real.exp (-a * w) * f w := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    have e1 : Real.exp (-a * |z - w|) = Real.exp (a * z) * Real.exp (-a * w) := by
      rw [abs_of_neg (by linarith [show z < w from hw] : z - w < 0), ← Real.exp_add]; ring_nf
    have e2 : Real.exp (-a * (z + w)) = Real.exp (-(a * z)) * Real.exp (-a * w) := by
      rw [← Real.exp_add]; ring_nf
    simp only [greenD]
    rw [e1, e2, Real.sinh_eq]
    field_simp
  have ht : ∫ w in Ioi z, Real.exp (-a * w) * f w = I2 a f z := by
    rw [I2, tailC, ← Ioc_union_Ioi_eq_Ioi hz, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hEint.mono_set Ioc_subset_Ioi_self) (hEint.mono_set (Ioi_subset_Ioi hz)),
      intervalIntegral.integral_of_le hz]
    ring
  rw [hp1, hp2, ht, solD]
  field_simp

/-- `∫₀^∞ G_R(z,w) f(w) dw = u_R(z)` for every `z ≥ 0`. -/
theorem integral_greenR_mul (ha : 0 < a) (hab : β < a) {f : ℝ → ℝ} (hf : Continuous f)
    (hint : IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0)) {z : ℝ} (hz : 0 ≤ z) :
    ∫ w in Ioi 0, greenR a β z w * f w = solR a β f z := by
  have hGD : IntegrableOn (fun w => greenD a z w * f w) (Ioi 0) := by
    refine Integrable.mono' (hint.norm.const_mul (Real.exp (a * |z|) / a)) ?_ ?_
    · exact ((continuous_greenD a z).mul hf).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |greenD a z w| * |f w|
          ≤ (Real.exp (a * |z|) / a * Real.exp (-a * w)) * |f w| :=
            mul_le_mul_of_nonneg_right (abs_greenD_le ha z hw) (abs_nonneg _)
        _ = _ := by ring
  have hsplit : (fun w => greenR a β z w * f w) = fun w =>
      greenD a z w * f w + Real.exp (-a * z) / (a - β) * (Real.exp (-a * w) * f w) := by
    funext w
    rw [← sub_add_cancel (greenR a β z w) (greenD a z w), greenR_sub_greenD ha hab]
    ring
  rw [hsplit, integral_add hGD (hint.const_mul _), integral_const_mul,
    integral_greenD_mul ha hf hint hz, solR, tailC]
  ring

/-! ### Assembly: Proposition 14.2 for continuous data in `L²(0,∞)` -/

theorem inner_expVec_toLp (ha : 0 < a) {f : ℝ → ℝ} (hL2 : MemLp (fun w => (f w : ℂ)) 2 μ) :
    ⟪expVec ha, hL2.toLp _⟫ = (tailC a f : ℂ) := by
  rw [L2.inner_def, tailC, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [expVec_ae ha, hL2.coeFn_toLp] with w h1 h2
  rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal, Complex.ofReal_mul, mul_comm]

/-- The Dirichlet integral operator `K_D` gives the classical Dirichlet solution. -/
theorem KD_toLp (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f)
    (hL2 : MemLp (fun w => (f w : ℂ)) 2 μ)
    (hint : IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0)) {z : ℝ} (hz : 0 ≤ z) :
    KD ha (hL2.toLp _) z = (solD a f z : ℂ) := by
  rw [KD_eq_integral, ← integral_greenD_mul ha hf hint hz, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hL2.coeFn_toLp] with w hw
  rw [hw, Complex.ofReal_mul]

/-- The Robin integral operator `K_R` gives the classical Robin solution. -/
theorem KR_toLp (ha : 0 < a) (hab : β < a) {f : ℝ → ℝ} (hf : Continuous f)
    (hL2 : MemLp (fun w => (f w : ℂ)) 2 μ)
    (hint : IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0)) {z : ℝ} (hz : 0 ≤ z) :
    KR ha β (hL2.toLp _) z = (solR a β f z : ℂ) := by
  rw [KR_eq_integral, ← integral_greenR_mul ha hab hf hint hz, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hL2.coeFn_toLp] with w hw
  rw [hw, Complex.ofReal_mul]

/-- Uniqueness of the Dirichlet solution among bounded classical solutions. -/
theorem dirichlet_solution_unique (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f)
    {v v' : ℝ → ℝ}
    (hv : ∀ z, 0 ≤ z → HasDerivWithinAt v (v' z) (Ici 0) z)
    (hv' : ∀ z, 0 ≤ z → HasDerivWithinAt v' (a ^ 2 * v z - f z) (Ici 0) z)
    (hvb : ∃ M, ∀ z, 0 ≤ z → |v z| ≤ M) (hv0 : v 0 = 0)
    (hsb : ∃ M, ∀ z, 0 ≤ z → |solD a f z| ≤ M) :
    ∀ z, 0 ≤ z → v z = solD a f z := by
  obtain ⟨M1, hM1⟩ := hvb
  obtain ⟨M2, hM2⟩ := hsb
  have h := dirichlet_uniqueness ha (u := fun z => v z - solD a f z)
    (u' := fun z => v' z - solD' a f z)
    (fun z hz => (hv z hz).sub (hasDerivAt_solD ha hf z).hasDerivWithinAt)
    (fun z hz => by
      convert (hv' z hz).sub (hasDerivAt_solD' ha hf z).hasDerivWithinAt using 1
      ring)
    ⟨M1 + M2, fun z hz => (abs_sub _ _).trans (add_le_add (hM1 z hz) (hM2 z hz))⟩
    (by simp [hv0, solD_zero])
  intro z hz
  exact sub_eq_zero.mp (h z hz)

/-- Uniqueness of the Robin solution among bounded classical solutions. -/
theorem robin_solution_unique (ha : 0 < a) (hab : β < a) {f : ℝ → ℝ} (hf : Continuous f)
    {v v' : ℝ → ℝ}
    (hv : ∀ z, 0 ≤ z → HasDerivWithinAt v (v' z) (Ici 0) z)
    (hv' : ∀ z, 0 ≤ z → HasDerivWithinAt v' (a ^ 2 * v z - f z) (Ici 0) z)
    (hvb : ∃ M, ∀ z, 0 ≤ z → |v z| ≤ M) (hvR : v' 0 = -β * v 0)
    (hsb : ∃ M, ∀ z, 0 ≤ z → |solR a β f z| ≤ M) :
    ∀ z, 0 ≤ z → v z = solR a β f z := by
  obtain ⟨M1, hM1⟩ := hvb
  obtain ⟨M2, hM2⟩ := hsb
  have h := robin_uniqueness ha hab (u := fun z => v z - solR a β f z)
    (u' := fun z => v' z - solR' a β f z)
    (fun z hz => (hv z hz).sub (hasDerivAt_solR ha hf z).hasDerivWithinAt)
    (fun z hz => by
      convert (hv' z hz).sub (hasDerivAt_solR' ha hf z).hasDerivWithinAt using 1
      ring)
    ⟨M1 + M2, fun z hz => (abs_sub _ _).trans (add_le_add (hM1 z hz) (hM2 z hz))⟩
    (by show v' 0 - solR' a β f 0 = -β * (v 0 - solR a β f 0)
        rw [hvR, solR_robin hab]; ring)
  intro z hz
  exact sub_eq_zero.mp (h z hz)

/-! ### Manuscript form -/

/-- `a = √(c − t)`. -/
def aOf (c t : ℝ) : ℝ := Real.sqrt (c - t)

theorem lt_aOf {c t : ℝ} (hβ : 0 < β) (ht : t < c - β ^ 2) : β < aOf c t := by
  unfold aOf
  rw [Real.lt_sqrt hβ.le]
  linarith

theorem aOf_pos {c t : ℝ} (hβ : 0 < β) (ht : t < c - β ^ 2) : 0 < aOf c t :=
  hβ.trans (lt_aOf hβ ht)

theorem aOf_sq {c t : ℝ} (ht : t < c - β ^ 2) : aOf c t ^ 2 = c - t := by
  unfold aOf
  rw [Real.sq_sqrt]
  nlinarith

/-- Proposition 14.2 for `c = |κ|²`, `κ ∈ ℝ²`, `β > 0`, `t < c − β²`, `a = √(c − t)`:
the operator `(a−β)⁻¹ |v_a⟩⟨v_a|` is positive, of rank one, of norm `1/(2a(a−β))`, equals
`K_R − K_D` on `L²(0,∞)`, and has diagonal sum `1/(2a(a−β))` on every Hilbert basis. -/
theorem prop14_2 {κ : EuclideanSpace ℝ (Fin 2)} {t : ℝ} (hβ : 0 < β)
    (ht : t < ‖κ‖ ^ 2 - β ^ 2) :
    (robinDiff (aOf_pos hβ ht) β).IsPositive ∧
    Module.finrank ℂ (LinearMap.range (robinDiff (aOf_pos hβ ht) β).toLinearMap) = 1 ∧
    ‖robinDiff (aOf_pos hβ ht) β‖ = (2 * aOf (‖κ‖ ^ 2) t * (aOf (‖κ‖ ^ 2) t - β))⁻¹ ∧
    (∀ f : L2, (robinDiff (aOf_pos hβ ht) β f : ℝ → ℂ) =ᵐ[μ]
      fun z => KR (aOf_pos hβ ht) β f z - KD (aOf_pos hβ ht) f z) ∧
    (∀ {ι : Type} (b : HilbertBasis ι ℂ L2),
      HasSum (fun i => ⟪b i, robinDiff (aOf_pos hβ ht) β (b i)⟫)
        (((2 * aOf (‖κ‖ ^ 2) t * (aOf (‖κ‖ ^ 2) t - β))⁻¹ : ℝ) : ℂ)) :=
  ⟨robinDiff_isPositive _ (lt_aOf hβ ht), finrank_range_robinDiff _ (lt_aOf hβ ht),
    norm_robinDiff _ (lt_aOf hβ ht), fun f => robinDiff_ae_eq _ (lt_aOf hβ ht) f,
    fun b => robinDiff_diagonal_hasSum _ b⟩

end

end Manuscript16.RobinDirichletRankOne

#print axioms Manuscript16.RobinDirichletRankOne.rho_pos
#print axioms Manuscript16.RobinDirichletRankOne.scalar_identity
#print axioms Manuscript16.RobinDirichletRankOne.greenR_sub_greenD
#print axioms Manuscript16.RobinDirichletRankOne.greenD_symm
#print axioms Manuscript16.RobinDirichletRankOne.greenR_symm
#print axioms Manuscript16.RobinDirichletRankOne.greenD_zero_left
#print axioms Manuscript16.RobinDirichletRankOne.greenR_eq_left
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_greenRLeft
#print axioms Manuscript16.RobinDirichletRankOne.greenR_robin_condition
#print axioms Manuscript16.RobinDirichletRankOne.memLp_exp_real
#print axioms Manuscript16.RobinDirichletRankOne.memLp_exp
#print axioms Manuscript16.RobinDirichletRankOne.expVec_ae
#print axioms Manuscript16.RobinDirichletRankOne.inner_expVec_self
#print axioms Manuscript16.RobinDirichletRankOne.norm_expVec_sq
#print axioms Manuscript16.RobinDirichletRankOne.expVec_ne_zero
#print axioms Manuscript16.RobinDirichletRankOne.robinDiff_apply
#print axioms Manuscript16.RobinDirichletRankOne.robinDiff_isPositive
#print axioms Manuscript16.RobinDirichletRankOne.norm_robinDiff
#print axioms Manuscript16.RobinDirichletRankOne.range_robinDiff
#print axioms Manuscript16.RobinDirichletRankOne.finrank_range_robinDiff
#print axioms Manuscript16.RobinDirichletRankOne.robinDiff_diagonal_hasSum
#print axioms Manuscript16.RobinDirichletRankOne.exp_abs_sub_le
#print axioms Manuscript16.RobinDirichletRankOne.exp_add_le
#print axioms Manuscript16.RobinDirichletRankOne.memLp_of_bound
#print axioms Manuscript16.RobinDirichletRankOne.abs_greenD_le
#print axioms Manuscript16.RobinDirichletRankOne.abs_greenR_le
#print axioms Manuscript16.RobinDirichletRankOne.continuous_greenD
#print axioms Manuscript16.RobinDirichletRankOne.continuous_greenR
#print axioms Manuscript16.RobinDirichletRankOne.memLp_greenD
#print axioms Manuscript16.RobinDirichletRankOne.memLp_greenR
#print axioms Manuscript16.RobinDirichletRankOne.kR_sub_kD
#print axioms Manuscript16.RobinDirichletRankOne.kD_zero
#print axioms Manuscript16.RobinDirichletRankOne.KD_eq_integral
#print axioms Manuscript16.RobinDirichletRankOne.KR_eq_integral
#print axioms Manuscript16.RobinDirichletRankOne.KD_zero_left
#print axioms Manuscript16.RobinDirichletRankOne.KR_sub_KD
#print axioms Manuscript16.RobinDirichletRankOne.robinDiff_ae_eq
#print axioms Manuscript16.RobinDirichletRankOne.eq_exp_of_hasDerivWithinAt
#print axioms Manuscript16.RobinDirichletRankOne.bounded_solution_eq
#print axioms Manuscript16.RobinDirichletRankOne.dirichlet_uniqueness
#print axioms Manuscript16.RobinDirichletRankOne.robin_uniqueness
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_I1
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_I2
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_expneg
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_sinh_mul
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_cosh_mul
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_solD
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_solD'
#print axioms Manuscript16.RobinDirichletRankOne.solD_zero
#print axioms Manuscript16.RobinDirichletRankOne.solD'_zero
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_solR
#print axioms Manuscript16.RobinDirichletRankOne.hasDerivAt_solR'
#print axioms Manuscript16.RobinDirichletRankOne.solR_robin
#print axioms Manuscript16.RobinDirichletRankOne.integral_greenD_mul
#print axioms Manuscript16.RobinDirichletRankOne.integral_greenR_mul
#print axioms Manuscript16.RobinDirichletRankOne.inner_expVec_toLp
#print axioms Manuscript16.RobinDirichletRankOne.KD_toLp
#print axioms Manuscript16.RobinDirichletRankOne.KR_toLp
#print axioms Manuscript16.RobinDirichletRankOne.dirichlet_solution_unique
#print axioms Manuscript16.RobinDirichletRankOne.robin_solution_unique
#print axioms Manuscript16.RobinDirichletRankOne.lt_aOf
#print axioms Manuscript16.RobinDirichletRankOne.aOf_pos
#print axioms Manuscript16.RobinDirichletRankOne.aOf_sq
#print axioms Manuscript16.RobinDirichletRankOne.prop14_2
