import Mathlib
import Manuscript16.RobinDirichletRankOne20261125

/-!
# M16 v16.5 §14.2: the Robin pole at `a = β`, its residue and the eigenprojection

Source lock: `Manoscritto_16_5_Magnetic_Evanescent_Spectral_Transport_20261116(1).zip`,
SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`; analytic audit
`audits/Manuscript16_v16_5_RobinResolventRankOne_20261116.md` (Proposition 14.2, equations
(147)–(149)).  That note states, after the rank-one resolvent difference already certified in
`Manuscript16.RobinDirichletRankOne` (PR #603):

> The Robin resolvent has a simple pole at `a = β`, corresponding to `t = c − β²`.  The normalized
> eigenfunction is `√(2β) e^{−βz}`.  The pole residue in the spectral parameter `t` equals minus
> the eigenprojection.

Those three assertions were listed in #603 as *not claimed*.  They are the content of this file.

With `μ` = Lebesgue measure on `(0, ∞)`, `L2 = L²((0,∞); ℂ)`, `v_a(z) = e^{−az}` (`vvec a`, the
total extension of `expVec` of #603 by `0` for `a ≤ 0`) and
`P_a = (a−β)⁻¹ |v_a⟩⟨v_a|` (`robinDiffT a β`, the total extension of `robinDiff`):

* Exact two-parameter geometry of the exponential family: `inner_vvec`
  (`⟪v_a, v_b⟫ = 1/(a+b)`) and the exact distance `norm_vvec_sub_sq`
  (`‖v_a − v_b‖² = (a−b)²/(2ab(a+b))`), hence right continuity `tendsto_vvec` at `β`.
* The normalized eigenfunction: `eigFun β z = e^{−βz}` is twice differentiable with
  `−u'' + c u = (c − β²) u` (`eigFun_ode`) and satisfies the Robin condition
  `u'(0) = −β u(0)` (`hasDerivAt_eigFun_zero`); `eigVec = √(2β) v_β` is a unit vector of `L2`
  (`norm_eigVec`) whose class is `√(2β) e^{−βz}` (`eigVec_ae`).
* The eigenprojection `Q = |eigVec⟩⟨eigVec|` (`eigProj`): `IsStarProjection`
  (self-adjoint idempotent), positive, of norm one, fixing `eigVec`, with range the line
  `ℂ v_β` and rank one.
* The pole: `‖P_a‖ = 1/(2a(a−β)) → ∞` as `a ↓ β` (`tendsto_norm_robinDiffT`), and in the
  spectral parameter `t` with `a = √(c−t)` as `t ↑ c − β²`
  (`tendsto_norm_robinDiffT_spectral`).
* The residue: `(a − β) • P_a = |v_a⟩⟨v_a|` exactly (`smul_robinDiffT`) and
  `(a − β) • P_a → (2β)⁻¹ • Q` as `a ↓ β` (`tendsto_residue_param`); in the spectral parameter,
  `(t − (c − β²)) • P_{√(c−t)} → −Q` as `t ↑ c − β²` (`tendsto_residue_spectral`): the residue of
  the resolvent difference at the pole is **minus** the eigenprojection, which is the assertion of
  the audit note.  The simple-pole normalisation is quantitative, not merely a limit: the exact
  identity `smul_robinDiffT_spectral` gives `(t − (c−β²)) • P_{√(c−t)} = −(a+β) • |v_a⟩⟨v_a|`.
* `prop14_2_pole`: manuscript form with `c = ‖κ‖²`, `κ ∈ ℝ²`, `β > 0`, `t₀ = ‖κ‖² − β²`.

Quantitative continuity used for the limits: `norm_rankOne_self_sub`
(`‖|x⟩⟨x| − |y⟩⟨y|‖ ≤ ‖x−y‖(‖x‖+‖y‖)`) and `tendsto_rankOne_self`.

Not claimed here (as in #603): the self-adjoint Robin and Dirichlet realisations on the half-line
Sobolev space `H²(0,∞)` and the identification of the integral operators `K_D`, `K_R` with their
resolvents on all of `L²`; therefore `eigVec` is **not** asserted to be an eigenvector of an
operator realisation, and `eigProj` is **not** asserted to be a spectral projection of one: the
classical eigenvalue equation and the Robin boundary condition are proved for the function
`e^{−βz}`, and the residue statement is proved for the rank-one family `P_a` of #603.  Nothing
about Schatten ideals, the essential spectrum, or any Maxwell identification is claimed.
-/

namespace Manuscript16.RobinDirichletPole

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace

open Manuscript16.RobinDirichletRankOne

noncomputable section

variable {a b β : ℝ}

/-! ### The exponential family: exact inner products and exact distances -/

/-- `⟪v_a, v_b⟫ = ∫₀^∞ e^{−(a+b)w} dw = 1/(a+b)`. -/
theorem inner_expVec (ha : 0 < a) (hb : 0 < b) :
    ⟪expVec ha, expVec hb⟫ = (((a + b)⁻¹ : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have h1 : (∫ w, ⟪(expVec ha : ℝ → ℂ) w, (expVec hb : ℝ → ℂ) w⟫ ∂μ) =
      ∫ w, ((Real.exp (-(a + b) * w) : ℝ) : ℂ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [expVec_ae ha, expVec_ae hb] with w hw hw'
    rw [hw, hw', RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
  have hint : (∫ w, Real.exp (-(a + b) * w) ∂μ) = (a + b)⁻¹ := by
    rw [integral_exp_mul_Ioi (show -(a + b) < 0 by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    rw [neg_div_neg_eq, one_div]
  rw [h1, integral_complex_ofReal, hint]

/-- `v_a ∈ L²(0,∞)` as a total function of the parameter: `v_a` for `a > 0`, `0` otherwise. -/
def vvec (a : ℝ) : L2 := if h : 0 < a then expVec h else 0

theorem vvec_eq (ha : 0 < a) : vvec a = expVec ha := by
  unfold vvec
  exact dite_eq_iff.mpr (Or.inl ⟨ha, rfl⟩)

/-- The class of `v_β` in `L²(0,∞)` is the exponential `e^{−βw}`. -/
theorem vvec_ae (hβ : 0 < β) :
    (vvec β : ℝ → ℂ) =ᵐ[μ] fun w => ((Real.exp (-β * w) : ℝ) : ℂ) := by
  rw [vvec_eq hβ]; exact expVec_ae hβ

theorem inner_vvec (ha : 0 < a) (hb : 0 < b) :
    ⟪vvec a, vvec b⟫ = (((a + b)⁻¹ : ℝ) : ℂ) := by
  rw [vvec_eq ha, vvec_eq hb]; exact inner_expVec ha hb

theorem norm_vvec_sq (ha : 0 < a) : ‖vvec a‖ ^ 2 = (2 * a)⁻¹ := by
  rw [vvec_eq ha]; exact norm_expVec_sq ha

theorem vvec_ne_zero (ha : 0 < a) : vvec a ≠ 0 := by
  rw [vvec_eq ha]; exact expVec_ne_zero ha

/-- Exact squared distance inside the exponential family:
`‖v_a − v_b‖² = (a − b)²/(2ab(a+b))`. -/
theorem norm_vvec_sub_sq (ha : 0 < a) (hb : 0 < b) :
    ‖vvec a - vvec b‖ ^ 2 = (a - b) ^ 2 / (2 * a * b * (a + b)) := by
  have hre : RCLike.re (⟪vvec a, vvec b⟫ : ℂ) = (a + b)⁻¹ := by
    rw [inner_vvec ha hb]
    exact Complex.ofReal_re _
  rw [norm_sub_sq (𝕜 := ℂ), hre, norm_vvec_sq ha, norm_vvec_sq hb]
  have h1 : a ≠ 0 := ha.ne'
  have h2 : b ≠ 0 := hb.ne'
  have h3 : a + b ≠ 0 := by positivity
  field_simp
  ring

/-- Exact distance inside the exponential family. -/
theorem norm_vvec_sub (ha : 0 < a) (hb : 0 < b) :
    ‖vvec a - vvec b‖ = Real.sqrt ((a - b) ^ 2 / (2 * a * b * (a + b))) := by
  rw [← norm_vvec_sub_sq ha hb, Real.sqrt_sq (norm_nonneg _)]

/-- Right continuity of `a ↦ v_a` at `β > 0`. -/
theorem tendsto_vvec (hβ : 0 < β) : Tendsto vvec (𝓝[>] β) (𝓝 (vvec β)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hden : (0 : ℝ) < 2 * β * β * (β + β) := by positivity
  have hcont : ContinuousAt (fun x : ℝ => (x - β) ^ 2 / (2 * x * β * (x + β))) β := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact ne_of_gt hden
  have hzero : ((β - β) ^ 2 / (2 * β * β * (β + β))) = 0 := by
    simp
  have hsq : Tendsto (fun x : ℝ => Real.sqrt ((x - β) ^ 2 / (2 * x * β * (x + β))))
      (𝓝[>] β) (𝓝 0) := by
    have h := (Real.continuous_sqrt.continuousAt.comp hcont).tendsto
    rw [Function.comp_apply, hzero, Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun x => dist_nonneg) ?_ hsq
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [dist_eq_norm, norm_vvec_sub (hβ.trans hx) hβ]

/-! ### The normalized eigenfunction at the pole -/

/-- The classical eigenfunction at the pole: `u(z) = e^{−βz}`. -/
def eigFun (β z : ℝ) : ℝ := Real.exp (-β * z)

theorem hasDerivAt_eigFun (β z : ℝ) :
    HasDerivAt (eigFun β) (-β * Real.exp (-β * z)) z := by
  have h : HasDerivAt (fun z : ℝ => -β * z) (-β) z := by
    simpa using (hasDerivAt_id z).const_mul (-β)
  have h2 := h.exp
  unfold eigFun
  convert h2 using 1
  ring

theorem hasDerivAt_eigFun_deriv (β z : ℝ) :
    HasDerivAt (fun z : ℝ => -β * Real.exp (-β * z)) (β ^ 2 * Real.exp (-β * z)) z := by
  have h := (hasDerivAt_eigFun β z).const_mul (-β)
  unfold eigFun at h
  convert h using 1
  ring

/-- The eigenvalue equation `−u'' + c u = (c − β²) u` for `u = e^{−βz}`: at the pole the spectral
parameter is `t₀ = c − β²`. -/
theorem eigFun_ode (c β z : ℝ) :
    -(β ^ 2 * Real.exp (-β * z)) + c * eigFun β z = (c - β ^ 2) * eigFun β z := by
  unfold eigFun; ring

/-- The Robin boundary condition `u'(0) = −β u(0)` for `u = e^{−βz}`. -/
theorem hasDerivAt_eigFun_zero (β : ℝ) :
    HasDerivAt (eigFun β) (-β * eigFun β 0) 0 :=
  hasDerivAt_eigFun β 0

/-- The normalized eigenfunction `√(2β) e^{−βz}` as a vector of `L²(0,∞)`. -/
def eigVec (β : ℝ) : L2 := ((Real.sqrt (2 * β) : ℝ) : ℂ) • vvec β

theorem eigVec_ae (hβ : 0 < β) :
    (eigVec β : ℝ → ℂ) =ᵐ[μ] fun w => ((Real.sqrt (2 * β) * eigFun β w : ℝ) : ℂ) := by
  unfold eigVec eigFun
  have h := Lp.coeFn_smul (((Real.sqrt (2 * β) : ℝ) : ℂ)) (vvec β)
  filter_upwards [h, vvec_ae hβ] with w hw hw'
  rw [hw, Pi.smul_apply, hw', smul_eq_mul, Complex.ofReal_mul]

/-- `‖√(2β) v_β‖ = 1`. -/
theorem norm_eigVec (hβ : 0 < β) : ‖eigVec β‖ = 1 := by
  have h2 : ‖eigVec β‖ ^ 2 = 1 := by
    rw [eigVec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr (by positivity)), mul_pow,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * β), norm_vvec_sq hβ]
    field_simp
  have hnn : (0 : ℝ) ≤ ‖eigVec β‖ := norm_nonneg _
  nlinarith [h2, hnn]

theorem eigVec_ne_zero (hβ : 0 < β) : eigVec β ≠ 0 := by
  intro h
  have := norm_eigVec hβ
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The eigenprojection at the pole: `Q = |u_β⟩⟨u_β|` with `u_β = √(2β) e^{−βz}` normalized. -/
def eigProj (β : ℝ) : L2 →L[ℂ] L2 := rankOne ℂ (eigVec β) (eigVec β)

/-- `Q` is a self-adjoint idempotent: an orthogonal projection. -/
theorem eigProj_isStarProjection (hβ : 0 < β) : IsStarProjection (eigProj β) :=
  InnerProductSpace.isStarProjection_rankOne_self (norm_eigVec hβ)

theorem eigProj_isIdempotentElem (hβ : 0 < β) : IsIdempotentElem (eigProj β) :=
  InnerProductSpace.isIdempotentElem_rankOne_self (norm_eigVec hβ)

theorem eigProj_isPositive (β : ℝ) : (eigProj β).IsPositive :=
  InnerProductSpace.isPositive_rankOne_self _

theorem norm_eigProj (hβ : 0 < β) : ‖eigProj β‖ = 1 := by
  rw [eigProj, norm_rankOne, norm_eigVec hβ, mul_one]

/-- `Q u_β = u_β`: the normalized eigenfunction is fixed by the eigenprojection. -/
theorem eigProj_apply_eigVec (hβ : 0 < β) : eigProj β (eigVec β) = eigVec β := by
  rw [eigProj, rankOne_apply, inner_self_eq_norm_sq_to_K, norm_eigVec hβ]
  simp

theorem ofReal_sqrt_ne_zero (hβ : 0 < β) : ((Real.sqrt (2 * β) : ℝ) : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

/-- The range of `Q` is the line spanned by `v_β`, the class of `e^{−βz}`. -/
theorem range_eigProj (hβ : 0 < β) :
    LinearMap.range (eigProj β).toLinearMap = ℂ ∙ vvec β := by
  have hs := ofReal_sqrt_ne_zero hβ
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    refine Submodule.mem_span_singleton.mpr
      ⟨⟪eigVec β, f⟫ * ((Real.sqrt (2 * β) : ℝ) : ℂ), ?_⟩
    show _ = eigProj β f
    simp only [eigProj, eigVec, rankOne_apply, smul_smul]
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨(((Real.sqrt (2 * β) : ℝ) : ℂ))⁻¹ • eigVec β, ?_⟩
    show eigProj β _ = _
    rw [map_smul, eigProj_apply_eigVec hβ]
    simp only [eigVec, smul_smul]
    rw [inv_mul_cancel₀ hs, one_smul]

theorem finrank_range_eigProj (hβ : 0 < β) :
    Module.finrank ℂ (LinearMap.range (eigProj β).toLinearMap) = 1 := by
  rw [range_eigProj hβ]
  exact finrank_span_singleton (vvec_ne_zero hβ)

/-- `|v_β⟩⟨v_β| = (2β)⁻¹ Q`: the unnormalized rank-one operator is `(2β)⁻¹` times the
eigenprojection. -/
theorem rankOne_vvec_eq (hβ : 0 < β) :
    rankOne ℂ (vvec β) (vvec β) = (((2 * β)⁻¹ : ℝ) : ℂ) • eigProj β := by
  have h2β : (0 : ℝ) < 2 * β := by positivity
  have hkey : (((2 * β)⁻¹ : ℝ) : ℂ) * (((Real.sqrt (2 * β) : ℝ) : ℂ) *
      ((Real.sqrt (2 * β) : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt h2β.le,
      inv_mul_cancel₀ h2β.ne']
    norm_num
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [eigProj, eigVec, rankOne_apply, smul_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]
  congr 1
  calc ⟪vvec β, f⟫
      = ((((2 * β)⁻¹ : ℝ) : ℂ) * (((Real.sqrt (2 * β) : ℝ) : ℂ) *
          ((Real.sqrt (2 * β) : ℝ) : ℂ))) * ⟪vvec β, f⟫ := by rw [hkey, one_mul]
    _ = _ := by ring

/-! ### The operator family, the pole and the residue -/

/-- `P_a = (a−β)⁻¹ |v_a⟩⟨v_a|` as a total function of the parameters. -/
def robinDiffT (a β : ℝ) : L2 →L[ℂ] L2 :=
  (((a - β)⁻¹ : ℝ) : ℂ) • rankOne ℂ (vvec a) (vvec a)

theorem robinDiffT_eq (ha : 0 < a) (β : ℝ) : robinDiffT a β = robinDiff ha β := by
  rw [robinDiffT, robinDiff, vvec_eq ha]

theorem norm_robinDiffT (ha : 0 < a) (hab : β < a) :
    ‖robinDiffT a β‖ = (2 * a * (a - β))⁻¹ := by
  rw [robinDiffT_eq ha]; exact norm_robinDiff ha hab

/-- Exact simple-pole normalisation: `(a − β) P_a = |v_a⟩⟨v_a|`. -/
theorem smul_robinDiffT (hab : β < a) :
    (((a - β : ℝ)) : ℂ) • robinDiffT a β = rankOne ℂ (vvec a) (vvec a) := by
  rw [robinDiffT, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (by linarith : a - β ≠ 0)]
  simp

/-! #### Quantitative continuity of `x ↦ |x⟩⟨x|` -/

theorem rankOne_self_sub (x y : L2) :
    rankOne ℂ x x - rankOne ℂ y y = rankOne ℂ (x - y) x + rankOne ℂ y (x - y) := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [sub_apply, add_apply, rankOne_apply,
    inner_sub_left, sub_smul, smul_sub]
  abel

theorem norm_rankOne_self_sub (x y : L2) :
    ‖rankOne ℂ x x - rankOne ℂ y y‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  rw [rankOne_self_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_rankOne, norm_rankOne]
  exact le_of_eq (by ring)

theorem tendsto_rankOne_self {ι : Type*} {l : Filter ι} {g : ι → L2} {x : L2}
    (hg : Tendsto g l (𝓝 x)) :
    Tendsto (fun i => rankOne ℂ (g i) (g i)) l (𝓝 (rankOne ℂ x x)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun i => ‖g i - x‖) l (𝓝 0) := by
    simpa using (hg.sub (tendsto_const_nhds (x := x) (f := l))).norm
  have h2 : Tendsto (fun i => ‖g i‖ + ‖x‖) l (𝓝 (‖x‖ + ‖x‖)) :=
    hg.norm.add tendsto_const_nhds
  have h3 : Tendsto (fun i => ‖g i - x‖ * (‖g i‖ + ‖x‖)) l (𝓝 0) := by
    simpa using h1.mul h2
  refine squeeze_zero (fun i => dist_nonneg) (fun i => ?_) h3
  rw [dist_eq_norm]
  exact norm_rankOne_self_sub (g i) x

/-! #### The pole in the parameter `a` -/

/-- The norm of `P_a` blows up as `a ↓ β`: the Robin resolvent difference has a pole at `a = β`. -/
theorem tendsto_norm_robinDiffT (hβ : 0 < β) :
    Tendsto (fun a : ℝ => ‖robinDiffT a β‖) (𝓝[>] β) atTop := by
  have hg : Tendsto (fun a : ℝ => 2 * a * (a - β)) (𝓝[>] β) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun a : ℝ => 2 * a * (a - β)) := by fun_prop
      have h : Tendsto (fun a : ℝ => 2 * a * (a - β)) (𝓝[>] β) (𝓝 0) := by
        have h2 : Tendsto (fun a : ℝ => 2 * a * (a - β)) (𝓝 β) (𝓝 (2 * β * (β - β))) :=
          hc.tendsto β
        simpa using h2.mono_left (nhdsWithin_le_nhds (s := Ioi β))
      exact h
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simp only [mem_Ioi] at ha ⊢
      have h1 : (0 : ℝ) < a := hβ.trans ha
      have h2 : (0 : ℝ) < a - β := by linarith
      exact mul_pos (by linarith : (0 : ℝ) < 2 * a) h2
  have h := tendsto_inv_nhdsGT_zero.comp hg
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [Function.comp_apply]
  exact (norm_robinDiffT (hβ.trans ha) ha).symm

/-- Residue in the parameter `a`: `(a − β) P_a → (2β)⁻¹ Q` as `a ↓ β`. -/
theorem tendsto_residue_param (hβ : 0 < β) :
    Tendsto (fun a : ℝ => (((a - β : ℝ)) : ℂ) • robinDiffT a β) (𝓝[>] β)
      (𝓝 ((((2 * β)⁻¹ : ℝ) : ℂ) • eigProj β)) := by
  have h := tendsto_rankOne_self (g := vvec) (x := vvec β) (tendsto_vvec hβ)
  rw [rankOne_vvec_eq hβ] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (smul_robinDiffT ha).symm

/-! #### The pole in the spectral parameter `t`, `a = √(c − t)` -/

/-- `t ↦ √(c − t)` maps `t ↑ c − β²` to `a ↓ β`. -/
theorem tendsto_aOf (hβ : 0 < β) (c : ℝ) :
    Tendsto (aOf c) (𝓝[<] (c - β ^ 2)) (𝓝[>] β) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : Continuous (aOf c) := by
      unfold aOf; fun_prop
    have hv : aOf c (c - β ^ 2) = β := by
      unfold aOf
      rw [show c - (c - β ^ 2) = β ^ 2 by ring, Real.sqrt_sq hβ.le]
    have h : Tendsto (aOf c) (𝓝[<] (c - β ^ 2)) (𝓝 β) := by
      have h2 : Tendsto (aOf c) (𝓝 (c - β ^ 2)) (𝓝 (aOf c (c - β ^ 2))) :=
        hc.tendsto (c - β ^ 2)
      rw [hv] at h2
      exact h2.mono_left (nhdsWithin_le_nhds (s := Iio (c - β ^ 2)))
    exact h
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact lt_aOf hβ ht

/-- Exact residue identity in the spectral parameter: for `t < c − β²` and `a = √(c − t)`,
`(t − (c − β²)) P_a = −(a + β) |v_a⟩⟨v_a|`. -/
theorem smul_robinDiffT_spectral (hβ : 0 < β) {c t : ℝ} (ht : t < c - β ^ 2) :
    (((t - (c - β ^ 2) : ℝ)) : ℂ) • robinDiffT (aOf c t) β
      = (((-(aOf c t + β) : ℝ)) : ℂ) • rankOne ℂ (vvec (aOf c t)) (vvec (aOf c t)) := by
  have hab : β < aOf c t := lt_aOf hβ ht
  have hsq : aOf c t ^ 2 = c - t := aOf_sq ht
  have hne : aOf c t - β ≠ 0 := sub_ne_zero.mpr (by intro h; rw [h] at hab; exact absurd hab (lt_irrefl β))
  have hscalar : (t - (c - β ^ 2)) * (aOf c t - β)⁻¹ = -(aOf c t + β) := by
    have h : t - (c - β ^ 2) = -(aOf c t + β) * (aOf c t - β) := by linear_combination hsq
    rw [h, mul_inv_cancel_right₀ hne]
  rw [robinDiffT, smul_smul, ← Complex.ofReal_mul, hscalar]

/-- The norm blows up as `t ↑ c − β²`. -/
theorem tendsto_norm_robinDiffT_spectral (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun t : ℝ => ‖robinDiffT (aOf c t) β‖) (𝓝[<] (c - β ^ 2)) atTop :=
  (tendsto_norm_robinDiffT hβ).comp (tendsto_aOf hβ c)

/-- **Residue at the pole.** In the spectral parameter `t`, the residue of the Robin–Dirichlet
resolvent difference at `t₀ = c − β²` is minus the eigenprojection:
`(t − t₀) P_{√(c−t)} → −Q` as `t ↑ t₀`. -/
theorem tendsto_residue_spectral (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun t : ℝ => (((t - (c - β ^ 2) : ℝ)) : ℂ) • robinDiffT (aOf c t) β)
      (𝓝[<] (c - β ^ 2)) (𝓝 (-eigProj β)) := by
  have hscal : Tendsto (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ)) (𝓝[>] β)
      (𝓝 (((-(2 * β) : ℝ)) : ℂ)) := by
    have hc : Continuous (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ)) := by fun_prop
    have h2 : Tendsto (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ)) (𝓝 β) (𝓝 (((-(β + β) : ℝ)) : ℂ)) :=
      hc.tendsto β
    rw [show (-(β + β) : ℝ) = (-(2 * β) : ℝ) by ring] at h2
    exact h2.mono_left (nhdsWithin_le_nhds (s := Ioi β))
  have h1 : Tendsto (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ) • rankOne ℂ (vvec a) (vvec a))
      (𝓝[>] β) (𝓝 ((((-(2 * β)) : ℝ) : ℂ) • rankOne ℂ (vvec β) (vvec β))) :=
    hscal.smul (tendsto_rankOne_self (g := vvec) (x := vvec β) (tendsto_vvec hβ))
  have h2 : ((((-(2 * β)) : ℝ) : ℂ)) • rankOne ℂ (vvec β) (vvec β) = -eigProj β := by
    rw [rankOne_vvec_eq hβ, smul_smul, ← Complex.ofReal_mul]
    rw [show (-(2 * β) * (2 * β)⁻¹ : ℝ) = -1 by
      field_simp]
    simp
  rw [h2] at h1
  refine (h1.comp (tendsto_aOf hβ c)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (smul_robinDiffT_spectral hβ ht).symm

/-! ### Manuscript form -/

/-- Proposition 14.2, pole part, for `c = |κ|²`, `κ ∈ ℝ²`, `β > 0`, `t₀ = c − β²`:

1. the normalized eigenfunction `u_β = √(2β) e^{−βz}` is a unit vector of `L²(0,∞)` solving
   `−u'' + c u = t₀ u` classically with the Robin condition `u'(0) = −β u(0)`;
2. the eigenprojection `Q = |u_β⟩⟨u_β|` is an orthogonal projection of rank one and norm one;
3. `‖P_{√(c−t)}‖ → ∞` as `t ↑ t₀` (simple pole);
4. `(t − t₀) P_{√(c−t)} → −Q` as `t ↑ t₀`: the residue is minus the eigenprojection. -/
theorem prop14_2_pole {κ : EuclideanSpace ℝ (Fin 2)} (hβ : 0 < β) :
    ‖eigVec β‖ = 1 ∧
    (∀ z : ℝ, -(β ^ 2 * Real.exp (-β * z)) + ‖κ‖ ^ 2 * eigFun β z
      = (‖κ‖ ^ 2 - β ^ 2) * eigFun β z) ∧
    HasDerivAt (eigFun β) (-β * eigFun β 0) 0 ∧
    IsStarProjection (eigProj β) ∧
    Module.finrank ℂ (LinearMap.range (eigProj β).toLinearMap) = 1 ∧
    ‖eigProj β‖ = 1 ∧
    Tendsto (fun t : ℝ => ‖robinDiffT (aOf (‖κ‖ ^ 2) t) β‖)
      (𝓝[<] (‖κ‖ ^ 2 - β ^ 2)) atTop ∧
    Tendsto (fun t : ℝ => (((t - (‖κ‖ ^ 2 - β ^ 2) : ℝ)) : ℂ) • robinDiffT (aOf (‖κ‖ ^ 2) t) β)
      (𝓝[<] (‖κ‖ ^ 2 - β ^ 2)) (𝓝 (-eigProj β)) :=
  ⟨norm_eigVec hβ, fun z => eigFun_ode (‖κ‖ ^ 2) β z, hasDerivAt_eigFun_zero β,
    eigProj_isStarProjection hβ, finrank_range_eigProj hβ, norm_eigProj hβ,
    tendsto_norm_robinDiffT_spectral hβ _, tendsto_residue_spectral hβ _⟩

end

end Manuscript16.RobinDirichletPole

#print axioms Manuscript16.RobinDirichletPole.inner_expVec
#print axioms Manuscript16.RobinDirichletPole.vvec_eq
#print axioms Manuscript16.RobinDirichletPole.vvec_ae
#print axioms Manuscript16.RobinDirichletPole.inner_vvec
#print axioms Manuscript16.RobinDirichletPole.norm_vvec_sq
#print axioms Manuscript16.RobinDirichletPole.vvec_ne_zero
#print axioms Manuscript16.RobinDirichletPole.norm_vvec_sub_sq
#print axioms Manuscript16.RobinDirichletPole.norm_vvec_sub
#print axioms Manuscript16.RobinDirichletPole.tendsto_vvec
#print axioms Manuscript16.RobinDirichletPole.hasDerivAt_eigFun
#print axioms Manuscript16.RobinDirichletPole.hasDerivAt_eigFun_deriv
#print axioms Manuscript16.RobinDirichletPole.eigFun_ode
#print axioms Manuscript16.RobinDirichletPole.hasDerivAt_eigFun_zero
#print axioms Manuscript16.RobinDirichletPole.eigVec_ae
#print axioms Manuscript16.RobinDirichletPole.norm_eigVec
#print axioms Manuscript16.RobinDirichletPole.eigVec_ne_zero
#print axioms Manuscript16.RobinDirichletPole.eigProj_isStarProjection
#print axioms Manuscript16.RobinDirichletPole.eigProj_isIdempotentElem
#print axioms Manuscript16.RobinDirichletPole.eigProj_isPositive
#print axioms Manuscript16.RobinDirichletPole.norm_eigProj
#print axioms Manuscript16.RobinDirichletPole.eigProj_apply_eigVec
#print axioms Manuscript16.RobinDirichletPole.ofReal_sqrt_ne_zero
#print axioms Manuscript16.RobinDirichletPole.range_eigProj
#print axioms Manuscript16.RobinDirichletPole.finrank_range_eigProj
#print axioms Manuscript16.RobinDirichletPole.rankOne_vvec_eq
#print axioms Manuscript16.RobinDirichletPole.robinDiffT_eq
#print axioms Manuscript16.RobinDirichletPole.norm_robinDiffT
#print axioms Manuscript16.RobinDirichletPole.smul_robinDiffT
#print axioms Manuscript16.RobinDirichletPole.rankOne_self_sub
#print axioms Manuscript16.RobinDirichletPole.norm_rankOne_self_sub
#print axioms Manuscript16.RobinDirichletPole.tendsto_rankOne_self
#print axioms Manuscript16.RobinDirichletPole.tendsto_norm_robinDiffT
#print axioms Manuscript16.RobinDirichletPole.tendsto_residue_param
#print axioms Manuscript16.RobinDirichletPole.tendsto_aOf
#print axioms Manuscript16.RobinDirichletPole.smul_robinDiffT_spectral
#print axioms Manuscript16.RobinDirichletPole.tendsto_norm_robinDiffT_spectral
#print axioms Manuscript16.RobinDirichletPole.tendsto_residue_spectral
#print axioms Manuscript16.RobinDirichletPole.prop14_2_pole
