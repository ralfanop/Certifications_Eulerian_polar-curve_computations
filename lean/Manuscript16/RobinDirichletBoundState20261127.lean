import Mathlib
import Manuscript16.RobinDirichletPole20261125
import Manuscript16.RobinDirichletLevelIndependence20261126

/-!
# M16 v16.5 §14.2, Proposition 14.2: the Robin bound state of the self-adjoint operator `H_R`

Setting of #603–#632: `c = |κ|²`, `β > 0`, `t₀ = c − β²`; for a level `t < t₀`, `a = √(c − t) > β`,
`K_D(a)`, `K_R(a) = K_D(a) + P_a` are the bounded Dirichlet and Robin Green operators on
`L²((0,∞); ℂ)` (#605), `H_D = t + K_D(a)⁻¹`, `H_R = t + K_R(a)⁻¹` the self-adjoint operators of #611,
independent of the level (#632).  `v_β(z) = e^{−βz}`, `u_β = √(2β) v_β` (unit vector) and
`Q = |u_β⟩⟨u_β|` (orthogonal projection of rank one) are those of #604.

#604 proved that `u_β` solves `−u'' + c u = t₀ u` classically with `u'(0) = −β u(0)` and that the
residue of `P_{√(c−t)}` at `t₀` is `−Q`, but it did not connect `u_β` and `Q` with the operator
`H_R` (register: "That `u_β` is an eigenvector of `H_R` and `Q` its spectral projection is not
claimed by any row").  This file proves:

* Part A (Green operators on `v_β`): for `0 < β < a`,
  `K_R(a) v_β = (a² − β²)⁻¹ v_β` (`KRop_vvec`, from the bounded classical Robin solution
  `e^{−βz}/(a² − β²)` and the uniqueness theorem of #603), `P_a v_β = (a² − β²)⁻¹ v_a`
  (`robinDiff_vvec`) and `K_D(a) v_β = (a² − β²)⁻¹ (v_β − v_a)` (`KDop_vvec`).
* Part B (eigenvector): `v_β`, hence `u_β`, lies in the domain of `H_R` and
  `H_R u_β = (t + a² − β²) u_β = t₀ u_β` (`HR_smul_vvec`, `HR_eigVec`).
* Part C (simplicity): if `u ∈ dom H_R` and `H_R u = t₀ u` then `u ∈ ℂ v_β`
  (`HR_eigen_mem_span`; `I − (a² − β²) K_D(a)` is injective because `‖K_D(a)‖ ≤ a⁻²`, and it maps
  `v_β` to `v_a` and every eigenvector to a multiple of `v_a`).  Hence
  `ker(H_R − t₀) = ℂ u_β = ran Q` (`HR_eigenspace`, `range_eigProj_eq_eigenspace`): `Q` is the
  orthogonal projection onto the eigenspace of `H_R` at `t₀`, which is one-dimensional.
* Part D (bottom of the spectrum): `H_R − λ` has a bounded two-sided inverse for every real
  `λ < t₀` (#632), so `H_R` has no eigenvalue `λ < t₀`; `H_D − λ` has a bounded two-sided inverse
  for every real `λ < c`, so `H_D` has no eigenvalue `λ < c` (`eq_zero_of_resolvent`).
* Part E (residue of the resolvent of `H_R`): `(t − t₀)(H_R − t)⁻¹ → −Q` in operator norm as
  `t ↑ t₀` (`tendsto_resolvent_residue`), with `(H_R − t)⁻¹ = K_R(√(c − t))`; the Dirichlet part
  `(t − t₀) K_D(√(c − t)) → 0` because `‖K_D(a)‖ ≤ a⁻² ≤ β⁻²`.
* Manuscript form `prop14_2_bound_state` on one fixed operator `H_R = t₁ + K_R(a₁)⁻¹`.

Published results cited, not re-proved: the identification of the orthogonal projection onto
`ker(H_R − t₀)` with the spectral projection `E_{H_R}({t₀})` of the spectral theorem for unbounded
self-adjoint operators (Mathlib has no unbounded spectral theorem at the pinned commit).

Not claimed: the resolvent of `H_R` for `t₀ < t < c` and the limit `t ↓ t₀`; that `t₀` is isolated in
`σ(H_R)` beyond the half-line `(−∞, t₀)`; the essential spectrum `[c, ∞)` of `H_D`, `H_R`;
identification of `H_D`, `H_R` with the `H²(0,∞)` realisations; essential self-adjointness on the
cores of #610; Schatten-ideal membership; any Maxwell identification; correspondence with the
printed Proposition 14.2 of `16.tex` (source not in the repository).
-/

namespace Manuscript16.RobinDirichletBoundState

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne Manuscript16.RobinDirichletL2Bounded
  Manuscript16.RobinDirichletPositive Manuscript16.RobinDirichletInjective
  Manuscript16.RobinDirichletRealisation Manuscript16.RobinDirichletLevelIndependence
  Manuscript16.RobinDirichletPole

noncomputable section

variable {a β : ℝ}

/-! ### Part A: the Green operators on `v_β = e^{−βz}` -/

theorem continuous_eigFun (β : ℝ) : Continuous (eigFun β) :=
  continuous_iff_continuousAt.mpr fun z => (hasDerivAt_eigFun β z).continuousAt

theorem memLp_eigFun (hβ : 0 < β) : MemLp (fun w => (eigFun β w : ℂ)) 2 μ :=
  memLp_exp hβ

theorem vvec_eq_toLp (hβ : 0 < β) : vvec β = (memLp_eigFun hβ).toLp _ := by
  rw [vvec_eq hβ]
  rfl

/-- `e^{−βz}/(a² − β²)` is the bounded classical Robin solution with datum `e^{−βz}` at level
`a > β`: `solR a β e^{−β·} = e^{−β·}/(a² − β²)` on `[0,∞)`. -/
theorem solR_eigFun (hβ : 0 < β) (ha : 0 < a) (hab : β < a) {z : ℝ} (hz : 0 ≤ z) :
    solR a β (eigFun β) z = eigFun β z / (a ^ 2 - β ^ 2) := by
  have hs : 0 < a ^ 2 - β ^ 2 := by nlinarith
  have hs' : a ^ 2 - β ^ 2 ≠ 0 := hs.ne'
  symm
  refine robin_solution_unique ha hab (continuous_eigFun β)
    (v := fun z => eigFun β z / (a ^ 2 - β ^ 2))
    (v' := fun z => -β * Real.exp (-β * z) / (a ^ 2 - β ^ 2)) ?_ ?_ ?_ ?_
    (solR_bounded ha hab (continuous_eigFun β) (memLp_eigFun hβ)) z hz
  · intro w _
    exact ((hasDerivAt_eigFun β w).div_const _).hasDerivWithinAt
  · intro w _
    have h := (hasDerivAt_eigFun_deriv β w).div_const (a ^ 2 - β ^ 2)
    convert h.hasDerivWithinAt using 1
    simp only [eigFun]
    field_simp
    ring
  · refine ⟨(a ^ 2 - β ^ 2)⁻¹, fun w hw => ?_⟩
    have h1 : Real.exp (-β * w) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    simp only [eigFun]
    rw [abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hs, div_eq_mul_inv]
    calc Real.exp (-β * w) * (a ^ 2 - β ^ 2)⁻¹ ≤ 1 * (a ^ 2 - β ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hs.le)
      _ = (a ^ 2 - β ^ 2)⁻¹ := one_mul _
  · simp only [eigFun, mul_zero, Real.exp_zero]
    ring

/-- **`K_R(a) v_β = (a² − β²)⁻¹ v_β`** for `0 < β < a`. -/
theorem KRop_vvec (hβ : 0 < β) (ha : 0 < a) (hab : β < a) :
    KRop ha β (vvec β) = (((a ^ 2 - β ^ 2)⁻¹ : ℝ) : ℂ) • vvec β := by
  have hL2 := memLp_eigFun hβ
  rw [vvec_eq_toLp hβ]
  apply Lp.ext
  filter_upwards [KRop_ae_eq ha hab (hL2.toLp _),
    Lp.coeFn_smul (((a ^ 2 - β ^ 2)⁻¹ : ℝ) : ℂ) (hL2.toLp _), hL2.coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with z h1 h2 h3 hz
  rw [h1, h2, Pi.smul_apply, h3,
    KR_toLp ha hab (continuous_eigFun β) hL2 (integrableOn_exp_mul ha hL2) (mem_Ioi.mp hz).le,
    solR_eigFun hβ ha hab (mem_Ioi.mp hz).le]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- `P_a v_β = (a² − β²)⁻¹ v_a` (for `a = β` both sides vanish with Lean's `0⁻¹ = 0`). -/
theorem robinDiff_vvec (hβ : 0 < β) (ha : 0 < a) :
    robinDiff ha β (vvec β) = (((a ^ 2 - β ^ 2)⁻¹ : ℝ) : ℂ) • vvec a := by
  rw [robinDiff_apply, ← vvec_eq ha, inner_vvec ha hβ, ← Complex.ofReal_mul]
  congr 2
  rw [← mul_inv, show (a - β) * (a + β) = a ^ 2 - β ^ 2 by ring]

/-- **`K_D(a) v_β = (a² − β²)⁻¹ (v_β − v_a)`** for `0 < β < a`, i.e.
`∫₀^∞ G_D(z,w) e^{−βw} dw = (e^{−βz} − e^{−az})/(a² − β²)`. -/
theorem KDop_vvec (hβ : 0 < β) (ha : 0 < a) (hab : β < a) :
    KDop ha (vvec β) = (((a ^ 2 - β ^ 2)⁻¹ : ℝ) : ℂ) • (vvec β - vvec a) := by
  have h3 : KRop ha β (vvec β) = KDop ha (vvec β) + robinDiff ha β (vvec β) := rfl
  rw [smul_sub, ← KRop_vvec hβ ha hab, ← robinDiff_vvec hβ ha, h3, add_sub_cancel_right]

/-! ### Part B: `u_β` is an eigenvector of `H_R` -/

/-- `K_R(a) ((a² − β²) c v_β) = c v_β`. -/
theorem KRop_smul_vvec (hβ : 0 < β) (ha : 0 < a) (hab : β < a) (c : ℂ) :
    KRop ha β (((a ^ 2 - β ^ 2 : ℝ) : ℂ) • (c • vvec β)) = c • vvec β := by
  have hs : ((a ^ 2 - β ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    nlinarith
  rw [map_smul, map_smul, KRop_vvec hβ ha hab, smul_smul, smul_smul]
  congr 1
  rw [Complex.ofReal_inv]
  generalize ((a ^ 2 - β ^ 2 : ℝ) : ℂ) = S at hs ⊢
  rw [mul_comm S c, mul_assoc, mul_inv_cancel₀ hs, mul_one]

/-- **`v_β ∈ dom H_R` and `H_R (c v_β) = (t + a² − β²) c v_β`** for every `c ∈ ℂ`, with
`H_R = t + K_R(a)⁻¹`. -/
theorem HR_smul_vvec (hβ : 0 < β) (ha : 0 < a) (hab : β < a) (t : ℝ) (c : ℂ) :
    ∃ h : c • vvec β ∈ (HR ha β t).domain,
      HR ha β t ⟨c • vvec β, h⟩ = ((t + (a ^ 2 - β ^ 2) : ℝ) : ℂ) • (c • vvec β) := by
  have hinj := KRop_injective ha hab
  have hK := KRop_smul_vvec hβ ha hab c
  have key : ∀ (x : L2) (hx : KRop ha β (((a ^ 2 - β ^ 2 : ℝ) : ℂ) • (c • vvec β)) = x)
      (h : x ∈ (HR ha β t).domain),
      HR ha β t ⟨x, h⟩ = ((a ^ 2 - β ^ 2 : ℝ) : ℂ) • (c • vvec β) + (t : ℂ) • x := by
    rintro x rfl h
    exact realisation_apply_K hinj _
  have hdom : c • vvec β ∈ (HR ha β t).domain := by
    rw [← hK]
    exact K_mem_domain hinj _
  refine ⟨hdom, ?_⟩
  rw [key _ hK, ← add_smul]
  congr 1
  push_cast
  ring

/-- **`H_R u_β = (t + a² − β²) u_β`**: the normalized `u_β = √(2β) e^{−βz}` is an eigenvector of
the self-adjoint `H_R = t + K_R(a)⁻¹`. -/
theorem HR_eigVec (hβ : 0 < β) (ha : 0 < a) (hab : β < a) (t : ℝ) :
    ∃ h : eigVec β ∈ (HR ha β t).domain,
      HR ha β t ⟨eigVec β, h⟩ = ((t + (a ^ 2 - β ^ 2) : ℝ) : ℂ) • eigVec β := by
  unfold eigVec
  exact HR_smul_vvec hβ ha hab t _

/-! ### Part C: the eigenvalue is simple and `Q` projects onto its eigenspace -/

/-- `x = s K_D(a) x` with `0 ≤ s < a²` forces `x = 0` (`‖K_D(a)‖ ≤ a⁻²`, #605). -/
theorem eq_zero_of_eq_smul_KDop (ha : 0 < a) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < a ^ 2) {x : L2}
    (hx : x = (s : ℂ) • KDop ha x) : x = 0 := by
  have hn : ‖x‖ ≤ s / a ^ 2 * ‖x‖ := by
    calc ‖x‖ = ‖(s : ℂ) • KDop ha x‖ := by rw [← hx]
      _ = s * ‖KDop ha x‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs0]
      _ ≤ s * ((a ^ 2)⁻¹ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((KDop ha).le_of_opNorm_le (norm_KDop_le ha) x) hs0
      _ = s / a ^ 2 * ‖x‖ := by ring
  have hq : s / a ^ 2 < 1 := by
    rw [div_lt_one (pow_pos ha 2)]
    exact hs
  have h0 : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
  exact norm_le_zero_iff.mp h0

/-- **Simplicity.** Every eigenvector of `H_R = t + K_R(a)⁻¹` with eigenvalue `t + a² − β²` is a
multiple of `v_β`. -/
theorem HR_eigen_mem_span (hβ : 0 < β) (ha : 0 < a) (hab : β < a) {t : ℝ}
    (u : (HR ha β t).domain)
    (hu : HR ha β t u = ((t + (a ^ 2 - β ^ 2) : ℝ) : ℂ) • (u : L2)) :
    (u : L2) ∈ ℂ ∙ vvec β := by
  have hinj := KRop_injective ha hab
  set s : ℝ := a ^ 2 - β ^ 2 with hs_def
  have hs0 : 0 ≤ s := by nlinarith
  have hsa : s < a ^ 2 := by nlinarith
  have h1 : KRop ha β ((s : ℂ) • (u : L2)) = u := by
    have h := K_realisation_sub (t := t) hinj u
    have h' : HR ha β t u - (t : ℂ) • (u : L2) = (s : ℂ) • (u : L2) := by
      rw [hu, ← sub_smul]
      congr 1
      push_cast
      ring
    rw [← h']
    exact h
  have h2 : KRop ha β ((s : ℂ) • vvec β) = vvec β := by
    have h := KRop_smul_vvec hβ ha hab 1
    rw [one_smul] at h
    exact h
  have hT : ∀ x : L2, KRop ha β ((s : ℂ) • x) = x →
      x - (s : ℂ) • KDop ha x =
        ((s : ℂ) * ((((a - β)⁻¹ : ℝ) : ℂ) * ⟪expVec ha, x⟫)) • expVec ha := by
    intro x hx
    have e : KRop ha β ((s : ℂ) • x) = (s : ℂ) • KDop ha x + (s : ℂ) • robinDiff ha β x := by
      rw [map_smul, show KRop ha β x = KDop ha x + robinDiff ha β x from rfl, smul_add]
    rw [robinDiff_apply, smul_smul] at e
    calc x - (s : ℂ) • KDop ha x = KRop ha β ((s : ℂ) • x) - (s : ℂ) • KDop ha x := by rw [hx]
      _ = _ := by rw [e, add_sub_cancel_left]
  have hu' := hT u h1
  have hv' := hT (vvec β) h2
  have hc2 : (s : ℂ) * ((((a - β)⁻¹ : ℝ) : ℂ) * ⟪expVec ha, vvec β⟫) = 1 := by
    have h3' : a ^ 2 - β ^ 2 ≠ 0 := by nlinarith
    rw [vvec_eq hβ, inner_expVec ha hβ, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_eq_one, hs_def, ← mul_inv, show (a - β) * (a + β) = a ^ 2 - β ^ 2 by ring]
    exact mul_inv_cancel₀ h3'
  rw [hc2, one_smul] at hv'
  set c₁ : ℂ := (s : ℂ) * ((((a - β)⁻¹ : ℝ) : ℂ) * ⟪expVec ha, (u : L2)⟫)
  have hx : (u : L2) - c₁ • vvec β = (s : ℂ) • KDop ha ((u : L2) - c₁ • vvec β) := by
    have e1 : (s : ℂ) • KDop ha (u : L2) = (u : L2) - c₁ • expVec ha := by
      rw [← hu']
      abel
    have e2 : (s : ℂ) • KDop ha (vvec β) = vvec β - expVec ha := by
      rw [← hv']
      abel
    rw [map_sub, map_smul, smul_sub, smul_comm (s : ℂ) c₁, e1, e2, smul_sub]
    abel
  have h0 := eq_zero_of_eq_smul_KDop ha hs0 hsa hx
  rw [sub_eq_zero] at h0
  rw [h0]
  exact Submodule.smul_mem _ c₁ (Submodule.mem_span_singleton_self (vvec β))

/-- **`ker(H_R − (t + a² − β²)) = ℂ v_β`.** -/
theorem HR_eigenspace (hβ : 0 < β) (ha : 0 < a) (hab : β < a) (t : ℝ) (x : L2) :
    x ∈ ℂ ∙ vvec β ↔ ∃ h : x ∈ (HR ha β t).domain,
      HR ha β t ⟨x, h⟩ = ((t + (a ^ 2 - β ^ 2) : ℝ) : ℂ) • x := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact HR_smul_vvec hβ ha hab t c
  · rintro ⟨h, hx⟩
    exact HR_eigen_mem_span hβ ha hab ⟨x, h⟩ hx

/-- **`ran Q = ker(H_R − (t + a² − β²))`**: the orthogonal projection `Q = |u_β⟩⟨u_β|` of #604
projects onto the eigenspace of `H_R`. -/
theorem range_eigProj_eq_eigenspace (hβ : 0 < β) (ha : 0 < a) (hab : β < a) (t : ℝ) (x : L2) :
    x ∈ LinearMap.range (eigProj β).toLinearMap ↔ ∃ h : x ∈ (HR ha β t).domain,
      HR ha β t ⟨x, h⟩ = ((t + (a ^ 2 - β ^ 2) : ℝ) : ℂ) • x := by
  rw [range_eigProj hβ]
  exact HR_eigenspace hβ ha hab t x

/-! ### Part D: no eigenvalue below the resolvent half-lines -/

/-- If `R (T u − λ u) = u` on the domain, `T` has no eigenvector with eigenvalue `λ`. -/
theorem eq_zero_of_resolvent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ.[ℂ] E} {R : E →L[ℂ] E} {lam : ℂ}
    (hR : ∀ u : T.domain, R (T u - lam • (u : E)) = u) (u : T.domain)
    (hu : T u = lam • (u : E)) : (u : E) = 0 := by
  rw [← hR u, hu, sub_self, map_zero]

/-! ### Part E: the residue of the resolvent of `H_R` at `t₀ = c − β²` -/

/-- `K_D(a)` as a total function of the parameter (`0` for `a ≤ 0`). -/
def KDopT (a : ℝ) : L2 →L[ℂ] L2 := if h : 0 < a then KDop h else 0

theorem KDopT_eq (ha : 0 < a) : KDopT a = KDop ha := by
  unfold KDopT
  exact dite_eq_iff.mpr (Or.inl ⟨ha, rfl⟩)

/-- `K_R(a) = K_D(a) + P_a` as a total function of the parameters. -/
def KRopT (a β : ℝ) : L2 →L[ℂ] L2 := KDopT a + robinDiffT a β

theorem KRopT_eq (ha : 0 < a) (β : ℝ) : KRopT a β = KRop ha β := by
  rw [KRopT, KDopT_eq ha, robinDiffT_eq ha]
  rfl

/-- `(t − t₀) K_D(√(c − t)) → 0` in operator norm as `t ↑ t₀ = c − β²`. -/
theorem tendsto_smul_KDopT_spectral (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun t : ℝ => (((t - (c - β ^ 2) : ℝ)) : ℂ) • KDopT (aOf c t))
      (𝓝[<] (c - β ^ 2)) (𝓝 0) := by
  have hcont : Continuous (fun t : ℝ => |t - (c - β ^ 2)| * (β ^ 2)⁻¹) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => |t - (c - β ^ 2)| * (β ^ 2)⁻¹) (𝓝[<] (c - β ^ 2)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto' _ _ (by simp))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hab : β < aOf c t := lt_aOf hβ ht
  have ha : 0 < aOf c t := hβ.trans hab
  rw [KDopT_eq ha, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc ‖KDop ha‖ ≤ (aOf c t ^ 2)⁻¹ := norm_KDop_le ha
    _ ≤ (β ^ 2)⁻¹ := inv_anti₀ (pow_pos hβ 2) (pow_le_pow_left₀ hβ.le hab.le 2)

/-- **Residue of the Robin resolvent.** `(t − t₀) K_R(√(c − t)) → −Q` in operator norm as
`t ↑ t₀ = c − β²`. -/
theorem tendsto_resolvent_residue (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun t : ℝ => (((t - (c - β ^ 2) : ℝ)) : ℂ) • KRopT (aOf c t) β)
      (𝓝[<] (c - β ^ 2)) (𝓝 (-eigProj β)) := by
  have h := (tendsto_smul_KDopT_spectral hβ c).add (tendsto_residue_spectral hβ c)
  rw [zero_add] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [KRopT, smul_add]

/-! ### Manuscript form -/

/-- **Proposition 14.2, bound state of `H_R`.**  With `c = ‖κ‖²`, `κ ∈ ℝ²`, `β > 0`,
`t₀ = c − β²`, a fixed level `t₁ < t₀`, `a₁ = √(c − t₁)` and the self-adjoint operators
`H_D = t₁ + K_D(a₁)⁻¹`, `H_R = t₁ + K_R(a₁)⁻¹` of #611 (independent of `t₁`, #632):

1. `u_β = √(2β) e^{−βz}` is a unit vector in `dom H_R` with `H_R u_β = t₀ u_β`;
2. `ran Q = ker(H_R − t₀)` for the orthogonal projection `Q = |u_β⟩⟨u_β|` of rank one: the
   eigenvalue `t₀` is simple and `Q` is the orthogonal projection onto its eigenspace;
3. `H_R` has no eigenvalue `λ < t₀`, and `H_D` has no eigenvalue `λ < c`;
4. for every `t < t₀`, `K_R(√(c − t))` is the two-sided inverse of `H_R − t` and maps
   `u_β` to `(t₀ − t)⁻¹ u_β`;
5. `(t − t₀)(H_R − t)⁻¹ = (t − t₀) K_R(√(c − t)) → −Q` in operator norm as `t ↑ t₀`. -/
theorem prop14_2_bound_state {κ : EuclideanSpace ℝ (Fin 2)} (hβ : 0 < β) {t₁ : ℝ}
    (ht₁ : t₁ < ‖κ‖ ^ 2 - β ^ 2) :
    IsSelfAdjoint (HR (aOf_pos hβ ht₁) β t₁) ∧
    ‖eigVec β‖ = 1 ∧
    (∃ h : eigVec β ∈ (HR (aOf_pos hβ ht₁) β t₁).domain,
      HR (aOf_pos hβ ht₁) β t₁ ⟨eigVec β, h⟩ = ((‖κ‖ ^ 2 - β ^ 2 : ℝ) : ℂ) • eigVec β) ∧
    IsStarProjection (eigProj β) ∧
    Module.finrank ℂ (LinearMap.range (eigProj β).toLinearMap) = 1 ∧
    (∀ x : L2, x ∈ LinearMap.range (eigProj β).toLinearMap ↔
      ∃ h : x ∈ (HR (aOf_pos hβ ht₁) β t₁).domain,
        HR (aOf_pos hβ ht₁) β t₁ ⟨x, h⟩ = ((‖κ‖ ^ 2 - β ^ 2 : ℝ) : ℂ) • x) ∧
    (∀ lam : ℝ, lam < ‖κ‖ ^ 2 - β ^ 2 → ∀ u : (HR (aOf_pos hβ ht₁) β t₁).domain,
      HR (aOf_pos hβ ht₁) β t₁ u = (lam : ℂ) • (u : L2) → (u : L2) = 0) ∧
    (∀ lam : ℝ, lam < ‖κ‖ ^ 2 → ∀ u : (HD (aOf_pos hβ ht₁) t₁).domain,
      HD (aOf_pos hβ ht₁) t₁ u = (lam : ℂ) • (u : L2) → (u : L2) = 0) ∧
    (∀ (t : ℝ) (ht : t < ‖κ‖ ^ 2 - β ^ 2),
      KRopT (aOf (‖κ‖ ^ 2) t) β = KRop (aOf_pos hβ ht) β ∧
      (∀ f : L2, ∃ h : KRopT (aOf (‖κ‖ ^ 2) t) β f ∈ (HR (aOf_pos hβ ht₁) β t₁).domain,
        HR (aOf_pos hβ ht₁) β t₁ ⟨KRopT (aOf (‖κ‖ ^ 2) t) β f, h⟩ -
          (t : ℂ) • KRopT (aOf (‖κ‖ ^ 2) t) β f = f) ∧
      (∀ u : (HR (aOf_pos hβ ht₁) β t₁).domain,
        KRopT (aOf (‖κ‖ ^ 2) t) β (HR (aOf_pos hβ ht₁) β t₁ u - (t : ℂ) • (u : L2)) = u) ∧
      KRopT (aOf (‖κ‖ ^ 2) t) β (eigVec β) =
        ((((‖κ‖ ^ 2 - β ^ 2) - t)⁻¹ : ℝ) : ℂ) • eigVec β) ∧
    Tendsto (fun t : ℝ => (((t - (‖κ‖ ^ 2 - β ^ 2) : ℝ)) : ℂ) • KRopT (aOf (‖κ‖ ^ 2) t) β)
      (𝓝[<] (‖κ‖ ^ 2 - β ^ 2)) (𝓝 (-eigProj β)) := by
  have ha₁ := aOf_pos hβ ht₁
  have hab₁ := lt_aOf hβ ht₁
  have hlev : t₁ + (aOf (‖κ‖ ^ 2) t₁ ^ 2 - β ^ 2) = ‖κ‖ ^ 2 - β ^ 2 := by
    rw [aOf_sq ht₁]
    ring
  have hindep := (prop14_2_level_independence (κ := κ) hβ ht₁).2.2
  refine ⟨HR_isSelfAdjoint ha₁ hab₁ t₁, norm_eigVec hβ, ?_, eigProj_isStarProjection hβ,
    finrank_range_eigProj hβ, ?_, ?_, ?_, ?_, tendsto_resolvent_residue hβ _⟩
  · have h := HR_eigVec hβ ha₁ hab₁ t₁
    rwa [hlev] at h
  · intro x
    have h := range_eigProj_eq_eigenspace hβ ha₁ hab₁ t₁ x
    rwa [hlev] at h
  · intro lam hlam u hu
    obtain ⟨-, -, -, -, -, hRinv, -⟩ := hindep lam hlam
    exact eq_zero_of_resolvent hRinv u hu
  · intro lam hlam u hu
    have hpos : 0 < ‖κ‖ ^ 2 - lam := by linarith
    have hb : 0 < Real.sqrt (‖κ‖ ^ 2 - lam) := Real.sqrt_pos.mpr hpos
    have hts : lam + Real.sqrt (‖κ‖ ^ 2 - lam) ^ 2 = t₁ + aOf (‖κ‖ ^ 2) t₁ ^ 2 := by
      rw [Real.sq_sqrt hpos.le, aOf_sq ht₁]
      ring
    obtain ⟨-, hDinv⟩ := resolvent_of_eq (KDop_injective hb) (HD_eq_of_level hb ha₁ hts)
    exact eq_zero_of_resolvent hDinv u hu
  · intro t ht
    have ha := aOf_pos hβ ht
    have hab := lt_aOf hβ ht
    obtain ⟨-, -, -, -, hR1, hR2, -⟩ := hindep t ht
    have hK : KRopT (aOf (‖κ‖ ^ 2) t) β = KRop ha β := KRopT_eq ha β
    refine ⟨hK, ?_, ?_, ?_⟩
    · rw [hK]
      exact hR1
    · rw [hK]
      exact hR2
    · have hs : aOf (‖κ‖ ^ 2) t ^ 2 - β ^ 2 = (‖κ‖ ^ 2 - β ^ 2) - t := by
        rw [aOf_sq ht]
        ring
      rw [hK, eigVec, map_smul, KRop_vvec hβ ha hab, hs, smul_comm]

end

end Manuscript16.RobinDirichletBoundState

#print axioms Manuscript16.RobinDirichletBoundState.continuous_eigFun
#print axioms Manuscript16.RobinDirichletBoundState.memLp_eigFun
#print axioms Manuscript16.RobinDirichletBoundState.vvec_eq_toLp
#print axioms Manuscript16.RobinDirichletBoundState.solR_eigFun
#print axioms Manuscript16.RobinDirichletBoundState.KRop_vvec
#print axioms Manuscript16.RobinDirichletBoundState.robinDiff_vvec
#print axioms Manuscript16.RobinDirichletBoundState.KDop_vvec
#print axioms Manuscript16.RobinDirichletBoundState.KRop_smul_vvec
#print axioms Manuscript16.RobinDirichletBoundState.HR_smul_vvec
#print axioms Manuscript16.RobinDirichletBoundState.HR_eigVec
#print axioms Manuscript16.RobinDirichletBoundState.eq_zero_of_eq_smul_KDop
#print axioms Manuscript16.RobinDirichletBoundState.HR_eigen_mem_span
#print axioms Manuscript16.RobinDirichletBoundState.HR_eigenspace
#print axioms Manuscript16.RobinDirichletBoundState.range_eigProj_eq_eigenspace
#print axioms Manuscript16.RobinDirichletBoundState.eq_zero_of_resolvent
#print axioms Manuscript16.RobinDirichletBoundState.KDopT
#print axioms Manuscript16.RobinDirichletBoundState.KDopT_eq
#print axioms Manuscript16.RobinDirichletBoundState.KRopT
#print axioms Manuscript16.RobinDirichletBoundState.KRopT_eq
#print axioms Manuscript16.RobinDirichletBoundState.tendsto_smul_KDopT_spectral
#print axioms Manuscript16.RobinDirichletBoundState.tendsto_resolvent_residue
#print axioms Manuscript16.RobinDirichletBoundState.prop14_2_bound_state
