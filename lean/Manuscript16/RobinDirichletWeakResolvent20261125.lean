import Mathlib
import Manuscript16.RobinDirichletPositive20261125

/-!
# M16 v16.5 §14.2, Proposition 14.2: the Green operators invert `−d²/dz² + a²` on test functions

`Manuscript16.RobinDirichletRankOne20261125` (PR #603), `Manuscript16.RobinDirichletL2Bounded20261125`
(PR #605) and `Manuscript16.RobinDirichletPositive20261125` (PR #606) realise the Dirichlet and Robin
Green kernels of Proposition 14.2,

* `G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)`,
* `G_R(z,w) = (e^{−a|z−w|} + ((a+β)/(a−β)) e^{−a(z+w)})/(2a)`,

as bounded, positive, self-adjoint operators `KDop`, `KRop` on `L² = L²((0,∞); ℂ)`, and show that for
continuous data they produce the classical solutions of the two boundary problems.  They list as not
claimed the distributional identity `(−∂_z² + a²) G(·, w) = δ_w` with the boundary condition, and the
relation between `KDop`, `KRop` and the differential operator `−d²/dz² + a²` on **all** of `L²(0,∞)`.
This file proves both, on the following test functions.

A *test function* is a `C²` function `φ : ℝ → ℝ` with compact support (`IsTest`); `Hloc a φ` is
`−φ'' + a² φ`.  The Dirichlet core is `φ(0) = 0`; the Robin core is `φ'(0) = −β φ(0)`.

* Part A: `Hloc a φ` is continuous with compact support; `φ`, `Hloc a φ ∈ L²(0,∞)`.
* Part B: `0 ≤ G_D(z,w) ≤ 1/(2a)` on `[0,∞)²`, hence the classical solutions `u_D`, `u_R` of
  `−u'' + a² u = f` are bounded on `[0,∞)` for continuous `f ∈ L¹(0,∞)`.
* Part C (left inverse on the core): `K_D (−φ'' + a² φ) = φ` on `[0,∞)` for the Dirichlet core and
  `K_R (−φ'' + a² φ) = φ` for the Robin core (`β < a`), pointwise and in `L²(0,∞)`
  (`KDop_Hloc`, `KRop_Hloc`).
* Part D (distributional identity for the kernels): for every `w ≥ 0`,
  `∫₀^∞ G_D(z,w) (−φ''(z) + a² φ(z)) dz = φ(w)` on the Dirichlet core and the same with `G_R` on the
  Robin core: `(−∂_z² + a²) G(·,w) = δ_w` in the sense of distributions on `(0,∞)`, together with the
  boundary condition encoded by the core (`integral_greenD_Hloc`, `integral_greenR_Hloc`).
* Part E (weak resolvent identity on all of `L²(0,∞)`): for **every** `f ∈ L²(0,∞)`,
  `∫₀^∞ (−φ'' + a² φ)(z) (K_D f)(z) dz = ∫₀^∞ φ(z) f(z) dz` on the Dirichlet core and the same with
  `K_R` on the Robin core; equivalently `⟪(−d² + a²) φ, K f⟫ = ⟪φ, f⟫` in `L²(0,∞)`
  (`weak_KD`, `weak_KR`).  So `K_D f`, `K_R f` solve `−u'' + a² u = f` weakly, for every `f ∈ L²`.
* Manuscript form `prop14_2_weak_resolvent` (`c = ‖κ‖²`, `β > 0`, `t < c − β²`, `a = √(c − t)`,
  so that `−φ'' + a² φ = (−d²/dz² + c − t) φ`).

Not claimed: the self-adjoint realisations `H_D`, `H_R` on `H²(0,∞)` (no Sobolev space or trace
theorem is used), essential self-adjointness of `−d²/dz² + c` on the two cores, and hence the
identification `KDop = (H_D − t)⁻¹`, `KRop = (H_R − t)⁻¹` as resolvents of self-adjoint operators;
the essential spectrum; Schatten-ideal membership; any Maxwell or geometric identification.
-/

namespace Manuscript16.RobinDirichletWeakResolvent

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne Manuscript16.RobinDirichletL2Bounded
  Manuscript16.RobinDirichletPositive

noncomputable section

variable {a β : ℝ}

/-! ### Part A: test functions -/

/-- `(−d²/dz² + a²) φ`. -/
def Hloc (a : ℝ) (φ : ℝ → ℝ) (z : ℝ) : ℝ := -deriv (deriv φ) z + a ^ 2 * φ z

/-- Test functions: `C²` functions with compact support. -/
def IsTest (φ : ℝ → ℝ) : Prop := ContDiff ℝ 2 φ ∧ HasCompactSupport φ

theorem memLp_of_continuous_hasCompactSupport {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) : MemLp (fun z => (g z : ℂ)) 2 μ := by
  have hc : Continuous (fun z => (g z : ℂ)) := Complex.continuous_ofReal.comp hg
  have hcs : HasCompactSupport (fun z => (g z : ℂ)) := hs.comp_left Complex.ofReal_zero
  exact (hc.memLp_of_hasCompactSupport hcs).restrict _

theorem integrableOn_of_continuous_hasCompactSupport {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) : IntegrableOn g (Ioi 0) :=
  (hg.integrable_of_hasCompactSupport hs).integrableOn

theorem integrableOn_exp_mul (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) :
    IntegrableOn (fun w => Real.exp (-a * w) * g w) (Ioi 0) := by
  have hc : Continuous (fun w => Real.exp (-a * w) * g w) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hg
  have hcs : HasCompactSupport ((fun w => Real.exp (-a * w)) * g) := hs.mul_left
  exact integrableOn_of_continuous_hasCompactSupport hc hcs

namespace IsTest

variable {φ : ℝ → ℝ}

theorem differentiable (h : IsTest φ) : Differentiable ℝ φ :=
  h.1.differentiable (by norm_num)

theorem contDiff_deriv (h : IsTest φ) : ContDiff ℝ 1 (deriv φ) :=
  h.1.deriv' (n := 1)

theorem differentiable_deriv (h : IsTest φ) : Differentiable ℝ (deriv φ) :=
  h.contDiff_deriv.differentiable one_ne_zero

theorem continuous_deriv2 (h : IsTest φ) : Continuous (deriv (deriv φ)) :=
  h.contDiff_deriv.continuous_deriv le_rfl

theorem continuous (h : IsTest φ) : Continuous φ := h.1.continuous

theorem continuous_Hloc (h : IsTest φ) (a : ℝ) : Continuous (Hloc a φ) :=
  h.continuous_deriv2.neg.add (continuous_const.mul h.continuous)

theorem hasCompactSupport_Hloc (h : IsTest φ) (a : ℝ) : HasCompactSupport (Hloc a φ) := by
  have he : Hloc a φ = -deriv (deriv φ) + (fun _ => a ^ 2) * φ := by
    funext z
    simp [Hloc]
  rw [he]
  have h2 : HasCompactSupport ((fun _ => a ^ 2) * φ) := h.2.mul_left
  exact h.2.deriv.deriv.neg.add h2

theorem memLp (h : IsTest φ) : MemLp (fun z => (φ z : ℂ)) 2 μ :=
  memLp_of_continuous_hasCompactSupport h.continuous h.2

theorem memLp_Hloc (h : IsTest φ) (a : ℝ) : MemLp (fun z => (Hloc a φ z : ℂ)) 2 μ :=
  memLp_of_continuous_hasCompactSupport (h.continuous_Hloc a) (h.hasCompactSupport_Hloc a)

theorem integrableOn_Hloc (h : IsTest φ) (a : ℝ) : IntegrableOn (Hloc a φ) (Ioi 0) :=
  integrableOn_of_continuous_hasCompactSupport (h.continuous_Hloc a) (h.hasCompactSupport_Hloc a)

theorem integrableOn_exp_Hloc (h : IsTest φ) (a : ℝ) :
    IntegrableOn (fun w => Real.exp (-a * w) * Hloc a φ w) (Ioi 0) :=
  integrableOn_exp_mul a (h.continuous_Hloc a) (h.hasCompactSupport_Hloc a)

theorem bounded (h : IsTest φ) : ∃ M, ∀ z, 0 ≤ z → |φ z| ≤ M := by
  obtain ⟨C, hC⟩ := h.continuous.bounded_above_of_compact_support h.2
  exact ⟨C, fun z _ => by simpa [Real.norm_eq_abs] using hC z⟩

/-- The equation `(φ')' = a² φ − (−φ'' + a² φ)`. -/
theorem hasDerivWithinAt_deriv (h : IsTest φ) (a z : ℝ) :
    HasDerivWithinAt (deriv φ) (a ^ 2 * φ z - Hloc a φ z) (Ici 0) z := by
  have hd := (h.differentiable_deriv z).hasDerivAt.hasDerivWithinAt (s := Ici 0)
  convert hd using 1
  simp only [Hloc]
  ring

end IsTest

/-- The cores are not empty: a `C^∞` bump `φ` vanishing on `(−∞, 1)` with `φ(3) = 1` is a test
function satisfying both `φ(0) = 0` and `φ'(0) = −β φ(0)`. -/
theorem exists_test_mem_cores (β : ℝ) :
    ∃ φ : ℝ → ℝ, IsTest φ ∧ φ 0 = 0 ∧ deriv φ 0 = -β * φ 0 ∧ φ 3 = 1 := by
  let b : ContDiffBump (3 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hnear : (b : ℝ → ℝ) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with x hx
    apply b.zero_of_le_dist
    have hx' : x < 1 := hx
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    show (2:ℝ) ≤ -(x - 3)
    linarith
  have h0 : (b : ℝ → ℝ) 0 = 0 := hnear.self_of_nhds
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩, h0, ?_, ?_⟩
  · rw [hnear.deriv_eq, h0]
    simp
  · exact b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)

/-! ### Part B: the classical solutions are bounded on `[0,∞)` -/

/-- `|G_D(z,w)| ≤ 1/(2a)` for `z, w ≥ 0`. -/
theorem abs_greenD_le_inv (ha : 0 < a) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) :
    |greenD a z w| ≤ (2 * a)⁻¹ := by
  rw [abs_of_nonneg (greenD_nonneg ha hz hw)]
  refine (greenD_le ha z w).trans ?_
  have he : Real.exp (-a * |z - w|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (z - w)])
  rw [← one_div]
  exact div_le_div_of_nonneg_right he (by positivity)

/-- `|u_D(z)| ≤ (2a)⁻¹ ∫₀^∞ |f|` for `z ≥ 0`. -/
theorem abs_solD_le (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f)
    (hint : IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0))
    (hf1 : IntegrableOn f (Ioi 0)) {z : ℝ} (hz : 0 ≤ z) :
    |solD a f z| ≤ (2 * a)⁻¹ * ∫ w in Ioi 0, |f w| := by
  rw [← integral_greenD_mul ha hf hint hz, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hf1.abs.const_mul _) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_greenD_le_inv ha hz (le_of_lt hw)) (abs_nonneg _)

theorem bounded_solD (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f)
    (hint : IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0))
    (hf1 : IntegrableOn f (Ioi 0)) : ∃ M, ∀ z, 0 ≤ z → |solD a f z| ≤ M :=
  ⟨_, fun _ hz => abs_solD_le ha hf hint hf1 hz⟩

theorem bounded_solR (ha : 0 < a) {f : ℝ → ℝ} (hf : Continuous f)
    (hint : IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0))
    (hf1 : IntegrableOn f (Ioi 0)) : ∃ M, ∀ z, 0 ≤ z → |solR a β f z| ≤ M := by
  obtain ⟨M, hM⟩ := bounded_solD ha hf hint hf1
  refine ⟨M + |tailC a f / (a - β)|, fun z hz => ?_⟩
  have he : Real.exp (-a * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold solR
  refine (abs_add_le _ _).trans (add_le_add (hM z hz) ?_)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |tailC a f / (a - β)| * Real.exp (-a * z) ≤ |tailC a f / (a - β)| * 1 :=
        mul_le_mul_of_nonneg_left he (abs_nonneg _)
    _ = _ := mul_one _

/-! ### Part C: the Green operators are left inverses of `−d²/dz² + a²` on the cores -/

/-- Dirichlet core: `u_D[−φ'' + a² φ] = φ` on `[0,∞)`. -/
theorem solD_Hloc (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsTest φ) (hφ0 : φ 0 = 0) {z : ℝ}
    (hz : 0 ≤ z) : solD a (Hloc a φ) z = φ z :=
  (dirichlet_solution_unique ha (hφ.continuous_Hloc a) (v := φ) (v' := deriv φ)
    (fun z _ => (hφ.differentiable z).hasDerivAt.hasDerivWithinAt)
    (fun z _ => hφ.hasDerivWithinAt_deriv a z) hφ.bounded hφ0
    (bounded_solD ha (hφ.continuous_Hloc a) (hφ.integrableOn_exp_Hloc a)
      (hφ.integrableOn_Hloc a)) z hz).symm

/-- Robin core: `u_R[−φ'' + a² φ] = φ` on `[0,∞)` when `β < a`. -/
theorem solR_Hloc (ha : 0 < a) (hab : β < a) {φ : ℝ → ℝ} (hφ : IsTest φ)
    (hφR : deriv φ 0 = -β * φ 0) {z : ℝ} (hz : 0 ≤ z) : solR a β (Hloc a φ) z = φ z :=
  (robin_solution_unique ha hab (hφ.continuous_Hloc a) (v := φ) (v' := deriv φ)
    (fun z _ => (hφ.differentiable z).hasDerivAt.hasDerivWithinAt)
    (fun z _ => hφ.hasDerivWithinAt_deriv a z) hφ.bounded hφR
    (bounded_solR ha (hφ.continuous_Hloc a) (hφ.integrableOn_exp_Hloc a)
      (hφ.integrableOn_Hloc a)) z hz).symm

/-- `(K_D (−φ'' + a² φ))(z) = φ(z)` for every `z ≥ 0` (Dirichlet core). -/
theorem KD_Hloc (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsTest φ) (hφ0 : φ 0 = 0) {z : ℝ} (hz : 0 ≤ z) :
    KD ha ((hφ.memLp_Hloc a).toLp _) z = (φ z : ℂ) := by
  rw [KD_toLp ha (hφ.continuous_Hloc a) (hφ.memLp_Hloc a) (hφ.integrableOn_exp_Hloc a) hz,
    solD_Hloc ha hφ hφ0 hz]

/-- `(K_R (−φ'' + a² φ))(z) = φ(z)` for every `z ≥ 0` (Robin core, `β < a`). -/
theorem KR_Hloc (ha : 0 < a) (hab : β < a) {φ : ℝ → ℝ} (hφ : IsTest φ)
    (hφR : deriv φ 0 = -β * φ 0) {z : ℝ} (hz : 0 ≤ z) :
    KR ha β ((hφ.memLp_Hloc a).toLp _) z = (φ z : ℂ) := by
  rw [KR_toLp ha hab (hφ.continuous_Hloc a) (hφ.memLp_Hloc a) (hφ.integrableOn_exp_Hloc a) hz,
    solR_Hloc ha hab hφ hφR hz]

/-- `K_D (−φ'' + a² φ) = φ` in `L²(0,∞)` (Dirichlet core). -/
theorem KDop_Hloc (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsTest φ) (hφ0 : φ 0 = 0) :
    KDop ha ((hφ.memLp_Hloc a).toLp _) = hφ.memLp.toLp _ := by
  apply Lp.ext
  filter_upwards [KDop_ae_eq ha ((hφ.memLp_Hloc a).toLp _), hφ.memLp.coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with z h1 h2 hz
  rw [h1, h2, KD_Hloc ha hφ hφ0 (le_of_lt hz)]

/-- `K_R (−φ'' + a² φ) = φ` in `L²(0,∞)` (Robin core, `β < a`). -/
theorem KRop_Hloc (ha : 0 < a) (hab : β < a) {φ : ℝ → ℝ} (hφ : IsTest φ)
    (hφR : deriv φ 0 = -β * φ 0) :
    KRop ha β ((hφ.memLp_Hloc a).toLp _) = hφ.memLp.toLp _ := by
  apply Lp.ext
  filter_upwards [KRop_ae_eq ha hab ((hφ.memLp_Hloc a).toLp _), hφ.memLp.coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with z h1 h2 hz
  rw [h1, h2, KR_Hloc ha hab hφ hφR (le_of_lt hz)]

/-! ### Part D: `(−∂_z² + a²) G(·, w) = δ_w` on the cores -/

/-- Dirichlet kernel: `∫₀^∞ G_D(z,w) (−φ''(z) + a² φ(z)) dz = φ(w)` for every `w ≥ 0`. -/
theorem integral_greenD_Hloc (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsTest φ) (hφ0 : φ 0 = 0) {w : ℝ}
    (hw : 0 ≤ w) : ∫ z in Ioi 0, greenD a z w * Hloc a φ z = φ w := by
  have h := integral_greenD_mul ha (hφ.continuous_Hloc a) (hφ.integrableOn_exp_Hloc a) hw
  rw [solD_Hloc ha hφ hφ0 hw] at h
  rw [← h]
  congr 1
  funext z
  rw [greenD_symm]

/-- Robin kernel: `∫₀^∞ G_R(z,w) (−φ''(z) + a² φ(z)) dz = φ(w)` for every `w ≥ 0` (`β < a`). -/
theorem integral_greenR_Hloc (ha : 0 < a) (hab : β < a) {φ : ℝ → ℝ} (hφ : IsTest φ)
    (hφR : deriv φ 0 = -β * φ 0) {w : ℝ} (hw : 0 ≤ w) :
    ∫ z in Ioi 0, greenR a β z w * Hloc a φ z = φ w := by
  have h := integral_greenR_mul ha hab (hφ.continuous_Hloc a) (hφ.integrableOn_exp_Hloc a) hw
  rw [solR_Hloc ha hab hφ hφR hw] at h
  rw [← h]
  congr 1
  funext z
  rw [greenR_symm]

/-! ### Part E: weak resolvent identity for every `f ∈ L²(0,∞)` -/

/-- `⟪(−d² + a²) φ, K_D f⟫ = ⟪φ, f⟫` for every `f ∈ L²(0,∞)` (Dirichlet core). -/
theorem inner_Hloc_KDop (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsTest φ) (hφ0 : φ 0 = 0) (f : L2) :
    ⟪(hφ.memLp_Hloc a).toLp _, KDop ha f⟫ = ⟪hφ.memLp.toLp _, f⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, (KDop_isSelfAdjoint ha).adjoint_eq,
    KDop_Hloc ha hφ hφ0]

/-- `⟪(−d² + a²) φ, K_R f⟫ = ⟪φ, f⟫` for every `f ∈ L²(0,∞)` (Robin core, `β < a`). -/
theorem inner_Hloc_KRop (ha : 0 < a) (hab : β < a) {φ : ℝ → ℝ} (hφ : IsTest φ)
    (hφR : deriv φ 0 = -β * φ 0) (f : L2) :
    ⟪(hφ.memLp_Hloc a).toLp _, KRop ha β f⟫ = ⟪hφ.memLp.toLp _, f⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, (KRop_isSelfAdjoint ha hab).adjoint_eq,
    KRop_Hloc ha hab hφ hφR]

theorem inner_toLp_real {g : ℝ → ℝ} (hg : MemLp (fun z => (g z : ℂ)) 2 μ) (F : L2) :
    ⟪hg.toLp _, F⟫ = ∫ z in Ioi 0, (g z : ℂ) * F z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with z hz
  rw [hz, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- Weak form, Dirichlet: `∫₀^∞ (−φ'' + a² φ) (K_D f) = ∫₀^∞ φ f` for every `f ∈ L²(0,∞)`. -/
theorem weak_KD (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsTest φ) (hφ0 : φ 0 = 0) (f : L2) :
    ∫ z in Ioi 0, (Hloc a φ z : ℂ) * KD ha f z = ∫ z in Ioi 0, (φ z : ℂ) * f z := by
  have h := inner_Hloc_KDop ha hφ hφ0 f
  rw [inner_toLp_real, inner_toLp_real] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [KDop_ae_eq ha f] with z hz
  rw [hz]

/-- Weak form, Robin: `∫₀^∞ (−φ'' + a² φ) (K_R f) = ∫₀^∞ φ f` for every `f ∈ L²(0,∞)` (`β < a`). -/
theorem weak_KR (ha : 0 < a) (hab : β < a) {φ : ℝ → ℝ} (hφ : IsTest φ)
    (hφR : deriv φ 0 = -β * φ 0) (f : L2) :
    ∫ z in Ioi 0, (Hloc a φ z : ℂ) * KR ha β f z = ∫ z in Ioi 0, (φ z : ℂ) * f z := by
  have h := inner_Hloc_KRop ha hab hφ hφR f
  rw [inner_toLp_real, inner_toLp_real] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [KRop_ae_eq ha hab f] with z hz
  rw [hz]

/-! ### Manuscript form -/

/-- With `a = √(c − t)`, `−φ'' + a² φ = (−d²/dz² + c) φ − t φ`. -/
theorem Hloc_aOf {c t : ℝ} (ht : t < c - β ^ 2) (φ : ℝ → ℝ) (z : ℝ) :
    Hloc (aOf c t) φ z = -deriv (deriv φ) z + c * φ z - t * φ z := by
  rw [Hloc, aOf_sq ht]
  ring

/-- Proposition 14.2 (§14.2), weak resolvent form: with `c = ‖κ‖²`, `β > 0`, `t < c − β²` and
`a = √(c − t)`, for every `C²` test function `φ` with compact support,
`(−d²/dz² + c − t) φ = −φ'' + a² φ`, and

* if `φ(0) = 0`: `K_D (−φ'' + a² φ) = φ` in `L²(0,∞)`,
  `∫₀^∞ G_D(z,w) (−φ'' + a² φ)(z) dz = φ(w)` for `w ≥ 0`, and
  `∫₀^∞ (−φ'' + a² φ) (K_D f) = ∫₀^∞ φ f` for every `f ∈ L²(0,∞)`;
* if `φ'(0) = −β φ(0)`: the same three identities with `K_R`, `G_R`. -/
theorem prop14_2_weak_resolvent {κ : EuclideanSpace ℝ (Fin 2)} {t : ℝ} (hβ : 0 < β)
    (ht : t < ‖κ‖ ^ 2 - β ^ 2) {φ : ℝ → ℝ} (hφ : IsTest φ) :
    (∀ z, Hloc (aOf (‖κ‖ ^ 2) t) φ z = -deriv (deriv φ) z + ‖κ‖ ^ 2 * φ z - t * φ z) ∧
    (φ 0 = 0 →
      KDop (aOf_pos hβ ht) ((hφ.memLp_Hloc (aOf (‖κ‖ ^ 2) t)).toLp _) = hφ.memLp.toLp _ ∧
      (∀ w, 0 ≤ w →
        ∫ z in Ioi 0, greenD (aOf (‖κ‖ ^ 2) t) z w * Hloc (aOf (‖κ‖ ^ 2) t) φ z = φ w) ∧
      (∀ f : L2, ∫ z in Ioi 0, (Hloc (aOf (‖κ‖ ^ 2) t) φ z : ℂ) * KD (aOf_pos hβ ht) f z =
        ∫ z in Ioi 0, (φ z : ℂ) * f z)) ∧
    (deriv φ 0 = -β * φ 0 →
      KRop (aOf_pos hβ ht) β ((hφ.memLp_Hloc (aOf (‖κ‖ ^ 2) t)).toLp _) = hφ.memLp.toLp _ ∧
      (∀ w, 0 ≤ w →
        ∫ z in Ioi 0, greenR (aOf (‖κ‖ ^ 2) t) β z w * Hloc (aOf (‖κ‖ ^ 2) t) φ z = φ w) ∧
      (∀ f : L2, ∫ z in Ioi 0, (Hloc (aOf (‖κ‖ ^ 2) t) φ z : ℂ) * KR (aOf_pos hβ ht) β f z =
        ∫ z in Ioi 0, (φ z : ℂ) * f z)) := by
  have hab := lt_aOf hβ ht
  have ha := aOf_pos hβ ht
  exact ⟨fun z => Hloc_aOf ht φ z, fun hφ0 => ⟨KDop_Hloc ha hφ hφ0,
    fun w hw => integral_greenD_Hloc ha hφ hφ0 hw, weak_KD ha hφ hφ0⟩,
    fun hφR => ⟨KRop_Hloc ha hab hφ hφR, fun w hw => integral_greenR_Hloc ha hab hφ hφR hw,
    weak_KR ha hab hφ hφR⟩⟩

end

end Manuscript16.RobinDirichletWeakResolvent

#print axioms Manuscript16.RobinDirichletWeakResolvent.memLp_of_continuous_hasCompactSupport
#print axioms Manuscript16.RobinDirichletWeakResolvent.integrableOn_of_continuous_hasCompactSupport
#print axioms Manuscript16.RobinDirichletWeakResolvent.integrableOn_exp_mul
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.differentiable
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.contDiff_deriv
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.differentiable_deriv
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.continuous_deriv2
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.continuous
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.continuous_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.hasCompactSupport_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.memLp
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.memLp_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.integrableOn_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.integrableOn_exp_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.bounded
#print axioms Manuscript16.RobinDirichletWeakResolvent.IsTest.hasDerivWithinAt_deriv
#print axioms Manuscript16.RobinDirichletWeakResolvent.exists_test_mem_cores
#print axioms Manuscript16.RobinDirichletWeakResolvent.abs_greenD_le_inv
#print axioms Manuscript16.RobinDirichletWeakResolvent.abs_solD_le
#print axioms Manuscript16.RobinDirichletWeakResolvent.bounded_solD
#print axioms Manuscript16.RobinDirichletWeakResolvent.bounded_solR
#print axioms Manuscript16.RobinDirichletWeakResolvent.solD_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.solR_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.KD_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.KR_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.KDop_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.KRop_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.integral_greenD_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.integral_greenR_Hloc
#print axioms Manuscript16.RobinDirichletWeakResolvent.inner_Hloc_KDop
#print axioms Manuscript16.RobinDirichletWeakResolvent.inner_Hloc_KRop
#print axioms Manuscript16.RobinDirichletWeakResolvent.inner_toLp_real
#print axioms Manuscript16.RobinDirichletWeakResolvent.weak_KD
#print axioms Manuscript16.RobinDirichletWeakResolvent.weak_KR
#print axioms Manuscript16.RobinDirichletWeakResolvent.Hloc_aOf
#print axioms Manuscript16.RobinDirichletWeakResolvent.prop14_2_weak_resolvent
