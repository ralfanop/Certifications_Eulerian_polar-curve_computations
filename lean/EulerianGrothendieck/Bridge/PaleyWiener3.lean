import Bridge.PaleyWiener2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Theorem 3.10 (orthonormal basis in `L²(ℝ)`) and Corollary 3.11 (the projector `P_E`)

Under the cited Plancherel hypothesis:
* the map `g ↦ T g` is a bounded linear map `L²(-1/2,1/2] → L²(ℝ)` with `‖T g‖ = ‖g‖/√(2π)`;
* (52) the translates `φ_n` form an orthonormal family in `L²(ℝ)` and every `f ∈ PW_{1/2}`
  is the `L²(ℝ)`-sum `∑ ⟨φ_n, f⟩ φ_n`;
* (55) `PW_{1/2}` (the range) is closed; `P_E` is the orthogonal projector onto it,
  `P_E² = P_E = P_E*`, `‖P_E‖ = 1`, `(P_E f)(x) = (1/2π) ∫ r_E(x-y) f(y) dy`, and for
  `f ∈ L¹ ∩ L²`, `P_E f` has Fourier data `f̂` on `[-1/2,1/2]` (multiplier with symbol `1_{[-1/2,1/2]}`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate

namespace EulerianBridge.PW

open EulerianGrothendieck.Fock

abbrev L2R := ↥(Lp ℂ 2 (volume : Measure ℝ))

section Plancherel

variable (hP : Plancherel)
include hP

/-- `T g` as an element of `L²(ℝ)`. -/
noncomputable def Fv (g : GI) : L2R := (hP g).1.toLp (fun x : ℝ => T g x)

theorem Fv_coe (g : GI) : (Fv hP g : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => T g x := (hP g).1.coeFn_toLp

theorem Fv_add (g h : GI) : Fv hP (g + h) = Fv hP g + Fv hP h := by
  apply Lp.ext
  filter_upwards [Fv_coe hP (g + h), Fv_coe hP g, Fv_coe hP h, Lp.coeFn_add (Fv hP g) (Fv hP h)]
    with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3, T_add]

theorem Fv_smul (c : ℂ) (g : GI) : Fv hP (c • g) = c • Fv hP g := by
  apply Lp.ext
  filter_upwards [Fv_coe hP (c • g), Fv_coe hP g, Lp.coeFn_smul c (Fv hP g)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, T_smul, smul_eq_mul]

theorem inner_Fv (g h : GI) : (inner ℂ (Fv hP g) (Fv hP h) : ℂ) = (1 / (2 * Real.pi)) * inner ℂ g h := by
  rw [← (hP g).2 h, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Fv_coe hP g, Fv_coe hP h] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]; ring

theorem norm_Fv_sq (g : GI) : ‖Fv hP g‖ ^ 2 = (1 / (2 * Real.pi)) * ‖g‖ ^ 2 := by
  have h := congrArg Complex.re (inner_Fv hP g g)
  rw [show ((1 / (2 * Real.pi)) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul] at h
  rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
  exact h

theorem norm_Fv (g : GI) : ‖Fv hP g‖ = ‖g‖ / Real.sqrt (2 * Real.pi) := by
  have h := norm_Fv_sq hP g
  have hs : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [← Real.sqrt_sq (norm_nonneg (Fv hP g)), h, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _),
    one_div, Real.sqrt_inv, div_eq_mul_inv, mul_comm]

/-- The bounded linear map `T : L²(-1/2,1/2] → L²(ℝ)`. -/
noncomputable def FL : GI →L[ℂ] L2R :=
  LinearMap.mkContinuous
    { toFun := Fv hP, map_add' := Fv_add hP, map_smul' := Fv_smul hP } 1 (fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [norm_Fv hP]
      have h1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])
      exact div_le_self (norm_nonneg _) h1)

theorem FL_apply (g : GI) : FL hP g = Fv hP g := rfl

/-- The translates `φ_n` as elements of `L²(ℝ)`. -/
noncomputable def Φ (n : ℤ) : L2R := Fv hP ((Real.sqrt (2 * Real.pi) : ℂ) • fourierLp 2 (-n))

theorem Φ_coe (n : ℤ) : (Φ hP n : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => φ n x := by
  filter_upwards [Fv_coe hP ((Real.sqrt (2 * Real.pi) : ℂ) • fourierLp 2 (-n))] with x hx
  rw [Φ, hx, φ_eq_T]

/-- (52): the translates are orthonormal in `L²(ℝ)`. -/
theorem orthonormal_Φ : Orthonormal ℂ (Φ hP) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [Φ, Φ, inner_Fv, inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp orthonormal_fourier]
  have hss : (Real.sqrt (2 * Real.pi) : ℂ) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
  simp only [neg_inj, Complex.conj_ofReal]
  split_ifs
  · try simp only [mul_one]
    field_simp
    linear_combination hss
  · simp

/-- The coefficients: `⟨φ_n, f⟩ = √(2π) f(2πn)` for `f = T g`. -/
theorem inner_Φ (g : GI) (n : ℤ) :
    (inner ℂ (Φ hP n) (Fv hP g) : ℂ) = Real.sqrt (2 * Real.pi) * T g (2 * Real.pi * n) := by
  rw [Φ, inner_Fv, inner_smul_left, Complex.conj_ofReal, T_sample]
  have hss : (Real.sqrt (2 * Real.pi) : ℂ) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  ring

/-- (52): every `f ∈ PW_{1/2}` is the `L²(ℝ)` sum of its expansion in the translates. -/
theorem expansion (g : GI) : HasSum (fun n : ℤ => (inner ℂ (Φ hP n) (Fv hP g) : ℂ) • Φ hP n) (Fv hP g) := by
  have h := (hasSum_neg g).mapL (FL hP)
  convert h using 1
  funext n
  rw [map_smul, FL_apply, inner_Φ]
  rw [Φ, Fv_smul, smul_smul]
  congr 1
  have hs : T g (2 * Real.pi * n) = (1 / (2 * Real.pi)) * fourierCoeff g (-n) := by
    rw [T_sample, show (fourierLp 2 (-n) : GI) = fourierBasis (-n) by rw [coe_fourierBasis],
      ← fourierBasis.repr_apply_apply, fourierBasis_repr]
  rw [hs]
  have hss : (Real.sqrt (2 * Real.pi) : ℂ) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
  field_simp
  linear_combination (fourierCoeff g (-n)) * hss

/-! ## Corollary 3.11 -/

/-- `PW_{1/2} ⊂ L²(ℝ)`, the range of `T`. -/
noncomputable def PWsub : Submodule ℂ L2R := LinearMap.range (FL hP).toLinearMap

theorem PWsub_closed : IsClosed (PWsub hP : Set L2R) := by
  have hanti : AntilipschitzWith ⟨Real.sqrt (2 * Real.pi), Real.sqrt_nonneg _⟩ (FL hP) := by
    apply ContinuousLinearMap.antilipschitz_of_bound
    intro g
    rw [FL_apply, norm_Fv]
    have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    simp only [NNReal.coe_mk]
    rw [mul_div_cancel₀ _ hpos.ne']
  have := hanti.isClosed_range (FL hP).uniformContinuous
  simpa [PWsub] using this

instance : CompleteSpace (PWsub hP) := (PWsub_closed hP).completeSpace_coe

/-- The orthogonal projector `P_E : L²(ℝ) → PW_{1/2}` (eq. (55)). -/
noncomputable def PE : L2R →L[ℂ] L2R := (PWsub hP).starProjection

theorem PE_idem : IsIdempotentElem (PE hP) := (PWsub hP).isIdempotentElem_starProjection

theorem PE_selfAdjoint : IsSelfAdjoint (PE hP) := isSelfAdjoint_starProjection (PWsub hP)

theorem PWsub_ne_bot : PWsub hP ≠ ⊥ := by
  intro h
  have hmem : Φ hP 0 ∈ PWsub hP := ⟨_, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  have := (orthonormal_Φ hP).1 0
  rw [hmem, norm_zero] at this
  exact zero_ne_one this

theorem PE_norm : ‖PE hP‖ = 1 := (PWsub hP).norm_starProjection (PWsub_ne_bot hP)

omit hP in
theorem conj_KE_real (x y : ℝ) : conj (KE y x) = rE (x - y) / (2 * Real.pi) := by
  rw [KE_eq, Complex.conj_ofReal, map_div₀,
    show (y:ℂ) - x = ((y - x : ℝ) : ℂ) by push_cast; ring, rE_real_conj,
    show ((y - x : ℝ) : ℂ) = -((x:ℂ) - y) by push_cast; ring, EulerianBridge.Fock3.rE_neg]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal]

/-- (55): the convolution kernel of `P_E`. -/
theorem PE_kernel (f : L2R) :
    ∃ g : GI, PE hP f = Fv hP g ∧
      ∀ x : ℝ, T g x = (1 / (2 * Real.pi)) * ∫ y : ℝ, rE (x - y) * f y := by
  obtain ⟨g, hg⟩ : PE hP f ∈ PWsub hP := (PWsub hP).starProjection_apply_mem f
  refine ⟨g, hg.symm, fun x => ?_⟩
  have hrep := reproducing hP g x
  -- `∫ \overline{K_E(t,x)} T g t = ⟨T k_x, T g⟩ = ⟨T k_x, P f⟩ = ⟨P T k_x, f⟩ = ⟨T k_x, f⟩`
  have h1 : ∫ t : ℝ, conj (KE t x) * T g t = inner ℂ (Fv hP (kz x)) (Fv hP g) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Fv_coe hP (kz x), Fv_coe hP g] with t h1 h2
    rw [h1, h2, RCLike.inner_apply, KE_eq_T]; ring
  have hmem : Fv hP (kz x) ∈ PWsub hP := ⟨kz x, rfl⟩
  have h2 : (inner ℂ (Fv hP (kz x)) (Fv hP g) : ℂ) = inner ℂ (Fv hP (kz x)) f := by
    have hg' : Fv hP g = PE hP f := hg
    rw [hg', PE, ← Submodule.inner_starProjection_left_eq_right,
      (PWsub hP).starProjection_eq_self_iff.mpr hmem]
  have h3 : (inner ℂ (Fv hP (kz x)) f : ℂ) = ∫ y : ℝ, conj (KE y x) * f y := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Fv_coe hP (kz x)] with y hy
    rw [hy, RCLike.inner_apply, KE_eq_T]; ring
  rw [hrep, h1, h2, h3, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
  show conj (KE y x) * f y = 1 / (2 * Real.pi) * (rE (x - y) * f y)
  rw [conj_KE_real]; ring

end Plancherel

end EulerianBridge.PW
