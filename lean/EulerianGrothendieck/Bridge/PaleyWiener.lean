import EulerianGrothendieck.GaussianFockBridge
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Theorem 3.10: the Eulerian Paley–Wiener kernel and cardinal sampling

Manuscript V173, eqs. (22)–(27).

**Model.** `PW_{1/2}` is realised through its Fourier data: for `g ∈ L²(-1/2,1/2]` (here
`L²` of the unit additive circle `𝕋 = ℝ/ℤ`, identified with `(-1/2,1/2]` by the representative map
`rep`), the entire function
`(T g)(z) = (1/2π) ∫_{-1/2}^{1/2} g(ξ) e^{izξ} dξ` (eq. (23), with `ĝ = g` on `[-1/2,1/2]`).

**Cited input (Plancherel), as a hypothesis.** For `g, h ∈ L²(-1/2,1/2]`, `T g ∈ L²(ℝ)` and
`∫_ℝ \overline{T g} T h = (1/2π) ⟨g, h⟩`. This is the Plancherel theorem for the convention (22)
restricted to band-limited functions.

Proved from it (and from Mathlib's Fourier-series theory on `𝕋`):
* (24) `K_E(z,w) = (1/2π)∫ e^{i(z-w̄)ξ} dξ = r_E(z-w̄)/(2π)` and `f(w) = ⟨K_E(·,w), f⟩_{L²(ℝ)}`;
* (25) `‖r_E‖² = 2π`;
* (26) `{r_E(z-2πn)/√(2π)}` is orthonormal in `L²(ℝ)` and every `f ∈ PW` is the `L²(ℝ)` sum of its
  expansion;
* (27) `f(z) = ∑ f(2πn) r_E(z-2πn)` pointwise, uniformly on every strip `|Im z| ≤ R`, and
  `‖f‖² = 2π ∑ |f(2πn)|²`.
-/

open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped ComplexConjugate

namespace EulerianBridge.PW

open EulerianGrothendieck.Fock

local notation "𝕋" => UnitAddCircle

/-- Normalised Haar measure on `𝕋` (= Lebesgue measure on `(-1/2,1/2]`). -/
noncomputable abbrev μT : Measure 𝕋 := AddCircle.haarAddCircle

theorem μT_eq : μT = (volume : Measure 𝕋) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]; simp

/-- `L²(-1/2,1/2]`. -/
abbrev GI := ↥(Lp ℂ 2 μT)

/-! ## The representative map -/

/-- The representative of `θ ∈ 𝕋` in `(-1/2,1/2]`. -/
noncomputable def rep (θ : 𝕋) : ℝ := (AddCircle.equivIoc 1 (-1/2) θ : ℝ)

theorem rep_mem (θ : 𝕋) : rep θ ∈ Ioc (-1/2:ℝ) (1/2) := by
  obtain ⟨h1, h2⟩ := (AddCircle.equivIoc 1 (-1/2) θ).2
  exact ⟨h1, by unfold rep; linarith⟩

theorem coe_rep (θ : 𝕋) : ((rep θ : ℝ) : 𝕋) = θ :=
  (AddCircle.equivIoc 1 (-1/2)).symm_apply_apply θ

theorem rep_coe {x : ℝ} (hx : x ∈ Ioc (-1/2:ℝ) (1/2)) : rep (x : 𝕋) = x := by
  have hx' : x ∈ Ioc (-1/2:ℝ) (-1/2 + 1) := by rw [show (-1/2:ℝ) + 1 = 1/2 by norm_num]; exact hx
  have : (AddCircle.equivIoc 1 (-1/2)) x = ⟨x, hx'⟩ := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]; rfl
  unfold rep; rw [this]

theorem measurable_rep : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 (-1/2)).measurable

theorem abs_rep_le (θ : 𝕋) : |rep θ| ≤ 1 / 2 := by
  have h := rep_mem θ; rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-- Transport of integrals: `∫_𝕋 h(rep θ) dθ = ∫_{-1/2}^{1/2} h`. -/
theorem integral_rep (h : ℝ → ℂ) : ∫ θ, h (rep θ) ∂μT = ∫ ξ in (-1/2:ℝ)..(1/2), h ξ := by
  rw [μT_eq, ← UnitAddCircle.intervalIntegral_preimage (-1/2) (fun θ => h (rep θ)),
    show (-1/2:ℝ) + 1 = 1/2 by norm_num]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall (fun x hx => ?_))
  rw [uIoc_of_le (by norm_num)] at hx
  rw [rep_coe hx]

theorem fourier_rep (n : ℤ) (θ : 𝕋) : fourier n θ = cexp (2 * Real.pi * I * n * rep θ) := by
  conv_lhs => rw [← coe_rep θ]
  rw [fourier_coe_apply]; simp

/-! ## The vectors `k_z(θ) = e^{-i z̄ rep θ}` and the transform `T` -/

theorem norm_exp_rep_le (z : ℂ) (θ : 𝕋) : ‖cexp (-(I * conj z * rep θ))‖ ≤ Real.exp (|z.im| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (-(I * conj z * (rep θ : ℂ))).re = -(z.im * rep θ) := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [hre]
  calc -(z.im * rep θ) ≤ |z.im * rep θ| := neg_le_abs _
    _ = |z.im| * |rep θ| := abs_mul _ _
    _ ≤ |z.im| * (1 / 2) := mul_le_mul_of_nonneg_left (abs_rep_le θ) (abs_nonneg _)
    _ = |z.im| / 2 := by ring

theorem memLp_kz (z : ℂ) : MemLp (fun θ : 𝕋 => cexp (-(I * conj z * rep θ))) 2 μT := by
  refine MemLp.of_bound (C := Real.exp (|z.im| / 2)) ?_ (Eventually.of_forall (norm_exp_rep_le z))
  exact (Continuous.measurable (by fun_prop : Continuous fun x : ℝ => cexp (-(I * conj z * x)))).comp
    measurable_rep |>.aestronglyMeasurable

/-- `k_z ∈ L²(𝕋)`. -/
noncomputable def kz (z : ℂ) : GI := (memLp_kz z).toLp _

/-- `(T g)(z) = (1/2π) ⟨k_z, g⟩ = (1/2π) ∫ e^{iz rep θ} g(θ) dθ`. -/
noncomputable def T (g : GI) (z : ℂ) : ℂ := (1 / (2 * Real.pi)) * inner ℂ (kz z) g

theorem T_eq_integral (g : GI) (z : ℂ) :
    T g z = (1 / (2 * Real.pi)) * ∫ θ, cexp (I * z * rep θ) * g θ ∂μT := by
  unfold T
  congr 1
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_kz z).coeFn_toLp] with θ hθ
  rw [kz, hθ, RCLike.inner_apply, ← Complex.exp_conj]
  have : conj (-(I * conj z * ((rep θ : ℝ) : ℂ))) = I * z * rep θ := by
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]; ring
  rw [this]; ring

theorem T_add (g h : GI) (z : ℂ) : T (g + h) z = T g z + T h z := by
  unfold T; rw [inner_add_right]; ring

theorem T_smul (c : ℂ) (g : GI) (z : ℂ) : T (c • g) z = c * T g z := by
  unfold T; rw [inner_smul_right]; ring

theorem norm_kz_le (z : ℂ) : ‖kz z‖ ≤ Real.exp (|z.im| / 2) := by
  have hC : 0 ≤ Real.exp (|z.im| / 2) := (Real.exp_pos _).le
  rw [kz]
  refine (Lp.norm_le_of_ae_bound hC ?_).trans ?_
  · filter_upwards [(memLp_kz z).coeFn_toLp] with θ hθ
    rw [hθ]; exact norm_exp_rep_le z θ
  · simp [measureUnivNNReal]

theorem norm_T_le (g : GI) (z : ℂ) : ‖T g z‖ ≤ (1 / (2 * Real.pi)) * Real.exp (|z.im| / 2) * ‖g‖ := by
  unfold T
  rw [norm_mul, show ((1 / (2 * Real.pi)) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), mul_assoc]
  gcongr
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_kz_le z) (norm_nonneg _))

/-! ## The Plancherel hypothesis -/

/-- Plancherel for band-limited functions (cited input). -/
def Plancherel : Prop :=
  ∀ g : GI, MemLp (fun x : ℝ => T g x) 2 volume ∧
    ∀ h : GI, ∫ x : ℝ, conj (T g x) * T h x = (1 / (2 * Real.pi)) * inner ℂ g h

/-! ## `r_E`, the kernel and the translates as transforms -/

/-- The constant function `1 ∈ L²(𝕋)`. -/
noncomputable def one : GI := (memLp_const (1:ℂ)).toLp _

/-- `T` of a function of `rep`. -/
theorem T_rep (h : ℝ → ℂ) (hm : MemLp (fun θ => h (rep θ)) 2 μT) (z : ℂ) :
    T (hm.toLp _) z = (1 / (2 * Real.pi)) * ∫ ξ in (-1/2:ℝ)..(1/2), cexp (I * z * ξ) * h ξ := by
  rw [T_eq_integral]
  congr 1
  rw [← integral_rep (fun ξ => cexp (I * z * ξ) * h ξ)]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp] with θ hθ
  rw [hθ]

theorem T_one (z : ℂ) : T one z = rE z / (2 * Real.pi) := by
  rw [T_eq_integral]
  have h : ∫ θ, cexp (I * z * rep θ) * (one : GI) θ ∂μT = ∫ θ, (fun ξ : ℝ => cexp (I * z * ξ)) (rep θ) ∂μT := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [(memLp_const (1:ℂ) : MemLp (fun _ : 𝕋 => (1:ℂ)) 2 μT).coeFn_toLp] with θ hθ
    rw [one, hθ, mul_one]
  rw [h, integral_rep (fun ξ : ℝ => cexp (I * z * ξ))]
  unfold rE
  rw [mul_comm, ← div_eq_mul_one_div]
  congr 1
  refine intervalIntegral.integral_congr (fun ξ _ => ?_)
  beta_reduce; ring_nf

/-- `r_E = T(2π · 1)`, so `r_E ∈ PW_{1/2}` (Theorem 3.10). -/
theorem rE_eq_T (z : ℂ) : rE z = T ((2 * Real.pi : ℂ) • one) z := by
  rw [T_smul, T_one]
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
  field_simp

/-- The Paley–Wiener kernel (24). -/
noncomputable def KE (z w : ℂ) : ℂ := (1 / (2 * Real.pi)) * ∫ ξ in (-1/2:ℝ)..(1/2), cexp (I * (z - conj w) * ξ)

theorem KE_eq (z w : ℂ) : KE z w = rE (z - conj w) / (2 * Real.pi) := by
  unfold KE rE
  rw [mul_comm, ← div_eq_mul_one_div]
  congr 1
  refine intervalIntegral.integral_congr (fun ξ _ => ?_)
  beta_reduce; ring_nf

/-- `K_E(·,w) = T(k_w)`. -/
theorem KE_eq_T (z w : ℂ) : KE z w = T (kz w) z := by
  rw [kz, T_rep (fun ξ => cexp (-(I * conj w * ξ)))]
  unfold KE
  congr 1
  refine intervalIntegral.integral_congr (fun ξ _ => ?_)
  beta_reduce
  rw [← Complex.exp_add]; congr 1; ring

/-- The translates `φ_n(z) = r_E(z - 2πn)/√(2π)`. -/
noncomputable def φ (n : ℤ) (z : ℂ) : ℂ := rE (z - 2 * Real.pi * n) / Real.sqrt (2 * Real.pi)

/-- `T(e_m)(z) = r_E(z + 2πm)/(2π)` for the Fourier basis `e_m`. -/
theorem T_fourier (m : ℤ) (z : ℂ) : T (fourierLp 2 m) z = rE (z + 2 * Real.pi * m) / (2 * Real.pi) := by
  rw [T_eq_integral]
  have h : ∫ θ, cexp (I * z * rep θ) * (fourierLp 2 m : GI) θ ∂μT
      = ∫ θ, (fun ξ : ℝ => cexp (I * z * ξ) * cexp (2 * Real.pi * I * m * ξ)) (rep θ) ∂μT := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fourierLp 2 m] with θ hθ
    rw [hθ, fourier_rep]
  rw [h, integral_rep (fun ξ : ℝ => cexp (I * z * ξ) * cexp (2 * Real.pi * I * m * ξ))]
  unfold rE
  rw [mul_comm, ← div_eq_mul_one_div]
  congr 1
  refine intervalIntegral.integral_congr (fun ξ _ => ?_)
  beta_reduce
  rw [← Complex.exp_add]; congr 1; ring

/-- `φ_n = T(√(2π) e_{-n})`. -/
theorem φ_eq_T (n : ℤ) (z : ℂ) : φ n z = T ((Real.sqrt (2 * Real.pi) : ℂ) • fourierLp 2 (-n)) z := by
  rw [T_smul, T_fourier]
  unfold φ
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hss : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hs' : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hss' : (Real.sqrt (2 * Real.pi) : ℂ) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
    exact_mod_cast hss
  push_cast
  rw [show z + 2 * (Real.pi : ℂ) * (-(n : ℂ)) = z - 2 * Real.pi * n by ring]
  rw [← hss']
  field_simp

/-- The point values `f(2πn) = (1/2π) ⟨e_{-n}, g⟩` for `f = T g`. -/
theorem T_sample (g : GI) (n : ℤ) :
    T g (2 * Real.pi * n) = (1 / (2 * Real.pi)) * inner ℂ (fourierLp 2 (-n) : GI) g := by
  unfold T
  congr 2
  rw [kz]
  apply Lp.ext
  filter_upwards [(memLp_kz (2 * Real.pi * n)).coeFn_toLp, coeFn_fourierLp 2 (-n)] with θ h1 h2
  rw [h1, h2, fourier_rep]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, map_intCast]
  push_cast; ring

/-! ## Theorem 3.10 -/

section Plancherel

variable (hP : Plancherel)
include hP

/-- (24) reproducing property: `f(w) = ∫_ℝ \overline{K_E(x,w)} f(x) dx` for `f = T g`. -/
theorem reproducing (g : GI) (w : ℂ) :
    T g w = ∫ x : ℝ, conj (KE x w) * T g x := by
  simp_rw [KE_eq_T]
  rw [(hP (kz w)).2 g]
  rfl

/-- (25): `‖r_E‖²_{L²(ℝ)} = 2π`. -/
theorem norm_rE_sq : ∫ x : ℝ, ‖rE x‖ ^ 2 = 2 * Real.pi := by
  have h := (hP ((2 * Real.pi : ℂ) • one)).2 ((2 * Real.pi : ℂ) • one)
  simp_rw [← rE_eq_T] at h
  rw [inner_smul_left, inner_smul_right, one] at h
  have h1 : (inner ℂ ((memLp_const (1:ℂ)).toLp (fun _ : 𝕋 => (1:ℂ)) : GI)
      ((memLp_const (1:ℂ)).toLp (fun _ : 𝕋 => (1:ℂ))) : ℂ) = 1 := by
    rw [L2.inner_def]
    rw [MeasureTheory.integral_congr_ae (g := fun _ => (1:ℂ)) ?_]
    · simp
    filter_upwards [(memLp_const (1:ℂ) : MemLp (fun _ : 𝕋 => (1:ℂ)) 2 μT).coeFn_toLp] with θ hθ
    rw [hθ]; simp
  rw [h1] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ x : ℝ, ((‖rE x‖ ^ 2 : ℝ) : ℂ) = conj (rE x) * rE x := by
    intro x; rw [Complex.conj_mul']; push_cast; ring
  simp_rw [e]
  rw [h]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [Complex.conj_ofReal, map_ofNat]
  field_simp

/-- (26), orthonormality of the translates in `L²(ℝ)`. -/
theorem orthonormal_φ (m n : ℤ) :
    ∫ x : ℝ, conj (φ m x) * φ n x = if m = n then 1 else 0 := by
  simp_rw [φ_eq_T]
  rw [(hP _).2, inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp orthonormal_fourier]
  have hss : (Real.sqrt (2 * Real.pi) : ℂ) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
  simp only [neg_inj, Complex.conj_ofReal]
  split_ifs
  · try simp only [mul_one]
    rw [hss]; field_simp
  · simp

omit hP in
/-- (27a): cardinal series, pointwise. -/
theorem sampling (g : GI) (z : ℂ) :
    HasSum (fun n : ℤ => T g (2 * Real.pi * n) * rE (z - 2 * Real.pi * n)) (T g z) := by
  let L : GI →L[ℂ] ℂ := (1 / (2 * Real.pi) : ℂ) • innerSL ℂ (kz z)
  have hLx : ∀ g' : GI, L g' = T g' z := fun g' => rfl
  have hL := (hasSum_fourier_series_L2 g).mapL L
  rw [hLx] at hL
  have hterm : ∀ i : ℤ, L (fourierCoeff g i • fourierLp 2 i) =
      fourierCoeff g i * (rE (z + 2 * Real.pi * i) / (2 * Real.pi)) := by
    intro i; rw [map_smul, hLx, T_fourier, smul_eq_mul]
  simp_rw [hterm] at hL
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hL
  convert hneg using 1
  funext n
  simp only [Function.comp_apply, Equiv.neg_apply]
  have hs : T g (2 * Real.pi * n) = (1 / (2 * Real.pi)) * fourierCoeff g (-n) := by
    rw [T_sample, show (fourierLp 2 (-n) : GI) = fourierBasis (-n) by rw [coe_fourierBasis],
      ← fourierBasis.repr_apply_apply, fourierBasis_repr]
  rw [hs]
  push_cast
  rw [show z + 2 * (Real.pi:ℂ) * (-(n:ℂ)) = z - 2 * Real.pi * n by ring]
  ring

end Plancherel

end EulerianBridge.PW
