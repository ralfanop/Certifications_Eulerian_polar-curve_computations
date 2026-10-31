import Bridge.PaleyWiener
import Bridge.Fock3

/-!
# Theorem 3.10 (continued) and the momentum normalisation of Proposition 3.1

* (27a) the cardinal series converges uniformly on every horizontal strip `|Im z| ≤ R`;
* (27b) Parseval: `∫_ℝ |f|² = 2π ∑ |f(2πn)|²`;
* (29) `∫ r_E(x-t) r_E(t-y) dt = 2π r_E(x-y)`;
* (17) `∫ |F_ħψ_L(p)|² dp = 1`.
All under the cited Plancherel hypothesis `PW.Plancherel`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate

namespace EulerianBridge.PW

open EulerianGrothendieck.Fock

theorem rE_conj (z : ℂ) : rE (conj z) = conj (rE z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [rE_zero]
  have hz' : conj z ≠ 0 := by simpa using hz
  rw [rE_eq_sin_div hz, rE_eq_sin_div hz', map_div₀, ← Complex.sin_conj, map_div₀, map_ofNat]

theorem rE_real_conj (x : ℝ) : conj (rE x) = rE x := by
  rw [← rE_conj, Complex.conj_ofReal]

/-- Each sampling term is `T` of a Fourier mode. -/
theorem term_eq (g : GI) (n : ℤ) (z : ℂ) :
    T g (2 * Real.pi * n) * rE (z - 2 * Real.pi * n) = T (fourierCoeff g (-n) • fourierLp 2 (-n)) z := by
  rw [T_smul, T_fourier]
  have hs : T g (2 * Real.pi * n) = (1 / (2 * Real.pi)) * fourierCoeff g (-n) := by
    rw [T_sample, show (fourierLp 2 (-n) : GI) = fourierBasis (-n) by rw [coe_fourierBasis],
      ← fourierBasis.repr_apply_apply, fourierBasis_repr]
  rw [hs]
  push_cast
  rw [show z + 2 * (Real.pi:ℂ) * (-(n:ℂ)) = z - 2 * Real.pi * n by ring]
  ring

theorem T_sum (S : Finset ℤ) (c : ℤ → GI) (z : ℂ) : T (∑ n ∈ S, c n) z = ∑ n ∈ S, T (c n) z := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold T; simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, T_add, ih]

theorem T_sub (g h : GI) (z : ℂ) : T (g - h) z = T g z - T h z := by
  unfold T; rw [inner_sub_right]; ring

/-- The Fourier series of `g`, reindexed by `n ↦ -n`. -/
theorem hasSum_neg (g : GI) : HasSum (fun n : ℤ => fourierCoeff g (-n) • (fourierLp 2 (-n) : GI)) g := by
  have h := ((Equiv.neg ℤ).hasSum_iff (f := fun i : ℤ => fourierCoeff g i • (fourierLp 2 i : GI))).mpr
    (hasSum_fourier_series_L2 g)
  exact h

/-- (27a): the cardinal series converges uniformly on every strip `|Im z| ≤ R`. -/
theorem sampling_uniform (g : GI) (R : ℝ) :
    TendstoUniformlyOn (fun (S : Finset ℤ) (z : ℂ) => ∑ n ∈ S, T g (2 * Real.pi * n) * rE (z - 2 * Real.pi * n))
      (T g) atTop {z : ℂ | |z.im| ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC : 0 < (1 / (2 * Real.pi)) * Real.exp (R / 2) := by positivity
  have ht := (hasSum_neg g)
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero] at ht
  have hev := (ht.eventually (gt_mem_nhds (div_pos hε hC)))
  filter_upwards [hev] with S hS z hz
  rw [dist_eq_norm]
  have hpart : ∑ n ∈ S, T g (2 * Real.pi * n) * rE (z - 2 * Real.pi * n) =
      T (∑ n ∈ S, fourierCoeff g (-n) • (fourierLp 2 (-n) : GI)) z := by
    rw [T_sum]; exact Finset.sum_congr rfl (fun n _ => term_eq g n z)
  rw [hpart, ← T_sub]
  calc ‖T (g - ∑ n ∈ S, fourierCoeff g (-n) • (fourierLp 2 (-n) : GI)) z‖
      ≤ (1 / (2 * Real.pi)) * Real.exp (|z.im| / 2) * ‖g - ∑ n ∈ S, fourierCoeff g (-n) • (fourierLp 2 (-n) : GI)‖ :=
        norm_T_le _ _
    _ ≤ (1 / (2 * Real.pi)) * Real.exp (R / 2) * ‖g - ∑ n ∈ S, fourierCoeff g (-n) • (fourierLp 2 (-n) : GI)‖ := by
        gcongr
    _ < (1 / (2 * Real.pi)) * Real.exp (R / 2) * (ε / ((1 / (2 * Real.pi)) * Real.exp (R / 2))) := by
        rw [norm_sub_rev] at hS
        exact mul_lt_mul_of_pos_left hS hC
    _ = ε := by field_simp

section Plancherel

variable (hP : Plancherel)
include hP

theorem integral_norm_sq_T (g : GI) : ∫ x : ℝ, ‖T g x‖ ^ 2 = (1 / (2 * Real.pi)) * ‖g‖ ^ 2 := by
  have h := (hP g).2 g
  rw [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ x : ℝ, ((‖T g x‖ ^ 2 : ℝ) : ℂ) = conj (T g x) * T g x := by
    intro x; rw [Complex.conj_mul']; push_cast; ring
  simp_rw [e]
  rw [h]; push_cast; rfl

/-- (27b) Parseval: `∫_ℝ |f|² = 2π ∑_n |f(2πn)|²` for `f = T g`. -/
theorem parseval (g : GI) :
    ∫ x : ℝ, ‖T g x‖ ^ 2 = 2 * Real.pi * ∑' n : ℤ, ‖T g (2 * Real.pi * n)‖ ^ 2 := by
  rw [integral_norm_sq_T hP]
  have hsamp : ∀ n : ℤ, ‖T g (2 * Real.pi * n)‖ = (1 / (2 * Real.pi)) * ‖fourierCoeff g (-n)‖ := by
    intro n
    rw [T_sample, show (fourierLp 2 (-n) : GI) = fourierBasis (-n) by rw [coe_fourierBasis],
      ← fourierBasis.repr_apply_apply, fourierBasis_repr, norm_mul]
    congr 1
    rw [show ((1 / (2 * Real.pi)) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [hsamp, mul_pow]
  rw [tsum_mul_left]
  have hpars : ∑' n : ℤ, ‖fourierCoeff g (-n)‖ ^ 2 = ‖g‖ ^ 2 := by
    have hn := (Equiv.neg ℤ).tsum_eq (fun i => ‖fourierCoeff g i‖ ^ 2)
    simp only [Equiv.neg_apply] at hn
    rw [hn]
    simp_rw [← fourierBasis_repr]
    have h1 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (fourierBasis.repr g)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
    rw [← h1]
    simp
  rw [hpars]
  have hp : (0:ℝ) < Real.pi := Real.pi_pos
  field_simp

/-- (29): `∫ r_E(x-t) r_E(t-y) dt = 2π r_E(x-y)` for real `x, y`. -/
theorem convolution (x y : ℝ) :
    ∫ t : ℝ, rE (x - t) * rE (t - y) = 2 * Real.pi * rE (x - y) := by
  have h := reproducing hP (kz y) x
  rw [← KE_eq_T] at h
  have e : ∀ t : ℝ, conj (KE t x) * T (kz y) t = rE (x - t) * rE (t - y) / (2 * Real.pi) ^ 2 := by
    intro t
    rw [← KE_eq_T, KE_eq, KE_eq, Complex.conj_ofReal, Complex.conj_ofReal, map_div₀]
    rw [show (t:ℂ) - x = ((t - x : ℝ) : ℂ) by push_cast; ring, rE_real_conj,
      show ((t - x : ℝ) : ℂ) = -((x:ℂ) - t) by push_cast; ring, EulerianBridge.Fock3.rE_neg]
    simp only [map_mul, map_ofNat, Complex.conj_ofReal]
    ring
  simp_rw [e] at h
  rw [MeasureTheory.integral_div, KE_eq, Complex.conj_ofReal] at h
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
  push_cast at h ⊢
  field_simp at h
  linear_combination -h

/-- Proposition 3.1, eq. (17): `∫ |(F_ħψ_L)(p)|² dp = 1`. -/
theorem momentum_normalisation {L ħ : ℝ} (hL : 0 < L) (hħ : 0 < ħ) :
    ∫ p : ℝ, ‖EulerianBridge.Fock3.momentum ħ (EulerianBridge.Fock3.psiL L) p‖ ^ 2 = 1 := by
  simp_rw [EulerianBridge.Fock3.momentum_psiL hL hħ, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  rw [MeasureTheory.integral_const_mul]
  have hc : L / ħ ≠ 0 := div_ne_zero hL.ne' hħ.ne'
  have h := MeasureTheory.Measure.integral_comp_mul_right (fun x : ℝ => ‖rE x‖ ^ 2) (L / ħ)
  have e : ∀ p : ℝ, ‖rE ((p * L / ħ : ℝ) : ℂ)‖ ^ 2 = (fun x : ℝ => ‖rE x‖ ^ 2) (p * (L / ħ)) := by
    intro p; simp only; congr 3; push_cast; ring
  rw [show (fun p : ℝ => ‖rE (↑p * ↑L / ↑ħ)‖ ^ 2) = fun p : ℝ => (fun x : ℝ => ‖rE x‖ ^ 2) (p * (L / ħ)) by
    funext p; rw [← e p]; push_cast; ring_nf]
  rw [h, norm_rE_sq hP, Real.sq_sqrt (by positivity), abs_inv, abs_of_pos (div_pos hL hħ)]
  have hp : (0:ℝ) < Real.pi := Real.pi_pos
  simp only [smul_eq_mul]
  field_simp

end Plancherel

end EulerianBridge.PW
