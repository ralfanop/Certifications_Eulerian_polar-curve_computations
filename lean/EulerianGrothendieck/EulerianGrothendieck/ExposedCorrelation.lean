import EulerianGrothendieck.VectorOptimum
import EulerianGrothendieck.Geometry
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Task C2, part 1: strictness and exposure (Theorem 9.13)

Code conventions (unchanged from the certified modules): `frameMatrix e z` is the 4×2 matrix
`W = V^*`, `e = √p`, the last row is `(e, √(1-e²)·conj z)`; `P = W(W^*W)^{-1}W^*`.
The Gram matrix of the manuscript is `K = V^*V = W W^*` (`frameGram`).

* `explicitFrameScalarNorm_lt_four`: `g(P) < 4` for `0 < p < 1`, `Im z ≠ 0`, `|z| = 1`;
* `bilinearRatio_gt_one`: `𝒬(p) > 1`;
* `frameGram_mem_elliptope`, `frameGram_rank`: `K` is a rank-two point of the complex
  correlation elliptope `{X ≥ 0, diag X = 1}` of order four;
* `frameGram_exposed`: `X ↦ Re Tr(P X)` is at most `4` on the elliptope, equals `4` at `K`,
  and `K` is its **unique** maximiser (exposure, not merely extremality). -/

noncomputable section
open scoped ComplexOrder ComplexConjugate
open Matrix
namespace EulerianGrothendieck
set_option maxHeartbeats 4000000

/-- The complex correlation elliptope of order four. -/
def correlationElliptope : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  {X | X.PosSemidef ∧ ∀ i, X i i = 1}

/-- `K = V^*V = W W^*`. -/
def frameGram (e : ℝ) (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  frameMatrix e z * (frameMatrix e z)ᴴ

/-! ### Strictness -/

theorem normSq_frame_coordinate (e s : ℝ) (a b : ℂ) :
    Complex.normSq ((e:ℂ) * a + (s:ℂ) * b) =
      e^2 * Complex.normSq a + s^2 * Complex.normSq b + 2 * e * s * (a * conj b).re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The four coordinates of a vector of `ran V^*`. -/
theorem frameVector_coords (e : ℝ) (z a b : ℂ) :
    frameVector e z a b 0 = a ∧ frameVector e z a b 1 = b ∧
    frameVector e z a b 2 = (e:ℂ) * a + (Real.sqrt (1 - e^2):ℂ) * b ∧
    frameVector e z a b 3 = (e:ℂ) * a + (Real.sqrt (1 - e^2):ℂ) * star z * b := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [frameVector]

/-- **Strictness**: `g(P) < 4` when `0 < p < 1` and `sin ϑ ≠ 0`. -/
theorem explicitFrameScalarNorm_lt_four (e : ℝ) (z : ℂ) (he0 : 0 < e) (he1 : e < 1)
    (hz : ‖z‖ = 1) (hzi : z.im ≠ 0) : explicitFrameScalarNorm e z < 4 := by
  rw [explicitFrameScalarNorm_eq]
  obtain ⟨u, hu, hmax⟩ := projectionScalarNorm_attained (frameSubspace e z)
  rw [hmax]
  have hp := projection_residual_pythagoras (frameSubspace e z) u
  rw [torusPoint_norm_sq u hu] at hp
  rcases lt_or_eq_of_le (show ‖(frameSubspace e z).starProjection u‖ ^ 2 ≤ 4 by
      nlinarith [sq_nonneg ‖u - (frameSubspace e z).starProjection u‖]) with h | h
  · exact h
  · exfalso
    have hres : u - (frameSubspace e z).starProjection u = 0 := by
      have : ‖u - (frameSubspace e z).starProjection u‖ ^ 2 = 0 := by linarith
      exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
    have hmem : u ∈ frameSubspace e z := by
      have : u = (frameSubspace e z).starProjection u := sub_eq_zero.mp hres
      rw [this]; exact (frameSubspace e z).starProjection_apply_mem u
    obtain ⟨⟨a, b⟩, hab⟩ := hmem
    change frameVector e z a b = u at hab
    obtain ⟨c0, c1, c2, c3⟩ := frameVector_coords e z a b
    have hs2 : Real.sqrt (1 - e^2) ^ 2 = 1 - e^2 := Real.sq_sqrt (by nlinarith)
    have hspos : 0 < Real.sqrt (1 - e^2) := Real.sqrt_pos.mpr (by nlinarith)
    have hc : ∀ i, ‖frameVector e z a b i‖ = 1 := by rw [hab]; exact hu
    have n0 : Complex.normSq a = 1 := by
      rw [Complex.normSq_eq_norm_sq, ← c0, hc 0]; norm_num
    have n1 : Complex.normSq b = 1 := by
      rw [Complex.normSq_eq_norm_sq, ← c1, hc 1]; norm_num
    have n2 : Complex.normSq ((e:ℂ) * a + (Real.sqrt (1 - e^2):ℂ) * b) = 1 := by
      rw [Complex.normSq_eq_norm_sq, ← c2, hc 2]; norm_num
    have n3 : Complex.normSq ((e:ℂ) * a + (Real.sqrt (1 - e^2):ℂ) * (star z * b)) = 1 := by
      rw [← mul_assoc, Complex.normSq_eq_norm_sq, ← c3, hc 3]; norm_num
    rw [normSq_frame_coordinate, n0, n1] at n2
    rw [normSq_frame_coordinate, n0, Complex.normSq_mul, n1] at n3
    have hzn : Complex.normSq (star z) = 1 := by
      rw [Complex.star_def, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
    rw [hzn] at n3
    have hes : 2 * e * Real.sqrt (1 - e^2) ≠ 0 := by positivity
    have hre0 : (a * conj b).re = 0 := by
      have : 2 * e * Real.sqrt (1 - e^2) * (a * conj b).re = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hes
    have hre1 : (a * conj (star z * b)).re = 0 := by
      have : 2 * e * Real.sqrt (1 - e^2) * (a * conj (star z * b)).re = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hes
    have hw : Complex.normSq (a * conj b) = 1 := by
      rw [Complex.normSq_mul, Complex.normSq_conj, n0, n1]; ring
    have hzw : (z * (a * conj b)).re = 0 := by
      have : a * conj (star z * b) = z * (a * conj b) := by
        rw [map_mul, Complex.star_def, Complex.conj_conj]; ring
      rw [← this]; exact hre1
    exact phase_constraints_impossible z (a * conj b) hzi hw hre0 hzw

/-- `𝒬(p) = q_ℂ(P)/g_ℂ(P) > 1` under the same hypotheses. -/
theorem bilinearRatio_gt_one (e : ℝ) (z : ℂ) (he0 : 0 < e) (he1 : e < 1)
    (hz : ‖z‖ = 1) (hzi : z.im ≠ 0) : 1 < bilinearRatio e z := by
  have he : e ^ 2 ≤ 1 := by nlinarith
  rw [bilinearRatio_explicit e z he hz, lt_div_iff₀ (explicitFrameScalarNorm_pos e z he), one_mul]
  exact explicitFrameScalarNorm_lt_four e z he0 he1 hz hzi

/-! ### The projector as a matrix -/

theorem frameGram_inv_hermitian (e : ℝ) (z : ℂ) :
    (((frameMatrix e z)ᴴ * frameMatrix e z)⁻¹)ᴴ = ((frameMatrix e z)ᴴ * frameMatrix e z)⁻¹ := by
  rw [conjTranspose_nonsing_inv, conjTranspose_mul, conjTranspose_conjTranspose]

theorem explicitFrameProjector_idem (e : ℝ) (z : ℂ) :
    explicitFrameProjector e z * explicitFrameProjector e z = explicitFrameProjector e z := by
  conv_lhs => rw [show explicitFrameProjector e z * explicitFrameProjector e z =
    (explicitFrameProjector e z * frameMatrix e z) *
      (((frameMatrix e z)ᴴ * frameMatrix e z)⁻¹ * (frameMatrix e z)ᴴ) by
        unfold explicitFrameProjector; simp only [Matrix.mul_assoc]]
  rw [explicitFrameProjector_mul_frameMatrix]
  unfold explicitFrameProjector
  simp only [Matrix.mul_assoc]

theorem explicitFrameProjector_hermitian (e : ℝ) (z : ℂ) :
    (explicitFrameProjector e z)ᴴ = explicitFrameProjector e z := by
  unfold explicitFrameProjector
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, frameGram_inv_hermitian]
  simp only [Matrix.mul_assoc]

theorem frameGram_trace_P (e : ℝ) (z : ℂ) :
    explicitFrameProjector e z * frameGram e z = frameGram e z := by
  unfold frameGram
  rw [← Matrix.mul_assoc, explicitFrameProjector_mul_frameMatrix]

/-! ### `K` in the elliptope -/

theorem frameGram_diag (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) (i : Fin 4) :
    frameGram e z i i = 1 := by
  unfold frameGram
  rw [Matrix.mul_apply]
  have h := frameMatrix_row_norm_sq e z he hz i
  have : ∑ k, frameMatrix e z i k * (frameMatrix e z)ᴴ k i =
      ((∑ k, ‖frameMatrix e z i k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj']
  rw [this, h]; simp

theorem frameGram_mem_elliptope (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) :
    frameGram e z ∈ correlationElliptope :=
  ⟨posSemidef_self_mul_conjTranspose _, frameGram_diag e z he hz⟩

theorem frameMatrix_rank (e : ℝ) (z : ℂ) : (frameMatrix e z).rank = 2 := by
  unfold Matrix.rank
  rw [LinearMap.finrank_range_of_inj (by
    intro x y h
    exact frameMatrix_injective e z (by simpa using h))]
  simp

/-- `K` has rank two. -/
theorem frameGram_rank (e : ℝ) (z : ℂ) : (frameGram e z).rank = 2 := by
  unfold frameGram
  rw [rank_self_mul_conjTranspose, frameMatrix_rank]

/-! ### The linear functional `X ↦ Re Tr(P X)` -/

theorem trace_P_le (e : ℝ) (z : ℂ) {X : Matrix (Fin 4) (Fin 4) ℂ} (hX : X.PosSemidef) :
    (explicitFrameProjector e z * X).trace.re ≤ X.trace.re ∧
    ((explicitFrameProjector e z * X).trace.re = X.trace.re →
      X * (1 - explicitFrameProjector e z) = 0) := by
  set P := explicitFrameProjector e z with hPdef
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hPdef, explicitFrameProjector_idem]
    abel
  have hQh : (1 - P)ᴴ = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPdef, explicitFrameProjector_hermitian]
  have htr : X.trace - (P * X).trace = ((1 - P)ᴴ * X * (1 - P)).trace := by
    rw [hQh, Matrix.mul_assoc, Matrix.trace_mul_comm (1 - P) (X * (1 - P)), Matrix.mul_assoc, hQQ,
      Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_mul_comm X P]
  have hpsd : ((1 - P)ᴴ * X * (1 - P)).PosSemidef := hX.conjTranspose_mul_mul_same (1 - P)
  have hnn : 0 ≤ ((1 - P)ᴴ * X * (1 - P)).trace := hpsd.trace_nonneg
  have hre : 0 ≤ ((1 - P)ᴴ * X * (1 - P)).trace.re := (Complex.nonneg_iff.mp hnn).1
  refine ⟨?_, ?_⟩
  · have := congrArg Complex.re htr
    rw [Complex.sub_re] at this
    linarith
  · intro heq
    have hzero : ((1 - P)ᴴ * X * (1 - P)).trace = 0 := by
      have hre0 : ((1 - P)ᴴ * X * (1 - P)).trace.re = 0 := by
        have := congrArg Complex.re htr
        rw [Complex.sub_re] at this
        linarith
      have him : ((1 - P)ᴴ * X * (1 - P)).trace.im = 0 := (Complex.nonneg_iff.mp hnn).2.symm
      exact Complex.ext hre0 him
    -- every diagonal term `star v ⬝ᵥ X *ᵥ v` (column `v` of `1 - P`) is nonnegative, so zero
    have hdiag : ∀ i : Fin 4, ((1 - P)ᴴ * X * (1 - P)).diag i =
        star (fun j => (1 - P) j i) ⬝ᵥ X *ᵥ (fun j => (1 - P) j i) := by
      intro i
      simp only [Matrix.diag_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec, conjTranspose_apply,
        Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      ring
    have hnonneg : ∀ i : Fin 4, 0 ≤ ((1 - P)ᴴ * X * (1 - P)).diag i := by
      intro i; rw [hdiag]; exact hX.2 _
    have hzero' : ∑ i : Fin 4, ((1 - P)ᴴ * X * (1 - P)).diag i = 0 := hzero
    have heach : ∀ i : Fin 4, ((1 - P)ᴴ * X * (1 - P)).diag i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero'
      exact fun i => this i (Finset.mem_univ i)
    ext j i
    have h0 : star (fun j => (1 - P) j i) ⬝ᵥ X *ᵥ (fun j => (1 - P) j i) = 0 := by
      rw [← hdiag]; exact heach i
    have hv := (hX.dotProduct_mulVec_zero_iff _).mp h0
    have := congrFun hv j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

/-! ### Exposure -/

theorem exposure_offdiag (e s : ℝ) (z w : ℂ) (hes : e * s ≠ 0) (hzi : z.im ≠ 0)
    (h2 : (e:ℂ) * s * (w + conj w) = 0) (h3 : (e:ℂ) * s * (z * w + conj z * conj w) = 0) :
    w = 0 := by
  have hes' : (e:ℂ) * s ≠ 0 := by
    rw [← Complex.ofReal_mul]; exact_mod_cast hes
  have h2' : w + conj w = 0 := (mul_eq_zero.mp h2).resolve_left hes'
  have h3' : z * w + conj z * conj w = 0 := (mul_eq_zero.mp h3).resolve_left hes'
  have hre : w.re = 0 := by
    have := congrArg Complex.re h2'
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  have hre2 : (z * w).re = 0 := by
    have := congrArg Complex.re h3'
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.zero_re] at this
    simp only [Complex.mul_re]
    linarith
  have him : w.im = 0 := by
    rw [Complex.mul_re, hre] at hre2
    have : z.im * w.im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hzi
  exact Complex.ext hre him

/-- Diagonal entries of `W H W^*` for a `4×2` matrix `W` and a `2×2` matrix `H`. -/
theorem gram_entry (W : Matrix (Fin 4) (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) :
    (W * H * Wᴴ) i i = W i 0 * H 0 0 * conj (W i 0) + W i 0 * H 0 1 * conj (W i 1) +
      W i 1 * H 1 0 * conj (W i 0) + W i 1 * H 1 1 * conj (W i 1) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two, Complex.star_def]
  ring

theorem frameMatrix_entries (e : ℝ) (z : ℂ) :
    frameMatrix e z 0 0 = 1 ∧ frameMatrix e z 0 1 = 0 ∧
    frameMatrix e z 1 0 = 0 ∧ frameMatrix e z 1 1 = 1 ∧
    frameMatrix e z 2 0 = (e:ℂ) ∧ frameMatrix e z 2 1 = (Real.sqrt (1 - e^2):ℂ) ∧
    frameMatrix e z 3 0 = (e:ℂ) ∧ frameMatrix e z 3 1 = (Real.sqrt (1 - e^2):ℂ) * conj z := by
  simp [frameMatrix, Complex.star_def]

/-- **Exposure**: on the elliptope, `Re Tr(P X) ≤ 4`, with equality exactly at `X = K`. -/
theorem frameGram_exposed (e : ℝ) (z : ℂ) (he0 : 0 < e) (he1 : e < 1)
    (hz : ‖z‖ = 1) (hzi : z.im ≠ 0) :
    (∀ X ∈ correlationElliptope, (explicitFrameProjector e z * X).trace.re ≤ 4) ∧
    (explicitFrameProjector e z * frameGram e z).trace.re = 4 ∧
    (∀ X ∈ correlationElliptope,
      (explicitFrameProjector e z * X).trace.re = 4 → X = frameGram e z) := by
  have he : e ^ 2 ≤ 1 := by nlinarith
  have htr4 : ∀ X ∈ correlationElliptope, X.trace.re = 4 := by
    intro X hX
    norm_num [Matrix.trace, Fin.sum_univ_four, hX.2]
  refine ⟨fun X hX => (trace_P_le e z hX.1).1.trans (htr4 X hX).le, ?_, ?_⟩
  · rw [frameGram_trace_P]; exact htr4 _ (frameGram_mem_elliptope e z he hz)
  · intro X hX heq
    have hXQ := (trace_P_le e z hX.1).2 (by rw [heq, htr4 X hX])
    have hXP : X = X * explicitFrameProjector e z := by
      rw [Matrix.mul_sub, Matrix.mul_one] at hXQ
      exact sub_eq_zero.mp hXQ
    have hPX : X = explicitFrameProjector e z * X := by
      have h := congrArg conjTranspose hXP
      rw [conjTranspose_mul, hX.1.1.eq, explicitFrameProjector_hermitian] at h
      exact h
    -- `X = W H W^*` with `H = G⁻¹ W^* X W G⁻¹`
    obtain ⟨H, hXH, hHh⟩ : ∃ H : Matrix (Fin 2) (Fin 2) ℂ,
        X = frameMatrix e z * H * (frameMatrix e z)ᴴ ∧ Hᴴ = H := by
      refine ⟨((frameMatrix e z)ᴴ * frameMatrix e z)⁻¹ * (frameMatrix e z)ᴴ * X * frameMatrix e z *
        ((frameMatrix e z)ᴴ * frameMatrix e z)⁻¹, ?_, ?_⟩
      · calc X = explicitFrameProjector e z * X * explicitFrameProjector e z := by
              conv_rhs => rw [Matrix.mul_assoc, ← hXP, ← hPX]
          _ = _ := by simp only [explicitFrameProjector, Matrix.mul_assoc]
      · simp only [conjTranspose_mul, conjTranspose_conjTranspose, frameGram_inv_hermitian,
          hX.1.1.eq, Matrix.mul_assoc]
    have hH10 : H 1 0 = conj (H 0 1) := by
      have := congrFun (congrFun hHh 1) 0
      rw [conjTranspose_apply] at this
      exact this.symm
    obtain ⟨w00, w01, w10, w11, w20, w21, w30, w31⟩ := frameMatrix_entries e z
    have hs2 : Real.sqrt (1 - e ^ 2) ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith)
    have hspos : 0 < Real.sqrt (1 - e ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have hdiag : ∀ i, (frameMatrix e z * H * (frameMatrix e z)ᴴ) i i = 1 := by
      intro i; rw [← hXH]; exact hX.2 i
    have hd0 := hdiag 0
    have hd1 := hdiag 1
    have hd2 := hdiag 2
    have hd3 := hdiag 3
    rw [gram_entry, w00, w01] at hd0
    rw [gram_entry, w10, w11] at hd1
    rw [gram_entry, w20, w21] at hd2
    rw [gram_entry, w30, w31] at hd3
    simp only [map_one, map_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add] at hd0 hd1
    simp only [Complex.conj_ofReal, map_mul, Complex.conj_conj, hd0, hd1, hH10] at hd2 hd3
    have hss : ((Real.sqrt (1 - e ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (e:ℂ) ^ 2 := by exact_mod_cast hs2
    have hzz : conj z * z = 1 := by
      rw [Complex.conj_mul', hz]; norm_num
    have hes : e * Real.sqrt (1 - e ^ 2) ≠ 0 := by positivity
    have hoff : H 0 1 = 0 := by
      apply exposure_offdiag e (Real.sqrt (1 - e ^ 2)) z (H 0 1) hes hzi
      · linear_combination hd2 - hss
      · linear_combination hd3 - hss - ((Real.sqrt (1 - e ^ 2) : ℝ) : ℂ) ^ 2 * hzz
    have hHone : H = 1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · simpa using hd0
      · simpa using hoff
      · simp [hH10, hoff]
      · simpa using hd1
    rw [hXH, hHone, Matrix.mul_one]
    rfl

end EulerianGrothendieck
