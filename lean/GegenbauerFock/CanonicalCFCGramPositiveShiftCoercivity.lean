import GegenbauerFock.GramSpectralTheorem
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# V007 — coercivity of the strictly positive-shifted source Gram

For the actual selfadjoint positive bounded Gram G=C* C on complex
weighted L², every eps>0 obeys eps * ‖x‖ ≤ ‖Gx+eps*x‖.
Unlike a spectral truncation or the abstract scalar resolvent-set
assertion, this inequality is on the genuine infinite-dimensional
operator and gives the uniform Tikhonov error contraction estimate
once its two-sided inverse is constructed.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Coercivity of the actual positive-shifted ultraspherical source Gram. -/
theorem sourceGram_positive_shift_norm_lower
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (x : Lp ℂ 2 (Ultraspherical.measure lam)) :
    eps * ‖x‖ ≤
      ‖gram lam alpha hlam ha x + (eps : ℂ) • x‖ := by
  let G := gram lam alpha hlam ha
  have hpos : G.IsPositive := by
    change ((C lam alpha hlam ha).adjoint ∘L
      (C lam alpha hlam ha)).IsPositive
    exact ContinuousLinearMap.isPositive_adjoint_comp_self
      (C lam alpha hlam ha)
  have hcross : 0 ≤
      (inner ℂ ((eps : ℂ) • x) (G x)).re := by
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg heps.le (hpos.re_inner_nonneg_right x)
  have hcrossR :
      0 ≤ RCLike.re (inner ℂ ((eps : ℂ) • x) (G x)) := by
    exact hcross
  have hsq := norm_add_sq (𝕜 := ℂ) ((eps : ℂ) • x) (G x)
  have hcross' : 0 ≤
      RCLike.re (inner ℂ ((eps : ℂ) • x) (G x)) := by
    simpa only using hcross
  have hnormsq :
      ‖(eps : ℂ) • x‖ ^ 2 ≤
        ‖(eps : ℂ) • x + G x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖G x‖)]
  have hnorm :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
  have h : eps * ‖x‖ ≤ ‖(eps : ℂ) • x + G x‖ := by
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos heps] using hnorm
  simpa only [add_comm] using h

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_positive_shift_norm_lower

end GegenbauerFock.GeneralUltrasphericalFock
