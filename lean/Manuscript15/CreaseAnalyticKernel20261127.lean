import Mathlib

/-! M15 Proposition 12.3 (615)-(617).
Actual analytic kernel after the substitution b=k/sqrt(1+k^2).
The inverse-square-root remainder is unconditional on x>=0, not an
assumed Taylor remainder for an arbitrary crease. The integration and
trigonometric sixth-order error are further obligations. -/

noncomputable section
namespace Manuscript15.CreaseAnalyticKernel20261127

theorem inv_sqrt_first_order_remainder (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 / Real.sqrt (1+x)-1+x/2 ∧
    1 / Real.sqrt (1+x)-1+x/2 ≤ 3/8*x^2 := by
  let s := Real.sqrt (1+x)
  change 0 ≤ 1/s-1+x/2 ∧ 1/s-1+x/2 ≤ 3/8*x^2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=1+x := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    by_contra h
    push_neg at h
    have hh := mul_pos (sub_pos.mpr h) (show 0 < 1+s by linarith)
    nlinarith
  have hs : 0 < s := by linarith
  have he : s*(1/s-1+x/2)=(s-1)^2*(s+2)/2 := by
    calc
      _ = 1-s+s*x/2 := by field_simp [hs.ne'] <;> ring
      _ = _ := by rw [show x=s^2-1 by linarith]; ring
  have hfac : x=(s-1)*(s+1) := by nlinarith
  have h4 : (4:ℝ) ≤ (s+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (show 0 ≤ s+3 by linarith)]
  have hsq : 4*(s-1)^2 ≤ x^2 := by
    rw [hfac,mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg (s-1))]
  constructor
  · apply nonneg_of_mul_nonneg_left _ hs
    rw [mul_comm,he]
    positivity
  · apply (mul_le_mul_left₀ hs).mp
    rw [he]
    have hlin : (s+2)/2 ≤ 3*s/2 := by linarith
    have hmid := mul_le_mul_of_nonneg_left hlin (sq_nonneg (s-1))
    have hlast := mul_le_mul_of_nonneg_left hsq hs0
    nlinarith [hmid,hlast]

theorem reparametrized_phase_radicand (k u : ℝ) :
    (Real.cosh u)^2-(k/Real.sqrt (1+k^2))^2 =
      (1+(1+k^2)*(Real.sinh u)^2)/(1+k^2) := by
  have hk : 0 < 1+k^2 := by positivity
  rw [div_pow, Real.sq_sqrt hk.le]
  apply (eq_div_iff hk.ne').2
  field_simp [hk.ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq u,
    congrArg (fun t : ℝ => k^2*t) (Real.cosh_sq_sub_sinh_sq u)]

theorem actual_phase_kernel_reparametrization (k u : ℝ) :
    (k/Real.sqrt (1+k^2)) /
      Real.sqrt ((Real.cosh u)^2-(k/Real.sqrt (1+k^2))^2) =
      k/Real.sqrt (1+(1+k^2)*(Real.sinh u)^2) := by
  have hk : 0 < 1+k^2 := by positivity
  have hq : 0 < 1+(1+k^2)*(Real.sinh u)^2 := by positivity
  rw [reparametrized_phase_radicand, Real.sqrt_div hq.le]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hk), ne_of_gt (Real.sqrt_pos.2 hq)] <;> ring

theorem actual_phase_kernel_bound (k u : ℝ) (hk : 0 ≤ k) :
    0 ≤ k/Real.sqrt (1+(1+k^2)*(Real.sinh u)^2)-k+
      k*(1+k^2)*(Real.sinh u)^2/2 ∧
    k/Real.sqrt (1+(1+k^2)*(Real.sinh u)^2)-k+
      k*(1+k^2)*(Real.sinh u)^2/2 ≤
      (3*k/8)*(1+k^2)^2*(Real.sinh u)^4 := by
  let x := (1+k^2)*(Real.sinh u)^2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h := inv_sqrt_first_order_remainder x hx
  have h1 := mul_nonneg hk h.1
  have h2 := mul_le_mul_of_nonneg_left h.2 hk
  have he' : k/Real.sqrt (1+(1+k^2)*(Real.sinh u)^2)-k+
      k*(1+k^2)*(Real.sinh u)^2/2 = k/Real.sqrt (1+x)-k+k*x/2 := by
    dsimp [x]
    ring
  rw [he']
  have he : k*(1/Real.sqrt (1+x)-1+x/2)=
      k/Real.sqrt (1+x)-k+k*x/2 := by ring
  rw [he] at h1 h2
  refine ⟨h1,?_⟩
  calc
    _ ≤ k*(3/8*x^2) := h2
    _ = _ := by dsimp [x]; ring

end Manuscript15.CreaseAnalyticKernel20261127

#print axioms Manuscript15.CreaseAnalyticKernel20261127.inv_sqrt_first_order_remainder
#print axioms Manuscript15.CreaseAnalyticKernel20261127.reparametrized_phase_radicand
#print axioms Manuscript15.CreaseAnalyticKernel20261127.actual_phase_kernel_reparametrization
#print axioms Manuscript15.CreaseAnalyticKernel20261127.actual_phase_kernel_bound
