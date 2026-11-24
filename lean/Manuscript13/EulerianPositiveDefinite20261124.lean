import Mathlib

/-! M13 Proposition 4.11: sinc as an actual cosine average, Fubini
and real finite Gram positivity of the cosine kernel. Integrability of
the product integrand is explicit in the Fubini bridge. General Cauchy
Fourier evaluation and complex positive definiteness remain separate.
This file does not depend on the pending #558. -/
open MeasureTheory Set
namespace Manuscript13.EulerianPositiveDefinite20261124
noncomputable section

def potential (a u : ℝ) : ℝ := a^2 / (u^2+a^2)^2
def sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

theorem sinc_zero : sinc 0 = 1 := by simp [sinc]

theorem sinc_even (x : ℝ) : sinc (-x) = sinc x := by
  by_cases h : x = 0
  · simp [h, sinc]
  · simp [sinc, h, Real.sin_neg]

theorem cosine_average (x : ℝ) :
    (∫ t in (0:ℝ)..1, Real.cos (t*x)) = sinc x := by
  by_cases hx : x = 0
  · simp [hx, sinc]
  · have hd : ∀ t : ℝ, HasDerivAt (fun y : ℝ => Real.sin (y*x)/x)
        (Real.cos (t*x)) t := by
      intro t
      have h := ((Real.hasDerivAt_sin (t*x)).comp t
        ((hasDerivAt_id t).mul_const x)).div_const x
      convert h using 1
      simp [id_eq, hx]
    have hi : IntervalIntegrable (fun t : ℝ => Real.cos (t*x)) volume 0 1 :=
      (by fun_prop : Continuous (fun t : ℝ => Real.cos (t*x))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
    simp [sinc, hx]

def cosKernel (a p : ℝ) (z : ℝ × ℝ) : ℝ :=
  potential a z.1 * Real.cos (z.2*p*z.1)

theorem product_fubini (a p : ℝ)
    (hi : Integrable (cosKernel a p)
      (volume.prod (volume.restrict (Ioc (0:ℝ) 1)))) :
    (∫ u : ℝ, ∫ t in Ioc (0:ℝ) 1, cosKernel a p (u,t)) =
    (∫ t in Ioc (0:ℝ) 1, ∫ u : ℝ, cosKernel a p (u,t)) := by
  first
  | exact integral_integral_swap hi
  | exact?

theorem cosine_gram_identity {ι : Type*} (s : Finset ι)
    (c p : ι → ℝ) (v : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i*c j*Real.cos (v*(p i-p j))) =
      (∑ i ∈ s, c i * Real.cos (v*p i))^2 +
      (∑ i ∈ s, c i * Real.sin (v*p i))^2 := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
      ((c i*Real.cos (v*p i))*(c j*Real.cos (v*p j)) +
       (c i*Real.sin (v*p i))*(c j*Real.sin (v*p j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_sub, Real.cos_sub]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

theorem cosine_gram_nonneg {ι : Type*} (s : Finset ι)
    (c p : ι → ℝ) (v : ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*Real.cos (v*(p i-p j)) := by
  rw [cosine_gram_identity]
  positivity

theorem weighted_gram_nonneg {ι : Type*} (s : Finset ι)
    (c p : ι → ℝ) (a u t : ℝ) :
    0 ≤ potential a u *
      (∑ i ∈ s, ∑ j ∈ s, c i*c j*Real.cos ((t*u)*(p i-p j))) := by
  apply mul_nonneg
  · unfold potential
    positivity
  · exact cosine_gram_nonneg s c p (t*u)

theorem integrated_gram_nonneg {ι : Type*} (s : Finset ι)
    (c p : ι → ℝ) (a : ℝ) :
    0 ≤ ∫ z : ℝ × ℝ, potential a z.1 *
      (∑ i ∈ s, ∑ j ∈ s, c i*c j*Real.cos ((z.2*z.1)*(p i-p j)))
      ∂(volume.prod (volume.restrict (Ioc (0:ℝ) 1))) := by
  apply integral_nonneg
  intro z
  exact weighted_gram_nonneg s c p a z.1 z.2

end
end Manuscript13.EulerianPositiveDefinite20261124

#print axioms Manuscript13.EulerianPositiveDefinite20261124.sinc_zero
#print axioms Manuscript13.EulerianPositiveDefinite20261124.sinc_even
#print axioms Manuscript13.EulerianPositiveDefinite20261124.cosine_average
#print axioms Manuscript13.EulerianPositiveDefinite20261124.product_fubini
#print axioms Manuscript13.EulerianPositiveDefinite20261124.cosine_gram_identity
#print axioms Manuscript13.EulerianPositiveDefinite20261124.cosine_gram_nonneg
#print axioms Manuscript13.EulerianPositiveDefinite20261124.weighted_gram_nonneg
#print axioms Manuscript13.EulerianPositiveDefinite20261124.integrated_gram_nonneg
