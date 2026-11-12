/-
Manuscript 15 — initial Lean 4 formalization, 10 November 2026.
Scope: exact real cycloidal reconstruction from the pre-existing Eulerian sinc.
This module is deliberately independent of any proposed gravitational interpretation.
It must be compiled and axiom-audited by CI before being counted as certified.
-/
import EulerianCert.FourierModes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

noncomputable section

namespace Manuscript15

/-- First coordinate of the cycloidal reconstruction from a real function. -/
def X (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * t * (1 - f (2 * t))

/-- Second coordinate of the cycloidal reconstruction from a real function. -/
def Y (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * t ^ 2 / 2 * (f t) ^ 2

/-- The existing, kernel-checked Eulerian sinc, from Manuscript 11. -/
abbrev eulerianSinc : ℝ → ℝ := EulerianCert.FourierModes.rE

/-- The Eulerian sinc reconstructs the cycloid's first coordinate. -/
theorem eulerian_X_eq_cycloid (a t : ℝ) :
    X a eulerianSinc t = a * (t - Real.sin t) := by
  by_cases ht : t = 0
  · subst t
    simp [X]
  · have h2 : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
    unfold X eulerianSinc
    rw [EulerianCert.FourierModes.rE_of_ne_zero h2]
    have hhalf : (2 * t) / 2 = t := by ring
    rw [hhalf]
    have hcancel : t * (2 * Real.sin t / (2 * t)) = Real.sin t := by
      field_simp [ht]
      <;> ring
    calc
      a * t * (1 - 2 * Real.sin t / (2 * t)) =
          a * (t - t * (2 * Real.sin t / (2 * t))) := by ring
      _ = a * (t - Real.sin t) := by rw [hcancel]

/-- The Eulerian sinc reconstructs the cycloid's second coordinate. -/
theorem eulerian_Y_eq_cycloid (a t : ℝ) :
    Y a eulerianSinc t = a * (1 - Real.cos t) := by
  by_cases ht : t = 0
  · subst t
    simp [Y]
  · have hsinc : eulerianSinc t = 2 * Real.sin (t / 2) / t :=
      EulerianCert.FourierModes.rE_of_ne_zero ht
    have hcancel :
        t ^ 2 / 2 * (2 * Real.sin (t / 2) / t) ^ 2 =
          2 * Real.sin (t / 2) ^ 2 := by
      field_simp [ht]
      <;> ring
    have hangle : 2 * Real.sin (t / 2) ^ 2 = 1 - Real.cos t := by
      have hc := Real.cos_two_mul (t / 2)
      have hsc := Real.sin_sq_add_cos_sq (t / 2)
      have htwice : 2 * (t / 2) = t := by ring
      rw [htwice] at hc
      nlinarith
    unfold Y
    rw [hsinc]
    calc
      a * t ^ 2 / 2 * (2 * Real.sin (t / 2) / t) ^ 2 =
          a * (t ^ 2 / 2 * (2 * Real.sin (t / 2) / t) ^ 2) := by ring
      _ = a * (2 * Real.sin (t / 2) ^ 2) := by rw [hcancel]
      _ = a * (1 - Real.cos t) := by rw [hangle]

/-- Kinematic identity of the reconstructed cycloid (Manuscript 15, Eq. X'=Y).
This does not yet certify uniqueness among probability measures. -/
theorem eulerian_kinematic (a t : ℝ) :
    HasDerivAt (X a eulerianSinc) (Y a eulerianSinc t) t := by
  have hfun : X a eulerianSinc = fun x => a * (x - Real.sin x) := by
    funext x
    exact eulerian_X_eq_cycloid a x
  rw [hfun, eulerian_Y_eq_cycloid]
  convert ((hasDerivAt_id' t).sub (hasDerivAt_sin t)).const_mul a using 1 <;> ring

/-- Algebraic leading-order cusp constant. The analytic limit is a later target. -/
theorem cusp_leading_coefficient (a v t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    (2 * a * v * t ^ 3) ^ 2 / ((a / 2 * t ^ 2) ^ 3) =
      32 * v ^ 2 / a := by
  field_simp [ha, ht]
  <;> ring

/-- The distinguished coordinate of the standard cycloid. -/
theorem eulerian_Y_pi (a : ℝ) :
    Y a eulerianSinc Real.pi = 2 * a := by
  rw [eulerian_Y_eq_cycloid, Real.cos_pi]
  ring


/-! ### Manuscript 15, Proposition: coordinate compatibility and injectivity -/

/-- Exact compatibility between the two reconstructed coordinates.
    In division-free form this holds also at a=0 and t=0. -/
theorem reconstruction_compatibility_polynomial (a t : ℝ) (f : ℝ → ℝ) :
    2 * a * Y a f t = (a * t - 2 * X a f (t / 2)) ^ 2 := by
  unfold X Y
  have htwo : 2 * (t / 2) = t := by ring
  rw [htwo]
  ring

/-- Manuscript 15, compatibility formula, for every nonzero scale a. -/
theorem reconstruction_compatibility (a t : ℝ) (f : ℝ → ℝ) (ha : a ≠ 0) :
    Y a f t = (a * t - 2 * X a f (t / 2)) ^ 2 / (2 * a) := by
  have h := reconstruction_compatibility_polynomial a t f
  apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).2
  nlinarith

/-- The first coordinate recovers the function away from t=0. -/
theorem reconstruction_inverse (a t : ℝ) (f : ℝ → ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) :
    f t = 1 - (2 / (a * t)) * X a f (t / 2) := by
  unfold X
  have htwo : 2 * (t / 2) = t := by ring
  rw [htwo]
  field_simp [ha, ht]
  <;> ring

/-- Injectivity of the first-coordinate map among functions with the same
    value at the origin. Characteristic-function uniqueness of probability
    measures is a distinct, downstream theorem. -/
theorem reconstruction_first_coordinate_injective
    (a : ℝ) (ha : a ≠ 0) (f g : ℝ → ℝ) (h0 : f 0 = g 0)
    (hX : ∀ t : ℝ, X a f t = X a g t) : f = g := by
  funext t
  by_cases ht : t = 0
  · simpa [ht] using h0
  · have hf := reconstruction_inverse a t f ha ht
    have hg := reconstruction_inverse a t g ha ht
    calc
      f t = 1 - (2 / (a * t)) * X a f (t / 2) := hf
      _ = 1 - (2 / (a * t)) * X a g (t / 2) := by rw [hX (t / 2)]
      _ = g t := hg.symm

/-! ### Abstract pointwise Lipschitz step used in the W₁ estimate -/

/-- Exact X-coordinate difference, before any coupling/transport estimate. -/
theorem reconstruction_X_difference (a t : ℝ) (f g : ℝ → ℝ) :
    |X a f t - X a g t| =
      |a| * |t| * |f (2 * t) - g (2 * t)| := by
  have h :
      X a f t - X a g t = a * t * (g (2 * t) - f (2 * t)) := by
    unfold X
    ring
  rw [h, abs_mul, abs_mul, abs_sub_comm]

/-- If two real kernels satisfy a pointwise |s|-Lipschitz difference bound,
    the first reconstructed coordinate satisfies Manuscript 15's sharp
    2 |a| t² bound. Here δ can later be instantiated with W₁(μ,ν). -/
theorem reconstruction_X_stability
    (a t δ : ℝ) (f g : ℝ → ℝ)
    (hfg : ∀ s : ℝ, |f s - g s| ≤ |s| * δ) :
    |X a f t - X a g t| ≤ 2 * |a| * t ^ 2 * δ := by
  rw [reconstruction_X_difference]
  calc
    |a| * |t| * |f (2 * t) - g (2 * t)|
        ≤ |a| * |t| * (|2 * t| * δ) :=
          mul_le_mul_of_nonneg_left (hfg (2 * t))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = 2 * |a| * t ^ 2 * δ := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [← sq_abs t]
      ring


/-- For two real values in [-1,1], squaring is 2-Lipschitz. -/
theorem squared_difference_bound (u v : ℝ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |u ^ 2 - v ^ 2| ≤ 2 * |u - v| := by
  have hsum : |u + v| ≤ (2 : ℝ) := by
    calc
      |u + v| ≤ |u| + |v| := abs_add_le u v
      _ ≤ 1 + 1 := add_le_add hu hv
      _ = 2 := by norm_num
  calc
    |u ^ 2 - v ^ 2| = |(u - v) * (u + v)| := by congr 1; ring
    _ = |u - v| * |u + v| := abs_mul _ _
    _ ≤ |u - v| * 2 :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = 2 * |u - v| := by ring

/-- Factorization of the Y difference for real kernels. -/
theorem reconstruction_Y_difference (a t : ℝ) (f g : ℝ → ℝ) :
    |Y a f t - Y a g t| =
      (|a| * t ^ 2 / 2) * |(f t) ^ 2 - (g t) ^ 2| := by
  have h :
      Y a f t - Y a g t =
      (a * t ^ 2 / 2) * ((f t) ^ 2 - (g t) ^ 2) := by
    unfold Y
    ring
  rw [h, abs_mul]
  have hfac : |a * t ^ 2 / 2| = |a| * t ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg t)]
    norm_num
  rw [hfac]

/-- The Y coordinate bound underlying the W₁ theorem. The unit-modulus
    hypotheses follow from characteristic functions, but that is not
    claimed as an independently formalized probability theorem here. -/
theorem reconstruction_Y_stability
    (a t δ : ℝ) (f g : ℝ → ℝ)
    (hf : ∀ s : ℝ, |f s| ≤ 1)
    (hg : ∀ s : ℝ, |g s| ≤ 1)
    (hfg : ∀ s : ℝ, |f s - g s| ≤ |s| * δ) :
    |Y a f t - Y a g t| ≤ |a| * |t| ^ 3 * δ := by
  rw [reconstruction_Y_difference]
  have hnonneg : 0 ≤ |a| * t ^ 2 / 2 :=
    div_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (by norm_num)
  calc
    (|a| * t ^ 2 / 2) * |(f t) ^ 2 - (g t) ^ 2|
        ≤ (|a| * t ^ 2 / 2) * (2 * |f t - g t|) :=
          mul_le_mul_of_nonneg_left
            (squared_difference_bound (f t) (g t) (hf t) (hg t)) hnonneg
    _ ≤ (|a| * t ^ 2 / 2) * (2 * (|t| * δ)) := by
          apply mul_le_mul_of_nonneg_left _ hnonneg
          exact mul_le_mul_of_nonneg_left (hfg t) (by norm_num)
    _ = |a| * |t| ^ 3 * δ := by
          rw [← sq_abs t]
          ring

#print axioms Manuscript15.squared_difference_bound
#print axioms Manuscript15.reconstruction_Y_difference
#print axioms Manuscript15.reconstruction_Y_stability

#print axioms Manuscript15.reconstruction_compatibility_polynomial
#print axioms Manuscript15.reconstruction_compatibility
#print axioms Manuscript15.reconstruction_inverse
#print axioms Manuscript15.reconstruction_first_coordinate_injective
#print axioms Manuscript15.reconstruction_X_difference
#print axioms Manuscript15.reconstruction_X_stability

#print axioms Manuscript15.eulerian_X_eq_cycloid
#print axioms Manuscript15.eulerian_Y_eq_cycloid
#print axioms Manuscript15.eulerian_kinematic
#print axioms Manuscript15.cusp_leading_coefficient
#print axioms Manuscript15.eulerian_Y_pi

end Manuscript15
