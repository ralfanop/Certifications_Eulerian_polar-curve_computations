import Mathlib

/-!
# Manuscript 15 (25 Nov 2026): exact quartic period-curve and crease algebra

Authoritative source:
- Manuscript_15_20261125_CROSS_CONNECTIONS(1).zip
- ZIP SHA256: 79a294f03b3cc645310b7fd1190b0b8e809b4b25f94b0a57a54f929a87a4785f
- LaTeX SHA256: 5b1d65a70d9121bcc7ef3ca7ca76af327ffaf9a8a9d8a62b8a7e7b0699f8fd28

New Section 10, Corollary 10.1 and Propositions 10.2--10.3.
Labels: eq:cross-curveZ, eq:cross-curveW, eq:cross-curveTarget,
eq:cross-curveDiff, eq:cross-curvePeriod15, eq:cross-creaseJet,
eq:cross-creaseSelf, eq:cross-creaseLim.

The theorem below verifies the ACTUAL affine rational map
z = sqrt(2) t/(1-t²), W = (1+t²)Y/(1-t²)²,
on Y²=1+t⁴, and its target equation W²=(1+z²)(1+2z²).

The second block certifies algebraic coefficients and exact rescaling
of the quartic Taylor polynomial of the self-dual crease.

The analytic assertions not covered by this module are:
(1) extension to smooth projective genus-one curves and degree two;
(2) derivative one-form and the real period INTEGRAL identity;
(3) equality between the ACTUAL analytic crease D_k and its
    quartic Taylor jet with a uniform O(u^6) remainder;
(4) the scaling LIMIT of the actual D_{k_M}, and the vacuum
    and amplitude identities involving external source manuscripts.
These must not be inferred from the polynomial identities alone.
-/

namespace Manuscript15.CrossQuartic20261125

/-- The precise real scale in the degree-two quartic parametrisation. -/
theorem sqrt_two_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
  exact Real.sq_sqrt (by norm_num)

/-- The first identity used in eq:cross-curveTarget. -/
theorem quartic_factor_one (t : ℝ) :
    (1 - t ^ 2) ^ 2 + (Real.sqrt 2) ^ 2 * t ^ 2 = 1 + t ^ 4 := by
  rw [sqrt_two_sq]
  ring

/-- The second identity used in eq:cross-curveTarget. -/
theorem quartic_factor_two (t : ℝ) :
    (1 - t ^ 2) ^ 2 + 2 * (Real.sqrt 2) ^ 2 * t ^ 2 =
      (1 + t ^ 2) ^ 2 := by
  rw [sqrt_two_sq]
  ring

/-- The true rational affine coordinate in eq:cross-curveZ. -/
noncomputable def quarticZ (t : ℝ) : ℝ :=
  Real.sqrt 2 * t / (1 - t ^ 2)

/-- The true rational affine coordinate in eq:cross-curveW. -/
noncomputable def quarticW (t Y : ℝ) : ℝ :=
  (1 + t ^ 2) * Y / (1 - t ^ 2) ^ 2

/-- Projective-numerator version of the quartic morphism target equation,
without any division or assumptions about t being a real nonsingular
source point except the actual curve equation. -/
theorem quartic_target_numerator (t Y : ℝ) (hY : Y ^ 2 = 1 + t ^ 4) :
    ((1 + t ^ 2) * Y) ^ 2 =
      ((1 - t ^ 2) ^ 2 + (Real.sqrt 2) ^ 2 * t ^ 2) *
      ((1 - t ^ 2) ^ 2 + 2 * (Real.sqrt 2) ^ 2 * t ^ 2) := by
  rw [mul_pow, hY, quartic_factor_one, quartic_factor_two]
  ring

/-- The actual rational map of Proposition 10.2 sends every affine
point of Y²=1+t⁴, t²≠1, onto the target quartic
W²=(1+z²)(1+2z²). This is NOT merely a relation between unnamed
symbols: both z and W are evaluated at the concrete source (t,Y). -/
theorem quartic_target_affine (t Y : ℝ)
    (ht : 1 - t ^ 2 ≠ 0) (hY : Y ^ 2 = 1 + t ^ 4) :
    quarticW t Y ^ 2 =
      (1 + quarticZ t ^ 2) * (1 + 2 * quarticZ t ^ 2) := by
  have hnum := quartic_target_numerator t Y hY
  calc
    quarticW t Y ^ 2 =
        (((1 + t ^ 2) * Y) ^ 2) / (1 - t ^ 2) ^ 4 := by
          unfold quarticW
          simp only [div_pow, ← pow_mul]
          norm_num
    _ = (((1 - t ^ 2) ^ 2 + (Real.sqrt 2) ^ 2 * t ^ 2) *
         ((1 - t ^ 2) ^ 2 + 2 * (Real.sqrt 2) ^ 2 * t ^ 2)) /
         (1 - t ^ 2) ^ 4 := by
           rw [hnum]
    _ = (1 + quarticZ t ^ 2) * (1 + 2 * quarticZ t ^ 2) := by
          unfold quarticZ
          field_simp [ht]

/-- Every source parameter t satisfies the quadratic equation
z*t²+sqrt(2)*t-z=0 at its actual target coordinate z.
This is the affine fibre polynomial underlying the degree-two
claim of Proposition 10.2. -/
theorem quartic_fibre_quadratic (t : ℝ)
    (ht : 1 - t ^ 2 ≠ 0) :
    quarticZ t * t ^ 2 + Real.sqrt 2 * t - quarticZ t = 0 := by
  have hz : quarticZ t * (1 - t ^ 2) = Real.sqrt 2 * t := by
    unfold quarticZ
    field_simp [ht]
  calc
    quarticZ t * t ^ 2 + Real.sqrt 2 * t - quarticZ t =
        -(quarticZ t * (1 - t ^ 2) - Real.sqrt 2 * t) := by ring
    _ = 0 := by rw [hz]; ring

/-- The real-analytic self-dual crease's claimed quartic TAYLOR
POLYNOMIAL, rather than the actual transcendental D_k. -/
noncomputable def creaseQuarticJet (k u : ℝ) : ℝ :=
  (1 - k ^ 2) / 2 * u ^ 2 +
    (1 - 2 * k ^ 2 + 5 * k ^ 4) / 24 * u ^ 4

/-- The precise quadratic coefficient in eq:cross-creaseJet. -/
theorem crease_quadratic_coefficient (k : ℝ) :
    (1 - k ^ 2) / 2 = (1 - k * k) / 2 := by
  ring

/-- The exact cancellation of the quadratic coefficient at k=1,
and its remaining positive quartic coefficient eq:cross-creaseSelf. -/
theorem crease_selfdual_quartic (u : ℝ) :
    creaseQuarticJet 1 u = u ^ 4 / 6 := by
  unfold creaseQuarticJet
  ring

/-- Polynomial identity for the critical scaling
k²=1-80 lam ε², u=εv of eq:cross-creaseLim,
including BOTH subleading corrections in ε² and ε⁴.
This is an exact identity for the source's quartic Taylor
POLYNOMIAL (not an unproved limiting theorem about D_k). -/
theorem crease_critical_exact_rescaling
    (k ε v lam : ℝ) (hk : k ^ 2 = 1 - 80 * lam * ε ^ 2) :
    3 * creaseQuarticJet k (ε * v) =
      20 * ε ^ 4 *
        (v ^ 4 / 40 + 6 * lam * v ^ 2 -
          4 * lam * ε ^ 2 * v ^ 4 +
          200 * lam ^ 2 * ε ^ 4 * v ^ 4) := by
  have hk4 : k ^ 4 = (1 - 80 * lam * ε ^ 2) ^ 2 := by
    calc
      k ^ 4 = (k ^ 2) ^ 2 := by ring
      _ = _ := by rw [hk]
  unfold creaseQuarticJet
  rw [hk4, hk]
  ring

#print axioms Manuscript15.CrossQuartic20261125.sqrt_two_sq
#print axioms Manuscript15.CrossQuartic20261125.quartic_factor_one
#print axioms Manuscript15.CrossQuartic20261125.quartic_factor_two
#print axioms Manuscript15.CrossQuartic20261125.quartic_target_numerator
#print axioms Manuscript15.CrossQuartic20261125.quartic_target_affine
#print axioms Manuscript15.CrossQuartic20261125.quartic_fibre_quadratic
#print axioms Manuscript15.CrossQuartic20261125.crease_quadratic_coefficient
#print axioms Manuscript15.CrossQuartic20261125.crease_selfdual_quartic
#print axioms Manuscript15.CrossQuartic20261125.crease_critical_exact_rescaling

end Manuscript15.CrossQuartic20261125
