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
(2) global one-form descent and the real period INTEGRAL identity;
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


/-! ## Actual affine derivative and the second quadratic fibre root -/

/-- Derivative of the actual z(t) rational map of Eq. (551). -/
theorem quarticZ_hasDerivAt (t : ℝ) (ht : 1 - t ^ 2 ≠ 0) :
    HasDerivAt quarticZ
      (Real.sqrt 2 * (1 + t ^ 2) / (1 - t ^ 2) ^ 2) t := by
  have hnum :
      HasDerivAt (fun x : ℝ => Real.sqrt 2 * x) (Real.sqrt 2) t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul (Real.sqrt 2))
  have hden :
      HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_sub (1 : ℝ) using 1
    · funext x
      simp only [Pi.pow_apply, id_eq]
    · norm_num <;> ring
  have h := hnum.div hden ht
  convert h using 1
  · funext x
    rfl
  · field_simp [ht] <;> ring

/-- The source quartic curve has no real branch point with Y zero. -/
theorem quartic_source_y_nonzero (t Y : ℝ)
    (hY : Y ^ 2 = 1 + t ^ 4) : Y ≠ 0 := by
  intro hy
  have hp : 0 ≤ t ^ 4 := by positivity
  rw [hy] at hY
  nlinarith

/-- Exact scalar Jacobian ratio, the affine differential identity
dz/W = sqrt(2) dt/Y in Eq. (554), using genuine Lean differentiation.
The period integration is a separate obligation. -/
theorem quartic_differential_ratio (t Y : ℝ)
    (ht : 1 - t ^ 2 ≠ 0) (hY : Y ≠ 0) :
    deriv quarticZ t / quarticW t Y = Real.sqrt 2 / Y := by
  rw [(quarticZ_hasDerivAt t ht).deriv]
  unfold quarticW
  have hp : 1 + t ^ 2 ≠ 0 := by positivity
  have hpow : (1 - t ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnum : (1 + t ^ 2) * Y ≠ 0 := mul_ne_zero hp hY
  have hW : (1 + t ^ 2) * Y / (1 - t ^ 2) ^ 2 ≠ 0 :=
    div_ne_zero hnum hpow
  field_simp [ht, hY, hp, hpow, hnum, hW] <;> ring

/-- For nonzero source t the companion root -1/t solves the
same quadratic fibre equation at z=z(t). -/
theorem quartic_fibre_companion_root (t : ℝ)
    (ht : t ≠ 0) (hd : 1 - t ^ 2 ≠ 0) :
    quarticZ t * (-1 / t) ^ 2 +
      Real.sqrt 2 * (-1 / t) - quarticZ t = 0 := by
  calc
    quarticZ t * (-1 / t) ^ 2 +
        Real.sqrt 2 * (-1 / t) - quarticZ t =
        -(quarticZ t * t ^ 2 + Real.sqrt 2 * t - quarticZ t) /
          t ^ 2 := by
            field_simp [ht] <;> ring
    _ = 0 := by rw [quartic_fibre_quadratic t hd]; ring

/-- Critical rescaling quotient of the exact quartic Taylor
polynomial. The true analytic remainder is a separate issue. -/
theorem crease_critical_scaled_quotient
    (k ε v lam : ℝ) (hε : ε ≠ 0)
    (hk : k ^ 2 = 1 - 80 * lam * ε ^ 2) :
    3 * creaseQuarticJet k (ε * v) / (20 * ε ^ 4) =
      v ^ 4 / 40 + 6 * lam * v ^ 2 -
        4 * lam * ε ^ 2 * v ^ 4 +
        200 * lam ^ 2 * ε ^ 4 * v ^ 4 := by
  rw [crease_critical_exact_rescaling k ε v lam hk]
  field_simp [hε] <;> ring

#print axioms Manuscript15.CrossQuartic20261125.quarticZ_hasDerivAt
#print axioms Manuscript15.CrossQuartic20261125.quartic_source_y_nonzero
#print axioms Manuscript15.CrossQuartic20261125.quartic_differential_ratio
#print axioms Manuscript15.CrossQuartic20261125.quartic_fibre_companion_root
#print axioms Manuscript15.CrossQuartic20261125.crease_critical_scaled_quotient


/-! ## Affine companion involution for the quartic period map -/

/-- The denominator of the companion parameter t'=-1/t,
cleared of its nonzero real denominator. -/
theorem companion_denominator_identity (t : ℝ) (ht : t ≠ 0) :
    (1 - (-1 / t) ^ 2) * t ^ 2 = t ^ 2 - 1 := by
  field_simp [ht] <;> ring

/-- The companion parameter remains in the SAME admissible
affine chart when the original source parameter is admissible. -/
theorem companion_denominator_nonzero (t : ℝ)
    (ht : t ≠ 0) (hd : 1 - t ^ 2 ≠ 0) :
    1 - (-1 / t) ^ 2 ≠ 0 := by
  intro h
  have hx := companion_denominator_identity t ht
  rw [h] at hx
  apply hd
  nlinarith [hx]

/-- The genuine companion point (t',Y')=(-1/t,Y/t²)
lies on the source curve Y'²=1+t'⁴ whenever (t,Y)
lies on Y²=1+t⁴. -/
theorem companion_source_curve (t Y : ℝ)
    (ht : t ≠ 0) (hY : Y ^ 2 = 1 + t ^ 4) :
    (Y / t ^ 2) ^ 2 = 1 + (-1 / t) ^ 4 := by
  calc
    (Y / t ^ 2) ^ 2 = Y ^ 2 / t ^ 4 := by
      simp only [div_pow, ← pow_mul]
    _ = (1 + t ^ 4) / t ^ 4 := by rw [hY]
    _ = 1 + (-1 / t) ^ 4 := by
      field_simp [ht] <;> ring

/-- Both source parameters t and -1/t have the SAME actual target z
coordinate. This proves a genuine companion fibre relation. -/
theorem quarticZ_companion (t : ℝ)
    (ht : t ≠ 0) (hd : 1 - t ^ 2 ≠ 0) :
    quarticZ (-1 / t) = quarticZ t := by
  have hdp := companion_denominator_nonzero t ht hd
  have hminus : -1 + t ^ 2 ≠ 0 := by
    intro hh
    apply hd
    linarith
  unfold quarticZ
  have hinv : (-1 + t ^ 2) * (-1 + t ^ 2)⁻¹ = 1 := by
    field_simp [hminus]
  field_simp [ht, hd, hdp, hminus] <;>
    linear_combination hinv

/-- Companion source points have the SAME actual target W
coordinate, not merely the same quadratic polynomial. -/
theorem quarticW_companion (t Y : ℝ)
    (ht : t ≠ 0) (hd : 1 - t ^ 2 ≠ 0) :
    quarticW (-1 / t) (Y / t ^ 2) = quarticW t Y := by
  have hdp := companion_denominator_nonzero t ht hd
  have hquartic : 1 - t ^ 2 * 2 + t ^ 4 ≠ 0 := by
    have hx : 1 - t ^ 2 * 2 + t ^ 4 = (1 - t ^ 2) ^ 2 := by ring
    rw [hx]
    exact pow_ne_zero 2 hd
  unfold quarticW
  have hinv :
      (1 - t ^ 2 * 2 + t ^ 4) * (1 - t ^ 2 * 2 + t ^ 4)⁻¹ = 1 := by
    field_simp [hquartic]
  field_simp [ht, hd, hdp, hquartic] <;>
    linear_combination ((1 + t ^ 2) * Y) * hinv

/-- The two real affine companion parameters are distinct.
This excludes a spurious double count of the two roots. -/
theorem quartic_companion_distinct (t : ℝ) (ht : t ≠ 0) :
    -1 / t ≠ t := by
  intro h
  have hm : (-1 / t) * t = t * t :=
    congrArg (fun x : ℝ => x * t) h
  have hdiv : (-1 / t) * t = -1 := by field_simp [ht]
  rw [hdiv] at hm
  nlinarith [sq_nonneg t]

#print axioms Manuscript15.CrossQuartic20261125.companion_denominator_identity
#print axioms Manuscript15.CrossQuartic20261125.companion_denominator_nonzero
#print axioms Manuscript15.CrossQuartic20261125.companion_source_curve
#print axioms Manuscript15.CrossQuartic20261125.quarticZ_companion
#print axioms Manuscript15.CrossQuartic20261125.quarticW_companion
#print axioms Manuscript15.CrossQuartic20261125.quartic_companion_distinct

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
