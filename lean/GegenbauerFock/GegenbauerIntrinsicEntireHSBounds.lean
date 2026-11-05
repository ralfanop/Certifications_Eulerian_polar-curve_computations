import GegenbauerFock.GegenbauerIntrinsicEntireHSRealGammaIntegral
import GegenbauerFock.GegenbauerIntrinsicEntireCompactQuasiaffinity
import GegenbauerFock.KummerVacuumFirstCorrection

/-!
# V007 — quantitative non-vacuum bounds for the intrinsic Fock Hilbert–Schmidt trace

The exact Kummer value of the true entire Gaussian Fock ultraspherical
Hilbert–Schmidt energy has a STRICT nonvacuum contribution, and sits
between the first two terms of the unregularized hypergeometric series
and the elementary exponential majorant.

All statements apply to every complete orthonormal Hilbert source
basis. They are not finite-matrix approximations, and no claim about
the singular values individually is needed.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- An explicit non-vacuum lower bound and exponential upper bound
for the full infinite-dimensional analytic-Fock S₂ energy. -/
theorem C_intrinsicEntire_HS_energy_two_sided_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    1 + KummerCoefficients.ratio lam 1 * (1 / (4 * alpha)) ≤
        (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) ∧
      (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) ≤
        Real.exp (1 / (4 * alpha)) := by
  have ht : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  constructor
  · rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b]
    exact KummerCoefficients.kummerSeries_ge_vacuum_add_first
      lam (1 / (4 * alpha)) hlam ht
  · rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b]
    exact KummerCoefficients.kummerSeries_le_exp
      lam (1 / (4 * alpha)) hlam ht

/-- For every finite α>0, the true S₂ energy is strictly larger than
the vacuum contribution 1: the first excited term is nonzero. -/
theorem C_intrinsicEntire_HS_energy_gt_one
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    1 < ∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2 := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b]
  exact KummerCoefficients.kummerSeries_gt_one
    lam (1 / (4 * alpha)) hlam (by positivity)

/-- The positive source Gram of the *actual* analytic Fock transform
inherits the same two-sided quantitative trace estimate, independently
of the choice of complete source Hilbert basis. -/
theorem C_intrinsicEntire_Gram_trace_two_sided_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    1 + KummerCoefficients.ratio lam 1 * (1 / (4 * alpha)) ≤
        (∑' i : ι,
          RCLike.re (inner ℂ
            (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) ∧
      (∑' i : ι,
          RCLike.re (inner ℂ
            (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) ≤
        Real.exp (1 / (4 * alpha)) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha hlam ha b]
  have ht : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  exact ⟨KummerCoefficients.kummerSeries_ge_vacuum_add_first
      lam (1 / (4 * alpha)) hlam ht,
    KummerCoefficients.kummerSeries_le_exp
      lam (1 / (4 * alpha)) hlam ht⟩

/-- The actual analytic ultraspherical operator norm is controlled by
the exact Kummer S₂ energy, improving the universal exponential bound. -/
theorem C_intrinsicEntire_opNorm_le_sqrt_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire lam alpha hlam ha‖ ≤
      Real.sqrt (KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  rw [C_intrinsicEntire_opNorm_eq lam alpha hlam ha]
  exact C_opNorm_le_sqrt_kummer lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_two_sided_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_gt_one
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_two_sided_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_opNorm_le_sqrt_kummer

end GegenbauerFock.GeneralUltrasphericalFock
