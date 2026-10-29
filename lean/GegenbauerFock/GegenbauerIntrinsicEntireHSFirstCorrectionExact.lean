import GegenbauerFock.GegenbauerIntrinsicEntireHSBounds

/-!
# V007 — explicit exact first excited correction in the genuine Fock S₂ mass

The positive non-vacuum coefficient of the unregularized Kummer
series is not just an abstract recursively defined ratio:
the n=1 term in the physical Gaussian argument 1/(4α) is precisely
1/[8 α (λ+1)]. The certified two-sided S₂ and analytic source-Gram
trace estimates thereby receive a fully explicit real rational form
with no hidden coefficient convention or conditional moment formula.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The exact n=1 unregularized Kummer contribution, with all
Gaussian and ultraspherical normalization factors accounted for. -/
theorem Kummer_first_excited_coefficient_exact
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    KummerCoefficients.ratio lam 1 * (1 / (4 * alpha)) =
      1 / (8 * alpha * (lam + 1)) := by
  have hλ : lam + 1 ≠ 0 := ne_of_gt (by linarith)
  have ha' : alpha ≠ 0 := ne_of_gt ha
  simp only [KummerCoefficients.ratio_succ, KummerCoefficients.ratio_zero,
    Nat.cast_zero, zero_add, one_mul]
  field_simp [hλ, ha']
  ring

/-- Exact first nonvacuum correction lower bound on the *actual*
infinite-dimensional entire-Gaussian Fock Hilbert–Schmidt energy. -/
theorem C_intrinsicEntire_HS_energy_explicit_first_lower
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    1 + 1 / (8 * alpha * (lam + 1)) ≤
      ∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2 := by
  have hbound := (C_intrinsicEntire_HS_energy_two_sided_bound
    lam alpha hlam ha b).1
  rw [Kummer_first_excited_coefficient_exact lam alpha hlam ha] at hbound
  exact hbound

/-- The exact same nonvacuum correction is a certified lower bound
for the basis-independent trace of the genuine analytic Fock source Gram. -/
theorem C_intrinsicEntire_Gram_trace_explicit_first_lower
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    1 + 1 / (8 * alpha * (lam + 1)) ≤
      (∑' i : ι, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) := by
  have hbound := (C_intrinsicEntire_Gram_trace_two_sided_bound
    lam alpha hlam ha b).1
  rw [Kummer_first_excited_coefficient_exact lam alpha hlam ha] at hbound
  exact hbound

#print axioms GegenbauerFock.GeneralUltrasphericalFock.Kummer_first_excited_coefficient_exact
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_explicit_first_lower
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_explicit_first_lower

end GegenbauerFock.GeneralUltrasphericalFock
