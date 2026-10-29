import GegenbauerFock.GegenbauerIntrinsicEntireApproximateNullSequence
import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation

/-!
# V007 — bounded-disk uniform control of the genuine Fourier–Bochner transform

The exact coherent reproducing evaluation has squared norm
exp(α‖z‖²). On a closed disk, the original ultraspherical
Fourier–Bochner transform is therefore bounded by a SINGLE constant
independent of the complex frequency z. Using the already kernel-checked
unit-norm approximate-null source sequence, this bound shows that
all genuine Fourier–Bochner data tend to zero uniformly on each
bounded disk, although the L² source sequence has no strong limit.

This makes precise the distinction between exact analytic uniqueness
and norm-stable inverse reconstruction: even locally uniform
convergence of the full complex Fourier transform does not imply
convergence of the ultraspherical L² sources.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine complex-frequency Fourier–Bochner integral admits
one frequency-independent Gaussian-Fock norm bound on each closed disk.
The real square root is strictly positive. -/
theorem ultraspherical_fourierBochner_norm_le_on_disk
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R : ℝ) (hR : 0 ≤ R)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (z : ℂ)
    (hz : ‖z‖ ≤ R) :
    ‖∫ v : ℝ, f v *
        Complex.exp (Complex.I * z * (v : ℂ) / 2)
        ∂(Ultraspherical.measure lam)‖ ≤
      Real.sqrt (Real.exp (alpha * R ^ 2)) *
        ‖C_intrinsicEntire lam alpha hlam ha f‖ := by
  have hpow : ‖z‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hexp : Real.exp (alpha * ‖z‖ ^ 2) ≤
      Real.exp (alpha * R ^ 2) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hpow (le_of_lt ha))
  have hsq : ‖FockEvaluation.evaluation alpha ha z‖ ^ 2 ≤
      Real.exp (alpha * R ^ 2) := by
    rw [FockEvaluation.evaluation_norm_sq alpha ha z]
    exact hexp
  have hroot :
      (Real.sqrt (Real.exp (alpha * R ^ 2))) ^ 2 =
        Real.exp (alpha * R ^ 2) :=
    Real.sq_sqrt (le_of_lt (Real.exp_pos _))
  have hnorm :
      ‖FockEvaluation.evaluation alpha ha z‖ ≤
        Real.sqrt (Real.exp (alpha * R ^ 2)) := by
    nlinarith [norm_nonneg (FockEvaluation.evaluation alpha ha z),
      Real.sqrt_nonneg (Real.exp (alpha * R ^ 2))]
  calc
    ‖∫ v : ℝ, f v *
        Complex.exp (Complex.I * z * (v : ℂ) / 2)
        ∂(Ultraspherical.measure lam)‖ ≤
      ‖FockEvaluation.evaluation alpha ha z‖ *
        ‖C lam alpha hlam ha f‖ :=
      intrinsicEntire_fourierIntegral_evaluation_bound lam alpha hlam ha f z
    _ ≤ Real.sqrt (Real.exp (alpha * R ^ 2)) *
        ‖C_intrinsicEntire lam alpha hlam ha f‖ := by
      rw [← C_intrinsicEntire_norm lam alpha hlam ha f]
      exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- Actual unit ultraspherical L² vectors may have Fourier–Bochner
images tending to zero UNIFORMLY on every bounded complex disk,
while their source sequence has no strong L² limit. This gives a
stronger instability witness than separate pointwise convergence. -/
theorem ultraspherical_fourierBochner_locallyUniform_null_no_strong_source_limit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      (∀ R : ℝ, 0 ≤ R →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
            ‖∫ v : ℝ, u n v *
              Complex.exp (Complex.I * z * (v : ℂ) / 2)
              ∂(Ultraspherical.measure lam)‖ < ε) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ¬ Tendsto u atTop (nhds f)) := by
  obtain ⟨u, hunit, hFock, hnostrong⟩ :=
    C_intrinsicEntire_normalized_approximate_null_no_strong_limit
      lam alpha hlam ha
  refine ⟨u, hunit, ?_, hnostrong⟩
  intro R hR ε hε
  let K : ℝ := Real.sqrt (Real.exp (alpha * R ^ 2))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hnorm :
      Tendsto (fun n : ℕ =>
        ‖C_intrinsicEntire lam alpha hlam ha (u n)‖)
        atTop (nhds (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hFock
  have hmul :
      Tendsto (fun n : ℕ =>
        K * ‖C_intrinsicEntire lam alpha hlam ha (u n)‖)
        atTop (nhds (0 : ℝ)) := by
    convert tendsto_const_nhds.mul hnorm using 1 <;> simp [K]
  have hsmall :
      ∀ᶠ n : ℕ in atTop,
        K * ‖C_intrinsicEntire lam alpha hlam ha (u n)‖ < ε := by
    exact (tendsto_order.1 hmul).2 ε hε
  filter_upwards [hsmall] with n hn z hz
  have hb := ultraspherical_fourierBochner_norm_le_on_disk
    lam alpha hlam ha R hR (u n) z hz
  exact lt_of_le_of_lt (by simpa only [K] using hb) hn

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_norm_le_on_disk
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_locallyUniform_null_no_strong_source_limit

end GegenbauerFock.GeneralUltrasphericalFock
