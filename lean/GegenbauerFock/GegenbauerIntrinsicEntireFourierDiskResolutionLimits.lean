import GegenbauerFock.GegenbauerIntrinsicEntireFourierLocallyUniformInstability

/-!
# V007 — arbitrary precision Fourier samples on bounded complex disks

The previously certified locally uniform approximate-null theorem gives
a quantitative obstruction to stable inverse reconstruction from ANY
bounded complex frequency window: for every radius R ≥ 0 and every
tolerance ε > 0, some ultraspherical L² input of norm exactly one
has genuine Fourier–Bochner integral uniformly smaller than ε on the
whole disk.

In particular no nonnegative lower stability constant K can recover
the source norm from the Fourier modulus at every frequency on such a
bounded disk.

These statements are existential exact infinite-dimensional facts,
not a numerical discretization, finite-data uniqueness assertion or
constructive approximation algorithm.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For ANY bounded complex frequency disk and arbitrary positive
precision ε, a unit ultraspherical L² input has uniformly negligible
actual Fourier–Bochner data on the entire disk. -/
theorem ultraspherical_fourierBochner_arbitrarilySmall_on_disk
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖f‖ = 1 ∧
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖∫ v : ℝ, f v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)‖ < ε := by
  obtain ⟨u, hunit, huniform, _⟩ :=
    ultraspherical_fourierBochner_locallyUniform_null_no_strong_source_limit
      lam alpha hlam ha
  obtain ⟨n, hn⟩ := (huniform R hR ε hε).exists
  exact ⟨u n, hunit n, hn⟩

/-- No nonnegative constant K provides even a pointwise-at-every-z
lower stability bound from the original Fourier modulus on a bounded
complex frequency disk. The counterexample has SOURCE NORM ONE. -/
theorem ultraspherical_fourierBochner_no_disk_lower_stability_constant
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R K : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖f‖ = 1 ∧
      ∀ z : ℂ, ‖z‖ ≤ R →
        K * ‖∫ v : ℝ, f v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)‖ < ‖f‖ := by
  have hK1 : 0 < K + 1 := by linarith
  obtain ⟨f, hf, hsmall⟩ :=
    ultraspherical_fourierBochner_arbitrarilySmall_on_disk
      lam alpha hlam ha R hR (1 / (K + 1)) (one_div_pos.mpr hK1)
  refine ⟨f, hf, ?_⟩
  intro z hz
  have hb :=
    mul_le_mul_of_nonneg_left (le_of_lt (hsmall z hz)) hK
  have hfrac : K * (1 / (K + 1)) < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_iff₀ hK1).mpr (by linarith)
  rw [hf]
  exact lt_of_le_of_lt hb hfrac

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_arbitrarilySmall_on_disk
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_no_disk_lower_stability_constant

end GegenbauerFock.GeneralUltrasphericalFock
