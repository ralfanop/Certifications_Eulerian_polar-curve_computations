import GegenbauerFock.GegenbauerIntrinsicEntireFourierLocallyUniformInstability

/-!
# V007 — instability of genuine real-frequency Fourier window measurements

The genuine complex-frequency Fourier–Bochner transform is already
proved locally uniformly unstable in the certified intrinsic Gaussian
Fock setting. This module extracts the physically more directly
observable consequence for REAL frequencies on ANY bounded interval.
At arbitrary accuracy ε>0, unit ultraspherical L² sources can have
Fourier observations below ε at every real frequency |t|≤R.

This is an exact operator-theoretic stability obstruction, NOT
non-injectivity and NOT a numerical approximation theorem.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For any bounded REAL frequency window and any ε>0, there
exists a genuine unit L² source whose Fourier–Bochner observations
are uniformly smaller than ε on the entire real window. -/
theorem ultraspherical_fourierBochner_realWindow_arbitrarilySmall
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖f‖ = 1 ∧
      ∀ t : ℝ, |t| ≤ R →
        ‖∫ v : ℝ, f v *
          Complex.exp (Complex.I * (t : ℂ) * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)‖ < ε := by
  obtain ⟨u, hunit, huniform, _⟩ :=
    ultraspherical_fourierBochner_locallyUniform_null_no_strong_source_limit
      lam alpha hlam ha
  obtain ⟨n, hn⟩ := (huniform R hR ε hε).exists
  refine ⟨u n, hunit n, ?_⟩
  intro t ht
  apply hn (t : ℂ)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using ht

/-- No finite lower reconstruction factor K≥0 controls the
ultraspherical L² source norm from the ENTIRE continuous real
frequency window [-R,R]; a source of norm one violates the
candidate bound simultaneously at every sampled real frequency. -/
theorem ultraspherical_fourierBochner_realWindow_no_lower_constant
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R K : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖f‖ = 1 ∧
      ∀ t : ℝ, |t| ≤ R →
        K * ‖∫ v : ℝ, f v *
          Complex.exp (Complex.I * (t : ℂ) * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)‖ < ‖f‖ := by
  have hK1 : 0 < K + 1 := by linarith
  obtain ⟨f, hf, hsmall⟩ :=
    ultraspherical_fourierBochner_realWindow_arbitrarilySmall
      lam alpha hlam ha R (1 / (K + 1)) hR (one_div_pos.mpr hK1)
  refine ⟨f, hf, ?_⟩
  intro t ht
  have hb := mul_le_mul_of_nonneg_left (le_of_lt (hsmall t ht)) hK
  have hfrac : K * (1 / (K + 1)) < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_iff₀ hK1).mpr (by linarith)
  rw [hf]
  exact lt_of_le_of_lt hb hfrac

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_realWindow_arbitrarilySmall
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_realWindow_no_lower_constant

end GegenbauerFock.GeneralUltrasphericalFock
