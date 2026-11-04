import GegenbauerFock.CanonicalCFCGramTikhonovStrongConvergence
import GegenbauerFock.GramApproximateZeroSpectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# V007 — sharp norm-one obstruction for the genuine source-Gram Tikhonov filter

Although E_eps = eps (G+eps I)⁻¹ tends strongly to zero on every
fixed vector (proved separately), its operator norm is exactly one
for every eps>0.

The lower bound uses the actual normalized approximate-zero sequence
of G=C* C on full weighted complex L². Along this sequence, G u_n→0
and the exact Gram-range identity forces u_n-E_eps u_n→0, while
‖u_n‖=1. Thus no strict uniform contraction bound is possible.

The proof does not assume a compact spectral diagonal model, an
unbounded inverse as a bounded map, or finite-rank truncation.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev SharpRegH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

/-- The actual regularization residual E_eps on the complete source
Hilbert space has operator norm exactly one for every eps>0. -/
theorem sourceGramTikhonov_error_opNorm_eq_one
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) :
    ‖(eps : ℂ) •
      Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)‖ = 1 := by
  let G := gram lam alpha hlam ha
  let E : SharpRegH lam →L[ℂ] SharpRegH lam :=
    (eps : ℂ) • Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)
  have hupper : ‖E‖ ≤ 1 :=
    sourceGramTikhonov_error_opNorm_le_one lam alpha hlam ha eps heps
  obtain ⟨u, hunit, hGramZero⟩ :=
    gram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  have hGzero :
      Tendsto (fun n : ℕ => G (u n))
        atTop (nhds (0 : SharpRegH lam)) := by
    exact hGramZero
  have hEGzero :
      Tendsto (fun n : ℕ => E (G (u n)))
        atTop (nhds (0 : SharpRegH lam)) := by
    have hcomp := E.continuous.continuousAt.tendsto.comp hGzero
    simpa only [Function.comp_def, map_zero] using hcomp
  have hconst :
      Tendsto (fun _ : ℕ => ((eps : ℂ)⁻¹))
        atTop (nhds ((eps : ℂ)⁻¹)) := tendsto_const_nhds
  have hscaledZero :
      Tendsto (fun n : ℕ => ((eps : ℂ)⁻¹) • E (G (u n)))
        atTop (nhds (0 : SharpRegH lam)) := by
    simpa only [smul_zero] using hconst.smul hEGzero
  have hepsNe : (eps : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt heps)
  have hresidual (n : ℕ) :
      ((eps : ℂ)⁻¹) • E (G (u n)) = u n - E (u n) := by
    have h := sourceGramTikhonov_error_on_range
      lam alpha hlam ha eps heps (u n)
    change E (G (u n)) = (eps : ℂ) • (u n - E (u n)) at h
    rw [h, smul_smul, inv_mul_cancel₀ hepsNe, one_smul]
  have hdiffZero :
      Tendsto (fun n : ℕ => u n - E (u n))
        atTop (nhds (0 : SharpRegH lam)) := by
    exact hscaledZero.congr' (Filter.Eventually.of_forall hresidual)
  have hdiffNormZero :
      Tendsto (fun n : ℕ => ‖u n - E (u n)‖)
        atTop (nhds (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hdiffZero
  have hbound (n : ℕ) :
      1 - ‖E‖ ≤ ‖u n - E (u n)‖ := by
    have hu : ‖u n‖ ≤ ‖u n - E (u n)‖ + ‖E (u n)‖ := by
      calc
        ‖u n‖ = ‖(u n - E (u n)) + E (u n)‖ := by congr 1; abel
        _ ≤ ‖u n - E (u n)‖ + ‖E (u n)‖ := norm_add_le _ _
    have hEu : ‖E (u n)‖ ≤ ‖E‖ * ‖u n‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [hunit n] at hu hEu
    nlinarith
  have hlower : (1 : ℝ) ≤ ‖E‖ := by
    by_contra hnot
    have hlt : ‖E‖ < 1 := lt_of_not_ge hnot
    have hpos : (0 : ℝ) < 1 - ‖E‖ := sub_pos.mpr hlt
    have hnear : ∀ᶠ z : ℝ in nhds (0 : ℝ), z < 1 - ‖E‖ := by
      exact isOpen_Iio.mem_nhds
        (show (0 : ℝ) ∈ Set.Iio (1 - ‖E‖) from hpos)
    have hevent :
        ∀ᶠ n : ℕ in atTop, ‖u n - E (u n)‖ < 1 - ‖E‖ :=
      hdiffNormZero.eventually hnear
    obtain ⟨n, hn⟩ := hevent.exists
    exact (not_lt_of_ge (hbound n)) hn
  change ‖E‖ = 1
  exact le_antisymm hupper hlower

/-- Despite full-source strong convergence, the genuine bounded
Tikhonov filter never converges to identity in operator norm. -/
theorem sourceGramTikhonov_filter_error_opNorm_eq_one
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) :
    ‖(1 : SharpRegH lam →L[ℂ] SharpRegH lam) -
      sourceGramTikhonovFilter lam alpha hlam ha eps‖ = 1 := by
  rw [sourceGramTikhonov_filter_error_identity lam alpha hlam ha eps heps]
  exact sourceGramTikhonov_error_opNorm_eq_one lam alpha hlam ha eps heps

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_error_opNorm_eq_one
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_filter_error_opNorm_eq_one

end GegenbauerFock.GeneralUltrasphericalFock
