import EulerianCert.EulerianFourier
import EulerianCert.KrapivskyLuckEnergy

/-! Recover the total sinc-square energy from the already proved
Eulerian Fourier inversion at the central sample, then discharge the
explicit normalization hypothesis in the sine-integral tail identities. -/

open MeasureTheory Set Real
noncomputable section
namespace Manuscripts14And15.KrapivskyLuck

local notation "rE" => EulerianCert.FourierModes.rE

theorem real_line_eulerian_energy :
    (∫ t : ℝ, rE t ^ 2) = 2 * Real.pi := by
  have hg : EulerianCert.EulerianFourier.g 1 0 = 1 := by
    have h := EulerianCert.EulerianFourier.g_sample (n := 1) (k := 1) (by decide) (by decide)
    norm_num [EulerianCert.Bracket.E_one_zero] at h
    exact h
  have h := EulerianCert.EulerianFourier.g_inversion (n := 1) (by decide) 0
  norm_num at h
  rw [hg] at h
  field_simp [Real.pi_ne_zero] at h
  linarith

theorem sine_integral_tail_unconditional :
    Manuscripts11And12.KrapivskyLuck.S =
      (1 / (4 * Real.pi)) * (∫ t in {t : ℝ | 2 * Real.pi < |t|}, rE t ^ 2) :=
  Manuscripts11And12.KrapivskyLuck.S_tail real_line_eulerian_energy

theorem sine_integral_normalized_tail_unconditional :
    Manuscripts11And12.KrapivskyLuck.S =
      (1 / 2) * (∫ t in {t : ℝ | 2 * Real.pi < |t|}, |Manuscripts11And12.KrapivskyLuck.k0 t| ^ 2) :=
  Manuscripts11And12.KrapivskyLuck.S_normalized_tail real_line_eulerian_energy

#print axioms real_line_eulerian_energy
#print axioms sine_integral_tail_unconditional
#print axioms sine_integral_normalized_tail_unconditional

end Manuscripts14And15.KrapivskyLuck
