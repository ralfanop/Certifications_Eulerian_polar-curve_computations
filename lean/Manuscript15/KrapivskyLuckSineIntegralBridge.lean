import Manuscript15.KrapivskyLuckEnergyFubini
import Manuscript15.KrapivskyLuckSincNormalization

/-! M15 §6.6. Combine the actual Laplace/Möbius bridge with the
unconditional Fourier normalization and the exact two-sided sinc tail.
The classical Stirling remainder identification remains separate. -/

open MeasureTheory Set Real ArithmeticFunction
noncomputable section
namespace Manuscripts14And15.KrapivskyLuck

local notation "rE" => EulerianCert.FourierModes.rE

theorem sinc_square_integrable : Integrable (fun t : ℝ => rE t ^ 2) := by
  by_contra h
  have he := real_line_eulerian_energy
  rw [integral_undef h] at he
  linarith [Real.pi_pos]

theorem sinc_square_negative_tail :
    (∫ t : ℝ in Iio (-(2 * Real.pi)), rE t ^ 2) =
      ∫ t : ℝ in Ioi (2 * Real.pi), rE t ^ 2 := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (fun t : ℝ => rE t ^ 2) (Ioi (2 * Real.pi))
  change (∫ t : ℝ in (fun t : ℝ => -t) ⁻¹' Ioi (2 * Real.pi), rE (-t) ^ 2) = _ at h
  have hs : (fun t : ℝ => -t) ⁻¹' Ioi (2 * Real.pi) = Iio (-(2 * Real.pi)) := by
    ext t
    change 2 * Real.pi < -t ↔ t < -(2 * Real.pi)
    constructor <;> intro ht <;> linarith
  rw [hs] at h
  simpa only [EulerianCert.FourierModes.rE_neg] using h

theorem sinc_square_two_sided_tail :
    (∫ t in {t : ℝ | 2 * Real.pi < |t|}, rE t ^ 2) =
      2 * (∫ t : ℝ in Ioi (2 * Real.pi), rE t ^ 2) := by
  have hs : {t : ℝ | 2 * Real.pi < |t|} =
      Iio (-(2 * Real.pi)) ∪ Ioi (2 * Real.pi) := by
    ext t
    change 2 * Real.pi < |t| ↔ t < -(2 * Real.pi) ∨ 2 * Real.pi < t
    rw [← not_le, abs_le]
    simp only [not_and_or, not_le]
  have hd : Disjoint (Iio (-(2 * Real.pi))) (Ioi (2 * Real.pi)) := by
    rw [Set.disjoint_left]
    intro t ht₁ ht₂
    change t < -(2 * Real.pi) at ht₁
    change 2 * Real.pi < t at ht₂
    linarith [Real.pi_pos]
  rw [hs, setIntegral_union hd measurableSet_Ioi sinc_square_integrable.integrableOn
    sinc_square_integrable.integrableOn, sinc_square_negative_tail] <;> ring

theorem sinc_square_positive_tail :
    (∫ t : ℝ in Ioi (2 * Real.pi), rE t ^ 2) =
      2 * ∫ t : ℝ in Ioi (2 * Real.pi), (1 - Real.cos t) / t ^ 2 := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  have ht0 : t ≠ 0 := by
    have ht' : 2 * Real.pi < t := ht
    linarith [Real.pi_pos]
  rw [EulerianCert.FourierModes.rE_of_ne_zero ht0,
    show 2 * Real.sin (t / 2) / t = Real.sin (t / 2) / (t / 2) by
      field_simp [ht0] <;> ring, sinc_square_kernel t ht0] <;> ring

theorem sine_integral_mobius_spectral_identity :
    (∑' n : ℕ, (↑(moebius n) : ℝ) * normalizedSpectralRemainder n) =
      1 / 2 - EulerianCert.FourierModes.Si (2 * Real.pi) / Real.pi := by
  have h := sine_integral_tail_unconditional
  rw [sinc_square_two_sided_tail, sinc_square_positive_tail] at h
  rw [normalizedSpectralRemainder_mobius_energy]
  change _ = Manuscripts11And12.KrapivskyLuck.S
  rw [h] <;> ring

end Manuscripts14And15.KrapivskyLuck

#print axioms Manuscripts14And15.KrapivskyLuck.sinc_square_integrable
#print axioms Manuscripts14And15.KrapivskyLuck.sinc_square_negative_tail
#print axioms Manuscripts14And15.KrapivskyLuck.sinc_square_two_sided_tail
#print axioms Manuscripts14And15.KrapivskyLuck.sinc_square_positive_tail
#print axioms Manuscripts14And15.KrapivskyLuck.sine_integral_mobius_spectral_identity
