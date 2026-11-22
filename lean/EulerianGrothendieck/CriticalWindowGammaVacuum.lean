import Mathlib

/-! M12 §9: exact quartic Gamma quadrature and vacuum inversion.
Independent of the analytic convergence of the Fock integrals. -/
set_option maxRecDepth 4096

namespace M12CriticalGamma
open MeasureTheory Set Filter
open scoped Topology

theorem gamma_quarter_unscaled :
    Real.Gamma (1/4) = 4 * ∫ x in Ioi (0:ℝ), Real.exp (-x^4) := by
  rw [Real.Gamma_eq_integral (by norm_num : (0:ℝ) < 1/4),
    ← integral_comp_rpow_Ioi_of_pos (by norm_num : (0:ℝ) < 4),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  have hp : (x ^ (4:ℝ)) ^ ((1:ℝ)/4-1) = (x^3)⁻¹ := by
    rw [← Real.rpow_mul hx'.le]
    norm_num [Real.rpow_neg hx'.le, Real.rpow_natCast]
  rw [smul_eq_mul, hp]
  norm_num [Real.rpow_natCast] <;> field_simp [ne_of_gt hx'] <;> ring

noncomputable def quarticProfile (x : ℝ) : ℝ := Real.exp (-x^4/40)

theorem quartic_scale_halfline :
    (∫ x in Ioi (0:ℝ), quarticProfile x) =
      (40:ℝ)^(1/4:ℝ) * Real.Gamma (1/4) / 4 := by
  let d : ℝ := (40:ℝ)^(1/4:ℝ)
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  have hd4 : d^4 = 40 := by
    dsimp [d]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 40)]
    norm_num
  have h := integral_comp_mul_left_Ioi quarticProfile 0 hd
  simp only [mul_zero, smul_eq_mul] at h
  have heq : (∫ x in Ioi (0:ℝ), quarticProfile (d*x)) =
      ∫ x in Ioi (0:ℝ), Real.exp (-x^4) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    unfold quarticProfile
    rw [mul_pow, hd4]
    congr 1
    ring
  rw [heq] at h
  have hG := gamma_quarter_unscaled
  change (∫ x in Ioi (0:ℝ), quarticProfile x) =
    d * Real.Gamma (1/4) / 4
  rw [h] at hG
  field_simp [ne_of_gt hd] at hG ⊢
  nlinarith only [hG]

theorem quarticProfile_integrable : Integrable quarticProfile := by
  have hp : IntegrableOn quarticProfile (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 4) (s := 0) (b := 1/40) (by norm_num) (by norm_num) (by norm_num)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp [quarticProfile, Real.rpow_natCast] <;> congr 1 <;> ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0:ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa [Function.comp_def, quarticProfile, neg_pow, neg_preimage, neg_Iio] using hp

theorem quartic_integral :
    (∫ x : ℝ, quarticProfile x) = (40:ℝ)^(1/4:ℝ) * Real.Gamma (1/4) / 2 := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding quarticProfile (Ioi (0:ℝ))
  have hsym : (∫ x in Iio (0:ℝ), quarticProfile x) =
      ∫ x in Ioi (0:ℝ), quarticProfile x := by
    simpa [quarticProfile, neg_preimage, neg_Ioi, neg_pow] using hneg
  rw [← integral_add_compl measurableSet_Ioi quarticProfile_integrable,
    compl_Ioi, integral_Iic_eq_integral_Iio, hsym, quartic_scale_halfline]
  ring

theorem critical_constant :
    (1/(2*Real.sqrt Real.pi)) * (∫ x : ℝ, quarticProfile x) =
      (40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi) := by
  rw [quartic_integral]
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hs] <;> ring

theorem critical_constant_pos :
    0 < (40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi) := by
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.Gamma_pos_of_pos (by norm_num))) (by positivity)

/-- Inversion is valid for a nonzero limiting normalization. The hypotheses
are supplied by the Fock dominated-convergence theorem in a separate module. -/
theorem vacuum_inversion (N scale : ℕ → ℝ) (L : ℝ)
    (h : Tendsto (fun n => N n / scale n) atTop (𝓝 L)) (hL : L ≠ 0) :
    Tendsto (fun n => scale n * (N n)⁻¹) atTop (𝓝 L⁻¹) := by
  simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv] using h.inv₀ hL

end M12CriticalGamma

#print axioms M12CriticalGamma.gamma_quarter_unscaled
#print axioms M12CriticalGamma.quartic_scale_halfline
#print axioms M12CriticalGamma.quarticProfile_integrable
#print axioms M12CriticalGamma.quartic_integral
#print axioms M12CriticalGamma.critical_constant
#print axioms M12CriticalGamma.critical_constant_pos
#print axioms M12CriticalGamma.vacuum_inversion
