import EulerianGrothendieck.QuadraticMinimum

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 1000000

theorem eulerianPhase_cartesian :
    eulerianPhase = (((Real.pi^2-1)/(Real.pi^2+1):ℝ):ℂ)+
      ((2*Real.pi/(Real.pi^2+1):ℝ):ℂ)*Complex.I := by
  have hd : 0 < Real.pi^2+1 := by positivity
  have hs := Real.sq_sqrt hd.le
  have hn := (Real.sqrt_pos.mpr hd).ne'
  apply Complex.ext
  · simp only [eulerianPhase,halfPhase,eulerianHalfC,eulerianHalfS,pow_two,
      Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    field_simp
    nlinarith [hs, congrArg (fun t : ℝ => t*Real.pi) hs]
  · simp only [eulerianPhase,halfPhase,eulerianHalfC,eulerianHalfS,pow_two,
      Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    field_simp
    nlinarith [hs, congrArg (fun t : ℝ => t*Real.pi) hs]

theorem eulerianPhase_fraction :
    eulerianPhase = ((Real.pi:ℂ)+Complex.I)/((Real.pi:ℂ)-Complex.I) := by
  rw [eulerianPhase_cartesian]
  apply Complex.ext <;>
    simp only [Complex.div_re,Complex.div_im,Complex.normSq_apply,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im]
  all_goals field_simp <;> ring

end EulerianGrothendieck
