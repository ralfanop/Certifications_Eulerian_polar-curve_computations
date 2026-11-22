import CriticalWindowGlobalMGF

/-! M12 §9: actual complex uniform MGF modulus bound and critical envelope.
No probabilistic or complex modulus inequality is assumed. -/
namespace M12ComplexMGF
open Complex

noncomputable def csinhc (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sinh z / z

noncomputable def mgf (z : ℂ) : ℂ :=
  csinhc ((Real.sqrt 3 : ℂ) * z)

theorem normSq_coordinate (x y : ℝ) :
    Complex.normSq ((x : ℂ) + (y : ℂ)*Complex.I) = x^2+y^2 := by
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, pow_two]

theorem normSq_sinh_coordinate (x y : ℝ) :
    Complex.normSq (Complex.sinh ((x : ℂ)+(y : ℂ)*Complex.I)) =
      (Real.sinh x)^2+(Real.sin y)^2 := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, mul_one, one_mul, neg_zero]
  linear_combination (Real.sinh x)^2 * Real.sin_sq_add_cos_sq y +
    (Real.sin y)^2 * Real.cosh_sq_sub_sinh_sq x

theorem sinh_sq_ge (x : ℝ) : x^2 ≤ (Real.sinh x)^2 := by
  have h := Real.self_le_sinh_iff.mpr (abs_nonneg x)
  rw [← Real.abs_sinh] at h
  exact sq_le_sq.mpr h

theorem real_sinhc_pos (x : ℝ) : 0 < M12GlobalMGF.sinhc x := by
  by_cases h : 0 ≤ x
  · exact M12GlobalMGF.sinhc_pos_of_nonneg x h
  · rw [← M12GlobalMGF.sinhc_neg x]
    exact M12GlobalMGF.sinhc_pos_of_nonneg (-x) (by linarith)

theorem real_sinhc_sq_ge_one (x : ℝ) : 1 ≤ (M12GlobalMGF.sinhc x)^2 := by
  by_cases h : x = 0
  · simp [h, M12GlobalMGF.sinhc]
  · rw [M12GlobalMGF.sinhc, if_neg h, div_pow]
    apply (le_div_iff₀ (sq_pos_of_ne_zero h)).2
    simpa only [one_mul] using sinh_sq_ge x

theorem real_sinhc_sq_mul (x : ℝ) :
    (M12GlobalMGF.sinhc x)^2 * x^2 = (Real.sinh x)^2 := by
  by_cases h : x = 0
  · simp [h]
  · rw [M12GlobalMGF.sinhc, if_neg h, div_pow]
    field_simp

theorem normSq_csinhc_le (x y : ℝ) :
    Complex.normSq (csinhc ((x : ℂ)+(y : ℂ)*Complex.I)) ≤
      (M12GlobalMGF.sinhc x)^2 := by
  let z : ℂ := (x : ℂ)+(y : ℂ)*Complex.I
  change Complex.normSq (csinhc z) ≤ _
  by_cases hz : z = 0
  · simpa [csinhc, hz] using real_sinhc_sq_ge_one x
  · rw [csinhc, if_neg hz, Complex.normSq_div]
    have hd : 0 < Complex.normSq z :=
      lt_of_le_of_ne (Complex.normSq_nonneg z)
        (Ne.symm (fun h => hz (Complex.normSq_eq_zero.mp h)))
    apply (div_le_iff₀ hd).2
    change Complex.normSq (Complex.sinh ((x : ℂ)+(y : ℂ)*Complex.I)) ≤
      (M12GlobalMGF.sinhc x)^2 * Complex.normSq ((x : ℂ)+(y : ℂ)*Complex.I)
    rw [normSq_sinh_coordinate, normSq_coordinate]
    calc
      (Real.sinh x)^2+(Real.sin y)^2 ≤ (Real.sinh x)^2+y^2 :=
        add_le_add_left (Real.sin_sq_le_sq (x := y)) _
      _ ≤ (Real.sinh x)^2+(M12GlobalMGF.sinhc x)^2*y^2 := by
        apply add_le_add_left
        have h := mul_le_mul_of_nonneg_right (real_sinhc_sq_ge_one x) (sq_nonneg y)
        simpa only [one_mul] using h
      _ = (M12GlobalMGF.sinhc x)^2*(x^2+y^2) := by
        rw [mul_add, real_sinhc_sq_mul]

theorem norm_csinhc_le (x y : ℝ) :
    ‖csinhc ((x : ℂ)+(y : ℂ)*Complex.I)‖ ≤ M12GlobalMGF.sinhc x := by
  have hs := normSq_csinhc_le x y
  rw [Complex.normSq_eq_norm_sq] at hs
  have h := sq_le_sq.mp hs
  simpa only [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (real_sinhc_pos x).le] using h

theorem modulus_bound (h k : ℝ) :
    ‖mgf ((h : ℂ)+(k : ℂ)*Complex.I)‖ ≤ M12GlobalMGF.sinhc (Real.sqrt 3*h) := by
  unfold mgf
  rw [mul_add, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  exact norm_csinhc_le (Real.sqrt 3*h) (Real.sqrt 3*k)

theorem critical_exponential_envelope (h k : ℝ) :
    ‖mgf ((h : ℂ)+(k : ℂ)*Complex.I)‖ ≤
      Real.exp (h^2/2 - M12GlobalMGF.deficitConstant * min (h^4) (h^2)) := by
  apply (modulus_bound h k).trans
  apply (Real.log_le_iff_le_exp (real_sinhc_pos (Real.sqrt 3*h))).mp
  linarith only [M12GlobalMGF.standardized_global_deficit h]

end M12ComplexMGF

#print axioms M12ComplexMGF.normSq_coordinate
#print axioms M12ComplexMGF.normSq_sinh_coordinate
#print axioms M12ComplexMGF.sinh_sq_ge
#print axioms M12ComplexMGF.real_sinhc_pos
#print axioms M12ComplexMGF.real_sinhc_sq_ge_one
#print axioms M12ComplexMGF.real_sinhc_sq_mul
#print axioms M12ComplexMGF.normSq_csinhc_le
#print axioms M12ComplexMGF.norm_csinhc_le
#print axioms M12ComplexMGF.modulus_bound
#print axioms M12ComplexMGF.critical_exponential_envelope
