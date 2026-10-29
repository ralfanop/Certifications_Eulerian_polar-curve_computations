import GegenbauerFock.GaussianAreaEntireCircularTaylor

/-!
# V007 — exact angular Fourier moments of an entire Gaussian representative

For every entire f, every n, and every radius R>0, the normalized
angular integral of f(z) * conj(z^n) on |z|=R is exactly
R^(2n) times the nth Taylor coefficient f⁽ⁿ⁾(0)/n!.

This is the essential angular extraction identity for the Gaussian
moment-to-Taylor argument. The radial Gaussian integral and Fubini
interchange remain to be certified separately; full Fock surjectivity
is NOT claimed here.
-/

noncomputable section

open Complex MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Exact Fourier/Taylor coefficient extraction on every centered
circle: the angular average of f(z) conj(z)^n equals
R^(2n) f⁽ⁿ⁾(0)/n!. -/
theorem entire_circleAverage_conj_monomial_eq_taylorCoeff
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R : ℝ) (hR : 0 < R) (n : ℕ) :
    Real.circleAverage (fun z : ℂ => f z * star (z ^ n)) 0 R =
      ((R ^ (2 * n) : ℝ) : ℂ) *
        (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)) := by
  have hcircle :
      Real.circleAverage (fun z : ℂ => f z * star (z ^ n)) 0 R =
        Real.circleAverage
          (fun z : ℂ => ((R ^ (2 * n) : ℝ) : ℂ) * (f z / z ^ n)) 0 R := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hnorm : ‖z‖ = R := by
      simpa [Metric.mem_sphere, abs_of_pos hR] using hz
    have hz0 : z ≠ 0 := by
      intro heq
      rw [heq, norm_zero] at hnorm
      linarith
    have hpow : z ^ n ≠ 0 := pow_ne_zero n hz0
    have hnormpow :
        z ^ n * star (z ^ n) = ((R ^ (2 * n) : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj']
      simp only [norm_pow, hnorm]
      congr 1
      rw [show 2 * n = n * 2 by omega, pow_mul]
      norm_cast
    calc
      f z * star (z ^ n) =
          (f z * (z ^ n * star (z ^ n))) / z ^ n := by
            field_simp [hpow] <;> ring
      _ = f z * ((R ^ (2 * n) : ℝ) : ℂ) / z ^ n := by
        rw [hnormpow]
      _ = ((R ^ (2 * n) : ℝ) : ℂ) * (f z / z ^ n) := by
        ring
  calc
    Real.circleAverage (fun z : ℂ => f z * star (z ^ n)) 0 R =
        Real.circleAverage
          (fun z : ℂ => ((R ^ (2 * n) : ℝ) : ℂ) * (f z / z ^ n)) 0 R :=
      hcircle
    _ = ((R ^ (2 * n) : ℝ) : ℂ) *
        Real.circleAverage (fun z : ℂ => f z / z ^ n) 0 R := by
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul
          (a := ((R ^ (2 * n) : ℝ) : ℂ))
          (f := fun z : ℂ => f z / z ^ n)
          (c := (0 : ℂ)) (R := R))
    _ = ((R ^ (2 * n) : ℝ) : ℂ) *
        (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)) := by
      have h := entire_circleAverage_div_pow_eq_taylorCoeff f hf 0 R hR n
      simpa only [sub_zero] using congrArg
        (fun v : ℂ => ((R ^ (2 * n) : ℝ) : ℂ) * v) h

/-- The same exact angular extraction formula for the intrinsic
entire representative of any Gaussian L² holomorphic class. -/
theorem intrinsicEntire_circleAverage_conj_monomial_eq_taylorCoeff
    (alpha : ℝ) (x : entireGaussianL2Submodule alpha)
    (R : ℝ) (hR : 0 < R) (n : ℕ) :
    Real.circleAverage
        (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n))
        0 R =
      ((R ^ (2 * n) : ℝ) : ℂ) *
        (iteratedDeriv n (entireRepresentative alpha x) 0 /
          (Nat.factorial n : ℂ)) := by
  exact entire_circleAverage_conj_monomial_eq_taylorCoeff
    (entireRepresentative alpha x)
    (entireRepresentative_differentiable alpha x) R hR n

#print axioms GegenbauerFock.GaussianArea.entire_circleAverage_conj_monomial_eq_taylorCoeff
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_circleAverage_conj_monomial_eq_taylorCoeff

end GegenbauerFock.GaussianArea
