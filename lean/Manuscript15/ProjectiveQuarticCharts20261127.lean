import Mathlib

/-! M15 Proposition 12.2, equations (610)-(613).
Homogeneous quadratic complete-intersection models in P^3.
This file establishes the homogeneous map equations, absence of a base
point on the source, and the full-rank Jacobian criterion for both
models over C. Scheme-level smoothness, projective descent and genus
via Riemann-Hurwitz are separate obligations. -/

noncomputable section
namespace Manuscript15.ProjectiveQuarticCharts20261127

private theorem sq_zero {x : ℂ} (h : x^2 = 0) : x = 0 := by
  by_contra hn
  exact (pow_ne_zero 2 hn) h

theorem homogeneous_map_equations (a b c d : ℂ)
    (hbc : b^2 = a*c) (hd : d^2 = a^2+c^2) :
    (↑(Real.sqrt (2:ℝ)) : ℂ)^2 * b^2 * (a-c)^2 = (a-c)^2*(2*b^2) ∧
    ((a+c)*d)^2 = ((a-c)^2)^2+3*(a-c)^2*(2*b^2)+2*(2*b^2)^2 := by
  have hsR : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (↑(Real.sqrt (2:ℝ)) : ℂ)^2 = 2 := by exact_mod_cast hsR
  constructor
  · rw [hs]; ring
  · calc
      _ = (a+c)^2*d^2 := by ring
      _ = ((a-c)^2)^2+3*(a-c)^2*(2*b^2)+2*(2*b^2)^2 := by
        rw [hd,hbc]
        ring

theorem no_homogeneous_basepoint (a b c d : ℂ)
    (hbc : b^2 = a*c) (hd : d^2 = a^2+c^2)
    (hne : ¬ (a=0 ∧ b=0 ∧ c=0 ∧ d=0)) :
    ¬ ((a-c)^2=0 ∧ (↑(Real.sqrt (2:ℝ)) : ℂ)*b*(a-c)=0 ∧
        2*b^2=0 ∧ (a+c)*d=0) := by
  rintro ⟨h1,_,h3,_⟩
  have hac : a=c := sub_eq_zero.mp (sq_zero h1)
  have hb2 : b^2=0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · norm_num at h
    · exact h
  have hb := sq_zero hb2
  have hc2 : c^2=0 := by
    rw [hb,hac] at hbc
    simpa [pow_two] using hbc.symm
  have hc := sq_zero hc2
  have ha := hac.trans hc
  have hd2 : d^2=0 := by simpa [ha,hc] using hd
  exact hne ⟨ha,hb,hc,sq_zero hd2⟩

theorem homogeneous_scaling (a b c d s : ℂ) :
    ((s*a-s*c)^2 = s^2*(a-c)^2) ∧
    ((↑(Real.sqrt (2:ℝ)) : ℂ)*(s*b)*(s*a-s*c) =
      s^2*((↑(Real.sqrt (2:ℝ)) : ℂ)*b*(a-c))) ∧
    (2*(s*b)^2 = s^2*(2*b^2)) ∧
    ((s*a+s*c)*(s*d) = s^2*((a+c)*d)) := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Full row rank of the two defining homogeneous gradients, on every
nonzero point. Here p=0,q=1 is the source and p=3,q=2 is the target. -/
theorem homogeneous_jacobian_rank (a b c d p q l m : ℂ)
    (hq : q ≠ 0) (hdisc : 4*q-p^2 ≠ 0)
    (hbc : b^2=a*c) (hd : d^2=a^2+p*a*c+q*c^2)
    (hne : ¬ (a=0 ∧ b=0 ∧ c=0 ∧ d=0))
    (ha : l*c+m*(2*a+p*c)=0) (hb : 2*l*b=0)
    (hc : l*a+m*(p*a+2*q*c)=0) (hz : 2*m*d=0) :
    l=0 ∧ m=0 := by
  have htwo : (2:ℂ) ≠ 0 := by norm_num
  have hlb : l*b=0 := by
    exact (mul_eq_zero.mp (show 2*(l*b)=0 by linear_combination hb)).resolve_left htwo
  have hmd : m*d=0 := by
    exact (mul_eq_zero.mp (show 2*(m*d)=0 by linear_combination hz)).resolve_left htwo
  by_cases hb0 : b=0
  · have hac : a*c=0 := by simpa [hb0] using hbc.symm
    rcases mul_eq_zero.mp hac with ha0 | hc0
    · have hcne : c ≠ 0 := by
        intro h
        have hd0 : d^2=0 := by simpa [ha0,h] using hd
        exact hne ⟨ha0,hb0,h,sq_zero hd0⟩
      have hdne : d ≠ 0 := by
        intro h
        have e : q*c^2=0 := by simpa [ha0,h] using hd.symm
        exact (pow_ne_zero 2 hcne) ((mul_eq_zero.mp e).resolve_left hq)
      have hm : m=0 := (mul_eq_zero.mp hmd).resolve_right hdne
      have e : l*c=0 := by simpa only [hm,zero_mul,add_zero] using ha
      exact ⟨(mul_eq_zero.mp e).resolve_right hcne,hm⟩
    · have hane : a ≠ 0 := by
        intro h
        have hd0 : d^2=0 := by simpa [hc0,h] using hd
        exact hne ⟨h,hb0,hc0,sq_zero hd0⟩
      have hdne : d ≠ 0 := by
        intro h
        have e : a^2=0 := by simpa [hc0,h] using hd.symm
        exact (pow_ne_zero 2 hane) e
      have hm : m=0 := (mul_eq_zero.mp hmd).resolve_right hdne
      have e : l*a=0 := by simpa only [hm,zero_mul,add_zero] using hc
      exact ⟨(mul_eq_zero.mp e).resolve_right hane,hm⟩
  · have hl : l=0 := (mul_eq_zero.mp hlb).resolve_right hb0
    refine ⟨hl,?_⟩
    by_contra hm
    have e1 : 2*a+p*c=0 := (mul_eq_zero.mp
      (show m*(2*a+p*c)=0 by simpa only [hl,zero_mul,zero_add] using ha)).resolve_left hm
    have e2 : p*a+2*q*c=0 := (mul_eq_zero.mp
      (show m*(p*a+2*q*c)=0 by simpa only [hl,zero_mul,zero_add] using hc)).resolve_left hm
    have e3 : (4*q-p^2)*c=0 := by linear_combination 2*e2-p*e1
    have hc0 : c=0 := (mul_eq_zero.mp e3).resolve_left hdisc
    have hb2 : b^2=0 := by simpa [hc0] using hbc
    exact hb0 (sq_zero hb2)

end Manuscript15.ProjectiveQuarticCharts20261127

#print axioms Manuscript15.ProjectiveQuarticCharts20261127.homogeneous_map_equations
#print axioms Manuscript15.ProjectiveQuarticCharts20261127.no_homogeneous_basepoint
#print axioms Manuscript15.ProjectiveQuarticCharts20261127.homogeneous_scaling
#print axioms Manuscript15.ProjectiveQuarticCharts20261127.homogeneous_jacobian_rank
