import Mathlib

namespace M16Krein

-- Scalar and associative-ring prerequisites for Proposition 9.13.
theorem weighted_pairing (x y : ℝ) (h : x = -2*y) : x + 2*y = 0 := by
  rw [h]
  ring

theorem scale_coupling (s x y : ℝ) (hs : s^2 = 2) (hx : x = -2*y) :
    x = -s * (s*y) := by
  rw [hx]
  nlinarith [congrArg (fun z : ℝ => z*y) hs]

theorem transport_involution {R : Type*} [Ring R] (u v s : R)
    (hu : u*v = 1) (hv : v*u = 1) (hs : s*s = 1) :
    (u*s*v)*(u*s*v) = 1 := by
  calc
    (u*s*v)*(u*s*v) = u*s*(v*u)*s*v := by noncomm_ring
    _ = 1 := by rw [hv, mul_one]; rw [mul_assoc u s s, hs, mul_one, hu]

-- Block elimination, with the factor of two and the sign in (171).
theorem schur_elimination {R : Type*} [Ring R] (a d r x y p q g : R)
    (hr : r*d = 1) (hx : x = -(y+y)) (hq : y*p + d*q = g) :
    a*p + x*q = (a+(y+y)*r*y)*p - (y+y)*r*g := by
  have hq' : q = r*g-r*y*p := by
    calc
      q = (r*d)*q := by rw [hr, one_mul]
      _ = r*g-r*y*p := by rw [← hq]; noncomm_ring
  rw [hx, hq']
  noncomm_ring

-- Corollary 9.14: exact scalar quadratic and its positive branch.
def gapRadius (a d c : ℝ) : ℝ :=
  (a+d-Real.sqrt ((a-d)^2+8*c^2))/2

theorem gap_root (a d c : ℝ) :
    (a-gapRadius a d c)*(d-gapRadius a d c)=2*c^2 := by
  have hs := Real.sq_sqrt (show 0 ≤ (a-d)^2+8*c^2 by positivity)
  unfold gapRadius
  nlinarith only [hs]

theorem gap_radius_positive (a d c : ℝ) (ha : 0<a) (hd : 0<d)
    (hc : 2*c^2<a*d) : 0<gapRadius a d c := by
  have hs := Real.sq_sqrt (show 0 ≤ (a-d)^2+8*c^2 by positivity)
  have hn := Real.sqrt_nonneg ((a-d)^2+8*c^2)
  unfold gapRadius
  by_contra! h
  have hp := mul_nonneg (show 0 ≤ Real.sqrt ((a-d)^2+8*c^2)-(a+d) by linarith)
    (show 0 ≤ Real.sqrt ((a-d)^2+8*c^2)+(a+d) by linarith)
  nlinarith only [hp, hs, hc]

theorem gap_radius_le_a (a d c : ℝ) : gapRadius a d c ≤ a := by
  have hs := Real.sq_sqrt (show 0 ≤ (a-d)^2+8*c^2 by positivity)
  have hn := Real.sqrt_nonneg ((a-d)^2+8*c^2)
  unfold gapRadius
  by_contra! h
  have hp := mul_pos (show 0 < d-a-Real.sqrt ((a-d)^2+8*c^2) by linarith)
    (show 0 < d-a+Real.sqrt ((a-d)^2+8*c^2) by linarith)
  nlinarith only [hp, hs, sq_nonneg c]

theorem gap_radius_le_d (a d c : ℝ) : gapRadius a d c ≤ d := by
  have hs := Real.sq_sqrt (show 0 ≤ (a-d)^2+8*c^2 by positivity)
  have hn := Real.sqrt_nonneg ((a-d)^2+8*c^2)
  unfold gapRadius
  by_contra! h
  have hp := mul_pos (show 0 < a-d-Real.sqrt ((a-d)^2+8*c^2) by linarith)
    (show 0 < a-d+Real.sqrt ((a-d)^2+8*c^2) by linarith)
  nlinarith only [hp, hs, sq_nonneg c]

theorem gap_polynomial_positive (a d c t : ℝ) (ht : t < gapRadius a d c) :
    2*c^2 < (a-t)*(d-t) := by
  have hr := gap_root a d c
  have ha := gap_radius_le_a a d c
  have hd := gap_radius_le_d a d c
  have hp := mul_pos (show 0 < gapRadius a d c-t by linarith)
    (show 0 < a+d-gapRadius a d c-t by linarith)
  nlinarith only [hp, hr]

theorem unperturbed_threshold (c : ℝ) (hc : 0 ≤ c) :
    2*c^2 < (4:ℝ)*(3/2) ↔ c < Real.sqrt 3 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg 3
  constructor
  · intro h
    by_contra! hh
    have hp := mul_nonneg (show 0 ≤ c-Real.sqrt 3 by linarith)
      (show 0 ≤ c+Real.sqrt 3 by linarith)
    nlinarith only [h, hs, hp]
  · intro h
    have hp := mul_pos (show 0 < Real.sqrt 3-c by linarith)
      (show 0 < Real.sqrt 3+c by linarith)
    nlinarith only [hs, hp]

#print axioms weighted_pairing
#print axioms scale_coupling
#print axioms transport_involution
#print axioms schur_elimination
#print axioms gap_root
#print axioms gap_radius_positive
#print axioms gap_radius_le_a
#print axioms gap_radius_le_d
#print axioms gap_polynomial_positive
#print axioms unperturbed_threshold

end M16Krein
