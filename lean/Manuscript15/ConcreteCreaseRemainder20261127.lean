import Manuscript15.QuarticUniformTransfer20261127

/-! Source: M15 26 Nov, FRENCH_YEN_1992_2002(4), prop:cross-crease15.
Real-coordinate prerequisite to the concrete sixth-order remainder.
The definitions use the u-coordinate density from cor:ridge-crease.
The pointwise density estimate below still takes the elementary sinh
estimates as hypotheses. No claim that the actual phase or crease
remainder has been kernel-certified at this checkpoint. -/

noncomputable section
open MeasureTheory
namespace Manuscript15.ConcreteCreaseRemainder20261127

def density (k t : ℝ) : ℝ :=
  k / Real.sqrt (1 + (1+k^2)*(Real.sinh t)^2)

def phase (k u : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..u, density k t

def crease (k u : ℝ) : ℝ :=
  Real.cosh u * Real.cos (phase k u) - 1

theorem sqrt_reciprocal_remainder (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 / Real.sqrt (1+x) - 1 + x/2 ∧
    1 / Real.sqrt (1+x) - 1 + x/2 ≤ x^2 := by
  let s := Real.sqrt (1+x)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = 1+x := Real.sq_sqrt (by linarith)
  have hs : 1 ≤ s := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < 1+s by linarith)
    nlinarith
  have hspos : 0 < s := by linarith
  have hiden : 1/s - 1 + x/2 = (s-1)^2*(s+2)/(2*s) := by
    calc
      _ = 1/s - 1 + (s^2-1)/2 := by rw [show x = s^2-1 by linarith]
      _ = _ := by field_simp [hspos.ne'] <;> ring
  have hx' : x = (s-1)*(s+1) := by nlinarith
  change 0 ≤ 1/s - 1 + x/2 ∧ 1/s - 1 + x/2 ≤ x^2
  rw [hiden]
  constructor
  · positivity
  · apply (div_le_iff₀ (show 0 < 2*s by positivity)).2
    have hfour : 4 ≤ (s+1)^2 := by
      nlinarith [sq_nonneg (s-1)]
    have hfactor : s+2 ≤ 2*s*(s+1)^2 := by
      have hm := mul_nonneg hs0 (sub_nonneg.mpr hfour)
      nlinarith
    calc
      (s-1)^2*(s+2) ≤ (s-1)^2*(2*s*(s+1)^2) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
      _ = x^2*(2*s) := by rw [hx']; ring

theorem density_continuous (k : ℝ) : Continuous (density k) := by
  unfold density
  apply continuous_const.div
  · fun_prop
  · intro t
    exact (Real.sqrt_pos.2 (by positivity)).ne'

theorem density_nonnegative_bounded (k t : ℝ) (hk : 0 ≤ k) :
    0 ≤ density k t ∧ density k t ≤ k := by
  let s := Real.sqrt (1+(1+k^2)*(Real.sinh t)^2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = 1+(1+k^2)*(Real.sinh t)^2 :=
    Real.sq_sqrt (by positivity)
  have hx : 0 ≤ (1+k^2)*(Real.sinh t)^2 := by positivity
  have hs : 1 ≤ s := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < 1+s by linarith)
    nlinarith
  change 0 ≤ k/s ∧ k/s ≤ k
  refine ⟨div_nonneg hk hs0, ?_⟩
  apply (div_le_iff₀ (show 0 < s by linarith)).2
  nlinarith [mul_nonneg hk (sub_nonneg.mpr hs)]

theorem density_quadratic_remainder_from_sinh (k t : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 3/2)
    (hS : |Real.sinh t| ≤ 2*|t|)
    (hSt : |Real.sinh t-t| ≤ |t|^3) :
    |density k t - (k-k*(1+k^2)/2*t^2)| ≤ 300*|t|^4 := by
  let x := (1+k^2)*(Real.sinh t)^2
  let r := 1/Real.sqrt (1+x)-1+x/2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hr := sqrt_reciprocal_remainder x hx0
  have hrabs : |r| ≤ x^2 := by
    change |1/Real.sqrt (1+x)-1+x/2| ≤ x^2
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hk2 : k^2 ≤ (3/2:ℝ)^2 := by gcongr
  have hkfac : 1+k^2 ≤ (13/4:ℝ) := by linarith
  have hs2 : (Real.sinh t)^2 ≤ 4*|t|^2 := by
    calc
      _ = |Real.sinh t|^2 := by simp
      _ ≤ (2*|t|)^2 := by gcongr
      _ = _ := by ring
  have hx1 : x ≤ 13*|t|^2 := by
    calc
      x ≤ (13/4:ℝ)*(4*|t|^2) := by dsimp [x]; gcongr
      _ = _ := by ring
  have hsum : |Real.sinh t+t| ≤ 3*|t| := by
    calc
      _ ≤ |Real.sinh t|+|t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hsqdiff : |(Real.sinh t)^2-t^2| ≤ 3*|t|^4 := by
    rw [show (Real.sinh t)^2-t^2 = (Real.sinh t-t)*(Real.sinh t+t) by ring, abs_mul]
    calc
      _ ≤ |t|^3*(3*|t|) := by gcongr
      _ = _ := by ring
  have hcoef : k*(1+k^2)/2 ≤ (3:ℝ) := by
    calc
      _ ≤ (3/2:ℝ)*(13/4)/2 := by gcongr
      _ ≤ _ := by norm_num
  have hiden : density k t - (k-k*(1+k^2)/2*t^2) =
      k*r + (-(k*(1+k^2)/2))*((Real.sinh t)^2-t^2) := by
    dsimp [density, r, x]
    ring
  rw [hiden]
  calc
    _ ≤ |k*r| + |(-(k*(1+k^2)/2))*((Real.sinh t)^2-t^2)| := abs_add_le _ _
    _ = k*|r| + (k*(1+k^2)/2)*|(Real.sinh t)^2-t^2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_neg,
        abs_of_nonneg (show 0 ≤ k*(1+k^2)/2 by positivity)]
    _ ≤ (3/2:ℝ)*(13*|t|^2)^2 + 3*(3*|t|^4) := by
      have hrbound : |r| ≤ (13*|t|^2)^2 := hrabs.trans (by gcongr)
      gcongr
    _ ≤ _ := by nlinarith [show 0 ≤ |t|^4 by positivity]

end Manuscript15.ConcreteCreaseRemainder20261127

#print axioms Manuscript15.ConcreteCreaseRemainder20261127.sqrt_reciprocal_remainder
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.density_continuous
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.density_nonnegative_bounded
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.density_quadratic_remainder_from_sinh
