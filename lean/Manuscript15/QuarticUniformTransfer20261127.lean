import Manuscript15.CrossQuarticCurve20261125

/-! M15 eq:cross-creaseLim: uniform error transfer from a sixth-order
analytic remainder. This module does not establish that remainder for
the actual cosh-cos crease. The algebraic jet is reused from #613. -/

noncomputable section
namespace Manuscript15.QuarticUniformTransfer20261127
open Manuscript15.CrossQuartic20261125

theorem scaled_error_from_remainder (D : ℝ → ℝ → ℝ)
    (k ε v lam C : ℝ) (hε : 0 < ε)
    (hk : k^2 = 1-80*lam*ε^2) (hC : 0 ≤ C)
    (hrem : |D k (ε*v)-creaseQuarticJet k (ε*v)| ≤ C* |ε*v|^6) :
    |3*D k (ε*v)/(20*ε^4)-(v^4/40+6*lam*v^2)| ≤
      (3*C/20)*ε^2* |v|^6+4* |lam| * ε^2*v^4+200*lam^2*ε^4*v^4 := by
  have hden : 0 < 20*ε^4 := by positivity
  have hq := crease_critical_scaled_quotient k ε v lam hε.ne' hk
  have he : 3*D k (ε*v)/(20*ε^4)-(v^4/40+6*lam*v^2) =
      3*(D k (ε*v)-creaseQuarticJet k (ε*v))/(20*ε^4) +
      (-4*lam*ε^2*v^4) + 200*lam^2*ε^4*v^4 := by
    calc
      _ = 3*(D k (ε*v)-creaseQuarticJet k (ε*v))/(20*ε^4) +
          (3*creaseQuarticJet k (ε*v)/(20*ε^4)-(v^4/40+6*lam*v^2)) := by ring
      _ = _ := by rw [hq]; ring
  have hr : |3*(D k (ε*v)-creaseQuarticJet k (ε*v))/(20*ε^4)| ≤
      (3*C/20)*ε^2* |v|^6 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    rw [abs_mul, abs_of_pos hε, mul_pow] at hrem
    nlinarith [hrem]
  have ha : |-4*lam*ε^2*v^4| = 4* |lam| * ε^2*v^4 := by
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg ε), abs_of_nonneg (by positivity : 0 ≤ v^4)]
    norm_num
  have hb : |200*lam^2*ε^4*v^4| = 200*lam^2*ε^4*v^4 :=
    abs_of_nonneg (by positivity)
  rw [he]
  calc
    _ ≤ |3*(D k (ε*v)-creaseQuarticJet k (ε*v))/(20*ε^4)+(-4*lam*ε^2*v^4)| +
        |200*lam^2*ε^4*v^4| := abs_add_le _ _
    _ ≤ (|3*(D k (ε*v)-creaseQuarticJet k (ε*v))/(20*ε^4)| + 
        |-4*lam*ε^2*v^4|)+|200*lam^2*ε^4*v^4| :=
      add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by rw [ha,hb]; linarith

theorem scaled_error_uniform_box (D : ℝ → ℝ → ℝ)
    (k ε v lam C V L : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hk : k^2 = 1-80*lam*ε^2) (hC : 0 ≤ C)
    (hv : |v| ≤ V) (hl : |lam| ≤ L)
    (hrem : |D k (ε*v)-creaseQuarticJet k (ε*v)| ≤ C* |ε*v|^6) :
    |3*D k (ε*v)/(20*ε^4)-(v^4/40+6*lam*v^2)| ≤
      ε^2*((3*C/20)*V^6+4*L*V^4+200*L^2*V^4) := by
  have hV : 0 ≤ V := (abs_nonneg v).trans hv
  have hL : 0 ≤ L := (abs_nonneg lam).trans hl
  have hv4 : v^4 ≤ V^4 := by
    calc
      _ = |v|^4 := by rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ v^4)]
      _ ≤ _ := by gcongr
  have hl2 : lam^2 ≤ L^2 := by
    calc
      _ = |lam|^2 := by rw [← abs_pow, abs_of_nonneg (sq_nonneg lam)]
      _ ≤ _ := by gcongr
  have he2 : ε^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hε.le]
  have he4 : ε^4 ≤ ε^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr he2) (sq_nonneg ε)]
  calc
    _ ≤ (3*C/20)*ε^2* |v|^6+4* |lam| * ε^2*v^4+200*lam^2*ε^4*v^4 :=
      scaled_error_from_remainder D k ε v lam C hε hk hC hrem
    _ ≤ (3*C/20)*ε^2*V^6+4*L*ε^2*V^4+200*L^2*ε^2*V^4 := by gcongr
    _ = _ := by ring

end Manuscript15.QuarticUniformTransfer20261127

#print axioms Manuscript15.QuarticUniformTransfer20261127.scaled_error_from_remainder
#print axioms Manuscript15.QuarticUniformTransfer20261127.scaled_error_uniform_box
