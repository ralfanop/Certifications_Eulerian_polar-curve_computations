import PrivateApex.SincGaussian
import PrivateApex.TailConstants
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PrivateApex
open Real Set MeasureTheory Filter Topology

def weight (N : ℕ) (x : ℝ) : ℝ := x^2 * |sinc x|^(N+2)
def gauss (N : ℕ) (x : ℝ) : ℝ := x^2 * exp (-(((N : ℝ)+2)/6)*x^2)

theorem weight_nonneg (N : ℕ) (x : ℝ) : 0 ≤ weight N x := by unfold weight; positivity

theorem weight_le_gauss (N : ℕ) {x : ℝ} (hx : x ∈ Icc 0 π) :
    weight N x ≤ gauss N x := by
  have h := pow_le_pow_left₀ (abs_nonneg (sinc x)) (abs_sinc_le_gaussian hx) (N+2)
  have he : (exp (-(x^2/6)))^(N+2) = exp (-(((N:ℝ)+2)/6)*x^2) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (sq_nonneg x)

theorem weight_le_tail (N : ℕ) {x : ℝ} (hx : π ≤ x) :
    weight N x ≤ 1 / x^N := by
  have hx0 : 0 < x := pi_pos.trans_le hx
  have hs : |sinc x| ≤ 1/x := by
    rw [sinc_of_ne_zero hx0.ne', abs_div, abs_of_pos hx0]
    exact div_le_div_of_nonneg_right (abs_sin_le_one x) hx0.le
  calc
    weight N x ≤ x^2 * (1/x)^(N+2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hs _) (sq_nonneg _)
    _ = 1/x^N := by
      rw [div_pow, pow_add]
      field_simp [hx0.ne']
      simp [pow_add, mul_comm]

theorem gauss_integrable (N : ℕ) : Integrable (gauss N) := by
  change Integrable (fun x : ℝ => x^2 * exp (-(((N : ℝ)+2)/6)*x^2))
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := ((N : ℝ)+2)/6) (by positivity) (s := 2) (by norm_num)
  simpa only [gauss, rpow_two] using h

theorem tail_integrable (N : ℕ) (hN : 2 ≤ N) :
    IntegrableOn (fun x : ℝ => 1/x^N) (Ioi π) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have h := integrableOn_Ioi_rpow_of_lt (a := -(N : ℝ)) (by linarith) pi_pos
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [rpow_neg (pi_pos.trans hx).le, rpow_natCast, one_div]

theorem weight_integrable_half (N : ℕ) (hN : 2 ≤ N) :
    IntegrableOn (weight N) (Ioi 0) := by
  have hsmall : IntegrableOn (weight N) (Ioc 0 π) := by
    have hc : Continuous (weight N) := by unfold weight; fun_prop
    exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (weight N) (Ioi π) := by
    apply (tail_integrable N hN).mono'
    · exact (by unfold weight; fun_prop : Continuous (weight N)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg N x)]
      exact weight_le_tail N hx.le
  have hu : Ioc (0 : ℝ) π ∪ Ioi π = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · exact pi_pos.trans h
    · intro h
      by_cases hp : x ≤ π
      · exact Or.inl ⟨h,hp⟩
      · exact Or.inr (lt_of_not_ge hp)
  rw [← hu, integrableOn_union]
  exact ⟨hsmall,htail⟩

theorem weight_integral_le (N : ℕ) (hN : 2 ≤ N) :
    (∫ x in Ioi (0 : ℝ), weight N x) ≤
      (∫ x in Ioi (0 : ℝ), gauss N x) + (∫ x in Ioi π, 1/x^N) := by
  have hi := weight_integrable_half N hN
  have hs := hi.mono_set (show Ioc (0 : ℝ) π ⊆ Ioi 0 from fun x hx => hx.1)
  have ht := hi.mono_set (Ioi_subset_Ioi pi_pos.le)
  have hu : Ioc (0 : ℝ) π ∪ Ioi π = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · exact pi_pos.trans h
    · intro h
      by_cases hp : x ≤ π
      · exact Or.inl ⟨h,hp⟩
      · exact Or.inr (lt_of_not_ge hp)
  have hd : Disjoint (Ioc (0 : ℝ) π) (Ioi π) := by
    rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hx.2) hy
  have he : (∫ x in Ioi (0 : ℝ), weight N x) =
      (∫ x in Ioc (0 : ℝ) π, weight N x) + (∫ x in Ioi π, weight N x) := by
    rw [← hu, setIntegral_union hd measurableSet_Ioi hs ht]
  rw [he]
  apply add_le_add
  · apply (setIntegral_mono_on hs (gauss_integrable N).integrableOn measurableSet_Ioc
      (fun x hx => weight_le_gauss N ⟨hx.1.le,hx.2⟩)).trans
    exact setIntegral_mono_set (gauss_integrable N).integrableOn
      (Eventually.of_forall (fun x => by unfold gauss; positivity))
      (Eventually.of_forall (fun x hx => hx.1))
  · exact setIntegral_mono_on ht (tail_integrable N hN) measurableSet_Ioi
      (fun x hx => weight_le_tail N hx.le)

theorem gaussian_half_integral (a : ℝ) (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), x^2 * exp (-a*x^2)) = sqrt π / (4*a*sqrt a) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := a)
    (by norm_num) (by norm_num) ha
  simp only [rpow_two] at h
  rw [h]
  have hg : Gamma ((2+1)/2 : ℝ) = sqrt π / 2 := by
    have hh := Gamma_nat_add_one_add_half 0
    norm_num [Nat.doubleFactorial] at hh
    convert hh using 1 <;> norm_num
  rw [hg]
  have hr : a^(-(2+1)/2 : ℝ) = 1/(a*sqrt a) := by
    rw [show (-(2+1)/2 : ℝ) = -(1+1/2) by norm_num, rpow_neg ha.le,
      rpow_add ha, rpow_one, ← sqrt_eq_rpow, one_div]
  rw [hr]
  ring

theorem tail_half_integral (N : ℕ) (hN : 2 ≤ N) :
    (∫ x in Ioi π, 1/x^N) = 1/(((N : ℝ)-1)*π^(N-1)) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have he : (∫ x in Ioi π, 1/x^N) = (∫ x in Ioi π, x^(-(N : ℝ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [rpow_neg (pi_pos.trans hx).le, rpow_natCast, one_div]
  rw [he, integral_Ioi_rpow_of_lt (by linarith) pi_pos]
  have hexp : -(N : ℝ)+1 = -((N-1 : ℕ) : ℝ) := by push_cast [show 1 ≤ N by omega]; ring
  rw [hexp, rpow_neg pi_pos.le, rpow_natCast]
  push_cast [show 1 ≤ N by omega]
  field_simp
  <;> ring

#print axioms weight_le_gauss
#print axioms weight_le_tail
#print axioms gauss_integrable
#print axioms tail_integrable
#print axioms weight_integrable_half
#print axioms weight_integral_le
#print axioms gaussian_half_integral
#print axioms tail_half_integral
end PrivateApex
