import Mathlib
import Manuscript13.EllisFourier20261124

/-! M13 Corollary 4.12. Real causal exponential factor of the actual
Birman--Schwinger integral kernel. The Hilbert--Schmidt kernel norm is
computed by Fubini, not inferred from a diagonal formula alone.
The standard integral-operator/trace-class correspondence and identification
with the unbounded free resolvent remain separate operator-theoretic bridges.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace Manuscript13.EllisBirman20261124
noncomputable section
open Manuscript13.EllisFourier20261124 (potential actual_potential_mass cauchy_integrable)

def causal (a κ u t : ℝ) : ℝ :=
  if u < t then Real.sqrt (potential a u) * Real.exp (-κ*(t-u)) else 0

def bsKernel (a κ u v : ℝ) : ℝ :=
  Real.sqrt (potential a u) * Real.sqrt (potential a v) *
    (Real.exp (-κ*|u-v|)/(2*κ))

theorem potential_nonneg (a u : ℝ) : 0 ≤ potential a u := by
  unfold potential
  positivity

theorem potential_integrable (a : ℝ) (ha : 0 < a) : Integrable (potential a) := by
  apply (cauchy_integrable a ha).mono'
  · apply Continuous.aestronglyMeasurable
    unfold potential
    exact continuous_const.div ((continuous_id.pow 2 |>.add continuous_const).pow 2)
      (fun u => by positivity)
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg a u)]
    unfold potential Manuscript13.EllisFourier20261124.cauchy
    have h : 0 < u^2+a^2 := by positivity
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (u^2+a^2)^2) h).2
    nlinarith [mul_nonneg (sq_nonneg u) h.le]

theorem overlap_exp (κ u v : ℝ) (hk : 0 < κ) :
    (∫ t in Ioi (max u v), Real.exp (-κ*(t-u))*Real.exp (-κ*(t-v))) =
      Real.exp (-κ*|u-v|)/(2*κ) := by
  have h : -2*κ < 0 := by linarith
  have he : ∀ t : ℝ, Real.exp (-κ*(t-u))*Real.exp (-κ*(t-v)) =
      Real.exp (κ*(u+v))*Real.exp ((-2*κ)*t) := by
    intro t
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_Ioi h, mul_neg, ← mul_div_assoc, ← Real.exp_add]
  have ha : κ*(u+v)+(-2*κ)*max u v = -κ*|u-v| := by
    rcases le_total u v with huv | hvu
    · rw [max_eq_right huv, abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    · rw [max_eq_left hvu, abs_of_nonneg (sub_nonneg.mpr hvu)]
      ring
  rw [ha]
  ring

theorem gram_kernel_identity (a κ u v : ℝ) (hk : 0 < κ) :
    (∫ t : ℝ, causal a κ u t * causal a κ v t) = bsKernel a κ u v := by
  have he : (fun t : ℝ => causal a κ u t * causal a κ v t) =
      (Ioi (max u v)).indicator (fun t => (Real.sqrt (potential a u)*Real.sqrt (potential a v)) *
        (Real.exp (-κ*(t-u))*Real.exp (-κ*(t-v)))) := by
    funext t
    by_cases hu : u < t <;> by_cases hv : v < t <;>
      simp [causal, hu, hv, Set.indicator, Set.mem_Ioi, max_lt_iff, mul_assoc, mul_left_comm, mul_comm]
  rw [he, integral_indicator measurableSet_Ioi, integral_const_mul, overlap_exp κ u v hk]
  rfl

theorem diagonal (a κ u : ℝ) :
    bsKernel a κ u u = potential a u / (2*κ) := by
  unfold bsKernel
  rw [sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero,
      ← pow_two, Real.sq_sqrt (potential_nonneg a u)]
  ring

theorem diagonal_mass (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    (∫ u : ℝ, bsKernel a κ u u) = Real.pi/(4*a*κ) := by
  simp_rw [diagonal]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, actual_potential_mass a ha]
  field_simp [ne_of_gt ha, ne_of_gt hk]
  <;> ring

theorem causal_square_section (a κ u : ℝ) (hk : 0 < κ) :
    Integrable (fun t : ℝ => causal a κ u t ^ 2) := by
  have h : -2*κ < 0 := by linarith
  have hf : (fun t : ℝ => causal a κ u t ^ 2) =
      (Ioi u).indicator (fun t => (potential a u*Real.exp (2*κ*u))*Real.exp ((-2*κ)*t)) := by
    funext t
    by_cases ht : u < t
    · simp [causal, ht, Set.indicator, Set.mem_Ioi, mul_pow, Real.sq_sqrt (potential_nonneg a u),
        pow_two, ← Real.exp_add, mul_assoc]
      congr 2 <;> ring
    · simp [causal, ht, Set.indicator, Set.mem_Ioi]
  rw [hf, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_exp_mul_Ioi h u).const_mul _

theorem causal_square_measurable (a κ : ℝ) :
    Measurable (fun p : ℝ × ℝ => causal a κ p.1 p.2 ^ 2) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  unfold causal
  apply Measurable.pow_const
  apply Measurable.ite hs
  · unfold potential
    fun_prop
  · exact measurable_const

theorem actual_hs_kernel_square_integrable (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    Integrable (fun p : ℝ × ℝ => causal a κ p.1 p.2 ^ 2)
      (volume.prod volume) := by
  apply (integrable_prod_iff (causal_square_measurable a κ).aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun u => causal_square_section a κ u hk), ?_⟩
  have he : (fun u : ℝ => ∫ t : ℝ, ‖causal a κ u t ^ 2‖) =
      fun u => potential a u / (2*κ) := by
    funext u
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    rw [gram_kernel_identity a κ u u hk, diagonal]
  rw [he]
  simpa [div_eq_mul_inv] using (potential_integrable a ha).mul_const (2*κ)⁻¹

theorem actual_hs_kernel_norm_sq (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    (∫ p : ℝ × ℝ, causal a κ p.1 p.2 ^ 2 ∂(volume.prod volume)) =
      Real.pi/(4*a*κ) := by
  rw [integral_prod _ (actual_hs_kernel_square_integrable a κ ha hk)]
  simp_rw [pow_two, gram_kernel_identity a κ _ _ hk]
  exact diagonal_mass a κ ha hk

def spectralDet (λ : ℕ → ℝ) : ℝ :=
  Real.exp (∑' n, Real.log (1+λ n))

/-- The actual spectral-series bound once the positive eigenvalues of the
trace-class operator have been supplied by the operator-theoretic bridge. -/
theorem spectral_det_bounds (λ : ℕ → ℝ) (hn : ∀ n, 0 ≤ λ n)
    (hs : Summable λ) (ht : 0 < ∑' n, λ n) :
    1 < spectralDet λ ∧ spectralDet λ ≤ Real.exp (∑' n, λ n) := by
  have hlognonneg : ∀ n, 0 ≤ Real.log (1+λ n) :=
    fun n => Real.log_nonneg (by linarith [hn n])
  have hlogle : ∀ n, Real.log (1+λ n) ≤ λ n := by
    intro n
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+λ n by linarith [hn n])
    linarith
  have hlogs : Summable (fun n => Real.log (1+λ n)) :=
    Summable.of_nonneg_of_le hlognonneg hlogle hs
  have hex : ∃ n, 0 < λ n := by
    by_contra! h
    have hz : λ = fun _ => 0 := funext (fun n => le_antisymm (h n) (hn n))
    rw [hz] at ht
    simpa using ht
  obtain ⟨n,hnpos⟩ := hex
  have hpos := hlogs.tsum_pos hlognonneg n (Real.log_pos (by linarith : 1 < 1+λ n))
  unfold spectralDet
  exact ⟨by simpa using Real.exp_lt_exp.mpr hpos,
    Real.exp_le_exp.mpr (hlogs.tsum_le_tsum hlogle hs)⟩

theorem det_trace_specialization (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (λ : ℕ → ℝ) (hn : ∀ n, 0 ≤ λ n) (hs : Summable λ)
    (ht : (∑' n, λ n) = Real.pi/(4*a*κ)) :
    1 < spectralDet λ ∧ spectralDet λ ≤ Real.exp (Real.pi/(4*a*κ)) := by
  have hpos : 0 < ∑' n, λ n := by rw [ht]; positivity
  simpa [ht] using spectral_det_bounds λ hn hs hpos

end
end Manuscript13.EllisBirman20261124

#print axioms Manuscript13.EllisBirman20261124.potential_nonneg
#print axioms Manuscript13.EllisBirman20261124.potential_integrable
#print axioms Manuscript13.EllisBirman20261124.overlap_exp
#print axioms Manuscript13.EllisBirman20261124.gram_kernel_identity
#print axioms Manuscript13.EllisBirman20261124.diagonal
#print axioms Manuscript13.EllisBirman20261124.diagonal_mass
#print axioms Manuscript13.EllisBirman20261124.causal_square_section
#print axioms Manuscript13.EllisBirman20261124.causal_square_measurable
#print axioms Manuscript13.EllisBirman20261124.actual_hs_kernel_square_integrable
#print axioms Manuscript13.EllisBirman20261124.actual_hs_kernel_norm_sq
#print axioms Manuscript13.EllisBirman20261124.spectral_det_bounds
#print axioms Manuscript13.EllisBirman20261124.det_trace_specialization
