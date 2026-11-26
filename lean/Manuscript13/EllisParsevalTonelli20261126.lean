import Mathlib
import Manuscript13.EllisGramKernelOperator20261124

/-! M13 Cor. 4.12, eqs. (74)–(77), revised 26 Nov.
Actual real L² causal integral operator; Parseval and Tonelli
discharge the Hilbert–Schmidt diagonal summability, including
the adjoint and AA*.  The diagonal criterion is expressed for
each countable Hilbert basis. Identification with the complex
differential resolvent and the genuine Fredholm spectral product
are not assumed or claimed by this module. -/
open MeasureTheory Set
open scoped ENNReal
namespace Manuscript13.EllisParsevalTonelli20261126
noncomputable section
open Manuscript13.EllisGramKernelOperator20261124
open Manuscript13.EllisBirman20261124
open Manuscript13.EllisFourier20261124 (potential potential_integrable potential_nonneg)

theorem lp_norm_sq_integral (f : H) :
    ‖f‖^2 = ∫ u : ℝ, (f u)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with u
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem lp_norm_sq_lintegral (f : H) :
    ENNReal.ofReal (‖f‖^2) = ∫⁻ u : ℝ, ENNReal.ofReal ((f u)^2) := by
  rw [lp_norm_sq_integral]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (memLp_two_iff_integrable_sq (Lp.memLp f).aestronglyMeasurable).1 (Lp.memLp f)
  · exact Filter.Eventually.of_forall fun u => sq_nonneg (f u)

theorem row_parseval (a κ : ℝ) (hk : 0 < κ) (e : HilbertBasis ℕ ℝ H) (u : ℝ) :
    HasSum (fun i => (rowApply a κ hk (e i) u)^2) (‖row a κ hk u‖^2) := by
  have h := e.hasSum_inner_mul_inner (row a κ hk u) (row a κ hk u)
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  funext i
  unfold rowApply
  rw [pow_two, real_inner_comm (e i) (row a κ hk u)]

theorem row_energy_lintegral (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    (∫⁻ u : ℝ, ENNReal.ofReal (‖row a κ hk u‖^2)) =
      ENNReal.ofReal (Real.pi/(4*a*κ)) := by
  rw [← weightLp_norm_sq a κ ha hk, lp_norm_sq_lintegral]
  apply lintegral_congr_ae
  filter_upwards [weightLp_ae a κ ha hk] with u hu
  rw [hu,row_weight_eq a κ hk u, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem row_coordinate_ae (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) :
    (fun u => kernelOperator a κ ha hk f u) =ᵐ[volume] rowApply a κ hk f :=
  applyLp_ae a κ ha hk f

theorem row_coordinate_measurable (a κ : ℝ) (hk : 0 < κ) (f : H) :
    AEMeasurable (fun u => ENNReal.ofReal ((rowApply a κ hk f u)^2)) volume := by
  exact ((rowApply_measurable a κ hk f).aemeasurable.pow_const 2).ennreal_ofReal

theorem kernel_hs_lintegral (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    (∑' i, ENNReal.ofReal (‖kernelOperator a κ ha hk (e i)‖^2)) =
      ENNReal.ofReal (Real.pi/(4*a*κ)) := by
  calc
    _ = ∑' i, ∫⁻ u : ℝ, ENNReal.ofReal ((rowApply a κ hk (e i) u)^2) := by
      apply tsum_congr
      intro i
      rw [lp_norm_sq_lintegral]
      apply lintegral_congr_ae
      filter_upwards [row_coordinate_ae a κ ha hk (e i)] with u hu
      rw [hu]
    _ = ∫⁻ u : ℝ, ∑' i, ENNReal.ofReal ((rowApply a κ hk (e i) u)^2) :=
      (lintegral_tsum (fun i => row_coordinate_measurable a κ hk (e i))).symm
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (‖row a κ hk u‖^2) := by
      apply lintegral_congr
      intro u
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (row_parseval a κ hk e u).summable,
        (row_parseval a κ hk e u).tsum_eq]
    _ = _ := row_energy_lintegral a κ ha hk

theorem kernel_hs_summable (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    Summable (fun i => ‖kernelOperator a κ ha hk (e i)‖^2) := by
  have h : (∑' i, ENNReal.ofReal (‖kernelOperator a κ ha hk (e i)‖^2)) ≠ ⊤ := by
    rw [kernel_hs_lintegral a κ ha hk e]
    exact ENNReal.ofReal_ne_top
  first
  | exact ENNReal.summable_toReal h
  | exact? 

theorem kernel_hs_exact (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    (∑' i, ‖kernelOperator a κ ha hk (e i)‖^2) = Real.pi/(4*a*κ) := by
  have h := kernel_hs_lintegral a κ ha hk e
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (kernel_hs_summable a κ ha hk e)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun i => sq_nonneg _) (by positivity)).1 h

/-- Adjoint Hilbert–Schmidt energy by nonnegative double sum of actual matrix entries. -/
theorem adjoint_hs_lintegral (A : H →L[ℝ] H) (e : HilbertBasis ℕ ℝ H) :
    (∑' i, ENNReal.ofReal (‖A.adjoint (e i)‖^2)) =
      ∑' i, ENNReal.ofReal (‖A (e i)‖^2) := by
  have hp (x : H) :
      (∑' j, ENNReal.ofReal ((inner ℝ (e j) x)^2)) = ENNReal.ofReal (‖x‖^2) := by
    have h := e.hasSum_inner_mul_inner x x
    rw [real_inner_self_eq_norm_sq] at h
    have hs : HasSum (fun j => (inner ℝ (e j) x)^2) (‖x‖^2) := by
      convert h using 1
      funext j
      rw [pow_two, real_inner_comm x (e j)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hs.summable,hs.tsum_eq]
  calc
    _ = ∑' i, ∑' j, ENNReal.ofReal ((inner ℝ (e j) (A.adjoint (e i)))^2) := by
      apply tsum_congr
      intro i
      exact (hp _).symm
    _ = ∑' i, ∑' j, ENNReal.ofReal ((inner ℝ (e i) (A (e j)))^2) := by
      apply tsum_congr
      intro i
      apply tsum_congr
      intro j
      rw [real_inner_comm (e j) (A.adjoint (e i)), A.adjoint_inner_left, real_inner_comm (e i) (A (e j))]
    _ = ∑' j, ∑' i, ENNReal.ofReal ((inner ℝ (e i) (A (e j)))^2) := by
      exact ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro j
      exact hp _

theorem gram_diagonal_trace (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    (∑' i, ENNReal.ofReal (inner ℝ (gramOperator a κ ha hk (e i)) (e i))) =
      ENNReal.ofReal (Real.pi/(4*a*κ)) := by
  have h (i : ℕ) : inner ℝ (gramOperator a κ ha hk (e i)) (e i) =
      ‖(kernelOperator a κ ha hk).adjoint (e i)‖^2 := by
    simpa [gramOperator,Manuscript13.BirmanOperator20261124.gram] using
      Manuscript13.BirmanOperator20261124.gram_quadratic (kernelOperator a κ ha hk).adjoint (e i)
  simp_rw [h]
  rw [adjoint_hs_lintegral, kernel_hs_lintegral a κ ha hk e]

theorem gram_diagonal_summable (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    Summable (fun i => inner ℝ (gramOperator a κ ha hk (e i)) (e i)) := by
  have h : (∑' i, ENNReal.ofReal (inner ℝ (gramOperator a κ ha hk (e i)) (e i))) ≠ ⊤ := by
    rw [gram_diagonal_trace a κ ha hk e]
    exact ENNReal.ofReal_ne_top
  have hh := ENNReal.summable_toReal h
  simpa only [ENNReal.toReal_ofReal (gramOperator_nonneg a κ ha hk _)] using hh

end
end Manuscript13.EllisParsevalTonelli20261126
#print axioms Manuscript13.EllisParsevalTonelli20261126.lp_norm_sq_integral
#print axioms Manuscript13.EllisParsevalTonelli20261126.lp_norm_sq_lintegral
#print axioms Manuscript13.EllisParsevalTonelli20261126.row_parseval
#print axioms Manuscript13.EllisParsevalTonelli20261126.row_energy_lintegral
#print axioms Manuscript13.EllisParsevalTonelli20261126.row_coordinate_ae
#print axioms Manuscript13.EllisParsevalTonelli20261126.row_coordinate_measurable
#print axioms Manuscript13.EllisParsevalTonelli20261126.kernel_hs_lintegral
#print axioms Manuscript13.EllisParsevalTonelli20261126.kernel_hs_summable
#print axioms Manuscript13.EllisParsevalTonelli20261126.kernel_hs_exact
#print axioms Manuscript13.EllisParsevalTonelli20261126.adjoint_hs_lintegral
#print axioms Manuscript13.EllisParsevalTonelli20261126.gram_diagonal_trace
#print axioms Manuscript13.EllisParsevalTonelli20261126.gram_diagonal_summable
