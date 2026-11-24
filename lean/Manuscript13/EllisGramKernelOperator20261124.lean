import Mathlib
import Manuscript13.EllisBirman20261124
import Manuscript13.BirmanOperator20261124

/-! M13 Corollary 4.12: actual bounded integral operator A from
the causal kernel. A maps the t-variable to the u-variable; the
Birman–Schwinger Gram operator has orientation AA*, not A*A.
Rows belong to L², their norm-square is the certified diagonal,
and the integral operator bound follows by Cauchy–Schwarz.
The Hilbert-basis Parseval/Tonelli trace-class proof, identification
of AA* with the weighted differential resolvent, and genuine Fredholm
determinant identification remain separate. -/
open MeasureTheory Set
namespace Manuscript13.EllisGramKernelOperator20261124
noncomputable section
open Manuscript13.EllisBirman20261124
open Manuscript13.EllisFourier20261124 (potential)
abbrev H := Lp ℝ 2 (volume : Measure ℝ)

theorem causal_measurable (a κ : ℝ) :
    Measurable (fun p : ℝ × ℝ => causal a κ p.1 p.2) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  unfold causal
  apply Measurable.ite hs
  · unfold potential
    fun_prop
  · exact measurable_const

theorem row_mem (a κ u : ℝ) (hk : 0 < κ) :
    MemLp (fun t => causal a κ u t) 2 volume := by
  apply (memLp_two_iff_integrable_sq _).2
  · exact causal_square_section a κ u hk
  · exact ((causal_measurable a κ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

def row (a κ : ℝ) (hk : 0 < κ) (u : ℝ) : H :=
  (row_mem a κ u hk).toLp _

theorem row_ae (a κ : ℝ) (hk : 0 < κ) (u : ℝ) :
    (fun t => row a κ hk u t) =ᵐ[volume] (fun t => causal a κ u t) :=
  (row_mem a κ u hk).coeFn_toLp

theorem row_inner (a κ : ℝ) (hk : 0 < κ) (u v : ℝ) :
    inner ℝ (row a κ hk u) (row a κ hk v) = bsKernel a κ u v := by
  rw [L2.inner_def, ← gram_kernel_identity a κ u v hk]
  apply integral_congr_ae
  filter_upwards [row_ae a κ hk u, row_ae a κ hk v] with t hu hv
  rw [hu, hv]
  simp [real_inner_eq_mul, mul_comm]

theorem row_norm_sq (a κ : ℝ) (hk : 0 < κ) (u : ℝ) :
    ‖row a κ hk u‖ ^ 2 = potential a u / (2*κ) := by
  rw [← real_inner_self_eq_norm_sq, row_inner, diagonal]

def rowWeight (a κ u : ℝ) : ℝ := Real.sqrt (potential a u / (2*κ))

theorem row_weight_eq (a κ : ℝ) (hk : 0 < κ) (u : ℝ) :
    rowWeight a κ u = ‖row a κ hk u‖ := by
  unfold rowWeight
  rw [← row_norm_sq a κ hk u, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem row_weight_mem (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    MemLp (rowWeight a κ) 2 volume := by
  have hm : Measurable (rowWeight a κ) := by unfold rowWeight potential; fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  have he : (fun u => rowWeight a κ u ^ 2) = fun u => potential a u / (2*κ) := by
    funext u
    unfold rowWeight
    rw [Real.sq_sqrt (div_nonneg (potential_nonneg a u) (by positivity))]
  rw [he]
  simpa [div_eq_mul_inv] using (potential_integrable a ha).mul_const (2*κ)⁻¹

def weightLp (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) : H :=
  (row_weight_mem a κ ha hk).toLp _

theorem weightLp_ae (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    (fun u => weightLp a κ ha hk u) =ᵐ[volume] rowWeight a κ :=
  (row_weight_mem a κ ha hk).coeFn_toLp

theorem weightLp_norm_sq (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    ‖weightLp a κ ha hk‖ ^ 2 = Real.pi/(4*a*κ) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← diagonal_mass a κ ha hk]
  apply integral_congr_ae
  filter_upwards [weightLp_ae a κ ha hk] with u hu
  rw [hu, diagonal]
  simp only [real_inner_eq_mul, ← pow_two, rowWeight]
  exact Real.sq_sqrt (div_nonneg (potential_nonneg a u) (by positivity))

def rowApply (a κ : ℝ) (hk : 0 < κ) (f : H) (u : ℝ) : ℝ :=
  inner ℝ (row a κ hk u) f

theorem rowApply_integral (a κ : ℝ) (hk : 0 < κ) (f : H) (u : ℝ) :
    rowApply a κ hk f u = ∫ t : ℝ, causal a κ u t * f t := by
  rw [rowApply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [row_ae a κ hk u] with t ht
  rw [ht]
  simp [real_inner_eq_mul, mul_comm]

theorem rowApply_measurable (a κ : ℝ) (hk : 0 < κ) (f : H) :
    AEStronglyMeasurable (rowApply a κ hk f) volume := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => causal a κ p.1 p.2 * f p.2) :=
    ((causal_measurable a κ).mul (f.stronglyMeasurable.measurable.comp measurable_snd)).stronglyMeasurable
  have he : rowApply a κ hk f = fun u => ∫ t : ℝ, causal a κ u t * f t := by
    funext u
    exact rowApply_integral a κ hk f u
  rw [he]
  exact hm.integral_prod_right'.aestronglyMeasurable

theorem rowApply_bound (a κ : ℝ) (hk : 0 < κ) (f : H) (u : ℝ) :
    ‖rowApply a κ hk f u‖ ≤ ‖f‖ * rowWeight a κ u := by
  rw [rowWeight, ← row_norm_sq a κ hk u, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [mul_comm]
  exact norm_inner_le_norm _ _

theorem rowApply_mem (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) :
    MemLp (rowApply a κ hk f) 2 volume := by
  apply ((row_weight_mem a κ ha hk).const_mul ‖f‖).mono'
  · exact rowApply_measurable a κ hk f
  · exact Filter.Eventually.of_forall (rowApply_bound a κ hk f)

def applyLp (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) : H :=
  (rowApply_mem a κ ha hk f).toLp _

theorem applyLp_ae (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) :
    (fun u => applyLp a κ ha hk f u) =ᵐ[volume] rowApply a κ hk f :=
  (rowApply_mem a κ ha hk f).coeFn_toLp

theorem applyLp_norm_bound (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) :
    ‖applyLp a κ ha hk f‖ ≤ ‖weightLp a κ ha hk‖ * ‖f‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyLp_ae a κ ha hk f, weightLp_ae a κ ha hk] with u hu hw
  rw [hu, hw, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact rowApply_bound a κ hk f u

def kernelLinear (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) : H →ₗ[ℝ] H where
  toFun := applyLp a κ ha hk
  map_add' f g := by
    apply Lp.ext
    filter_upwards [applyLp_ae a κ ha hk (f+g), applyLp_ae a κ ha hk f,
      applyLp_ae a κ ha hk g, Lp.coeFn_add (applyLp a κ ha hk f) (applyLp a κ ha hk g)]
      with u hfg hf hg hout
    rw [hfg, hout, hf, hg]
    simp [rowApply, inner_add_right]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [applyLp_ae a κ ha hk (c • f), applyLp_ae a κ ha hk f,
      Lp.coeFn_smul c (applyLp a κ ha hk f)] with u hcf hf hout
    rw [hcf, hout, hf]
    simp [rowApply, inner_smul_right]

def kernelOperator (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) : H →L[ℝ] H :=
  (kernelLinear a κ ha hk).mkContinuous ‖weightLp a κ ha hk‖
    (applyLp_norm_bound a κ ha hk)

theorem kernelOperator_ae (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) :
    (fun u => kernelOperator a κ ha hk f u) =ᵐ[volume]
      (fun u => ∫ t : ℝ, causal a κ u t * f t) := by
  filter_upwards [applyLp_ae a κ ha hk f] with u hu
  exact hu.trans (rowApply_integral a κ hk f u)

theorem kernelOperator_bound (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    ‖kernelOperator a κ ha hk‖ ≤ Real.sqrt (Real.pi/(4*a*κ)) := by
  rw [← weightLp_norm_sq a κ ha hk, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (applyLp_norm_bound a κ ha hk)

def gramOperator (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) : H →L[ℝ] H :=
  (kernelOperator a κ ha hk).comp (kernelOperator a κ ha hk).adjoint

theorem gramOperator_nonneg (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) :
    0 ≤ inner ℝ (gramOperator a κ ha hk f) f := by
  have h := Manuscript13.BirmanOperator20261124.gram_nonneg
    (kernelOperator a κ ha hk).adjoint f
  simpa [Manuscript13.BirmanOperator20261124.gram, gramOperator] using h

end
end Manuscript13.EllisGramKernelOperator20261124
#print axioms Manuscript13.EllisGramKernelOperator20261124.causal_measurable
#print axioms Manuscript13.EllisGramKernelOperator20261124.row_mem
#print axioms Manuscript13.EllisGramKernelOperator20261124.row
#print axioms Manuscript13.EllisGramKernelOperator20261124.row_ae
#print axioms Manuscript13.EllisGramKernelOperator20261124.row_inner
#print axioms Manuscript13.EllisGramKernelOperator20261124.row_norm_sq
#print axioms Manuscript13.EllisGramKernelOperator20261124.row_weight_eq
#print axioms Manuscript13.EllisGramKernelOperator20261124.row_weight_mem
#print axioms Manuscript13.EllisGramKernelOperator20261124.weightLp_norm_sq
#print axioms Manuscript13.EllisGramKernelOperator20261124.rowApply_integral
#print axioms Manuscript13.EllisGramKernelOperator20261124.rowApply_measurable
#print axioms Manuscript13.EllisGramKernelOperator20261124.rowApply_bound
#print axioms Manuscript13.EllisGramKernelOperator20261124.rowApply_mem
#print axioms Manuscript13.EllisGramKernelOperator20261124.applyLp
#print axioms Manuscript13.EllisGramKernelOperator20261124.applyLp_ae
#print axioms Manuscript13.EllisGramKernelOperator20261124.applyLp_norm_bound
#print axioms Manuscript13.EllisGramKernelOperator20261124.kernelLinear
#print axioms Manuscript13.EllisGramKernelOperator20261124.kernelOperator
#print axioms Manuscript13.EllisGramKernelOperator20261124.kernelOperator_ae
#print axioms Manuscript13.EllisGramKernelOperator20261124.kernelOperator_bound
#print axioms Manuscript13.EllisGramKernelOperator20261124.gramOperator
#print axioms Manuscript13.EllisGramKernelOperator20261124.gramOperator_nonneg
