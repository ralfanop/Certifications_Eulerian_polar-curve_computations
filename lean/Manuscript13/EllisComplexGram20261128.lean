import Mathlib
import Manuscript13.EllisGreenConvolution20261127
import Manuscript13.EllisSpectralEnumeration20261127

/-! Concrete real Gram / complex weighted Green operator bridge.
No abstract kernel-operator identity is assumed. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Manuscript13.EllisComplexGram20261128
noncomputable section
open Manuscript13.EllisGramKernelOperator20261124 (gramOperator kernelOperator row rowApply row_inner applyLp_ae)
open Manuscript13.EllisBirman20261124 (bsKernel spectralDet)
open Manuscript13.EllisComplexResolvent20261127 (weight weightOperator weightOperator_ae birmanSchwinger birmanSchwinger_apply freeResolvent)
open Manuscript13.EllisGreenKernel20261127 (green)
open Manuscript13.EllisGreenConvolution20261127 (resolvent_convolution_ae)
abbrev HR := Manuscript13.EllisGramKernelOperator20261124.H
abbrev HC := Manuscript13.EllisComplexResolvent20261127.H

theorem gram_integral_ae (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : HR) :
    (fun u => gramOperator a κ ha hk f u) =ᵐ[volume]
      (fun u => ∫ v : ℝ, bsKernel a κ u v * f v) := by
  let A := kernelOperator a κ ha hk
  filter_upwards [applyLp_ae a κ ha hk (A.adjoint f)] with u hu
  change gramOperator a κ ha hk f u = rowApply a κ hk (A.adjoint f) u at hu
  rw [hu]
  unfold rowApply
  calc
    _ = inner ℝ (A.adjoint f) (row a κ hk u) := real_inner_comm _ _
    _ = inner ℝ f (A (row a κ hk u)) := A.adjoint_inner_left _ _
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [applyLp_ae a κ ha hk (row a κ hk u)] with v hv
      change A (row a κ hk u) v = rowApply a κ hk (row a κ hk u) v at hv
      rw [hv, rowApply, real_inner_comm (row a κ hk v) (row a κ hk u), row_inner]
      first
      | change f v * bsKernel a κ u v = bsKernel a κ u v * f v
        ring
      | rfl
      | simp [RCLike.inner_apply, mul_comm]

theorem kernel_cast (a κ u v : ℝ) :
    (bsKernel a κ u v : ℂ) = weight a u * (green κ (u-v) * weight a v) := by
  unfold bsKernel weight green
  push_cast
  ring

theorem weighted_integral_ae (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : HC) :
    (fun u => birmanSchwinger a κ ha hk f u) =ᵐ[volume]
      (fun u => ∫ v : ℝ, (bsKernel a κ u v : ℂ) * f v) := by
  rw [birmanSchwinger_apply]
  filter_upwards [weightOperator_ae a ha (freeResolvent κ hk (weightOperator a ha f)),
    resolvent_convolution_ae κ hk (weightOperator a ha f)] with u hu hv
  rw [hu, hv, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [weightOperator_ae a ha f] with v h
  rw [h, kernel_cast]
  ring

theorem complex_mem (f : HR) : MemLp (fun x : ℝ => (f x : ℂ)) 2 volume := by
  apply (Lp.memLp f).of_le
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable)
  · filter_upwards [] with x
    rw [Complex.norm_real]

def complexify (f : HR) : HC := (complex_mem f).toLp _

theorem complexify_ae (f : HR) :
    (fun x => complexify f x) =ᵐ[volume] (fun x : ℝ => (f x : ℂ)) :=
  (complex_mem f).coeFn_toLp

theorem complexify_injective : Function.Injective complexify := by
  intro f g h
  apply Lp.ext
  filter_upwards [complexify_ae f,complexify_ae g] with x hf hg
  rw [h,hg] at hf
  exact Complex.ofReal_injective hf.symm

theorem gram_intertwine (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : HR) :
    birmanSchwinger a κ ha hk (complexify f) = complexify (gramOperator a κ ha hk f) := by
  apply Lp.ext
  filter_upwards [weighted_integral_ae a κ ha hk (complexify f),
    complexify_ae (gramOperator a κ ha hk f),gram_integral_ae a κ ha hk f] with u hu hv hw
  rw [hu,hv,hw]
  calc
    _ = ∫ v : ℝ, ((bsKernel a κ u v * f v : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [complexify_ae f] with v h
      rw [h]
      push_cast
      rfl
    _ = _ := by
      first
      | exact Complex.ofReal_integral.symm
      | rw [Complex.ofReal_integral]
      | exact?

theorem complexify_real_smul (c : ℝ) (f : HR) :
    complexify (c • f) = (c : ℂ) • complexify f := by
  apply Lp.ext
  filter_upwards [complexify_ae (c • f),complexify_ae f,Lp.coeFn_smul c f,
    Lp.coeFn_smul (c : ℂ) (complexify f)] with x h1 h2 h3 h4
  rw [h1,h3,h4,h2]
  simp [smul_eq_mul,Complex.ofReal_mul]

theorem complex_eigenvector (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (f : HR) (λ : ℝ) (h : gramOperator a κ ha hk f = λ • f) :
    birmanSchwinger a κ ha hk (complexify f) = (λ : ℂ) • complexify f := by
  rw [gram_intertwine a κ ha hk f,h,complexify_real_smul]

theorem complexify_inner (f g : HR) :
    inner ℂ (complexify f) (complexify g) = (inner ℝ f g : ℂ) := by
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ x : ℝ, ((inner ℝ (f x) (g x) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [complexify_ae f,complexify_ae g] with x hf hg
      rw [hf,hg]
      simp [RCLike.inner_apply,Complex.ofReal_mul,mul_comm]
    _ = _ := by
      first
      | exact Complex.ofReal_integral.symm
      | rw [Complex.ofReal_integral]
      | exact?

theorem complexify_orthonormal (e : ℕ → HR) (he : Orthonormal ℝ e) :
    Orthonormal ℂ (fun n => complexify (e n)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [complexify_inner,(orthonormal_iff_ite.mp he) i j]
  split <;> simp_all

end
end Manuscript13.EllisComplexGram20261128
#print axioms Manuscript13.EllisComplexGram20261128.gram_integral_ae
#print axioms Manuscript13.EllisComplexGram20261128.kernel_cast
#print axioms Manuscript13.EllisComplexGram20261128.weighted_integral_ae
#print axioms Manuscript13.EllisComplexGram20261128.complex_mem
#print axioms Manuscript13.EllisComplexGram20261128.complexify
#print axioms Manuscript13.EllisComplexGram20261128.complexify_ae
#print axioms Manuscript13.EllisComplexGram20261128.complexify_injective
#print axioms Manuscript13.EllisComplexGram20261128.gram_intertwine
#print axioms Manuscript13.EllisComplexGram20261128.complexify_real_smul
#print axioms Manuscript13.EllisComplexGram20261128.complex_eigenvector
#print axioms Manuscript13.EllisComplexGram20261128.complexify_inner
#print axioms Manuscript13.EllisComplexGram20261128.complexify_orthonormal
