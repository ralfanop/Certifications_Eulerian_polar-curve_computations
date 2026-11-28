import Mathlib
import Manuscript13.EllisComplexGram20261128

/-! Complexification of the *complete* real eigenbasis, with no
assumed complex eigenbasis, multiplicities, or trace bound. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Manuscript13.EllisComplexSpectral20261128
noncomputable section
open Manuscript13.EllisComplexGram20261128
open Manuscript13.EllisGramKernelOperator20261124 (gramOperator)
open Manuscript13.EllisComplexResolvent20261127 (birmanSchwinger)
open Manuscript13.EllisBirman20261124 (spectralDet)
open Manuscript13.EllisFredholmProduct20261127 (eigen_nonneg eigen_summable eigen_trace)
open Manuscript13.EllisSpectralEnumeration20261127 (gram_product_unconditional)

theorem real_mem (z : HC) : MemLp (fun x : ℝ => (z x).re) 2 volume := by
  apply (Lp.memLp z).of_le
  · exact Complex.continuous_re.comp_aestronglyMeasurable (Lp.memLp z).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _

theorem imag_mem (z : HC) : MemLp (fun x : ℝ => (z x).im) 2 volume := by
  apply (Lp.memLp z).of_le
  · exact Complex.continuous_im.comp_aestronglyMeasurable (Lp.memLp z).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _

def realPart (z : HC) : HR := (real_mem z).toLp _
def imagPart (z : HC) : HR := (imag_mem z).toLp _

theorem realPart_ae (z : HC) :
    (fun x => realPart z x) =ᵐ[volume] (fun x => (z x).re) :=
  (real_mem z).coeFn_toLp

theorem imagPart_ae (z : HC) :
    (fun x => imagPart z x) =ᵐ[volume] (fun x => (z x).im) :=
  (imag_mem z).coeFn_toLp

theorem split_complex (z : HC) :
    complexify (realPart z) + Complex.I • complexify (imagPart z) = z := by
  apply Lp.ext
  filter_upwards [realPart_ae z,imagPart_ae z,complexify_ae (realPart z),
    complexify_ae (imagPart z),Lp.coeFn_smul Complex.I (complexify (imagPart z)),
    Lp.coeFn_add (complexify (realPart z)) (Complex.I • complexify (imagPart z))]
      with x hr hi hcr hci hs hadd
  rw [hadd,hs,hcr,hci,hr,hi]
  change ((z x).re : ℂ) + Complex.I * ((z x).im : ℂ) = z x
  rw [mul_comm Complex.I]
  exact Complex.re_add_im _

theorem real_basis_zero (e : HilbertBasis ℕ ℝ HR) (x : HR)
    (h : ∀ i, inner ℝ (e i) x = 0) : x = 0 := by
  have hr : ∀ i, e.repr x i = 0 := by
    intro i
    first
    | simpa only [HilbertBasis.repr_apply_apply] using h i
    | rw [HilbertBasis.repr_apply_apply]; exact h i
    | exact?
  have hs : HasSum (fun _ : ℕ => (0 : HR)) x := by
    simpa only [hr,zero_smul] using e.hasSum_repr x
  exact hs.unique hasSum_zero

theorem complex_span_orthogonal (e : HilbertBasis ℕ ℝ HR) :
    (Submodule.span ℂ (Set.range (fun i => complexify (e i))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  have h (i : ℕ) : inner ℂ (complexify (e i)) z = 0 :=
    (Submodule.mem_orthogonal _ _).mp hz _ (Submodule.subset_span ⟨i,rfl⟩)
  have hparts (i : ℕ) :
      ((inner ℝ (e i) (realPart z) : ℝ) : ℂ) +
        Complex.I * ((inner ℝ (e i) (imagPart z) : ℝ) : ℂ) = 0 := by
    have hi := h i
    rw [← split_complex z,inner_add_right,inner_smul_right,complexify_inner,complexify_inner] at hi
    simpa only [smul_eq_mul] using hi
  have hr : realPart z = 0 := by
    apply real_basis_zero e
    intro i
    have hi := congrArg Complex.re (hparts i)
    simpa using hi
  have him : imagPart z = 0 := by
    apply real_basis_zero e
    intro i
    have hi := congrArg Complex.im (hparts i)
    simpa using hi
  have hzero : complexify (0 : HR) = 0 := by
    apply Lp.ext
    filter_upwards [complexify_ae (0 : HR),Lp.coeFn_zero ℝ 2 volume,
      Lp.coeFn_zero ℂ 2 volume] with x h1 h2 h3
    rw [h1,h2,h3]
    simp
  rw [Submodule.mem_bot]
  calc
    z = complexify (realPart z) + Complex.I • complexify (imagPart z) := (split_complex z).symm
    _ = 0 := by simp [hr,him,hzero]

def complexBasis (e : HilbertBasis ℕ ℝ HR) : HilbertBasis ℕ ℂ HC :=
  HilbertBasis.mkOfOrthogonalEqBot (complexify_orthonormal e e.orthonormal)
    (complex_span_orthogonal e)

theorem complexBasis_apply (e : HilbertBasis ℕ ℝ HR) (i : ℕ) :
    complexBasis e i = complexify (e i) := by
  simp [complexBasis]

theorem complex_spectral_corollary (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    ∃ (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ),
      (∀ i, birmanSchwinger a κ ha hk (e i) = (eig i : ℂ) • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      (∑' i, eig i) = Real.pi/(4*a*κ) ∧
      HasProd (fun i => 1 + eig i) (spectralDet eig) ∧
      1 < spectralDet eig ∧ spectralDet eig ≤ Real.exp (Real.pi/(4*a*κ)) := by
  obtain ⟨e,eig,he,hprod,hlo,hhi⟩ := gram_product_unconditional a κ ha hk
  refine ⟨complexBasis e,eig,?_,eigen_nonneg a κ ha hk e eig he,
    eigen_summable a κ ha hk e eig he,eigen_trace a κ ha hk e eig he,hprod,hlo,hhi⟩
  intro i
  rw [complexBasis_apply]
  exact complex_eigenvector a κ ha hk (e i) (eig i) (he i)

end
end Manuscript13.EllisComplexSpectral20261128
#print axioms Manuscript13.EllisComplexSpectral20261128.real_mem
#print axioms Manuscript13.EllisComplexSpectral20261128.imag_mem
#print axioms Manuscript13.EllisComplexSpectral20261128.realPart
#print axioms Manuscript13.EllisComplexSpectral20261128.imagPart
#print axioms Manuscript13.EllisComplexSpectral20261128.realPart_ae
#print axioms Manuscript13.EllisComplexSpectral20261128.imagPart_ae
#print axioms Manuscript13.EllisComplexSpectral20261128.split_complex
#print axioms Manuscript13.EllisComplexSpectral20261128.real_basis_zero
#print axioms Manuscript13.EllisComplexSpectral20261128.complex_span_orthogonal
#print axioms Manuscript13.EllisComplexSpectral20261128.complexBasis
#print axioms Manuscript13.EllisComplexSpectral20261128.complexBasis_apply
#print axioms Manuscript13.EllisComplexSpectral20261128.complex_spectral_corollary
