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

/-- The diagonal expansion is a theorem for every vector, not merely
an assertion on a family of eigenvectors. -/
theorem diagonal_action (T : HC →L[ℂ] HC) (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ)
    (he : ∀ i, T (e i) = (eig i : ℂ) • e i) (x : HC) :
    HasSum (fun i => ((eig i : ℂ) * inner ℂ (e i) x) • e i) (T x) := by
  have h := T.hasSum (e.hasSum_repr x)
  convert h using 1
  funext i
  rw [map_smul,he,HilbertBasis.repr_apply_apply,smul_smul,mul_comm]

theorem diagonal_inner_sum (T : HC →L[ℂ] HC) (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ)
    (he : ∀ i, T (e i) = (eig i : ℂ) • e i) (x y : HC) :
    HasSum (fun i => (eig i : ℂ) * inner ℂ x (e i) * inner ℂ (e i) y)
      (inner ℂ x (T y)) := by
  have h := (innerSL ℂ x).hasSum (diagonal_action T e eig he y)
  convert h using 1
  funext i
  rw [innerSL_apply_apply,inner_smul_right]
  ring

theorem diagonal_selfAdjoint (T : HC →L[ℂ] HC) (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ)
    (he : ∀ i, T (e i) = (eig i : ℂ) • e i) : IsSelfAdjoint T := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have h1 := diagonal_inner_sum T e eig he x y
  have h2 := Complex.conjCLE.toContinuousLinearMap.hasSum (diagonal_inner_sum T e eig he y x)
  have h3 : HasSum (fun i => (eig i : ℂ) * inner ℂ x (e i) * inner ℂ (e i) y)
      (inner ℂ (T x) y) := by
    convert h2 using 1
    · funext i
      simp only [ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,map_mul,Complex.conj_ofReal,
        inner_conj_symm]
      ring
    · simpa only [ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,inner_conj_symm]
  exact h3.unique h1

theorem diagonal_positive (T : HC →L[ℂ] HC) (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ)
    (he : ∀ i, T (e i) = (eig i : ℂ) • e i) (hn : ∀ i, 0 ≤ eig i) (x : HC) :
    0 ≤ (inner ℂ x (T x)).re := by
  have h := Complex.reCLM.hasSum (diagonal_inner_sum T e eig he x x)
  rw [← h.tsum_eq]
  apply tsum_nonneg
  intro i
  change 0 ≤ ((eig i : ℂ) * inner ℂ x (e i) * inner ℂ (e i) x).re
  rw [← inner_conj_symm x (e i)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,zero_mul,sub_zero,zero_add,add_zero]
  nlinarith [mul_nonneg (hn i) (sq_nonneg (inner ℂ (e i) x).re),
    mul_nonneg (hn i) (sq_nonneg (inner ℂ (e i) x).im)]

def complexRank (v : HC) : HC →L[ℂ] HC := (innerSL ℂ v).smulRight v

theorem complexRank_norm_le (v : HC) : ‖complexRank v‖ ≤ ‖v‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro x
  change ‖inner ℂ v x • v‖ ≤ ‖v‖^2 * ‖x‖
  rw [norm_smul]
  calc
    _ ≤ (‖v‖ * ‖x‖) * ‖v‖ := mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

theorem complex_rank_summable (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ)
    (hn : ∀ i, 0 ≤ eig i) (hs : Summable eig) :
    Summable (fun i => (eig i : ℂ) • complexRank (e i)) := by
  apply Summable.of_norm_bounded hs
  intro i
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn i)]
  have hb := complexRank_norm_le (e i)
  rw [e.orthonormal.norm_eq_one i,one_pow] at hb
  nlinarith [mul_le_mul_of_nonneg_left hb (hn i)]

theorem complex_rank_expansion (T : HC →L[ℂ] HC) (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ)
    (he : ∀ i, T (e i) = (eig i : ℂ) • e i) (hn : ∀ i, 0 ≤ eig i) (hs : Summable eig) :
    (∑' i, (eig i : ℂ) • complexRank (e i)) = T := by
  apply ContinuousLinearMap.ext
  intro x
  have h := (ContinuousLinearMap.apply ℂ HC x).hasSum (complex_rank_summable e eig hn hs).hasSum
  have hx := diagonal_action T e eig he x
  have h' : HasSum (fun i => ((eig i : ℂ) * inner ℂ (e i) x) • e i)
      ((∑' i, (eig i : ℂ) • complexRank (e i)) x) := by
    convert h using 1
    funext i
    change _ = (eig i : ℂ) • (inner ℂ (e i) x • e i)
    rw [smul_smul]
  exact h'.unique hx

theorem weighted_selfAdjoint (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    IsSelfAdjoint (birmanSchwinger a κ ha hk) := by
  obtain ⟨e,eig,he,_⟩ := complex_spectral_corollary a κ ha hk
  exact diagonal_selfAdjoint _ e eig he

theorem weighted_positive (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (x : HC) :
    0 ≤ (inner ℂ x (birmanSchwinger a κ ha hk x)).re := by
  obtain ⟨e,eig,he,hn,_⟩ := complex_spectral_corollary a κ ha hk
  exact diagonal_positive _ e eig he hn x

/-- A summable rank-one representation, with exact sum of the
nonnegative rank-one coefficients, for the actual weighted operator.
This explicitly exhibits a nuclear decomposition. -/
theorem weighted_nuclear_expansion (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    ∃ (e : HilbertBasis ℕ ℂ HC) (eig : ℕ → ℝ),
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = Real.pi/(4*a*κ) ∧
      Summable (fun i => (eig i : ℂ) • complexRank (e i)) ∧
      (∑' i, (eig i : ℂ) • complexRank (e i)) = birmanSchwinger a κ ha hk := by
  obtain ⟨e,eig,he,hn,hs,ht,_⟩ := complex_spectral_corollary a κ ha hk
  exact ⟨e,eig,hn,hs,ht,complex_rank_summable e eig hn hs,
    complex_rank_expansion _ e eig he hn hs⟩

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
#print axioms Manuscript13.EllisComplexSpectral20261128.diagonal_action
#print axioms Manuscript13.EllisComplexSpectral20261128.diagonal_inner_sum
#print axioms Manuscript13.EllisComplexSpectral20261128.diagonal_selfAdjoint
#print axioms Manuscript13.EllisComplexSpectral20261128.diagonal_positive
#print axioms Manuscript13.EllisComplexSpectral20261128.complexRank
#print axioms Manuscript13.EllisComplexSpectral20261128.complexRank_norm_le
#print axioms Manuscript13.EllisComplexSpectral20261128.complex_rank_summable
#print axioms Manuscript13.EllisComplexSpectral20261128.complex_rank_expansion
#print axioms Manuscript13.EllisComplexSpectral20261128.weighted_selfAdjoint
#print axioms Manuscript13.EllisComplexSpectral20261128.weighted_positive
#print axioms Manuscript13.EllisComplexSpectral20261128.weighted_nuclear_expansion
