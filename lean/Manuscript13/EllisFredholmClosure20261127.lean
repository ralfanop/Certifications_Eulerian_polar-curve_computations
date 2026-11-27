import Mathlib
import Manuscript13.EllisCompactSpectrum20261127
import Manuscript13.EllisFredholmProduct20261127
open Filter MeasureTheory
open scoped Topology
namespace Manuscript13.EllisFredholmClosure20261127
noncomputable section
open Manuscript13.EllisGramKernelOperator20261124
open Manuscript13.EllisCompactSpectrum20261127
open Manuscript13.EllisFredholmProduct20261127
open Manuscript13.EllisBirman20261124 (spectralDet)

/-! Construct an eigenfamily from the bases of the closed eigenspaces,
including the zero eigenspace. Reuse the compact spectral theorem,
not an assumed eigenbasis of the concrete Gram operator.
The final Nat-indexed application still takes the enumeration
equivalence of the assembled index type as a separate input. -/
abbrev eigSpace (T : H →L[ℝ] H) (μ : ℝ) :=
  Module.End.eigenspace (T : H →ₗ[ℝ] H) μ

def eigIndex (T : H →L[ℝ] H) (μ : ℝ) : Set (eigSpace T μ) :=
  Classical.choose (exists_hilbertBasis ℝ (eigSpace T μ))

def eigBasis (T : H →L[ℝ] H) (μ : ℝ) :
    HilbertBasis (eigIndex T μ) ℝ (eigSpace T μ) :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℝ (eigSpace T μ)))

abbrev Index (T : H →L[ℝ] H) := Σ μ : ℝ, eigIndex T μ

def eigVec (T : H →L[ℝ] H) (i : Index T) : H :=
  (eigBasis T i.1 i.2 : H)

theorem eigVec_eigen (T : H →L[ℝ] H) (i : Index T) :
    T (eigVec T i) = i.1 • eigVec T i := by
  exact Module.End.mem_eigenspace_iff.mp (eigBasis T i.1 i.2).property

theorem eigVec_orthonormal (T : H →L[ℝ] H)
    (hs : (T : H →ₗ[ℝ] H).IsSymmetric) :
    Orthonormal ℝ (eigVec T) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨μ,i⟩ ⟨ν,j⟩
  by_cases h : μ = ν
  · subst ν
    have he := (orthonormal_iff_ite.mp (eigBasis T μ).orthonormal) i j
    simpa [eigVec] using he
  · have ho := hs.orthogonalFamily_eigenspaces h (eigBasis T μ i) (eigBasis T ν j)
    simpa [eigVec,h] using ho

theorem eigVec_span_orthogonal (T : H →L[ℝ] H)
    (hc : IsCompactOperator (T : H → H))
    (hs : (T : H →ₗ[ℝ] H).IsSymmetric) :
    (Submodule.span ℝ (Set.range (eigVec T)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hall : x ∈ (⨆ μ : ℝ, eigSpace T μ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hz : ∀ μ : ℝ, eigSpace T μ ≤ (ℝ ∙ x)ᗮ := by
      intro μ z hz
      rw [Submodule.mem_orthogonal']
      intro v hv
      have hzx : inner ℝ z x = 0 := by
        let f := eigBasis T μ
        have hb := f.hasSum_repr (⟨z,hz⟩ : eigSpace T μ)
        have hmap := (eigSpace T μ).subtypeL.hasSum hb
        have hinner := (innerSL ℝ x).hasSum hmap
        have hzero : ∀ i : eigIndex T μ,
            inner ℝ x (eigVec T ⟨μ,i⟩) = 0 := by
          intro i
          rw [real_inner_comm]
          exact (Submodule.mem_orthogonal _ _).mp hx _
            (Submodule.subset_span ⟨⟨μ,i⟩,rfl⟩)
        have hsum : HasSum (fun _ : eigIndex T μ => (0:ℝ)) (inner ℝ x z) := by
          convert hinner using 1
          · funext i
            have hi : inner ℝ x (eigBasis T μ i : H) = 0 := hzero i
            simp [f, hi]
          · rfl
        rw [real_inner_comm]
        exact hsum.unique (hasSum_zero)
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [real_inner_smul_right,hzx,mul_zero]
    have hle : (⨆ μ : ℝ, eigSpace T μ) ≤ (ℝ ∙ x)ᗮ := iSup_le hz
    exact (Submodule.mem_orthogonal' _ _).mp (hle hy) x (Submodule.subset_span (by simp))
  rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] at hall
  exact hall

def spectralBasis (T : H →L[ℝ] H) (hc : IsCompactOperator (T : H → H))
    (hs : (T : H →ₗ[ℝ] H).IsSymmetric) : HilbertBasis (Index T) ℝ H :=
  HilbertBasis.mkOfOrthogonalEqBot (eigVec_orthonormal T hs)
    (eigVec_span_orthogonal T hc hs)

theorem spectralBasis_apply (T : H →L[ℝ] H) (hc : IsCompactOperator (T : H → H))
    (hs : (T : H →ₗ[ℝ] H).IsSymmetric) (i : Index T) :
    spectralBasis T hc hs i = eigVec T i := by
  simp [spectralBasis]

theorem gram_product_from_enumeration (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (ordinary : HilbertBasis ℕ ℝ H)
    (enumerate : Index (gramOperator a κ ha hk) ≃ ℕ) :
    ∃ (e : HilbertBasis ℕ ℝ H) (eig : ℕ → ℝ),
      (∀ i, gramOperator a κ ha hk (e i) = eig i • e i) ∧
      HasProd (fun i => 1 + eig i) (spectralDet eig) ∧
      1 < spectralDet eig ∧ spectralDet eig ≤ Real.exp (Real.pi/(4*a*κ)) := by
  let T := gramOperator a κ ha hk
  let v : ℕ → H := fun i => eigVec T (enumerate.symm i)
  have ho : Orthonormal ℝ v :=
    (eigVec_orthonormal T (gram_symmetric a κ ha hk)).comp enumerate.symm enumerate.symm.injective
  have hr : Set.range v = Set.range (eigVec T) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨enumerate.symm i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨enumerate i,by simp [v]⟩
  have ht : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [hr]
    exact eigVec_span_orthogonal T (gram_compact a κ ha hk ordinary) (gram_symmetric a κ ha hk)
  let e := HilbertBasis.mkOfOrthogonalEqBot ho ht
  let eig : ℕ → ℝ := fun i => (enumerate.symm i).1
  have he : ∀ i, T (e i) = eig i • e i := by
    intro i
    have hcoe : (e : ℕ → H) = v := HilbertBasis.coe_mkOfOrthogonalEqBot ho ht
    change T ((e : ℕ → H) i) = eig i • (e : ℕ → H) i
    rw [hcoe]
    exact eigVec_eigen T (enumerate.symm i)
  exact ⟨e,eig,he,gram_eigen_product a κ ha hk e eig he⟩

end
end Manuscript13.EllisFredholmClosure20261127
#print axioms Manuscript13.EllisFredholmClosure20261127.eigIndex
#print axioms Manuscript13.EllisFredholmClosure20261127.eigBasis
#print axioms Manuscript13.EllisFredholmClosure20261127.eigVec
#print axioms Manuscript13.EllisFredholmClosure20261127.eigVec_eigen
#print axioms Manuscript13.EllisFredholmClosure20261127.eigVec_orthonormal
#print axioms Manuscript13.EllisFredholmClosure20261127.eigVec_span_orthogonal
#print axioms Manuscript13.EllisFredholmClosure20261127.spectralBasis
#print axioms Manuscript13.EllisFredholmClosure20261127.spectralBasis_apply
#print axioms Manuscript13.EllisFredholmClosure20261127.gram_product_from_enumeration
