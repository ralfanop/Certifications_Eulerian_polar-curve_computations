import Mathlib
import Manuscript13.EllisFredholmClosure20261127
open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option maxHeartbeats 2000000
namespace Manuscript13.EllisSpectralEnumeration20261127
noncomputable section
open Manuscript13.EllisGramKernelOperator20261124
open Manuscript13.EllisFredholmClosure20261127
open Manuscript13.EllisBirman20261124 (spectralDet)

theorem orthonormal_countable {ι : Type*} (v : ι → H) (hv : Orthonormal ℝ v) :
    Countable ι := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  haveI : SecondCountableTopology H := by infer_instance
  apply Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (v i) (1/2))
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hd : ‖v i - v j‖^2 = 2 := by
      rw [@norm_sub_sq ℝ]
      have ho := (orthonormal_iff_ite.mp hv) i j
      simp [hij] at ho
      rw [hv.norm_eq_one i, hv.norm_eq_one j, ho]
      norm_num
    have hlt : dist (v i) (v j) < 1 := by
      have hi := Metric.mem_ball.mp hxi
      have hj := Metric.mem_ball.mp hxj
      have h := dist_triangle (v i) x (v j)
      rw [dist_comm (v i) x] at h
      linarith
    rw [dist_eq_norm] at hlt
    nlinarith [norm_nonneg (v i - v j)]
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨v i, Metric.mem_ball_self (by norm_num)⟩

def intervalSet (n : ℕ) : Set ℝ := Ico (n : ℝ) ((n : ℝ)+1)

theorem interval_mass (n : ℕ) : volume (intervalSet n) = 1 := by
  rw [intervalSet, Real.volume_Ico]
  simp

def intervalVector (n : ℕ) : H :=
  indicatorConstLp 2 (s := intervalSet n) (by exact measurableSet_Ico) (by rw [interval_mass]; simp) (1 : ℝ)

theorem intervalVector_ae (n : ℕ) :
    (fun x => intervalVector n x) =ᵐ[volume] (intervalSet n).indicator (fun _ => (1:ℝ)) :=
  by unfold intervalVector; exact indicatorConstLp_coeFn

theorem interval_disjoint {i j : ℕ} (h : i ≠ j) :
    Disjoint (intervalSet i) (intervalSet j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hi' : (i : ℝ) ≤ x ∧ x < (i : ℝ)+1 := hi
  have hj' : (j : ℝ) ≤ x ∧ x < (j : ℝ)+1 := hj
  rcases lt_or_gt_of_ne h with hij | hji
  · have hle : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij)
    linarith
  · have hle : (j : ℝ)+1 ≤ (i : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hji)
    linarith

theorem interval_orthonormal : Orthonormal ℝ intervalVector := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [L2.inner_def]
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    calc
      _ = ∫ x : ℝ, (intervalSet i).indicator (fun _ => (1:ℝ)) x := by
        apply integral_congr_ae
        filter_upwards [intervalVector_ae i] with x hx
        rw [hx]
        by_cases h : x ∈ intervalSet i <;> simp [Set.indicator,h]
      _ = 1 := by
        have hm : MeasurableSet (intervalSet i) := measurableSet_Ico
        rw [integral_indicator hm, integral_const]
        change (volume (intervalSet i)).toReal = 1
        rw [interval_mass]
        norm_num
  · simp only [if_neg hij]
    calc
      _ = ∫ x : ℝ, (0:ℝ) := by
        apply integral_congr_ae
        filter_upwards [intervalVector_ae i, intervalVector_ae j] with x hx hy
        rw [hx,hy]
        by_cases h : x ∈ intervalSet i
        · have h' : x ∉ intervalSet j := fun hj => Set.disjoint_left.mp (interval_disjoint hij) h hj
          simp [Set.indicator,h,h']
        · simp [Set.indicator,h]
      _ = _ := integral_zero _ _

theorem not_finiteDimensional_H : ¬ FiniteDimensional ℝ H := by
  intro h
  letI : FiniteDimensional ℝ H := h
  have hh := interval_orthonormal.linearIndependent.lt_aleph0_of_finiteDimensional
  simpa using hh

theorem hilbertBasis_index_infinite {ι : Type*} (b : HilbertBasis ι ℝ H) : Infinite ι := by
  by_contra h
  have h : Finite ι := not_infinite_iff_finite.mp h
  letI : Finite ι := h
  letI : Fintype ι := Fintype.ofFinite ι
  apply not_finiteDimensional_H
  exact Module.Finite.of_basis b.toOrthonormalBasis.toBasis

def enumerateBasis {ι : Type*} (b : HilbertBasis ι ℝ H) : ι ≃ ℕ := by
  letI : Countable ι := orthonormal_countable b b.orthonormal
  letI : Infinite ι := hilbertBasis_index_infinite b
  letI : Encodable ι := Encodable.ofCountable ι
  first
  | exact (Denumerable.ofEncodableOfInfinite ι).eqv
  | exact Denumerable.eqv
  | exact Classical.choice (nonempty_equiv_of_countable (α := ι) (β := ℕ))
  | exact?

theorem ordinary_basis_exists : Nonempty (HilbertBasis ℕ ℝ H) := by
  obtain ⟨s,b,hb⟩ := exists_hilbertBasis ℝ H
  let q := enumerateBasis b
  let v : ℕ → H := fun i => b (q.symm i)
  have ho : Orthonormal ℝ v := b.orthonormal.comp q.symm q.symm.injective
  have hr : Set.range v = Set.range b := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨q.symm i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨q i,by simp [v]⟩
  have ht : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [hr]
    rw [← Submodule.orthogonal_closure, b.dense_span, Submodule.top_orthogonal_eq_bot]
  exact ⟨HilbertBasis.mkOfOrthogonalEqBot ho ht⟩

theorem gram_product_unconditional (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    ∃ (e : HilbertBasis ℕ ℝ H) (eig : ℕ → ℝ),
      (∀ i, gramOperator a κ ha hk (e i) = eig i • e i) ∧
      HasProd (fun i => 1 + eig i) (spectralDet eig) ∧
      1 < spectralDet eig ∧ spectralDet eig ≤ Real.exp (Real.pi/(4*a*κ)) := by
  let ordinary := Classical.choice ordinary_basis_exists
  let b := spectralBasis (gramOperator a κ ha hk)
    (Manuscript13.EllisCompactSpectrum20261127.gram_compact a κ ha hk ordinary)
    (Manuscript13.EllisCompactSpectrum20261127.gram_symmetric a κ ha hk)
  exact gram_product_from_enumeration a κ ha hk ordinary (enumerateBasis b)

end
end Manuscript13.EllisSpectralEnumeration20261127
#print axioms Manuscript13.EllisSpectralEnumeration20261127.orthonormal_countable
#print axioms Manuscript13.EllisSpectralEnumeration20261127.intervalSet
#print axioms Manuscript13.EllisSpectralEnumeration20261127.interval_mass
#print axioms Manuscript13.EllisSpectralEnumeration20261127.intervalVector
#print axioms Manuscript13.EllisSpectralEnumeration20261127.intervalVector_ae
#print axioms Manuscript13.EllisSpectralEnumeration20261127.interval_disjoint
#print axioms Manuscript13.EllisSpectralEnumeration20261127.interval_orthonormal
#print axioms Manuscript13.EllisSpectralEnumeration20261127.not_finiteDimensional_H
#print axioms Manuscript13.EllisSpectralEnumeration20261127.hilbertBasis_index_infinite
#print axioms Manuscript13.EllisSpectralEnumeration20261127.enumerateBasis
#print axioms Manuscript13.EllisSpectralEnumeration20261127.ordinary_basis_exists
#print axioms Manuscript13.EllisSpectralEnumeration20261127.gram_product_unconditional
