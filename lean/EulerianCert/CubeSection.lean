/-
# V001 Lemma 3.14, Eq. (79), second equality: the cube section

With `D = n + 1` and `𝓗^{D−1}` the `(D−1)`-dimensional Hausdorff measure normalised to agree with
Euclidean volume on affine subspaces (Mathlib's `μHE`):
  `E(n, k−1)/n! = (1/√D) 𝓗^{D−1}([0,1]^D ∩ {x₁ + ⋯ + x_D = k})`.
The affine injection `T_k(x) = (k − ∑ x_j, x)` maps the slab of `CubeSlabs` onto the section;
its linear part is `J` (module `Combinatorics`, `JᵀJ = I + 𝟙𝟙ᵀ`, `det JᵀJ = n + 1`), so its
norm determinant is `√(n+1)` and Mathlib's area formula for linear maps
(`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`) gives the factor `√D`.
-/
import EulerianCert.CubeSlabs
import EulerianCert.Combinatorics
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open Real Finset MeasureTheory Set

noncomputable section

namespace EulerianCert.CubeSection

open EulerianCert.CubeSlabs

variable (n : ℕ)

/-- The linear part `J` of `T_k`, `x ↦ (−∑ x_j, x)`, as a map `ℝⁿ → ℝ^{n+1}` of Euclidean spaces. -/
def Lmap : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 (Fin.cons (-∑ j, x j) (fun j => x j))
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [Finset.sum_add_distrib]; ring
    · simp
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [Finset.mul_sum]
    · simp

lemma Lmap_zero (x : EuclideanSpace ℝ (Fin n)) : Lmap n x 0 = -∑ j, x j := rfl

lemma Lmap_succ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : Lmap n x i.succ = x i := rfl

lemma gram_eq :
    Matrix.gram ℝ (fun i => Lmap n (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      (EulerianCert.Combinatorics.J n).transpose * EulerianCert.Combinatorics.J n := by
  rw [EulerianCert.Combinatorics.JtJ]
  ext i j
  simp only [Matrix.gram, Matrix.of_apply, PiLp.inner_apply, Fin.sum_univ_succ, Lmap_zero,
    Lmap_succ, EuclideanSpace.basisFun_apply, Matrix.add_apply, Matrix.one_apply]
  simp [PiLp.single_apply, eq_comm]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `normDet J = √(n+1)`. -/
lemma normDet_Lmap : (Lmap n).normDet = √(n + 1) := by
  have h := (Lmap n).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [gram_eq, EulerianCert.Combinatorics.det_JtJ] at h
  have h' : (Lmap n).normDet ^ 2 = n + 1 := by exact_mod_cast h
  rw [← h', Real.sqrt_sq (LinearMap.normDet_nonneg _)]

/-- The section `[0,1]^{n+1} ∩ {∑ x = k}`. -/
def Sec (k : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {y | (∀ i, y i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, y i = k}

/-- The slab in Euclidean coordinates. -/
def SlabE (k : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ (k : ℝ) - 1 ≤ ∑ i, x i ∧ ∑ i, x i ≤ k}

/-- The translation part `k e₀` of `T_k`. -/
def v0 (k : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 (k : ℝ)

lemma v0_zero (k : ℕ) : v0 n k 0 = k := by simp [v0]

lemma v0_succ (k : ℕ) (i : Fin n) : v0 n k i.succ = 0 := by simp [v0, Fin.succ_ne_zero]

lemma Sec_eq (k : ℕ) : Sec n k = (fun y => y + v0 n k) '' (Lmap n '' SlabE n k) := by
  ext y
  simp only [Sec, SlabE, Set.mem_setOf_eq, Set.mem_image]
  have hsum : ∀ z : EuclideanSpace ℝ (Fin (n + 1)), ∑ i, z i = z 0 + ∑ j : Fin n, z j.succ :=
    fun z => Fin.sum_univ_succ _
  constructor
  · rintro ⟨hc, hs⟩
    set x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => y j.succ)
    have hx : ∀ j, x j = y j.succ := fun j => rfl
    rw [hsum] at hs
    refine ⟨Lmap n x, ⟨x, ⟨fun j => by rw [hx]; exact hc j.succ, ?_, ?_⟩, rfl⟩, ?_⟩
    · simp only [hx]; linarith [(hc 0).2]
    · simp only [hx]; linarith [(hc 0).1]
    · ext i
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [PiLp.add_apply, Lmap_zero, v0_zero]; simp only [hx]; linarith
      · rw [PiLp.add_apply, Lmap_succ, v0_succ, hx, add_zero]
  · rintro ⟨z, ⟨x, ⟨hc, h1, h2⟩, rfl⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i' => ?_) i
      · rw [PiLp.add_apply, Lmap_zero, v0_zero]; constructor <;> linarith
      · rw [PiLp.add_apply, Lmap_succ, v0_succ, add_zero]; exact hc i'
    · rw [hsum, PiLp.add_apply, Lmap_zero, v0_zero]
      simp only [PiLp.add_apply, Lmap_succ, v0_succ, add_zero]
      ring

lemma volume_SlabE (k : ℕ) : volume (SlabE n k) = volume (Slab n k) := by
  have := PiLp.volume_preserving_ofLp (ι := Fin n)
  rw [show SlabE n k = WithLp.ofLp ⁻¹' Slab n k from rfl, this.measure_preimage]
  · -- measurability of the slab
    have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
      rw [show {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} = ⋂ i, (fun x => x i) ⁻¹' Icc 0 1 by
        ext x; simp]
      exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (measurable_pi_apply i))
    have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
      Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
    exact (h1.inter ((measurableSet_le measurable_const hm).inter
      (measurableSet_le hm measurable_const))).nullMeasurableSet

/-- **Lemma 3.14, Eq. (79), second equality**: `𝓗^{D−1}(section) = √D · Vol_n(slab)`. -/
theorem hausdorff_section (k : ℕ) :
    μHE[n] (Sec n k) = ENNReal.ofReal (√(n + 1)) * volume (Slab n k) := by
  rw [Sec_eq, (isometry_add_right (v0 n k)).euclideanHausdorffMeasure_image,
    ← volume_SlabE, ← normDet_Lmap]
  have := (Lmap n).euclideanHausdorffMeasure_image_eq_normDet_mul_volume (SlabE n k)
  rwa [finrank_euclideanSpace_fin] at this

/-- **Lemma 3.14, Eq. (79)** in full: for `n ≥ 1`, `1 ≤ k`, with `D = n + 1`,
`Vol_n(slab) = E(n,k−1)/n! = (1/√D) 𝓗^{D−1}([0,1]^D ∩ {∑ x = k})`. -/
theorem eulerian_section {k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    volume (Slab n k) = ENNReal.ofReal ((EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial) ∧
    ENNReal.ofReal ((EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial) =
      ENNReal.ofReal (1 / √(n + 1)) * μHE[n] (Sec n k) := by
  have hv := volume_slab hn hk
  refine ⟨hv, ?_⟩
  rw [hausdorff_section, ← hv, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hs : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [one_div_mul_cancel hs.ne', ENNReal.ofReal_one, one_mul]

end EulerianCert.CubeSection
