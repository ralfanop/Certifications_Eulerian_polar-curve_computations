import SpecialImaginaryPoint.V14119Priority3ComplexDiagonalS1

/-!
# Manuscript 14.119 Priority 3 — complex operatorial diagonal Fredholm sector

For arbitrary absolutely summable COMPLEX spectral data, including
non-selfadjoint diagonal operators in the genuine CFC Schatten S₁
class, the finite compressed complex matrices have actual matrix
determinants converging to a complex infinite Fredholm product.

The product is shown to depend only on the underlying trace-class
operator, not on a chosen coefficient witness. It is also invariant
under permutations of the fixed basis indices.

This extends the positive real diagonal operatorial sector. It does
not assert invariance under arbitrary Hilbert-space unitary changes,
nor construct det_F on every non-diagonal trace-class operator.
-/

noncomputable section

namespace Manuscript14Priority3.ComplexDiagonalFredholm
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- Matrix of an actual infinite-dimensional, potentially
nonselfadjoint CFC S₁ Hilbert-space operator compressed to N basis
vectors. This is not a scalar-product surrogate. -/
def compressed (D : Data) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (b i.val) ((S1Diagonal D).1 (b j.val))

theorem compressed_eq_diagonal (D : Data) (N : ℕ) :
    compressed D N = Matrix.diagonal (fun i : Fin N => D.coeff i.val) := by
  ext i j
  change inner ℂ (b i.val) ((S1Diagonal D).1 (b j.val)) =
    Matrix.diagonal (fun k : Fin N => D.coeff k.val) i j
  rw [S1Diagonal_eigen D j.val, inner_smul_right]
  by_cases hij : i = j
  · subst j
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one i.val]
  · have hv : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    rw [b.orthonormal.inner_eq_zero hv]
    simp [Matrix.diagonal_apply, hij]

/-- Complex-shifted actual N-dimensional operator compression. -/
def finiteShift (D : Data) (N : ℕ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  1 + z • compressed D N

theorem finiteShift_eq_diagonal (D : Data) (N : ℕ) (z : ℂ) :
    finiteShift D N z =
      Matrix.diagonal (fun i : Fin N => 1 + z * D.coeff i.val) := by
  rw [finiteShift, compressed_eq_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, smul_eq_mul]
  · simp [Matrix.diagonal_apply, hij]

/-- Matrix determinant of the genuine compressed complex operator. -/
theorem finiteShift_det (D : Data) (N : ℕ) (z : ℂ) :
    Matrix.det (finiteShift D N z) =
      ∏ i : Fin N, (1 + z * D.coeff i.val) := by
  rw [finiteShift_eq_diagonal, Matrix.det_diagonal]

/-- General complex diagonal Fredholm product for absolute complex
summable data, defined independently of any Dirichlet eigenvalues. -/
def determinant (D : Data) (z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 + z * D.coeff n)

/-- Absolute summability of the non-selfadjoint S₁ spectral
coefficients establishes a genuinely convergent complex product. -/
theorem multipliable_factor (D : Data) (z : ℂ) :
    Multipliable (fun n : ℕ => 1 + z * D.coeff n) := by
  have hnorm : Summable (fun n : ℕ => ‖z * D.coeff n‖) := by
    have heq :
        (fun n : ℕ => ‖z * D.coeff n‖) =
          (fun n : ℕ => ‖z‖ * ‖D.coeff n‖) := by
      funext n
      exact norm_mul z (D.coeff n)
    rw [heq]
    exact D.summableNorm.mul_left ‖z‖
  exact multipliable_one_add_of_summable hnorm

/-- Genuine complex operator compressed determinants converge to
the complex S₁ diagonal Fredholm product. No positivity condition
is used, and the coupling z is any complex number. -/
theorem finiteShift_det_tendsto (D : Data) (z : ℂ) :
    Tendsto (fun N : ℕ => Matrix.det (finiteShift D N z))
      atTop (𝓝 (determinant D z)) := by
  have hprod :
      Tendsto
        (fun N : ℕ => ∏ n ∈ Finset.range N, (1 + z * D.coeff n))
        atTop (𝓝 (determinant D z)) := by
    simpa only [determinant] using
      ((multipliable_factor D z).hasProd_iff_tendsto_nat).mp
        (multipliable_factor D z).hasProd
  convert hprod using 1
  funext N
  simpa only [Finset.prod_range] using finiteShift_det D N z

/-- Two genuine S₁ complex diagonal operators which are equal have
identical complex spectral coefficients in the shared Hilbert basis. -/
theorem coeff_eq_of_S1_eq (D E : Data)
    (h : S1Diagonal D = S1Diagonal E) (n : ℕ) :
    D.coeff n = E.coeff n := by
  have hop : (S1Diagonal D).1 = (S1Diagonal E).1 :=
    congrArg Subtype.val h
  have hh := congrArg
    (fun A : H →L[ℂ] H => inner ℂ (b n) (A (b n))) hop
  have hD :
      inner ℂ (b n) ((S1Diagonal D).1 (b n)) = D.coeff n := by
    rw [S1Diagonal_eigen D n, inner_smul_right]
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one n]
  have hE :
      inner ℂ (b n) ((S1Diagonal E).1 (b n)) = E.coeff n := by
    rw [S1Diagonal_eigen E n, inner_smul_right]
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one n]
  exact hD.symm.trans (hh.trans hE)

/-- Well-definedness of the complex product at the level of the
actual trace-class operator rather than an arbitrary sequence witness. -/
theorem determinant_eq_of_S1_eq (D E : Data)
    (h : S1Diagonal D = S1Diagonal E) (z : ℂ) :
    determinant D z = determinant E z := by
  have heq : D.coeff = E.coeff :=
    funext (coeff_eq_of_S1_eq D E h)
  simp only [determinant, heq]

/-- The set of actual trace-class operators that are complex
diagonal with absolutely summable coefficients in the selected basis. -/
def sector : Set (ProbabilisticTheory.TraceClass H) :=
  Set.range S1Diagonal

/-- Complex determinant as an OPERATOR-ARGUMENT functional on the
nonpositive, non-selfadjoint complex diagonal Schatten S₁ sector. -/
def determinantOnSector (T : sector) (z : ℂ) : ℂ :=
  determinant (Classical.choose T.property) z

theorem determinantOnSector_eq (T : sector)
    (D : Data) (h : S1Diagonal D = T.val) (z : ℂ) :
    determinantOnSector T z = determinant D z := by
  unfold determinantOnSector
  apply determinant_eq_of_S1_eq
  exact (Classical.choose_spec T.property).trans h.symm

theorem determinantOnSector_ofData (D : Data) (z : ℂ) :
    determinantOnSector ⟨S1Diagonal D, ⟨D, rfl⟩⟩ z =
      determinant D z :=
  determinantOnSector_eq _ D rfl z

/-- Arbitrary permutation of spectral index labels does not change
the complex diagonal determinant, even for nonreal coefficients. -/
def reindex (D : Data) (e : ℕ ≃ ℕ) : Data where
  coeff := D.coeff ∘ e
  summableNorm := (e.summable_iff).2 D.summableNorm

theorem determinant_reindex (D : Data) (e : ℕ ≃ ℕ) (z : ℂ) :
    determinant (reindex D e) z = determinant D z := by
  unfold determinant
  change (∏' n : ℕ, (1 + z * D.coeff (e n))) =
    (∏' n : ℕ, (1 + z * D.coeff n))
  exact e.tprod_eq (fun n : ℕ => 1 + z * D.coeff n)

#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.compressed_eq_diagonal
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.finiteShift_det
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.multipliable_factor
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.finiteShift_det_tendsto
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.coeff_eq_of_S1_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.determinant_eq_of_S1_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.determinantOnSector_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.determinant_reindex

end Manuscript14Priority3.ComplexDiagonalFredholm
