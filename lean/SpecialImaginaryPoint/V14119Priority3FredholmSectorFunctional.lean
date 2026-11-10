import SpecialImaginaryPoint.V14119Priority3PositiveDiagonalFredholm

/-!
# Manuscript 14.119 Priority 3 — a well-defined operator functional on
# the actual positive diagonal CFC S₁ sector

This module strengthens the preceding generic diagonal construction:
the Fredholm product is shown to be independent of the *Data witness*
representing an actual CFC trace-class operator. We therefore define
a genuine function whose argument is a trace-class OPERATOR belonging
to the image of the positive diagonal construction.

The infinite product is also invariant under permutations of the
spectral indices and admits the absolutely convergent finite-subset
Fredholm expansion. No unproved determinant axiom is used.

Scope is deliberately limited to the positive diagonal S₁ sector of
the fixed complex Hilbert basis. General unitary invariance, global
S₁ continuity, and the universal determinant on all S₁(H) remain open.
-/

noncomputable section
namespace Manuscript14Priority3.PositiveDiagonalFredholm
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- An actual S₁ operator uniquely determines its positive diagonal
coefficients within the diagonal sector. In particular, the sector
determinant does not depend on a chosen Data presentation. -/
theorem coeff_eq_of_S1_eq (D E : Data)
    (h : S1Diagonal D = S1Diagonal E) (n : ℕ) :
    D.coeff n = E.coeff n := by
  have hop : (S1Diagonal D).1 = (S1Diagonal E).1 :=
    congrArg Subtype.val h
  have hh := congrArg
    (fun A : H →L[ℂ] H => (inner ℂ (b n) (A (b n))).re) hop
  simpa only [S1Diagonal_operator_eq, boundedDiagonal_diagonal] using hh

theorem determinant_eq_of_S1_eq (D E : Data)
    (h : S1Diagonal D = S1Diagonal E) (t : ℝ) :
    determinant D t = determinant E t := by
  have hcoeff : D.coeff = E.coeff :=
    funext (coeff_eq_of_S1_eq D E h)
  simp only [determinant, hcoeff]

/-- The actual set of positive diagonal elements in the genuine
CFC-absolute Schatten S₁ Banach space of infinite Hilbert operators. -/
def sector : Set (ProbabilisticTheory.TraceClass H) :=
  Set.range S1Diagonal

/-- A genuine FUNCTION OF THE TRACE-CLASS OPERATOR on the positive
diagonal sector, rather than a scalar function of Dirichlet eigenvalues.
Independence of the chosen witness is certified below. -/
def determinantOnSector (T : sector) (t : ℝ) : ℝ :=
  determinant (Classical.choose T.property) t

/-- This operatorial determinant is exactly the arbitrary spectral
product for any presentation of the same true S₁ operator. -/
theorem determinantOnSector_eq (T : sector)
    (D : Data) (h : S1Diagonal D = T.val) (t : ℝ) :
    determinantOnSector T t = determinant D t := by
  unfold determinantOnSector
  apply determinant_eq_of_S1_eq
  exact (Classical.choose_spec T.property).trans h.symm

theorem determinantOnSector_ofData (D : Data) (t : ℝ) :
    determinantOnSector
      ⟨S1Diagonal D, ⟨D, rfl⟩⟩ t = determinant D t :=
  determinantOnSector_eq _ D rfl t

/-- Unconditional invariance of the infinite determinant product
under arbitrary permutations of the spectral coordinate labels.
This is reindexing invariance, not general Hilbert-unitary invariance. -/
def reindex (D : Data) (e : ℕ ≃ ℕ) : Data where
  coeff := D.coeff ∘ e
  nonneg n := D.nonneg (e n)
  summable := (e.summable_iff).2 D.summable

theorem determinant_reindex (D : Data) (e : ℕ ≃ ℕ) (t : ℝ) :
    determinant (reindex D e) t = determinant D t := by
  unfold determinant
  change (∏' n : ℕ, (1 + t * D.coeff (e n))) =
    (∏' n : ℕ, (1 + t * D.coeff n))
  exact e.tprod_eq (fun n : ℕ => 1 + t * D.coeff n)

/-- An actual Fredholm finite-subset expansion:
det(I+tT_a) = Σ_{s finite} ∏_{i∈s} (t a_i).
The coefficient series is absolutely summable because the diagonal
has the genuine S₁ finite total mass. -/
theorem determinant_eq_finite_subset_sum (D : Data) (t : ℝ) :
    determinant D t =
      ∑' s : Finset ℕ, ∏ i ∈ s, t * D.coeff i := by
  have hnorm : Summable (fun n : ℕ => ‖t * D.coeff n‖) := by
    have heq : (fun n : ℕ => ‖t * D.coeff n‖) =
        fun n : ℕ => |t| * D.coeff n := by
      funext n
      simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (D.nonneg n)]
    rw [heq]
    exact D.summable.mul_left |t|
  unfold determinant
  exact tprod_one_add (summable_finsetProd_of_summable_norm hnorm)

/-- The general operatorial sector determinant specializes EXACTLY to
the Dirichlet spectral product, without identifying either quantity
with the zeta-regularized determinant. -/
theorem dirichlet_determinant_eq_spectral (t : ℝ) :
    determinant dirichlet t =
      Manuscript14Priority3.spectralProduct t := by
  unfold determinant Manuscript14Priority3.spectralProduct
  apply tprod_congr
  intro n
  change 1 + t * σ n = Manuscript14Dirichlet.factor n t
  have hh := Manuscript14Priority3.OperatorCompression.factor_eq_real n t
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul] using hh

/-- The fully constructed operatorial sector functional takes the
certified Eulerian Dirichlet value at the actual S₁ inverse. -/
theorem dirichlet_determinantOnSector_sq (x : ℝ) (hx : x ≠ 0) :
    determinantOnSector
      ⟨S1Diagonal dirichlet, ⟨dirichlet, rfl⟩⟩ (x ^ 2) =
        Real.sinh x / x := by
  rw [determinantOnSector_ofData, dirichlet_determinant_eq_spectral]
  exact Manuscript14Priority3.spectralProduct_sq x hx

#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.coeff_eq_of_S1_eq
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinant_eq_of_S1_eq
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinantOnSector_eq
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinantOnSector_ofData
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinant_reindex
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.determinant_eq_finite_subset_sum
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.dirichlet_determinant_eq_spectral
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.dirichlet_determinantOnSector_sq

end Manuscript14Priority3.PositiveDiagonalFredholm
